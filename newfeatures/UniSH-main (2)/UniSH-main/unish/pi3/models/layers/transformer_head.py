from .attention import FlashAttentionRope, FlashCrossAttentionRope
from .block import BlockRope, CrossBlockRope
from ..dinov2.layers import Mlp
import torch.nn as nn
from functools import partial
from torch.utils.checkpoint import checkpoint
import torch
import torch.nn.functional as F
from typing import *
import functools
import itertools

class TransformerDecoder(nn.Module):
    def __init__(
        self,
        in_dim,
        out_dim,
        dec_embed_dim=512,
        depth=5,
        dec_num_heads=8,
        mlp_ratio=4,
        rope=None,
        need_project=True,
        use_checkpoint=False,
        return_intermediate_layers=None,  # list of layer indices to return
    ):
        super().__init__()

        self.projects = nn.Linear(in_dim, dec_embed_dim) if need_project else nn.Identity()
        self.use_checkpoint = use_checkpoint
        self.return_intermediate_layers = return_intermediate_layers or []

        self.blocks = nn.ModuleList([
            BlockRope(
                dim=dec_embed_dim,
                num_heads=dec_num_heads,
                mlp_ratio=mlp_ratio,
                qkv_bias=True,
                proj_bias=True,
                ffn_bias=True,
                drop_path=0.0,
                norm_layer=partial(nn.LayerNorm, eps=1e-6),
                act_layer=nn.GELU,
                ffn_layer=Mlp,
                init_values=None,
                qk_norm=False,
                # attn_class=MemEffAttentionRope,
                attn_class=FlashAttentionRope,
                rope=rope
            ) for _ in range(depth)])

        self.linear_out = nn.Linear(dec_embed_dim, out_dim)

    def gradient_checkpointing_enable(self):
        """Enable gradient checkpointing for memory optimization."""
        self.use_checkpoint = True

    def forward(self, hidden, xpos=None):
        hidden = self.projects(hidden)
        intermediate_features = [hidden]
        
        for i, blk in enumerate(self.blocks):
            if self.use_checkpoint and self.training:
                hidden = checkpoint(blk, hidden, xpos=xpos, use_reentrant=False)
            else:
                hidden = blk(hidden, xpos=xpos)
            
            # Store intermediate features if requested
            if i in self.return_intermediate_layers:
                intermediate_features.append(hidden)
        
        out = self.linear_out(hidden)
        
        if self.return_intermediate_layers:
            return out, intermediate_features
        return out

class LinearPts3d (nn.Module):
    """ 
    Linear head for dust3r
    Each token outputs: - 16x16 3D points (+ confidence)
    """

    def __init__(self, patch_size, dec_embed_dim, output_dim=3,):
        super().__init__()
        self.patch_size = patch_size

        self.proj = nn.Linear(dec_embed_dim, (output_dim)*self.patch_size**2)

    def enable_gradient_checkpointing(self):
        """Enable gradient checkpointing for memory optimization."""
        # LinearPts3d is relatively simple, gradient checkpointing might not be necessary
        # but we provide this method for consistency
        pass

    def forward(self, decout, img_shape):
        H, W = img_shape
        tokens = decout[-1]
        B, S, D = tokens.shape

        # extract 3D points
        feat = self.proj(tokens)  # B,S,D
        feat = feat.transpose(-1, -2).view(B, -1, H//self.patch_size, W//self.patch_size)
        feat = F.pixel_shuffle(feat, self.patch_size)  # B,3,H,W

        # permute + norm depth
        return feat.permute(0, 2, 3, 1)
    

class ContextTransformerDecoder(nn.Module):
    def __init__(
        self,
        in_dim,
        out_dim,
        dec_embed_dim=512,
        depth=5,
        dec_num_heads=8,
        mlp_ratio=4,
        rope=None,
    ):
        super().__init__()

        self.projects_x = nn.Linear(in_dim, dec_embed_dim)
        self.projects_y = nn.Linear(in_dim, dec_embed_dim)

        self.blocks = nn.ModuleList([
            CrossBlockRope(
                dim=dec_embed_dim,
                num_heads=dec_num_heads,
                mlp_ratio=mlp_ratio,
                qkv_bias=True,
                proj_bias=True,
                ffn_bias=True,
                norm_layer=partial(nn.LayerNorm, eps=1e-6),
                act_layer=nn.GELU,
                ffn_layer=Mlp,
                init_values=None,
                qk_norm=False,
                # attn_class=MemEffAttentionRope, 
                # cross_attn_class=MemEffCrossAttentionRope,
                attn_class=FlashAttentionRope, 
                cross_attn_class=FlashCrossAttentionRope,
                rope=rope
            ) for _ in range(depth)])

        self.linear_out = nn.Linear(dec_embed_dim, out_dim)
        self.use_checkpoint = False

    def gradient_checkpointing_enable(self):
        """Enable gradient checkpointing for memory optimization."""
        self.use_checkpoint = True

    def forward(self, hidden, context, xpos=None, ypos=None):
        hidden = self.projects_x(hidden)
        context = self.projects_y(context)

        for i, blk in enumerate(self.blocks):
            if self.use_checkpoint and self.training:
                hidden = checkpoint(blk, hidden, context, xpos=xpos, ypos=ypos, use_reentrant=False)
            else:
                hidden = blk(hidden, context, xpos=xpos, ypos=ypos)

        out = self.linear_out(hidden)

        return out


def wrap_module_with_gradient_checkpointing(module: nn.Module):
    from torch.utils.checkpoint import checkpoint
    class _CheckpointingWrapper(module.__class__):
        _restore_cls = module.__class__
        def forward(self, *args, **kwargs):
            return checkpoint(super().forward, *args, use_reentrant=False, **kwargs)
        
    module.__class__ = _CheckpointingWrapper
    return module


class ResidualConvBlock(nn.Module):  
    def __init__(
        self, 
        in_channels: int, 
        out_channels: int = None, 
        hidden_channels: int = None, 
        kernel_size: int = 3, 
        padding_mode: str = 'replicate', 
        activation: Literal['relu', 'leaky_relu', 'silu', 'elu'] = 'relu', 
        in_norm: Literal['group_norm', 'layer_norm', 'instance_norm', 'none'] = 'layer_norm',
        hidden_norm: Literal['group_norm', 'layer_norm', 'instance_norm'] = 'group_norm',
    ):  
        super(ResidualConvBlock, self).__init__()  
        if out_channels is None:  
            out_channels = in_channels
        if hidden_channels is None:
            hidden_channels = in_channels

        if activation =='relu':
            activation_cls = nn.ReLU
        elif activation == 'leaky_relu':
            activation_cls = functools.partial(nn.LeakyReLU, negative_slope=0.2)
        elif activation =='silu':
            activation_cls = nn.SiLU
        elif activation == 'elu':
            activation_cls = nn.ELU
        else:
            raise ValueError(f'Unsupported activation function: {activation}')

        self.layers = nn.Sequential(
            nn.GroupNorm(in_channels // 32, in_channels) if in_norm == 'group_norm' else \
                nn.GroupNorm(1, in_channels) if in_norm == 'layer_norm' else \
                nn.InstanceNorm2d(in_channels) if in_norm == 'instance_norm' else \
                nn.Identity(),
            activation_cls(),
            nn.Conv2d(in_channels, hidden_channels, kernel_size=kernel_size, padding=kernel_size // 2, padding_mode=padding_mode),
            nn.GroupNorm(hidden_channels // 32, hidden_channels) if hidden_norm == 'group_norm' else \
                nn.GroupNorm(1, hidden_channels) if hidden_norm == 'layer_norm' else \
                nn.InstanceNorm2d(hidden_channels) if hidden_norm == 'instance_norm' else\
                nn.Identity(),
            activation_cls(),
            nn.Conv2d(hidden_channels, out_channels, kernel_size=kernel_size, padding=kernel_size // 2, padding_mode=padding_mode)
        )
        
        self.skip_connection = nn.Conv2d(in_channels, out_channels, kernel_size=1, padding=0) if in_channels != out_channels else nn.Identity()  
  
    def forward(self, x):  
        skip = self.skip_connection(x)  
        x = self.layers(x)
        x = x + skip
        return x  


class Resampler(nn.Sequential):
    def __init__(self, 
        in_channels: int, 
        out_channels: int, 
        type_: Literal['pixel_shuffle', 'nearest', 'bilinear', 'conv_transpose', 'pixel_unshuffle', 'avg_pool', 'max_pool'],
        scale_factor: int = 2, 
    ):
        if type_ == 'pixel_shuffle':
            nn.Sequential.__init__(self,
                nn.Conv2d(in_channels, out_channels * (scale_factor ** 2), kernel_size=3, stride=1, padding=1, padding_mode='replicate'),
                nn.PixelShuffle(scale_factor),
                nn.Conv2d(out_channels, out_channels, kernel_size=3, stride=1, padding=1, padding_mode='replicate')
            )
            for i in range(1, scale_factor ** 2):
                self[0].weight.data[i::scale_factor ** 2] = self[0].weight.data[0::scale_factor ** 2]
                self[0].bias.data[i::scale_factor ** 2] = self[0].bias.data[0::scale_factor ** 2]
        elif type_ in ['nearest', 'bilinear']:
            nn.Sequential.__init__(self,
                nn.Upsample(scale_factor=scale_factor, mode=type_, align_corners=False if type_ == 'bilinear' else None),
                nn.Conv2d(in_channels, out_channels, kernel_size=3, stride=1, padding=1, padding_mode='replicate')
            )
        elif type_ == 'conv_transpose':
            nn.Sequential.__init__(self,
                nn.ConvTranspose2d(in_channels, out_channels, kernel_size=scale_factor, stride=scale_factor),
                nn.Conv2d(out_channels, out_channels, kernel_size=3, stride=1, padding=1, padding_mode='replicate')
            )
            self[0].weight.data[:] = self[0].weight.data[:, :, :1, :1]
        elif type_ == 'pixel_unshuffle':
            nn.Sequential.__init__(self,
                nn.PixelUnshuffle(scale_factor),
                nn.Conv2d(in_channels * (scale_factor ** 2), out_channels, kernel_size=3, stride=1, padding=1, padding_mode='replicate')
            )
        elif type_ == 'avg_pool': 
            nn.Sequential.__init__(self,
                nn.Conv2d(in_channels, out_channels, kernel_size=3, stride=1, padding=1, padding_mode='replicate'),
                nn.AvgPool2d(kernel_size=scale_factor, stride=scale_factor),
            )
        elif type_ == 'max_pool':
            nn.Sequential.__init__(self,
                nn.Conv2d(in_channels, out_channels, kernel_size=3, stride=1, padding=1, padding_mode='replicate'),
                nn.MaxPool2d(kernel_size=scale_factor, stride=scale_factor),
            )
        else:
            raise ValueError(f'Unsupported resampler type: {type_}')
        

class ConvStack(nn.Module):
    def __init__(self, 
        dim_in: List[Optional[int]],
        dim_res_blocks: List[int],
        dim_out: List[Optional[int]],
        resamplers: Union[Literal['pixel_shuffle', 'nearest', 'bilinear', 'conv_transpose', 'pixel_unshuffle', 'avg_pool', 'max_pool'], List],
        dim_times_res_block_hidden: int = 1,
        num_res_blocks: int = 1,
        res_block_in_norm: Literal['layer_norm', 'group_norm' , 'instance_norm', 'none'] = 'layer_norm',
        res_block_hidden_norm: Literal['layer_norm', 'group_norm' , 'instance_norm', 'none'] = 'group_norm',
        activation: Literal['relu', 'leaky_relu', 'silu', 'elu'] = 'relu',
    ):
        super().__init__()
        self.input_blocks = nn.ModuleList([
            nn.Conv2d(dim_in_, dim_res_block_, kernel_size=1, stride=1, padding=0) if dim_in_ is not None else nn.Identity() 
                for dim_in_, dim_res_block_ in zip(dim_in if isinstance(dim_in, Sequence) else itertools.repeat(dim_in), dim_res_blocks)
        ])
        self.resamplers = nn.ModuleList([
            Resampler(dim_prev, dim_succ, scale_factor=2, type_=resampler) 
                for i, (dim_prev, dim_succ, resampler) in enumerate(zip(
                    dim_res_blocks[:-1], 
                    dim_res_blocks[1:], 
                    resamplers if isinstance(resamplers, Sequence) else itertools.repeat(resamplers)
                ))
        ])
        self.res_blocks = nn.ModuleList([
            nn.Sequential(
                *(
                    ResidualConvBlock(
                        dim_res_block_, dim_res_block_, dim_times_res_block_hidden * dim_res_block_, 
                        activation=activation, in_norm=res_block_in_norm, hidden_norm=res_block_hidden_norm
                    ) for _ in range(num_res_blocks[i] if isinstance(num_res_blocks, list) else num_res_blocks)
                )
            ) for i, dim_res_block_ in enumerate(dim_res_blocks)
        ])
        self.output_blocks = nn.ModuleList([
            nn.Conv2d(dim_res_block_, dim_out_, kernel_size=1, stride=1, padding=0) if dim_out_ is not None else nn.Identity() 
                for dim_out_, dim_res_block_ in zip(dim_out if isinstance(dim_out, Sequence) else itertools.repeat(dim_out), dim_res_blocks)
        ])

    def enable_gradient_checkpointing(self):
        for i in range(len(self.resamplers)):
            self.resamplers[i] = wrap_module_with_gradient_checkpointing(self.resamplers[i])
        for i in range(len(self.res_blocks)):
            for j in range(len(self.res_blocks[i])):
                self.res_blocks[i][j] = wrap_module_with_gradient_checkpointing(self.res_blocks[i][j])

    def forward(self, in_features: List[torch.Tensor]):
        out_features = []
        for i in range(len(self.res_blocks)):
            feature = self.input_blocks[i](in_features[i])
            if i == 0:
                x = feature
            elif feature is not None:
                x = x + feature
            x = self.res_blocks[i](x)
            out_features.append(self.output_blocks[i](x))
            if i < len(self.res_blocks) - 1:
                x = self.resamplers[i](x)
        return out_features