import torch
import torch.nn as nn
import torch.nn.functional as F
from functools import partial
from copy import deepcopy
import itertools

from .dinov2.layers import Mlp
from ..utils.geometry import homogenize_points, se3_inverse
from .layers.pos_embed import RoPE2D, PositionGetter
from .layers.block import BlockRope
from .layers.attention import FlashAttentionRope
from .layers.transformer_head import TransformerDecoder, LinearPts3d, ConvStack
from .layers.camera_head import CameraHead
from ...heads.dpt_head import DPTHead
from .dinov2.hub.backbones import dinov2_vitl14, dinov2_vitl14_reg
from huggingface_hub import PyTorchModelHubMixin

class Pi3(nn.Module, PyTorchModelHubMixin):
    def __init__(
            self,
            pos_type='rope100',
            decoder_size='large',
        ):
        super().__init__()

        # ----------------------
        #        Encoder
        # ----------------------
        self.encoder = dinov2_vitl14_reg(pretrained=False)
        self.patch_size = 14
        del self.encoder.mask_token

        # ----------------------
        #  Positonal Encoding
        # ----------------------
        self.pos_type = pos_type if pos_type is not None else 'none'
        self.rope=None
        if self.pos_type.startswith('rope'): # eg rope100 
            if RoPE2D is None: raise ImportError("Cannot find cuRoPE2D, please install it following the README instructions")
            freq = float(self.pos_type[len('rope'):])
            self.rope = RoPE2D(freq=freq)
            self.position_getter = PositionGetter()
        else:
            raise NotImplementedError
        

        # ----------------------
        #        Decoder
        # ----------------------
        enc_embed_dim = self.encoder.blocks[0].attn.qkv.in_features        # 1024
        if decoder_size == 'small':
            dec_embed_dim = 384
            dec_num_heads = 6
            mlp_ratio = 4
            dec_depth = 24
        elif decoder_size == 'base':
            dec_embed_dim = 768
            dec_num_heads = 12
            mlp_ratio = 4
            dec_depth = 24
        elif decoder_size == 'large':
            dec_embed_dim = 1024
            dec_num_heads = 16
            mlp_ratio = 4
            dec_depth = 36
        else:
            raise NotImplementedError
        self.decoder = nn.ModuleList([
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
                init_values=0.01,
                qk_norm=True,
                attn_class=FlashAttentionRope,
                rope=self.rope
            ) for _ in range(dec_depth)])
        self.dec_embed_dim = dec_embed_dim

        # ----------------------
        #     Register_token
        # ----------------------
        num_register_tokens = 5
        self.patch_start_idx = num_register_tokens
        self.register_token = nn.Parameter(torch.randn(1, 1, num_register_tokens, self.dec_embed_dim))
        nn.init.normal_(self.register_token, std=1e-6)

        # ----------------------
        #  Local Points Decoder
        # ----------------------
        self.point_decoder = TransformerDecoder(
            in_dim=2*self.dec_embed_dim, 
            dec_embed_dim=1024,
            dec_num_heads=16,
            out_dim=1024,
            rope=self.rope,
            return_intermediate_layers=[0, 2, 4],  # layers 1, 3, 5 (0-indexed)
        )
        # DPTHead for multi-scale point prediction
        self.point_head = LinearPts3d(patch_size=14, dec_embed_dim=1024, output_dim=3)
        # self.point_head_2 = DPTHead(
        #     dim_in=self.dec_embed_dim,  # input dimension from decoder
        #     patch_size=14,
        #     output_dim=4,  # 3D points + 1 dummy channel (we'll ignore confidence)
        #     activation="linear",  # linear activation for raw 3D coordinates
        #     conf_activation="expp1",  # for the dummy confidence channel
        #     intermediate_layer_idx=[0, 1, 2, 3],  # use input + 3 intermediate layers
        # )
        
        # # Zero-initialize point_head_2 for ControlNet-like behavior
        # self._zero_init_point_head_2()

        # ----------------------
        #     Conf Decoder
        # ----------------------
        self.conf_decoder = deepcopy(self.point_decoder)
        self.conf_head = LinearPts3d(patch_size=14, dec_embed_dim=1024, output_dim=1)

        # ----------------------
        #  Camera Pose Decoder
        # ----------------------
        self.camera_decoder = TransformerDecoder(
            in_dim=2*self.dec_embed_dim, 
            dec_embed_dim=1024,
            dec_num_heads=16,                # 8
            out_dim=512,
            rope=self.rope,
            use_checkpoint=False
        )
        self.camera_head = CameraHead(dim=512)

        # For ImageNet Normalize
        image_mean = torch.tensor([0.485, 0.456, 0.406]).view(1, 3, 1, 1)
        image_std = torch.tensor([0.229, 0.224, 0.225]).view(1, 3, 1, 1)

        self.register_buffer("image_mean", image_mean)
        self.register_buffer("image_std", image_std)

    def gradient_checkpointing_enable(self):
        """Enable gradient checkpointing for memory optimization."""
        # Enable gradient checkpointing for encoder (DinoV2)
        if hasattr(self.encoder, 'gradient_checkpointing_enable'):
            self.encoder.gradient_checkpointing_enable()
        
        # Enable gradient checkpointing for decoder blocks
        from torch.utils.checkpoint import checkpoint
        from .layers.transformer_head import wrap_module_with_gradient_checkpointing
        for i, block in enumerate(self.decoder):
            self.decoder[i] = wrap_module_with_gradient_checkpointing(block)
        
        # Enable gradient checkpointing for transformer decoders
        if hasattr(self.point_decoder, 'gradient_checkpointing_enable'):
            self.point_decoder.gradient_checkpointing_enable()
        if hasattr(self.conf_decoder, 'gradient_checkpointing_enable'):
            self.conf_decoder.gradient_checkpointing_enable()
        if hasattr(self.camera_decoder, 'gradient_checkpointing_enable'):
            self.camera_decoder.gradient_checkpointing_enable()
        
        # Enable gradient checkpointing for heads that support it
        if hasattr(self.point_head, 'enable_gradient_checkpointing'):
            self.point_head.enable_gradient_checkpointing()
        if hasattr(self.conf_head, 'enable_gradient_checkpointing'):
            self.conf_head.enable_gradient_checkpointing()

    def _zero_init_point_head_2(self):
        """
        Zero-initialize the final output layer of point_head_2 for ControlNet-like behavior.
        This ensures that point_head_2 outputs zero initially and doesn't affect the original model.
        """
        # Zero-initialize the final output convolution layer
        final_conv = self.point_head_2.scratch.output_conv2[-1]  # Last Conv2d layer
        nn.init.zeros_(final_conv.weight)
        if final_conv.bias is not None:
            nn.init.zeros_(final_conv.bias)
        
        # Optionally, also zero-initialize the output convolution layers in fusion blocks
        # This provides additional stability during early training
        for refinenet in [self.point_head_2.scratch.refinenet1, 
                         self.point_head_2.scratch.refinenet2,
                         self.point_head_2.scratch.refinenet3,
                         self.point_head_2.scratch.refinenet4]:
            if hasattr(refinenet, 'out_conv'):
                nn.init.zeros_(refinenet.out_conv.weight)
                if refinenet.out_conv.bias is not None:
                    nn.init.zeros_(refinenet.out_conv.bias)

    def decode(self, hidden, N, H, W):
        BN, hw, _ = hidden.shape
        B = BN // N

        final_output = []
        
        hidden = hidden.reshape(B*N, hw, -1)

        register_token = self.register_token.repeat(B, N, 1, 1).reshape(B*N, *self.register_token.shape[-2:])

        # Concatenate special tokens with patch tokens
        hidden = torch.cat([register_token, hidden], dim=1)
        hw = hidden.shape[1]

        if self.pos_type.startswith('rope'):
            pos = self.position_getter(B * N, H//self.patch_size, W//self.patch_size, hidden.device)

        if self.patch_start_idx > 0:
            # do not use position embedding for special tokens (camera and register tokens)
            # so set pos to 0 for the special tokens
            pos = pos + 1
            pos_special = torch.zeros(B * N, self.patch_start_idx, 2).to(hidden.device).to(pos.dtype)
            pos = torch.cat([pos_special, pos], dim=1)
       
        for i in range(len(self.decoder)):
            blk = self.decoder[i]

            if i % 2 == 0:
                pos = pos.reshape(B*N, hw, -1)
                hidden = hidden.reshape(B*N, hw, -1)
            else:
                pos = pos.reshape(B, N*hw, -1)
                hidden = hidden.reshape(B, N*hw, -1)

            hidden = blk(hidden, xpos=pos)

            if i+1 in [len(self.decoder)-1, len(self.decoder)]:
                final_output.append(hidden.reshape(B*N, hw, -1))

        return torch.cat([final_output[0], final_output[1]], dim=-1), pos.reshape(B*N, hw, -1)
    
    def forward(self, imgs):
        imgs = (imgs - self.image_mean) / self.image_std

        B, N, _, H, W = imgs.shape
        patch_h, patch_w = H // 14, W // 14
        
        # encode by dinov2
        imgs = imgs.reshape(B*N, _, H, W).to(torch.bfloat16)
        encoder_output = self.encoder(imgs, is_training=True)

        if isinstance(encoder_output, dict):
            hidden = encoder_output["x_norm_patchtokens"]
        else:
            hidden = encoder_output

        hidden, pos = self.decode(hidden, N, H, W)

        point_hidden, point_intermediates = self.point_decoder(hidden, xpos=pos)
        conf_hidden, _ = self.conf_decoder(hidden, xpos=pos)  # ignore intermediate features for conf
        camera_hidden = self.camera_decoder(hidden, xpos=pos)

        with torch.amp.autocast(device_type='cuda', enabled=False, dtype=torch.float32):
            # local points - prepare aggregated tokens list for DPTHead
            point_hidden = point_hidden.float()
            self.point_head.to(torch.float32)
            self.conf_head.to(torch.float32)
            self.camera_head.to(torch.float32)
            
            # Prepare aggregated_tokens_list: [input, intermediate_layer_1, intermediate_layer_3, intermediate_layer_5]
            # Reshape to [B, N, num_patches, dim] format expected by DPTHead
            # patch_h, patch_w = H // self.patch_size, W // self.patch_size
                        
            # # Intermediate tokens from point_decoder (layers 1, 3, 5)
            # for i, feat in enumerate(point_intermediates):
            #     point_intermediates[i] = feat.reshape(B, N, -1, feat.shape[-1])  # [B, N, hw+register, dim]
            
            # # Create fake images tensor with correct shape for DPTHead
            # fake_images = torch.zeros(B, N, 3, H, W, device=hidden.device, dtype=torch.float32)            

            # # Call DPTHead
            # dpt_output, dpt_conf = self.point_head_2(
            #     aggregated_tokens_list=point_intermediates,
            #     images=fake_images,
            #     patch_start_idx=self.patch_start_idx
            # )
            
            # # dpt_output shape: [B, N, H, W, 4] (3D points + 1 dummy confidence)
            # # We only use the first 3 channels for 3D points, ignore the 4th channel
            # res= dpt_output[..., :3]  # [B, N, H, W, 3]

            # # Apply depth processing similar to original code
            # xy, z = local_points_raw.split([2, 1], dim=-1)

            ret = self.point_head([point_hidden[:, self.patch_start_idx:]], (H, W)).reshape(B, N, H, W, -1)
            # ret += res
            xy, z = ret.split([2, 1], dim=-1)
            z = torch.exp(z)
            local_points = torch.cat([xy * z, z], dim=-1)

            # confidence
            conf_hidden = conf_hidden.float()
            conf = self.conf_head([conf_hidden[:, self.patch_start_idx:]], (H, W)).reshape(B, N, H, W, -1)

            # camera
            camera_hidden = camera_hidden.float()
            camera_poses = self.camera_head(camera_hidden[:, self.patch_start_idx:], patch_h, patch_w).reshape(B, N, 4, 4)

            # transform to first frame camera coordinate
            w2c_target = se3_inverse(camera_poses[:, 0])
            # gt_pts = torch.einsum('bij, bnhwj -> bnhwi', w2c_target, homogenize_points(gt_pts))[..., :3]
            camera_poses_cano = torch.einsum('bij, bnjk -> bnik', w2c_target, camera_poses)

            # unproject local points using camera poses
            points_cano = torch.einsum('bnij, bnhwj -> bnhwi', camera_poses_cano, homogenize_points(local_points))[..., :3]


        return dict(
            world_points=points_cano,
            local_points=local_points,
            point_conf=conf,  # only from original conf_head
            c2ws=camera_poses,
            c2ws_cano=camera_poses_cano,
            hidden=hidden,
        )
