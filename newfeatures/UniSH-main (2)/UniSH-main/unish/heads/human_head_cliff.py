import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np
import einops


from unish.utils.data_utils import rot6d_to_rotmat
from unish.utils.constants import SMPL_MEAN_PARAMS
from .pose_transformer import TransformerDecoder

TRANSFORMER_DECODER={'depth': 6,
                    'heads': 8,
                    'mlp_dim': 1024,
                    'dim_head': 64,
                    'dropout': 0.0,
                    'emb_dropout': 0.0,
                    'norm': 'layer',
                    'context_dim': 1280}

NUM_POSE_INPUT = 23
NUM_BETAS_INPUT = 10
NUM_BETAS = 10
NUM_POSE_PARAMS = 23

class HumanHeadCliff(nn.Module):

    def __init__(self):
        super().__init__()
        self.joint_rep_dim = 6
        npose = self.joint_rep_dim * (NUM_POSE_INPUT + 1)
        self.npose = npose
        transformer_args = dict(
            num_tokens=1,
            token_dim=(3 + npose + NUM_BETAS_INPUT + 3),
            dim=1024,
        )
        transformer_args = (transformer_args | dict(TRANSFORMER_DECODER))
        self.transformer = TransformerDecoder(
            **transformer_args
        )
        dim=transformer_args['dim']
        self.decpose = nn.Linear(dim, self.joint_rep_dim * (NUM_POSE_PARAMS + 1))
        self.decshape = nn.Linear(dim, NUM_BETAS)
        # self.deccam = nn.Linear(dim, 3)
        # self.deckp = nn.Linear(dim, 88)

        mean_params = SMPL_MEAN_PARAMS
        init_body_pose = torch.from_numpy(mean_params['pose'].astype(np.float32)).unsqueeze(0)
        init_betas = torch.from_numpy(mean_params['shape'].astype('float32')).unsqueeze(0)
        init_cam = torch.from_numpy(mean_params['cam'].astype(np.float32)).unsqueeze(0)
        self.register_buffer('init_body_pose', init_body_pose)
        self.register_buffer('init_betas', init_betas)
        self.register_buffer('init_cam', init_cam)

    def gradient_checkpointing_enable(self):
        """Enable gradient checkpointing for memory optimization."""
        if hasattr(self.transformer, 'gradient_checkpointing_enable'):
            self.transformer.gradient_checkpointing_enable()

    def forward(self, x, bbox_info, **kwargs):
        """
        x: (B, N, C, H, W)
        bbox_info: [cx / f, cy / f, box_size / f], (B, N, 3)
        """

        batch_size, num_views = x.shape[:2]
        x = einops.rearrange(x, 'b n c h w -> (b n) (h w) c')

        init_body_pose = self.init_body_pose.expand(batch_size * num_views, -1)
        init_betas = self.init_betas.expand(batch_size * num_views, -1)
        init_cam = self.init_cam.expand(batch_size * num_views, -1)
        bbox_info = bbox_info.view(-1, 3)

        pred_body_pose = init_body_pose
        pred_betas = init_betas
        pred_cam = init_cam
        token = torch.cat([bbox_info, pred_body_pose, pred_betas, pred_cam], dim=-1)[:, None, :]

        # Pass through transformer
        token_out = self.transformer(token, context=x)
        token_out = token_out.squeeze(1) # (B, C)

        pred_body_pose = self.decpose(token_out) + pred_body_pose
        pred_betas = self.decshape(token_out) + pred_betas

        joint_conversion_fn = rot6d_to_rotmat

        pred_body_pose = pred_body_pose.view(-1, 6)
        pred_body_pose = joint_conversion_fn(pred_body_pose).view(batch_size, num_views, -1)
        pred_betas = pred_betas.view(batch_size, num_views, -1).mean(dim=1)
        token_out = token_out.view(batch_size, num_views, -1)

        pred_smpl_params = {'pose_cam': pred_body_pose,
                            'token_out': token_out,
                            'betas': pred_betas}
        return pred_smpl_params
