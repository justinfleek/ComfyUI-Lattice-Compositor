import torch
import torch.nn as nn
import logging
from huggingface_hub import PyTorchModelHubMixin

from unish.pi3.models.pi3 import Pi3
from unish.heads.vit import vit
from unish.heads.human_head_cliff import HumanHeadCliff
from unish.heads.align_net import AlignNet
from unish.utils.data_utils import rotmat_to_aa, depth_to_points
from unish.utils.smpl_utils import transform_smpl
from unish.pi3.utils.geometry import recover_focal_shift, se3_inverse
import utils3d

logger = logging.getLogger(__name__)

class UniSHPipeline(nn.Module, PyTorchModelHubMixin):
    def __init__(self, dtype='float32'):
        super().__init__()
        self.pi3 = Pi3()

        self.human_head = HumanHeadCliff()
        self.alignnet = AlignNet()
        self.backbone = vit()
        
    def get_human_prediction(self, human_patches, bbox_info):
        b, s, c, h, w = human_patches.shape
        human_patches = human_patches.reshape(b * s, c, h, w)
        features = self.backbone(human_patches[..., 32:-32])
        _, c, h_patch, w_patch = features.shape
        features = features.reshape(b, s, c, h_patch, w_patch).float()
        smpl_feats = self.human_head(features, bbox_info)
        return smpl_feats
    
    def get_normalize_factor(self, local_points, masks):
        B, N, H, W, _ = local_points.shape

        # normalize predict points
        all_pts = local_points.clone()
        all_pts[~masks] = 0
        all_pts = all_pts.reshape(B, N, -1, 3)
        all_dis = all_pts.norm(dim=-1)
        norm_factor = all_dis.sum(dim=[-1, -2]) / (masks.float().sum(dim=[-1, -2, -3]) + 1e-8)

        return norm_factor.view(B)

    def scale_predictions(self, predictions, scale):

        batch_size, num_views = predictions["world_points"].shape[:2]

        norm_factor = self.get_normalize_factor(predictions["local_points"], predictions["masks"])
        # Ensure scale has the correct shape [batch_size] for element-wise division
        scale = scale.squeeze(-1)  # [batch, 1] -> [batch]
        scale /= norm_factor # (batch_size)
        predictions["world_points"] *= scale.view(batch_size, 1, 1, 1, 1)
        predictions["local_points"] *= scale.view(batch_size, 1, 1, 1, 1)
        predictions["c2ws"][:, :, :3, 3] *= scale.view(batch_size, 1, 1)
        predictions["c2ws_cano"][:, :, :3, 3] *= scale.view(batch_size, 1, 1)
        predictions["w2cs_cano"] = se3_inverse(predictions["c2ws_cano"])
        predictions["trans_cam"] *= scale.view(batch_size, 1, 1)
        predictions["trans_world"] *= scale.view(batch_size, 1, 1)

        return predictions, scale
    
    def get_depth_intrinsic_shift(self, predictions):

        points = predictions["local_points"]
        masks = predictions["masks"]

        with torch.autocast(device_type='cuda', enabled=False, dtype=torch.float32):
            points = points.to(torch.float32)
            focal, shift = recover_focal_shift(points, masks)
            
            original_height, original_width = points.shape[-3:-1]
            aspect_ratio = original_width / original_height
            fx, fy = focal / 2 * (1 + aspect_ratio ** 2) ** 0.5 / aspect_ratio, focal / 2 * (1 + aspect_ratio ** 2) ** 0.5 
            
            # Ensure all inputs are on the same device for utils3d
            device = points.device
            cx_norm = torch.tensor(0.5, device=device)
            cy_norm = torch.tensor(0.5, device=device)
            cx = torch.tensor(original_width / 2.0, device=device)
            cy = torch.tensor(original_height / 2.0, device=device)
            
            intrinsics_normed = utils3d.torch.intrinsics_from_focal_center(fx, fy, cx_norm, cy_norm)
            intrinsics = utils3d.torch.intrinsics_from_focal_center(fx * original_width, fy * original_height, cx, cy)
            shifted_points = points.clone()
            shifted_points[..., 2] += shift[..., None, None]
            masks &= shifted_points[..., 2] > 0        # in case depth is contains negative values (which should never happen in practice)
            depth = shifted_points[..., 2].clone()
        
        return depth, intrinsics, intrinsics_normed, shift

    def forward(self, batch):
        batch_size, num_views = batch["images"].shape[:2]
        geometry_results = self.pi3(batch["images"])

        with torch.amp.autocast(device_type='cuda', enabled=False, dtype=torch.float32):

            for k, v in geometry_results.items():
                if isinstance(v, torch.Tensor):
                    geometry_results[k] = v.to(torch.float32)

            # Predict Cameras
            c2ws_cano = geometry_results["c2ws_cano"] # (B, S, 4, 4)
            w2cs_cano = se3_inverse(c2ws_cano)
            geometry_results["point_conf"] = torch.sigmoid(geometry_results["point_conf"])
            masks = geometry_results["point_conf"] > 0.1

            # Predict SMPL
            self.human_head.to(torch.float32)
            
            human_predict = self.get_human_prediction(batch["human_patches"], batch["bbox_info"])

            if isinstance(human_predict, dict):
                cam_token = human_predict["token_out"].view(batch_size, num_views, 1, 1024)
            else:
                cam_token = human_predict.view(batch_size, num_views, 1, 1024)
            
            # predict scale and smpl z-trans
            hidden = geometry_results["hidden"].view(batch_size, num_views, -1, geometry_results["hidden"].shape[-1]) # [1, 10, 782, 2048]
            self.alignnet.to(torch.float32)
            align_results = self.alignnet(hidden, cam_token)
            pred_scale = align_results["scale"] # [1]

            if isinstance(human_predict, dict):
                align_results["betas"] = human_predict["betas"]
                align_results["pose_cam"] = human_predict["pose_cam"]

            align_results_world = transform_smpl(align_results, w2cs_cano, copy_dict=True)

        ret_dict = {
            "pose_world": align_results_world["pose_world"], # [B, S, 72]
            "trans_world": align_results_world["trans_world"], # [B, S, 3]
            "pose_cam": align_results["pose_cam"], # [B, S, 72]
            "trans_cam": align_results["trans_cam"], # [B, S, 3]
            "betas": align_results["betas"], # [B, S, 10]
            "world_points": geometry_results["world_points"], # [B, S, H, W, 3]
            "local_points": geometry_results["local_points"], # [B, S, H, W, 3]
            "point_conf": geometry_results["point_conf"].squeeze(-1), # [B, S, H, W]
            "c2ws": geometry_results["c2ws"], # [B, S, 4, 4]
            "c2ws_cano": geometry_results["c2ws_cano"], # [B, S, 4, 4]
            "scale": pred_scale, # [B]
            "w2cs_cano": w2cs_cano, # [B, S, 4, 4]
            "masks": masks.squeeze(-1), # [B, S, H, W]
        }

        return ret_dict
    
    def inference(self, batch):
        batch_size, num_views = batch["images"].shape[:2]
        geometry_results = self.pi3(batch["images"])

        with torch.amp.autocast(device_type='cuda', enabled=False, dtype=torch.float32):

            for k, v in geometry_results.items():
                if isinstance(v, torch.Tensor):
                    geometry_results[k] = v.to(torch.float32)

            # Predict Cameras
            c2ws_cano = geometry_results["c2ws_cano"] # (B, S, 4, 4)
            w2cs_cano = se3_inverse(c2ws_cano)
            geometry_results["point_conf"] = torch.sigmoid(geometry_results["point_conf"])
            masks = geometry_results["point_conf"] > 0.1
            geometry_results["masks"] = masks.squeeze(-1)

            _, pred_intrinsics, _, _ = self.get_depth_intrinsic_shift(geometry_results)
            
            # Predict SMPL
            self.human_head.to(torch.float32)

            bbox_info = batch["bbox_info"]

            if "intrinsics" in batch:
                intrinsics_gt = batch["intrinsics"]
                focal_gt = (intrinsics_gt[..., 0, 0] + intrinsics_gt[..., 1, 1]) / 2
                focal_pred = (pred_intrinsics[..., 0, 0] + pred_intrinsics[..., 1, 1]) / 2
                focal_gt = focal_gt.view(batch_size, -1, 1).to(bbox_info)
                focal_pred = focal_pred.view(batch_size, -1, 1).to(bbox_info)
                bbox_info = bbox_info * focal_gt / focal_pred
            else:
                intrinsics = pred_intrinsics
                focal = (intrinsics[..., 0, 0] + intrinsics[..., 1, 1]) / 2
                focal = focal.view(batch_size, -1, 1).to(bbox_info)
                bbox_info = bbox_info / focal

            
            human_predict = self.get_human_prediction(batch["human_patches"], bbox_info)

            if isinstance(human_predict, dict):
                cam_token = human_predict["token_out"].view(batch_size, num_views, 1, 1024)
            else:
                cam_token = human_predict.view(batch_size, num_views, 1, 1024)
            
            # predict scale and smpl z-trans
            hidden = geometry_results["hidden"].view(batch_size, num_views, -1, geometry_results["hidden"].shape[-1]) # [1, 10, 782, 2048]
            self.alignnet.to(torch.float32)
            align_results = self.alignnet(hidden, cam_token)
            pred_scale = align_results["scale"] # [1]

            if isinstance(human_predict, dict):
                align_results["betas"] = human_predict["betas"]
                align_results["pose_cam"] = human_predict["pose_cam"]

            align_results_world = transform_smpl(align_results, w2cs_cano, copy_dict=True)

            pred_pose_world = align_results_world["pose_world"]
            pred_pose_world_aa = rotmat_to_aa(pred_pose_world.reshape(-1, 3, 3))
            pred_pose_world_aa = pred_pose_world_aa.reshape(batch_size, num_views, -1)
            align_results_world["pose_world"] = pred_pose_world_aa

            pred_pose_cam = align_results["pose_cam"]
            pred_pose_cam_aa = rotmat_to_aa(pred_pose_cam.reshape(-1, 3, 3))
            pred_pose_cam_aa = pred_pose_cam_aa.reshape(batch_size, num_views, -1)
            align_results["pose_cam"] = pred_pose_cam_aa

            align_results["betas"] = align_results["betas"].repeat(1, num_views, 1)

            ret_dict = {
                "pose_world": align_results_world["pose_world"], # [B, S, 72]
                "trans_world": align_results_world["trans_world"], # [B, S, 3]
                "pose_cam": align_results["pose_cam"], # [B, S, 72]
                "trans_cam": align_results["trans_cam"], # [B, S, 3]
                "betas": align_results["betas"], # [B, S, 10]
                "world_points": geometry_results["world_points"], # [B, S, H, W, 3]
                "local_points": geometry_results["local_points"], # [B, S, H, W, 3]
                "point_conf": geometry_results["point_conf"].squeeze(-1), # [B, S, H, W]
                "c2ws": geometry_results["c2ws"], # [B, S, 4, 4]
                "c2ws_cano": geometry_results["c2ws_cano"], # [B, S, 4, 4]
                "scale": pred_scale, # [B]
                "w2cs_cano": w2cs_cano, # [B, S, 4, 4]
                "masks": masks.squeeze(-1), # [B, S, H, W]
                "intrinsics": pred_intrinsics, # [B, S, 3, 3]
            }

            ret_dict, scale = self.scale_predictions(ret_dict, ret_dict["scale"])
            depth_map, intrinsics, intrinsics_normed, shift = self.get_depth_intrinsic_shift(ret_dict)
            ret_dict["trans_cam"][..., 2] += shift.view(1, -1)
            ret_dict["depth_map"] = depth_map
            ret_dict["point_map"] = depth_to_points(depth_map, intrinsics=intrinsics_normed)
            ret_dict["intrinsics"] = intrinsics

        return ret_dict
    