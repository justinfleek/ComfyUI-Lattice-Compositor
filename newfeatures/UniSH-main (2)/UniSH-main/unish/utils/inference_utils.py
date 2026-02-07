import torch
import torch.nn.functional as F
import numpy as np
from tqdm import tqdm
import os
import cv2
import trimesh
import open3d as o3d
import glob
import tempfile
import shutil
from PIL import Image
from ultralytics import YOLO
from sam2.sam2_video_predictor import SAM2VideoPredictor
import logging
from huggingface_hub import hf_hub_download


from unish.pipeline import UniSHPipeline
from safetensors.torch import load_file
from unish.utils.data_utils import generate_image_patch_cv2, closed_form_inverse_se3
from unish.utils.smpl_utils import SMPLWrapper, transform_smpl

logger = logging.getLogger(__name__)

def aa_to_quat(axis_angle: torch.Tensor) -> torch.Tensor:
    """
    Convert axis-angle representation to quaternion (w, x, y, z).
    Args:
        axis_angle (torch.Tensor): Tensor of shape (B, 3) containing axis-angle representations.
    Returns:
        torch.Tensor: Corresponding quaternions with shape (B, 4) in (w, x, y, z) format.
    """
    norm = torch.norm(axis_angle + 1e-8, p=2, dim=1)
    angle = torch.unsqueeze(norm, -1)
    normalized = torch.div(axis_angle, angle)
    angle = angle * 0.5
    v_cos = torch.cos(angle)
    v_sin = torch.sin(angle)
    quat = torch.cat([v_cos, v_sin * normalized], dim=1)  # [w, x, y, z]
    return quat


def quat_to_aa(quaternion: torch.Tensor) -> torch.Tensor:
    """
    Convert quaternion to axis-angle representation.
    Args:
        quaternion (torch.Tensor): Tensor of shape (B, 4) in (w, x, y, z) format.
    Returns:
        torch.Tensor: Corresponding axis-angle with shape (B, 3).
    """
    # Normalize quaternion
    quaternion = quaternion / quaternion.norm(p=2, dim=1, keepdim=True)
    
    w, x, y, z = quaternion[:, 0], quaternion[:, 1], quaternion[:, 2], quaternion[:, 3]
    sin_squared_theta = x * x + y * y + z * z
    
    sin_theta = torch.sqrt(sin_squared_theta)
    cos_theta = w
    two_theta = 2.0 * torch.where(
        cos_theta < 0.0,
        torch.atan2(-sin_theta, -cos_theta),
        torch.atan2(sin_theta, cos_theta)
    )
    
    k_pos = two_theta / sin_theta
    k_neg = 2.0 * torch.ones_like(sin_theta)
    k = torch.where(sin_squared_theta > 0.0, k_pos, k_neg)
    
    axis_angle = torch.zeros_like(quaternion)[:, :3]
    axis_angle[:, 0] = x * k
    axis_angle[:, 1] = y * k
    axis_angle[:, 2] = z * k
    return axis_angle

def load_model(checkpoint_path=None):
    """
    Load the trained model.
    Supports loading from local path OR automatic download from Hugging Face.
    """
    
    logger.info("Creating model...")
    model = UniSHPipeline()

    if checkpoint_path is None:
        logger.info(f"No checkpoint_path provided. Downloading default model from HuggingFace")
        checkpoint_path = hf_hub_download(repo_id="Murphyyyy/UniSH/UniSH", filename="checkpoints/unish_release.safetensors")
        
    elif not os.path.exists(checkpoint_path):
        logger.info(f"File '{checkpoint_path}' not found locally. Trying to download from Hugging Face...")
        try:
            checkpoint_path = hf_hub_download(repo_id="Murphyyyy/UniSH", filename="checkpoints/unish_release.safetensors")
        except Exception as e:
            raise FileNotFoundError(f"Checkpoint not found locally at '{checkpoint_path}' and failed to download from HuggingFace'. Error: {e}")

    logger.info(f"Loading model weights from {checkpoint_path}...")
    
    if checkpoint_path.endswith(('.safetensor', '.safetensors')):
        state_dict = load_file(checkpoint_path)
    else:
        state_dict = torch.load(checkpoint_path, map_location='cpu')
    
    model.load_state_dict(state_dict, strict=True)

    weight_dtype = torch.bfloat16
    if weight_dtype != torch.float32:
        logger.info(f"Casting model to {weight_dtype}...")
        for module in model.modules():
            if hasattr(module, 'weight') and module.weight is not None:
                module.weight.data = module.weight.data.to(dtype=weight_dtype)
            if hasattr(module, 'bias') and module.bias is not None:
                module.bias.data = module.bias.data.to(dtype=weight_dtype)
            
            for param_name, param in module.named_parameters(recurse=False):
                if param_name not in ['weight', 'bias']:
                    param.data = param.data.to(dtype=weight_dtype)
    
    return model

def resize_frames(frames, target_size=518):
    """Resize frames with proper scaling logic (following load_and_preprocess_data_from_npz_pi3)"""
        
    # Process frames with proper resizing logic
    processed_frames = []
    for frame in frames:
        # Convert to torch tensor and reorder to (C, H, W)
        frame_tensor = torch.from_numpy(frame).float() / 255.0  # Normalize to 0-1
        frame_tensor = frame_tensor.permute(2, 0, 1)  # Shape: (3, H, W)
        
        # Get original size
        original_height, original_width = frame_tensor.shape[1], frame_tensor.shape[2]
        
        # Determine if video is landscape or portrait and scale the longer dimension to target_size
        if original_width >= original_height:
            # Landscape video: scale width to target_size
            new_width = target_size
            new_height = round(original_height * (new_width / original_width) / 14) * 14
        else:
            # Portrait video: scale height to target_size
            new_height = target_size
            new_width = round(original_width * (new_height / original_height) / 14) * 14
        
        # Resize frame
        frame_resized = torch.nn.functional.interpolate(
            frame_tensor.unsqueeze(0),  # Add batch dimension
            size=(new_height, new_width),
            mode='bilinear',
            align_corners=False
        ).squeeze(0)  # Remove batch dimension
        
        # Center crop if any dimension is larger than target_size (crop mode)
        if new_height > target_size:
            start_y = (new_height - target_size) // 2
            frame_resized = frame_resized[:, start_y : start_y + target_size, :]
        if new_width > target_size:
            start_x = (new_width - target_size) // 2
            frame_resized = frame_resized[:, :, start_x : start_x + target_size]
        
        processed_frames.append(frame_resized)
    
    # Stack all processed frames
    rgbs = torch.stack(processed_frames)  # Shape: (N, 3, H, W)
    
    return rgbs

def generate_patches_and_bbox(rgbs, human_boxes, box_scale=1.0):
    """Generate human patches and bbox info from processed RGB frames and human bounding boxes"""    
    
    height, width = rgbs.shape[2], rgbs.shape[3]
    num_frames = rgbs.shape[0]
    num_humans = human_boxes.shape[0] if len(human_boxes.shape) > 0 else 0
    
    if num_humans == 0:
        raise ValueError("No humans detected in the video. Cannot generate patches and bbox info.")
        
    # human_boxes shape: (num_humans, num_frames, 4) in xyxy format [0,1]
    all_human_patches = []
    all_bbox_info = []
    
    # Process each human separately
    for human_idx in range(num_humans):
        human_boxes_single = human_boxes[human_idx]  # Shape: (num_frames, 4)
        
        # Calculate center coordinates and box sizes from normalized xyxy format
        box_centers = []
        box_sizes = []
        for frame_idx in range(num_frames):
            # Get normalized bbox: [x1, y1, x2, y2] in [0,1] range
            x1, y1, x2, y2 = human_boxes_single[frame_idx]
            
            # Convert to pixel coordinates
            x1_pixel = x1 * width
            y1_pixel = y1 * height
            x2_pixel = x2 * width
            y2_pixel = y2 * height
            
            # Calculate center coordinates in pixels
            center_x = (x1_pixel + x2_pixel) / 2.0
            center_y = (y1_pixel + y2_pixel) / 2.0
            
            # Calculate box size as the longer edge in pixels
            bbox_width = x2_pixel - x1_pixel
            bbox_height = y2_pixel - y1_pixel
            box_size = max(bbox_width, bbox_height) * box_scale
            
            box_centers.append([center_x, center_y])
            box_sizes.append(box_size)
        
        box_centers = torch.tensor(box_centers).float()  # Shape: (num_frames, 2)
        box_sizes = torch.tensor(box_sizes).float()      # Shape: (num_frames,)
        
        # Calculate bbox_info for human head prediction
        cx, cy = box_centers[:, 0], box_centers[:, 1]
        bbox_info = torch.stack([cx - width / 2.0, cy - height / 2.0, box_sizes], dim=-1)
        all_bbox_info.append(bbox_info)
        
        # Generate human patches using calculated centers and sizes
        np_rgbs = rgbs.permute(0, 2, 3, 1).numpy()
        rgbs_patch = []
        for i in range(num_frames):
            img_patch_cv, _ = generate_image_patch_cv2(
                np_rgbs[i],
                box_centers[i, 0], box_centers[i, 1],
                box_sizes[i], box_sizes[i],
                256, 256,
                False, 1.0, 0,
                border_mode=cv2.BORDER_CONSTANT
            )
            rgbs_patch.append(img_patch_cv)
        rgbs_patch = torch.from_numpy(np.stack(rgbs_patch)).permute(0, 3, 1, 2)
        all_human_patches.append(rgbs_patch)
    
    # Stack all humans' data
    # all_human_patches: list of (num_frames, 3, 256, 256) -> (num_humans, num_frames, 3, 256, 256)
    all_human_patches = torch.stack(all_human_patches, dim=0)
    # all_bbox_info: list of (num_frames, 3) -> (num_humans, num_frames, 3)
    all_bbox_info = torch.stack(all_bbox_info, dim=0)
    
    return all_human_patches, all_bbox_info

def save_smpl_meshes_per_frame(results, output_dir, body_models_path="body_models/"):
    """Save SMPL meshes (not just points) for each frame using world coordinates - supports multiple humans"""
    seq_name = results['seq_name']
    selected_views = results['selected_views']
    num_humans = results.get('num_humans', 1)
    
    smpl_meshes_dir = os.path.join(output_dir, seq_name, "smpl_meshes_per_frame")
    os.makedirs(smpl_meshes_dir, exist_ok=True)
        
    # Initialize SMPL visualizer
    device = torch.device('cpu')  # Work on CPU for file saving
    smpl_visualizer = SMPLWrapper(
        model_folder=body_models_path,
        model_type='smpl',
        device=device,
        dtype=torch.float32
    )
    
    # Process each human
    all_human_vertices = []
    for human_idx in range(num_humans):
        if num_humans > 1:
            # Multi-human case: use the _all_humans data
            pred_pose_world_aa = results['pred_pose_world_aa_all_humans'][human_idx]
            pred_trans_world = results['pred_trans_world_all_humans'][human_idx]
            pred_betas = results['pred_betas_all_humans'][human_idx]
        else:
            # Single human case: use the original data
            pred_pose_world_aa = results['pred_pose_world_aa']
            pred_trans_world = results['pred_trans_world']
            pred_betas = results['pred_betas']
        
        # Get vertices for all frames in batch using world coordinates
        vertices, joints = smpl_visualizer.get_batch_vertices(
            pred_pose_world_aa, pred_betas, pred_trans_world, "neutral"
        )
        all_human_vertices.append(vertices)
    
    # Get SMPL faces (same for all frames and humans)
    smpl_faces = smpl_visualizer.models['neutral'].faces.astype(np.int32)
    
    # Save each frame as mesh PLY file
    for i in tqdm(range(len(selected_views)), desc="Processing SMPL meshes per frame"):
        frame_idx = selected_views[i]
        
        if num_humans == 1:
            # Single human: save individual mesh
            frame_vertices = all_human_vertices[0][i].cpu().numpy()  # [V, 3]
            
            # Create vertex colors (skin color)
            vertex_colors = np.ones((len(frame_vertices), 3)) * [0.8, 0.6, 0.4]
            vertex_colors = (vertex_colors * 255).astype(np.uint8)
            
            # Create mesh
            mesh = trimesh.Trimesh(
                vertices=frame_vertices,
                faces=smpl_faces,
                vertex_colors=vertex_colors
            )
            
            # Save mesh
            mesh_filename = f"smpl_mesh_frame_{frame_idx:04d}.ply"
            mesh_path = os.path.join(smpl_meshes_dir, mesh_filename)
            mesh.export(mesh_path)
        else:
            # Multiple humans: save combined mesh and individual meshes
            combined_vertices = []
            combined_faces = []
            combined_colors = []
            vertex_offset = 0
            
            # Colors for different humans
            colors_palette = [
                [0.8, 0.6, 0.4],  # Skin color for human 0
                [0.2, 0.8, 0.2],  # Green for human 1
                [0.2, 0.2, 0.8],  # Blue for human 2
                [0.8, 0.2, 0.2],  # Red for human 3
                [0.8, 0.8, 0.2],  # Yellow for human 4
                [0.8, 0.2, 0.8],  # Magenta for human 5
                [0.2, 0.8, 0.8],  # Cyan for human 6
            ]
            
            for human_idx in range(num_humans):
                frame_vertices = all_human_vertices[human_idx][i].cpu().numpy()  # [V, 3]
                
                # Add vertices to combined mesh
                combined_vertices.append(frame_vertices)
                
                # Add faces with vertex offset
                faces_with_offset = smpl_faces + vertex_offset
                combined_faces.append(faces_with_offset)
                vertex_offset += len(frame_vertices)
                
                # Create colors for this human
                human_color = colors_palette[human_idx % len(colors_palette)]
                vertex_colors = np.ones((len(frame_vertices), 3)) * human_color
                vertex_colors = (vertex_colors * 255).astype(np.uint8)
                combined_colors.append(vertex_colors)
                
                # Also save individual mesh for each human
                individual_mesh = trimesh.Trimesh(
                    vertices=frame_vertices,
                    faces=smpl_faces,
                    vertex_colors=vertex_colors
                )
                individual_mesh_filename = f"human_{human_idx:02d}_smpl_mesh_frame_{frame_idx:04d}.ply"
                individual_mesh_path = os.path.join(smpl_meshes_dir, individual_mesh_filename)
                individual_mesh.export(individual_mesh_path)
            
            # Create and save combined mesh
            if combined_vertices:
                combined_vertices_array = np.concatenate(combined_vertices, axis=0)
                combined_faces_array = np.concatenate(combined_faces, axis=0)
                combined_colors_array = np.concatenate(combined_colors, axis=0)
                
                combined_mesh = trimesh.Trimesh(
                    vertices=combined_vertices_array,
                    faces=combined_faces_array,
                    vertex_colors=combined_colors_array
                )
                
                combined_mesh_filename = f"combined_smpl_mesh_frame_{frame_idx:04d}.ply"
                combined_mesh_path = os.path.join(smpl_meshes_dir, combined_mesh_filename)
                combined_mesh.export(combined_mesh_path)

def save_scene_only_point_clouds(scene_only_point_clouds, output_dir, seq_name):
    """
    Save scene-only point clouds (without human regions) as PLY files.

    Args:
        scene_only_point_clouds: List of Open3D point clouds for scene-only
        output_dir: Output directory
        seq_name: Sequence name
    """
    scene_only_dir = os.path.join(
        output_dir, seq_name, "scene_only_point_clouds")
    os.makedirs(scene_only_dir, exist_ok=True)

    for i, scene_pcd in enumerate(scene_only_point_clouds):
        if len(scene_pcd.points) > 0:
            ply_path = os.path.join(
                scene_only_dir, f"scene_only_frame_{i:04d}.ply")
            o3d.io.write_point_cloud(ply_path, scene_pcd)

def save_human_point_clouds(complete_scene_point_clouds, scene_only_point_clouds, output_dir, seq_name, results=None):
    """
    Save human point clouds (extracted using human masks from point cloud) as PLY files.
    Single human processing.

    Args:
        complete_scene_point_clouds: List of complete scene point clouds
        scene_only_point_clouds: List of scene-only point clouds
        output_dir: Output directory
        seq_name: Sequence name
        results: Results dictionary containing human masks and point maps
    """
    human_only_dir = os.path.join(
        output_dir, seq_name, "human_only_point_clouds")
    os.makedirs(human_only_dir, exist_ok=True)

    # Try to use human masks for more accurate extraction
    if results is not None and 'human_masks' in results and 'point_map' in results:
        point_map = results['point_map']  # [S, H, W, 3] - Camera coordinates
        depth_conf = results['depth_conf']  # [S, H, W, 1]
        human_masks = results['human_masks']  # [num_humans, S, H, W]
        # [S, 3, 4] or [S, 4, 4] - World-to-camera transformation
        extrinsics = results['extrinsics']
        # [S, 3, H, W] - Original RGB images
        rgb_images = results.get('rgb_images', None)

        for frame_idx in range(point_map.shape[0]):
            human_pcd = o3d.geometry.PointCloud()

            # Extract human points using masks
            # [H, W, 3] - Camera coordinates
            frame_points = point_map[frame_idx].numpy()
            frame_conf = depth_conf[frame_idx].squeeze(-1).numpy()  # [H, W]

            # Get extrinsics for this frame
            extr = extrinsics[frame_idx].numpy()  # [3, 4] or [4, 4]
            if extr.shape[0] == 3:  # Convert [3, 4] to [4, 4]
                extr = np.vstack([extr, [0, 0, 0, 1]])

            # Convert camera coordinates to world coordinates
            cam_to_world = closed_form_inverse_se3(extr[None])[0]  # [4, 4]
            R_cam_to_world = cam_to_world[:3, :3]  # [3, 3]
            t_cam_to_world = cam_to_world[:3, 3]   # [3]

            # Transform all points to world coordinates
            frame_points_world = np.dot(
                frame_points, R_cam_to_world.T) + t_cam_to_world  # [H, W, 3]

            # Single human processing
            target_h, target_w = frame_points.shape[0], frame_points.shape[1]
            combined_human_mask = np.zeros((target_h, target_w), dtype=bool)

            human_idx = 0
            if frame_idx < human_masks.shape[1]:
                # [H_orig, W_orig]
                human_mask = human_masks[human_idx,
                                         frame_idx].cpu().numpy()

                # Resize human mask to match point_map dimensions
                if human_mask.shape != (target_h, target_w):
                    # Resize mask using nearest neighbor to preserve binary values
                    human_mask_resized = cv2.resize(human_mask.astype(np.uint8),
                                                    (target_w, target_h),
                                                    interpolation=cv2.INTER_NEAREST).astype(bool)
                else:
                    human_mask_resized = human_mask

                combined_human_mask = human_mask_resized

            # Apply confidence threshold and human mask
            valid_mask = (frame_conf > 0.05) & combined_human_mask

            if np.any(valid_mask):
                # Get valid human points in world coordinates
                # [N, 3] - World coordinates
                valid_points_world = frame_points_world[valid_mask]

                # Filter out zero points (in original camera coordinates)
                # [N, 3] - Camera coordinates for zero check
                valid_points_cam = frame_points[valid_mask]
                non_zero_mask = np.any(valid_points_cam != 0, axis=1)
                if np.any(non_zero_mask):
                    # [N, 3] - World coordinates
                    human_points_world = valid_points_world[non_zero_mask]

                    # Get colors from RGB image if available
                    if rgb_images is not None and frame_idx < rgb_images.shape[0]:
                        rgb_image = rgb_images[frame_idx].permute(
                            1, 2, 0).numpy()  # [H, W, 3], values in [0, 1]

                        # Get 2D coordinates of valid human points
                        valid_coords_2d = np.where(valid_mask)
                        y_coords, x_coords = valid_coords_2d

                        # Apply non-zero mask to get final coordinates
                        y_coords_final = y_coords[non_zero_mask]
                        x_coords_final = x_coords[non_zero_mask]

                        # Extract colors from RGB image
                        # [N, 3], values in [0, 1]
                        human_colors = rgb_image[y_coords_final,
                                                 x_coords_final]
                    else:
                        # Fallback to red color if RGB not available
                        human_colors = np.tile(
                            [0.8, 0.2, 0.2], (len(human_points_world), 1))

                    human_pcd.points = o3d.utility.Vector3dVector(
                        human_points_world)
                    human_pcd.colors = o3d.utility.Vector3dVector(human_colors)

            # Save human point cloud
            if len(human_pcd.points) > 0:
                ply_path = os.path.join(
                    human_only_dir, f"human_frame_{frame_idx:04d}.ply")
                o3d.io.write_point_cloud(ply_path, human_pcd)

def save_camera_parameters_per_frame(results, output_dir, seq_name):
    """
    Save camera parameters (extrinsics and intrinsics) for each frame as NPZ files.

    Args:
        results: Results dictionary containing camera parameters
        output_dir: Output directory
        seq_name: Sequence name
    """
    seq_dir = os.path.join(output_dir, seq_name)
    os.makedirs(seq_dir, exist_ok=True)

    extrinsics = results.get('extrinsics', None)
    intrinsics = results.get('pred_intrinsics', None)

    if extrinsics is None or intrinsics is None:
        logger.warning("Camera parameters not found in results")
        return

    # Convert to numpy if needed
    if hasattr(extrinsics, 'cpu'):
        extrinsics = extrinsics.cpu().numpy()
    if hasattr(intrinsics, 'cpu'):
        intrinsics = intrinsics.cpu().numpy()

    num_frames = len(extrinsics)

    # Ensure extrinsics is 4x4 for all frames
    if extrinsics.shape[-2] == 3:  # [S, 3, 4] -> [S, 4, 4]
        bottom_row = np.tile([0, 0, 0, 1], (num_frames, 1, 1))
        extrinsics = np.concatenate([extrinsics, bottom_row], axis=-2)

    # Save all camera parameters in one NPZ file
    summary_file = os.path.join(seq_dir, "camera_parameters.npz")
    np.savez(summary_file,
             # [S, 4, 4] - World-to-Camera (w2c) transformation matrices
             extrinsics=extrinsics,
             intrinsics=intrinsics,    # [S, 3, 3] - Camera intrinsic matrices
             num_frames=num_frames)

def segment_human(frames, human_idx, yolo_ckpt="yolo11n.pt", sam2_model="facebook/sam2-hiera-large"):
    """
    Segment human using YOLO detection + SAM2 video segmentation

    Args:
        frames: List of RGB frames (numpy arrays in RGB format)
        human_idx: Index of the human to segment (0-based)
        yolo_ckpt: Path to YOLO checkpoint
        sam2_model: SAM2 model name

    Returns:
        human_boxes: (1, num_frames, 4) in xyxy format ranging from 0 to 1
        human_masks: (1, num_frames, H, W) boolean masks
    """

    logger.info(f"Segmenting human {human_idx} from {len(frames)} frames...")

    # Step 1: Use YOLO to detect humans in the first frame
    yolo_model = YOLO(yolo_ckpt)

    # Convert first frame to BGR for YOLO (frames are in RGB format)
    first_frame_bgr = cv2.cvtColor(frames[0], cv2.COLOR_RGB2BGR)

    # Run YOLO detection on first frame
    results = yolo_model(first_frame_bgr)
    first_frame_result = results[0]
 
    # Extract human detections from first frame
    human_detections = []
    if first_frame_result.boxes is not None and len(first_frame_result.boxes) > 0:
        boxes = first_frame_result.boxes
        classes = boxes.cls
        confs = boxes.conf
        xyxyn_boxes = boxes.xyxyn  # Normalized coordinates [0,1]

        if classes is not None and confs is not None and xyxyn_boxes is not None:
            for i in range(len(classes)):
                if classes[i] == 0:  # person class
                    confidence = float(confs[i].item())
                    # [x1, y1, x2, y2] in [0,1]
                    bbox = xyxyn_boxes[i].cpu().numpy()
                    human_detections.append((confidence, bbox))

    # Sort by confidence and select the human_idx-th human
    human_detections.sort(key=lambda x: x[0], reverse=True)

    if len(human_detections) <= human_idx:
        raise ValueError(
            f"Only {len(human_detections)} humans detected, but requested human_idx={human_idx}")

    # [x1, y1, x2, y2] in [0,1]
    selected_human_bbox = human_detections[human_idx][1]
    selected_human_conf = human_detections[human_idx][0]

    logger.info(
        f"Selected human {human_idx} with confidence {selected_human_conf:.3f}")
    logger.info(f"Initial bbox: {selected_human_bbox}")

    # Release YOLO model
    del yolo_model
    torch.cuda.empty_cache()

    # Step 2: Prepare frames for SAM2 (save to temporary directory)
    temp_dir = tempfile.mkdtemp()
    try:
        # Save frames to temporary directory
        for i, frame in enumerate(frames):
            frame_path = os.path.join(temp_dir, f"{i:08d}.jpg")
            # Convert RGB to BGR for saving
            frame_bgr = cv2.cvtColor(frame, cv2.COLOR_RGB2BGR)
            cv2.imwrite(frame_path, frame_bgr)

        # Step 3: Initialize SAM2
        predictor = SAM2VideoPredictor.from_pretrained(sam2_model)
        inference_state = predictor.init_state(video_path=temp_dir)
        predictor.reset_state(inference_state)

        # Step 4: Convert normalized bbox to pixel coordinates for SAM2
        frame_height, frame_width = frames[0].shape[:2]
        x1, y1, x2, y2 = selected_human_bbox
        box_pixel = [
            x1 * frame_width,   # x_min
            y1 * frame_height,  # y_min
            x2 * frame_width,   # x_max
            y2 * frame_height   # y_max
        ]

        logger.info(f"SAM2 input box (pixels): {box_pixel}")

        # Step 5: Add box to SAM2 for first frame
        ann_frame_idx = 0  # First frame
        ann_obj_id = 0     # Object ID

        _, out_obj_ids, out_mask_logits = predictor.add_new_points_or_box(
            inference_state=inference_state,
            frame_idx=ann_frame_idx,
            obj_id=ann_obj_id,
            box=box_pixel,
        )

        # Step 6: Propagate segmentation through all frames
        masks = []
        bboxes = []

        for out_frame_idx, out_obj_ids, out_mask_logits in predictor.propagate_in_video(inference_state):
            # Get mask for our object
            mask = (out_mask_logits[ann_obj_id] > 0.0).squeeze(0).cpu().numpy()

            # Apply dilation to clean up the mask (like in segment_example.py)
            kernel = cv2.getStructuringElement(cv2.MORPH_ELLIPSE, (5, 5))
            mask = cv2.dilate(mask.astype(np.uint8), kernel, iterations=5)
            mask = mask.astype(bool)

            masks.append(mask)

            # Calculate bbox from mask
            if np.any(mask):
                # Find bounding box of the mask
                rows = np.any(mask, axis=1)
                cols = np.any(mask, axis=0)

                if np.any(rows) and np.any(cols):
                    y_min, y_max = np.where(rows)[0][[0, -1]]
                    x_min, x_max = np.where(cols)[0][[0, -1]]

                    # Normalize to [0, 1]
                    bbox = [
                        x_min / frame_width,
                        y_min / frame_height,
                        x_max / frame_width,
                        y_max / frame_height
                    ]
                else:
                    # Use previous bbox if mask is empty
                    bbox = bboxes[-1] if bboxes else selected_human_bbox.tolist()
            else:
                # Use previous bbox if mask is empty
                bbox = bboxes[-1] if bboxes else selected_human_bbox.tolist()

            bboxes.append(bbox)

        # Release SAM2 model
        del predictor
        torch.cuda.empty_cache()

    finally:
        # Clean up temporary directory
        shutil.rmtree(temp_dir, ignore_errors=True)

    # Step 7: Format output
    num_frames = len(frames)

    # Convert to tensors with correct shapes
    human_boxes = torch.tensor(bboxes).unsqueeze(0)  # (1, num_frames, 4)
    human_masks = torch.tensor(np.stack(masks)).unsqueeze(
        0)  # (1, num_frames, H, W)

    logger.info(f"Segmentation completed. Output shapes:")
    logger.info(f"  human_boxes: {human_boxes.shape}")
    logger.info(f"  human_masks: {human_masks.shape}")

    return human_boxes, human_masks


def extract_frames(video_path, fps, human_idx, start_idx=None, end_idx=None, original_fps=30.0, yolo_ckpt="yolo11n.pt", sam2_model="facebook/sam2-hiera-large"):
    """Extract frames from video or directory at specified fps

    Args:
        video_path: Path to video file or directory
        fps: Target fps for frame extraction
        human_idx: Human index for segmentation
        start_idx: Start frame index (default: None, process from beginning)
        end_idx: End frame index (default: None, process to end)
        original_fps: Original fps of the image sequence (default: 30.0, used only for directory input)
        yolo_ckpt: Path to YOLO checkpoint
        sam2_model: SAM2 model name
    """

    if not os.path.exists(video_path):
        raise FileNotFoundError(f"Path not found: {video_path}")

    # Determine frame sampling interval based on input type
    if os.path.isdir(video_path):
        logger.info(f"Processing directory: {video_path} at {fps} fps...")
        # For directory, use provided original fps
        frames = extract_frames_from_directory(
            video_path, fps, original_fps=original_fps, start_idx=start_idx, end_idx=end_idx)
    else:
        logger.info(f"Processing video file: {video_path} at {fps} fps...")
        # For video file, get actual fps
        cap = cv2.VideoCapture(video_path)
        video_fps = cap.get(cv2.CAP_PROP_FPS)
        cap.release()
        frames = extract_frames_from_video(
            video_path, fps, start_idx=start_idx, end_idx=end_idx)

    num_frames = len(frames)
    human_boxes, human_masks = segment_human(frames, human_idx, yolo_ckpt=yolo_ckpt, sam2_model=sam2_model)

    # frame: (1, num_frames, 3, H, W)
    # human_boxes: (1, num_frames, 4) in xyxy format ranging from 0 to 1
    # human_masks: (1, num_frames, H, W)
    return frames, human_boxes, human_masks


def extract_frames_from_directory(directory_path, fps, original_fps=30.0, start_idx=None, end_idx=None):
    """Extract frames from directory of images at specified fps

    Args:
        directory_path: Path to directory containing image files
        fps: Target fps for frame extraction
        original_fps: Original fps of the image sequence (default: 30.0)
        start_idx: Start frame index (default: None, process from beginning)
        end_idx: End frame index (default: None, process to end)
    """
    # Supported image extensions
    image_extensions = ['*.jpg', '*.jpeg', '*.png', '*.bmp', '*.tiff', '*.tif']

    # Find all image files in the directory
    image_files = []
    for ext in image_extensions:
        image_files.extend(glob.glob(os.path.join(directory_path, ext)))
        image_files.extend(
            glob.glob(os.path.join(directory_path, ext.upper())))

    if len(image_files) == 0:
        raise ValueError(
            f"No image files found in directory: {directory_path}")

    # Sort files to ensure consistent ordering
    image_files.sort()
    total_images = len(image_files)

    logger.info(f"Found {total_images} images in directory")
    logger.info(f"Assuming original fps: {original_fps}, target fps: {fps}")

    # Calculate frame interval for desired fps
    # Assume the image sequence has original_fps
    # To get target fps, we need to sample every (original_fps / target_fps) frames
    frame_interval = max(1, int(round(original_fps / fps)))

    logger.info(
        f"Frame interval: {frame_interval} (sampling every {frame_interval} frames)")

    # First, extract frames based on fps
    frames = []
    extracted_count = 0

    for i, image_file in enumerate(image_files):
        if i % frame_interval == 0:
            # Load image
            frame = cv2.imread(image_file)
            if frame is None:
                logger.warning(f"Could not load image {image_file}")
                continue

            # Convert BGR to RGB for further processing
            frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            frames.append(frame_rgb)
            extracted_count += 1

    if len(frames) == 0:
        raise ValueError("No frames extracted from directory")

    logger.info(
        f"Extracted {len(frames)} frames from directory (every {frame_interval} images)")

    # Then apply start_idx and end_idx filtering on the extracted frames
    total_extracted_frames = len(frames)

    if start_idx is not None:
        start_idx = max(0, start_idx)
    else:
        start_idx = 0

    if end_idx is not None:
        end_idx = min(total_extracted_frames, end_idx)
    else:
        end_idx = total_extracted_frames

    # Filter extracted frames based on indices
    frames = frames[start_idx:end_idx]
    filtered_frames = len(frames)

    logger.info(
        f"Applied frame range filtering: frames {start_idx} to {end_idx-1} ({filtered_frames} frames)")

    return frames


def extract_frames_from_video(video_path, fps, start_idx=None, end_idx=None):
    """Extract frames from video file at specified fps

    Args:
        video_path: Path to video file
        fps: Target fps for frame extraction
        start_idx: Start frame index (default: None, process from beginning)
        end_idx: End frame index (default: None, process to end)
    """

    # Extract frames from video
    cap = cv2.VideoCapture(video_path)
    if not cap.isOpened():
        raise ValueError(f"Cannot open video file: {video_path}")

    # Get video properties
    video_fps = cap.get(cv2.CAP_PROP_FPS)
    total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))

    logger.info(f"Video has {total_frames} frames at {video_fps} fps")

    # Calculate frame interval for desired fps
    frame_interval = max(1, int(round(video_fps / fps)))

    logger.info(
        f"Frame interval: {frame_interval} (sampling every {frame_interval} frames)")

    # First, extract frames based on fps from the entire video
    frames = []
    frame_count = 0
    extracted_count = 0

    while frame_count < total_frames:
        ret, frame = cap.read()
        if not ret:
            break

        if frame_count % frame_interval == 0:
            # Convert BGR to RGB for further processing
            frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            frames.append(frame_rgb)
            extracted_count += 1

        frame_count += 1

    cap.release()

    if len(frames) == 0:
        raise ValueError("No frames extracted from video")

    logger.info(
        f"Extracted {len(frames)} frames from video (every {frame_interval} frames)")

    # Then apply start_idx and end_idx filtering on the extracted frames
    total_extracted_frames = len(frames)

    if start_idx is not None:
        start_idx = max(0, start_idx)
    else:
        start_idx = 0

    if end_idx is not None:
        end_idx = min(total_extracted_frames, end_idx)
    else:
        end_idx = total_extracted_frames

    # Filter extracted frames based on indices
    frames = frames[start_idx:end_idx]
    filtered_frames = len(frames)

    logger.info(
        f"Applied frame range filtering: frames {start_idx} to {end_idx-1} ({filtered_frames} frames)")

    return frames


def process_video(video_path, fps, human_idx, target_size=518, bbox_scale=1.0, start_idx=None, end_idx=None, original_fps=30.0, yolo_ckpt="yolo11n.pt", sam2_model="facebook/sam2-hiera-large"):
    """Process video by extracting frames at specified fps

    Args:
        video_path: Path to video file or directory
        fps: Target fps for frame extraction
        human_idx: Human index for segmentation
        target_size: Target size for frame processing (default: 518)
        bbox_scale: Scale factor for bounding box size (default: 1.0)
        start_idx: Start frame index (default: None, process from beginning)
        end_idx: End frame index (default: None, process to end)
        original_fps: Original fps of the image sequence (default: 30.0, used only for directory input)
        yolo_ckpt: Path to YOLO checkpoint
        sam2_model: SAM2 model name
    """
    # Step 1: Extract frames
    frames, human_boxes, human_masks = extract_frames(
        video_path, fps, human_idx, start_idx=start_idx, end_idx=end_idx, original_fps=original_fps,
        yolo_ckpt=yolo_ckpt, sam2_model=sam2_model)

    # Step 3: Resize frames
    rgbs = resize_frames(frames, target_size)

    # Step 4: Generate human patches and bbox info
    # human_boxes: tensor of shape (num_humans, num_frames, 4) in xyxy format ranging from 0 to 1
    rgbs_patch, bbox_info = generate_patches_and_bbox(
        rgbs, human_boxes, box_scale=bbox_scale)

    # Step 5: Prepare return data
    data_basename = os.path.splitext(os.path.basename(video_path))[
        0]  # e.g., "downtown_arguing_00_0"
    seq_name = data_basename  # Use the full basename including person ID
    selected_views = list(range(len(frames)))

    return {
        'seq_name': seq_name,
        'images': rgbs,
        'human_patches': rgbs_patch,
        'bbox_info': bbox_info,
        'selected_views': selected_views,
        'human_boxes': human_boxes,
        'human_masks': human_masks,
    }


def run_inference(unish_model, data_dict, device, chunk_size=30):
    """Run inference on the loaded scene data - processed for single human"""
    seq_name = data_dict['seq_name']
    rgbs = data_dict['images'].to(device)
    # [1, num_frames, 3, 256, 256]
    human_patches = data_dict['human_patches'].to(device)
    # [1, num_frames, 3]
    bbox_info = data_dict['bbox_info'].to(device)
    selected_views = data_dict['selected_views']

    total_frames = rgbs.shape[0]
    human_idx = 0

    # Initialize lists to store chunk results
    chunk_results = {
        'depth_map': [],
        'point_map': [],
        'extrinsics': [],
        'pred_intrinsics': [],
        'depth_conf': [],
        'pred_pose_aa': [],
        'pred_trans_cam': [],
        'pred_betas': [],
    }

    # Process frames in chunks
    num_chunks = (total_frames + chunk_size -
                  1) // chunk_size  # Ceiling division
    for chunk_idx in range(num_chunks):
        start_idx = chunk_idx * chunk_size
        end_idx = min(start_idx + chunk_size, total_frames)

        # Extract chunk data
        rgbs_chunk = rgbs[start_idx:end_idx]  # [chunk_frames, 3, H, W]
        # [chunk_frames, 3, 256, 256]
        human_patches_chunk = human_patches[human_idx, start_idx:end_idx]
        bbox_info_chunk = bbox_info[human_idx,
                                    start_idx:end_idx]  # [chunk_frames, 3]

        # Add batch dimension for model input
        rgbs_batched = rgbs_chunk.unsqueeze(
            0)  # [1, chunk_frames, 3, H, W]
        human_patches_single = human_patches_chunk.unsqueeze(
            0).to(torch.bfloat16)  # [1, chunk_frames, 3, 256, 256]
        bbox_info_single = bbox_info_chunk.unsqueeze(
            0)  # [1, chunk_frames, 3]

        input_dict = {
            "images": rgbs_batched,
            "human_patches": human_patches_single,
            "bbox_info": bbox_info_single,
        }

        unish_model.eval()
        with torch.no_grad():
            predictions = unish_model.inference(input_dict)

            # Store chunk predictions (remove batch dimension and move to CPU)
            chunk_results['depth_map'].append(
                predictions["depth_map"].squeeze(0).cpu())  # [chunk_frames, H, W, 1]
            chunk_results['point_map'].append(
                predictions["point_map"].squeeze(0).cpu())  # [chunk_frames, H, W, 3]
            chunk_results['extrinsics'].append(
                predictions["w2cs_cano"].squeeze(0).cpu())  # [chunk_frames, 4, 4]
            chunk_results['pred_intrinsics'].append(
                predictions["intrinsics"].squeeze(0).cpu())  # [chunk_frames, 3, 3]
            chunk_results['depth_conf'].append(
                predictions["point_conf"].squeeze(0).cpu())  # [chunk_frames, H, W, 1]
            chunk_results['pred_pose_aa'].append(
                predictions["pose_cam"].squeeze(0).cpu())  # [chunk_frames, 165]
            chunk_results['pred_trans_cam'].append(
                predictions["trans_cam"].squeeze(0).cpu())  # [chunk_frames, 3]
            chunk_results['pred_betas'].append(
                predictions["betas"].squeeze(0).cpu())  # [chunk_frames, 10]

    # Concatenate all chunk results
    human_result = {}
    for key in chunk_results:
        # Concatenate along frame dimension
        human_result[key] = torch.cat(chunk_results[key], dim=0)

    # Transform pred_trans_cam from camera coordinates to world coordinates
    # Create SMPL dict for transformation
    smpl_dict = {
        # Add batch dimension: [1, S, 165]
        'pose_cam': human_result['pred_pose_aa'].unsqueeze(0),
        # Add batch dimension: [1, S, 3]
        'trans_cam': human_result['pred_trans_cam'].unsqueeze(0),
        # Add batch dimension: [1, S, 10]
        'betas': human_result['pred_betas'].unsqueeze(0)
    }

    # Transform to world coordinates using extrinsics
    smpl_world_dict = transform_smpl(smpl_dict, human_result['extrinsics'].unsqueeze(
        0))  # Add batch dimension to extrinsics

    # Extract world coordinates (remove batch dimension)
    human_result['pred_trans_world'] = smpl_world_dict['trans_world'].squeeze(
        0)  # [S, 3]
    human_result['pred_pose_world_aa'] = smpl_world_dict['pose_world'].squeeze(
        0)  # [S, 165]

    main_result = human_result

    # Add metadata
    main_result['seq_name'] = seq_name
    main_result['selected_views'] = selected_views
    # Add original RGB images for point cloud coloring
    main_result['rgb_images'] = data_dict['images'].cpu()
    # Add human segmentation masks for point cloud separation
    main_result['human_masks'] = data_dict['human_masks']
    # Add human bounding boxes for visualization
    main_result['human_boxes'] = data_dict['human_boxes']
    return main_result

def generate_mixed_geometries_in_memory(results, body_models_path="body_models/", fps=6, conf_thres=0.1):
    """
    Generate mixed geometries (scene point clouds + SMPL meshes) for visualization.
    Returns lists of scene point clouds and SMPL meshes for each frame.

    Args:
        results: inference results dictionary
        body_models_path: path to SMPL body models
        fps: FPS of the input video and point cloud frequency (default: 6)
        conf_thres: confidence threshold for point cloud generation

    Returns:
        scene_point_clouds: list of Open3D point clouds for scene
        smpl_meshes: list of lists of Open3D triangle meshes for SMPL
        smpl_points_for_camera: list of SMPL vertices in camera coordinates (for camera positioning)
        smpl_joints_for_camera: list of SMPL joints in camera coordinates
        smpl_points_for_world: list of SMPL vertices in world coordinates (for NPZ saving)
        smpl_joints_for_world: list of SMPL joints in world coordinates (for NPZ saving)
        viz_scene_point_clouds: list of Open3D point clouds for complete scene
        viz_smpl_meshes: list of lists of Open3D triangle meshes for SMPL
        viz_scene_only_point_clouds: list of Open3D point clouds for scene-only (excluding human regions)
    """
    seq_name = results['seq_name']
    point_map_original = results['point_map']  # [S, H, W, 3] - 3D points
    extrinsics = results['extrinsics']  # [S, 3, 4]
    intrinsics = results['pred_intrinsics']  # [S, 3, 3]
    selected_views = results['selected_views']
    rgb_images = results['rgb_images']  # [S, 3, H, W]
    # [S, H, W, 1] - same fps as point_map
    depth_conf_original = results['depth_conf']

    rgb_images_original = rgb_images
    point_map = point_map_original  # [S, H, W, 3]
    depth_conf = depth_conf_original  # [S, H, W, 1]

    # Create confidence mask for valid points - use lower threshold for denser point cloud
    # [S, H, W] - lower threshold for more points
    conf_mask = depth_conf.squeeze(-1) > conf_thres
    # Apply mask to point_map to filter out invalid points
    point_map_masked = point_map.clone()
    point_map_masked[~conf_mask.unsqueeze(-1).expand_as(point_map)] = 0

    # Initialize SMPL visualizer
    device = torch.device('cpu')  # Work on CPU for visualization
    smpl_visualizer = SMPLWrapper(
        model_folder=body_models_path,
        model_type='smpl',
        device=device,
        dtype=torch.float32
    )

    # Get SMPL faces (same for all frames and humans)
    smpl_faces = smpl_visualizer.models['neutral'].faces.astype(np.int32)

    # Get SMPL vertices and joints for single human using camera coordinates
    all_human_vertices = []
    # all_human_joints = []
    human_idx = 0
    
    # Single human case
    pred_pose_cam_aa = results['pred_pose_aa']
    pred_trans_cam = results['pred_trans_cam']
    pred_betas = results['pred_betas']

    # Get vertices and joints for all frames using camera coordinates
    vertices, joints = smpl_visualizer.get_batch_vertices(
        pred_pose_cam_aa, pred_betas, pred_trans_cam, "neutral"
    )
    all_human_vertices.append(vertices)
    # all_human_joints.append(joints)

    # Output lists
    # scene_point_clouds = []  # Scene point clouds (one per frame)
    # smpl_meshes = []  # SMPL meshes (list of lists: [frame][human])
    # smpl_points_for_camera = []  # Camera coordinates
    # smpl_joints_for_camera = []  # Camera coordinates
    # smpl_points_for_world = []   # World coordinates
    # smpl_joints_for_world = []   # World coordinates
    
    # Collect SMPL points for camera targeting (from first human)
    # Convert all vertices to a list of points in camera coordinates
    if len(all_human_vertices) > 0:
        # [S, V, 3] -> [S*V, 3]
        all_verts_np = all_human_vertices[0].cpu().numpy().reshape(-1, 3)
        # Convert to list of (3,) arrays to match original format expected by run_visualization
        smpl_points_for_camera = list(all_verts_np)
    else:
        smpl_points_for_camera = []

    # Generate current frame only scene point clouds (at original fps, no downsampling)
    print("Generating visualization scene point clouds at original fps...")
    # Complete scene point clouds (all valid points)
    viz_scene_point_clouds = []
    # Scene-only point clouds (excluding human regions)
    viz_scene_only_point_clouds = []
    viz_smpl_meshes = []

    # Use original fps data for current frame visualization
    original_point_map = point_map_original  # [S_original, H, W, 3]
    original_depth_conf = depth_conf_original  # [S_original, H, W, 1]
    # [S_original, H, W]
    original_conf_mask = original_depth_conf.squeeze(-1) > conf_thres

    # Get original RGB images for coloring
    original_rgb_for_coloring = rgb_images_original

    human_masks_data = results['human_masks']

    for i in range(original_point_map.shape[0]):
        # Create scene point cloud for current frame
        points_3d = original_point_map[i]  # [H, W, 3]
        conf_mask_frame = original_conf_mask[i]  # [H, W]

        # Get valid points (complete scene)
        valid_points = points_3d[conf_mask_frame]  # [N, 3]

        # Create complete scene point cloud
        if len(valid_points) > 0:
            # Create complete point cloud
            complete_scene_pcd = o3d.geometry.PointCloud()
            complete_scene_pcd.points = o3d.utility.Vector3dVector(
                valid_points.cpu().numpy())

            # Add colors from RGB image
            if i < len(original_rgb_for_coloring):
                rgb_frame = original_rgb_for_coloring[i]  # [3, H, W]
                if rgb_frame.dim() == 3 and rgb_frame.shape[0] == 3:
                    # Convert from [3, H, W] to [H, W, 3] and normalize
                    rgb_frame = rgb_frame.permute(1, 2, 0)  # [H, W, 3]
                    rgb_frame = rgb_frame.cpu().numpy()
                    if rgb_frame.max() > 1.0:
                        rgb_frame = rgb_frame / 255.0  # Normalize to [0, 1]
                    
                    # Get colors for valid points
                    valid_colors = rgb_frame[conf_mask_frame]  # [N, 3]
                    complete_scene_pcd.colors = o3d.utility.Vector3dVector(
                        valid_colors)
                else:
                    # Default gray color if RGB format is unexpected
                    default_colors = np.tile(
                        [0.7, 0.7, 0.7], (len(valid_points), 1))
                    complete_scene_pcd.colors = o3d.utility.Vector3dVector(
                        default_colors)
            else:
                # Default gray color if no RGB available
                default_colors = np.tile(
                    [0.7, 0.7, 0.7], (len(valid_points), 1))
                complete_scene_pcd.colors = o3d.utility.Vector3dVector(
                    default_colors)
        else:
            # Empty point cloud
            complete_scene_pcd = o3d.geometry.PointCloud()

        viz_scene_point_clouds.append(complete_scene_pcd)

        # Create scene-only point cloud (excluding human regions) if masks are available
        if human_masks_data is not None:
            # Combine all human masks for this frame
            combined_human_mask = torch.zeros_like(
                conf_mask_frame, dtype=torch.bool)
            
            # Single human mask
            human_idx = 0
            if i < human_masks_data.shape[1]:  # Check frame index bounds
                human_mask = human_masks_data[human_idx, i]  # [H, W]
                # Resize mask if needed to match point cloud resolution
                if human_mask.shape != conf_mask_frame.shape:
                    human_mask_np = human_mask.cpu().numpy().astype(np.uint8)
                    target_h, target_w = conf_mask_frame.shape
                    human_mask_resized = cv2.resize(
                        human_mask_np, (target_w, target_h), interpolation=cv2.INTER_NEAREST)
                    human_mask = torch.from_numpy(
                        human_mask_resized.astype(bool))
                combined_human_mask |= human_mask.cpu()

            # Create scene-only mask (valid points AND NOT human regions)
            scene_only_mask = conf_mask_frame & (~combined_human_mask)
            scene_only_points = points_3d[scene_only_mask]  # [N_scene, 3]

            if len(scene_only_points) > 0:
                # Create scene-only point cloud
                scene_only_pcd = o3d.geometry.PointCloud()
                scene_only_pcd.points = o3d.utility.Vector3dVector(
                    scene_only_points.cpu().numpy())

                # Add colors from RGB image
                if i < len(original_rgb_for_coloring):
                    rgb_frame = original_rgb_for_coloring[i]  # [3, H, W]
                    if rgb_frame.dim() == 3 and rgb_frame.shape[0] == 3:
                        # Convert from [3, H, W] to [H, W, 3] and normalize
                        rgb_frame = rgb_frame.permute(1, 2, 0)  # [H, W, 3]
                        rgb_frame = rgb_frame.cpu().numpy()
                        if rgb_frame.max() > 1.0:
                            # Normalize to [0, 1]
                            rgb_frame = rgb_frame / 255.0

                        # Get colors for scene-only points
                        # [N_scene, 3]
                        scene_only_colors = rgb_frame[scene_only_mask]
                        scene_only_pcd.colors = o3d.utility.Vector3dVector(
                            scene_only_colors)
                    else:
                        # Default gray color if RGB format is unexpected
                        default_colors = np.tile(
                            [0.7, 0.7, 0.7], (len(scene_only_points), 1))
                        scene_only_pcd.colors = o3d.utility.Vector3dVector(
                            default_colors)
                else:
                    # Default gray color if no RGB available
                    default_colors = np.tile(
                        [0.7, 0.7, 0.7], (len(scene_only_points), 1))
                    scene_only_pcd.colors = o3d.utility.Vector3dVector(
                        default_colors)
            else:
                # Empty scene-only point cloud
                scene_only_pcd = o3d.geometry.PointCloud()
        else:
            # No masks available, use complete scene as scene-only
            scene_only_pcd = complete_scene_pcd

        viz_scene_only_point_clouds.append(scene_only_pcd)

    # Generate SMPL meshes at original fps (no upsampling)
    print("Generating SMPL meshes at original fps for visualization...")
    for i in range(original_point_map.shape[0]):
        frame_smpl_meshes = []

        # Use direct frame mapping (no upsampling)
        smpl_idx = min(i, len(all_human_vertices[0]) - 1)

        # Single human
        human_idx = 0
        # Get SMPL vertices and joints for this frame and human - use correct mapping
        # [num_vertices, 3]
        frame_vertices = all_human_vertices[human_idx][smpl_idx].cpu(
        ).numpy()

        # Create SMPL mesh
        smpl_mesh = o3d.geometry.TriangleMesh()
        smpl_mesh.vertices = o3d.utility.Vector3dVector(frame_vertices)
        smpl_mesh.triangles = o3d.utility.Vector3iVector(smpl_faces)

        # Single human: use reddish color
        human_color = np.array([0.8, 0.2, 0.2])

        # Set vertex colors
        vertex_colors = np.tile(human_color, (len(frame_vertices), 1))
        smpl_mesh.vertex_colors = o3d.utility.Vector3dVector(vertex_colors)

        # Compute normals for better rendering
        smpl_mesh.compute_vertex_normals()

        frame_smpl_meshes.append(smpl_mesh)

        viz_smpl_meshes.append(frame_smpl_meshes)

    # Transform scene point clouds and SMPL meshes to world coordinates
    for i in range(len(viz_scene_point_clouds)):
        # Use direct frame mapping (no upsampling)
        extr_idx = min(i, len(extrinsics) - 1)

        extr = extrinsics[extr_idx].numpy()  # [3, 4] or [4, 4]
        if extr.shape[0] == 3:  # Convert [3, 4] to [4, 4] if needed
            extr = np.vstack([extr, [0, 0, 0, 1]])

        # Get camera-to-world transformation
        cam_to_world_extr = closed_form_inverse_se3(extr[None])[0]
        R_cam_to_world = cam_to_world_extr[:3, :3]
        t_cam_to_world = cam_to_world_extr[:3, 3]

        # Transform complete scene point cloud to world coordinates
        scene_pcd = viz_scene_point_clouds[i]
        if len(scene_pcd.points) > 0:
            points_cam = np.asarray(scene_pcd.points)  # Camera coordinates
            # Transform to world coordinates
            points_world = np.dot(
                points_cam, R_cam_to_world.T) + t_cam_to_world
            scene_pcd.points = o3d.utility.Vector3dVector(points_world)

        # Transform scene-only point cloud to world coordinates
        scene_only_pcd = viz_scene_only_point_clouds[i]
        if len(scene_only_pcd.points) > 0:
            points_cam = np.asarray(
                scene_only_pcd.points)  # Camera coordinates
            # Transform to world coordinates
            points_world = np.dot(
                points_cam, R_cam_to_world.T) + t_cam_to_world
            scene_only_pcd.points = o3d.utility.Vector3dVector(points_world)

        # Transform SMPL meshes to world coordinates
        for smpl_mesh in viz_smpl_meshes[i]:
            if len(smpl_mesh.vertices) > 0:
                vertices_cam = np.asarray(
                    smpl_mesh.vertices)  # Camera coordinates
                # Transform to world coordinates
                vertices_world = np.dot(
                    vertices_cam, R_cam_to_world.T) + t_cam_to_world
                smpl_mesh.vertices = o3d.utility.Vector3dVector(vertices_world)
                # Recompute normals after transformation
                smpl_mesh.compute_vertex_normals()

    return viz_scene_point_clouds, viz_smpl_meshes, viz_scene_only_point_clouds, smpl_points_for_camera


def create_mp4_from_frames(frames, output_path, fps):
    """
    Create MP4 video from a list of RGB frames.

    Args:
        frames: List of RGB numpy arrays (H, W, 3)
        output_path: Path to save the MP4 file
        fps: Frames per second
    """
    if not frames:
        return

    height, width = frames[0].shape[:2]
    fourcc = cv2.VideoWriter_fourcc(*'mp4v')
    video_writer = cv2.VideoWriter(output_path, fourcc, fps, (width, height))

    for frame in frames:
        frame_bgr = cv2.cvtColor(frame, cv2.COLOR_RGB2BGR)
        video_writer.write(frame_bgr)

    video_writer.release()


def run_visualization(scene_point_clouds, smpl_meshes, smpl_points_for_camera, output_dir, seq_name, fps=6, rgb_images=None, human_boxes=None, chunk_size=30, results=None,  use_predicted_camera=True, scene_only_point_clouds=None, conf_thres=0.1):
    """
    Visualize current frame scene point clouds + human points without accumulation.
    Creates two types of visualizations:
    1. Complete point clouds: scene point clouds (based on rendering mode) + human point clouds (extracted from complete point cloud using masks)
    2. Scene-only point clouds (excluding human regions) + SMPL meshes

    Rendering modes:
    - Default: scene point clouds contain only current frame
    """

    # Calculate frame counts - use original fps data directly
    total_frames = len(scene_point_clouds)

    print(f"Starting visualization:")
    print(f"  - Total frames: {total_frames} at {fps} fps")

    # Configuration
    FIXED_ANGLE = 270
    CAMERA_DISTANCE_MULTIPLIER = 2.0
    CAMERA_HEIGHT_OFFSET_MULTIPLIER = 0.3
    RENDER_WIDTH = 960
    RENDER_HEIGHT = 540
    FPS = fps  # Use original fps
    POINT_SIZE = 4.0

    # Setup output paths - create separate folders for current frame only results
    viz_folder = os.path.join(output_dir, seq_name, "visualization")

    # Type 1: Scene point clouds + human point clouds (renamed from complete)
    scene_human_frames_folder = os.path.join(
        viz_folder, "scene_human_frames")
    scene_human_gifs_folder = os.path.join(viz_folder, "scene_human_gifs")
    scene_human_video_path = os.path.join(
        viz_folder, "scene_human_video.mp4")
    scene_human_gif_path = os.path.join(
        scene_human_gifs_folder, "scene_human_animation.gif")
    scene_human_gif_mp4_path = os.path.join(
        scene_human_gifs_folder, "scene_human_animation.mp4")

    # Type 2: Scene point clouds + SMPL meshes (renamed from scene_only)
    scene_smpl_frames_folder = os.path.join(
        viz_folder, "scene_smpl_frames")
    scene_smpl_gifs_folder = os.path.join(
        viz_folder, "scene_smpl_gifs")
    scene_smpl_video_path = os.path.join(
        viz_folder, "scene_smpl_video.mp4")
    scene_smpl_gif_path = os.path.join(
        scene_smpl_gifs_folder, "scene_smpl_animation.gif")
    scene_smpl_gif_mp4_path = os.path.join(
        scene_smpl_gifs_folder, "scene_smpl_animation.mp4")

    # Common folders
    bbox_frames_folder = os.path.join(viz_folder, "bbox_frames")
    input_frames_folder = os.path.join(viz_folder, "input_frames")
    input_gif_path = os.path.join(
        viz_folder, "input_frames_animation.gif")
    input_gif_mp4_path = os.path.join(
        viz_folder, "input_frames_animation.mp4")

    # Create all directories
    os.makedirs(scene_human_frames_folder, exist_ok=True)
    os.makedirs(scene_human_gifs_folder, exist_ok=True)
    os.makedirs(scene_smpl_frames_folder, exist_ok=True)
    os.makedirs(scene_smpl_gifs_folder, exist_ok=True)
    os.makedirs(bbox_frames_folder, exist_ok=True)
    os.makedirs(input_frames_folder, exist_ok=True)

    # Setup camera parameters
    if use_predicted_camera and results is not None:
        print("Using predicted camera parameters from model")
        pred_extrinsics = results['extrinsics']
        pred_intrinsics = results['pred_intrinsics']

        if pred_extrinsics is None or pred_intrinsics is None:
            raise KeyError("Missing camera parameters")
        if len(pred_extrinsics) == 0 or len(pred_intrinsics) == 0:
            raise ValueError("Empty camera parameters")

        # Map frames to camera parameters
        camera_positions = []
        camera_rotations = []
        camera_intrinsics = []

        for i in range(total_frames):
            # Use direct mapping or closest available parameter
            camera_idx = min(i, len(pred_extrinsics) - 1)

            extr = pred_extrinsics[camera_idx].numpy()
            intr = pred_intrinsics[camera_idx].numpy()

            if extr.shape[0] == 3:
                extr = np.vstack([extr, [0, 0, 0, 1]])

            cam_to_world = closed_form_inverse_se3(extr[None])[0]

            camera_pos_orig = cam_to_world[:3, 3]
            camera_rot_orig = cam_to_world[:3, :3]

            camera_positions.append(camera_pos_orig.copy())
            camera_rotations.append(camera_rot_orig.copy())
            camera_intrinsics.append(intr)

    # Calculate fixed camera target (needed for both predicted and fixed camera modes)
    if smpl_points_for_camera and len(smpl_points_for_camera) > 0:
        all_smpl_points = []
        for frame_points in smpl_points_for_camera:
            if hasattr(frame_points, '__len__') and len(frame_points) > 0:
                if isinstance(frame_points, np.ndarray):
                    all_smpl_points.extend(frame_points.tolist())
                else:
                    all_smpl_points.extend(frame_points)

        if all_smpl_points:
            all_smpl_points = np.array(all_smpl_points)
            # Ensure we have a proper 2D array with shape (N, 3)
            if all_smpl_points.ndim == 1:
                all_smpl_points = all_smpl_points.reshape(-1, 3)
            center = np.mean(all_smpl_points, axis=0)
            # Ensure center is a 3D vector
            if center.shape[0] != 3:
                print(
                    f"Warning: Invalid center shape {center.shape}, using default [0, 0, 0]")
                fixed_target = np.array([0.0, 0.0, 0.0], dtype=np.float32)
            else:
                fixed_target = center.astype(np.float32)

            # Calculate fixed camera position only if not using predicted camera
            if not use_predicted_camera:
                bbox_min = np.min(all_smpl_points, axis=0)
                bbox_max = np.max(all_smpl_points, axis=0)
                bbox_size = np.linalg.norm(bbox_max - bbox_min)
                camera_distance = bbox_size * CAMERA_DISTANCE_MULTIPLIER

                angle_rad = np.radians(FIXED_ANGLE)
                camera_x = center[0] + camera_distance * np.cos(angle_rad)
                camera_z = center[2] + camera_distance * np.sin(angle_rad)
                camera_y = center[1] + bbox_size * \
                    CAMERA_HEIGHT_OFFSET_MULTIPLIER

                fixed_camera_pos = np.array(
                    [camera_x, camera_y, camera_z], dtype=np.float32)
        else:
            fixed_target = np.array([0.0, 0.0, 0.0], dtype=np.float32)
            if not use_predicted_camera:
                fixed_camera_pos = np.array([0.0, 2.0, 5.0], dtype=np.float32)
    else:
        fixed_target = np.array([0.0, 0.0, 0.0], dtype=np.float32)
        if not use_predicted_camera:
            fixed_camera_pos = np.array([0.0, 2.0, 5.0], dtype=np.float32)

    # Setup renderer (same as inference_video_eval.py)
    render = o3d.visualization.rendering.OffscreenRenderer(
        RENDER_WIDTH, RENDER_HEIGHT)

    # Setup materials
    point_mat = o3d.visualization.rendering.MaterialRecord()
    point_mat.shader = "defaultUnlit"  # Unlit to avoid lighting effects on points
    point_mat.point_size = POINT_SIZE

    mesh_mat = o3d.visualization.rendering.MaterialRecord()
    mesh_mat.shader = "defaultUnlit"  # Change to unlit to avoid lighting effects
    mesh_mat.base_color = [0.8, 0.6, 0.4, 1.0]  # Skin-like color
    mesh_mat.base_metallic = 0.0
    mesh_mat.base_roughness = 0.8

    # Setup camera projection - will be updated per frame if using predicted camera
    default_fov = 60
    render.scene.camera.set_projection(default_fov, RENDER_WIDTH/RENDER_HEIGHT, 0.1, 100.0,
                                       o3d.visualization.rendering.Camera.FovType.Vertical)

    # Setup lighting and background
    render.scene.set_background([1.0, 1.0, 1.0, 1.0])

    # Try to disable all lighting effects to ensure pure white background
    try:
        render.scene.set_lighting(
            o3d.visualization.rendering.Open3DScene.LightingProfile.NO_SHADOWS, np.array([0, 0, 0]))

        try:
            render.scene.scene.enable_sun_light(False)
        except:
            pass

        try:
            render.scene.scene.set_indirect_light_intensity(1.0)
        except:
            pass

    except Exception as e:
        print(f"Warning: Could not set lighting profile: {e}")
        # Fallback: just set background without lighting
        pass

    scene_human_frames = []
    scene_smpl_frames = []  # Scene point clouds + SMPL meshes
    bbox_frames = []
    input_gif_frames = []

    # Main rendering loop - Create both visualizations
    for i in tqdm(range(total_frames), desc="Rendering visualization"):
        # Set camera position and intrinsics
        if use_predicted_camera and i < len(camera_positions):
            camera_pos = np.array(camera_positions[i], dtype=np.float32)
            camera_rot = np.array(camera_rotations[i], dtype=np.float32)
            camera_intr = np.array(camera_intrinsics[i], dtype=np.float32)

            forward = camera_rot[:, 2]
            up = -camera_rot[:, 1]  # Flip Y axis for correct orientation

            # Target point is camera position + forward direction
            target = camera_pos + forward

            # Set camera using look_at: look_at(target, eye, up)
            render.scene.camera.look_at(target, camera_pos, up)

            # Update camera intrinsics if available
            if camera_intr is not None and camera_intr.shape == (3, 3):
                # Calculate FOV from intrinsics
                fx = camera_intr[0, 0]
                fy = camera_intr[1, 1]
                # Use vertical FOV based on fy
                fov_y_rad = 2 * np.arctan(RENDER_HEIGHT / (2 * fy))
                fov_y_deg = np.degrees(fov_y_rad)

                # Clamp FOV to reasonable range
                fov_y_deg = np.clip(fov_y_deg, 10, 120)

                render.scene.camera.set_projection(fov_y_deg, RENDER_WIDTH/RENDER_HEIGHT, 0.1, 100.0,
                                                   o3d.visualization.rendering.Camera.FovType.Vertical)

        else:
            # Use fixed camera
            up_vector = np.array([0.0, 1.0, 0.0], dtype=np.float32)
            render.scene.camera.look_at(
                fixed_target, fixed_camera_pos, up_vector)

            # Reset to default FOV for fixed camera
            render.scene.camera.set_projection(default_fov, RENDER_WIDTH/RENDER_HEIGHT, 0.1, 100.0,
                                               o3d.visualization.rendering.Camera.FovType.Vertical)

        # === Type 1: Complete point clouds (scene + human points from mask) ===
        render.scene.clear_geometry()
        # Ensure white background is set for each frame
        render.scene.set_background([1.0, 1.0, 1.0, 1.0])

        # Add scene point cloud (based on rendering mode)
        current_scene_pcd = scene_point_clouds[i]
        if len(current_scene_pcd.points) > 0:
            render.scene.add_geometry(
                f"scene_pointcloud_{i}", current_scene_pcd, point_mat)

        # Add human point clouds (extracted from complete point cloud using masks)
        if results and 'human_masks' in results and 'point_map' in results and 'rgb_images' in results:
            human_masks_data = results['human_masks']  # [num_humans, S, H, W]
            point_map = results['point_map']  # [S, H, W, 3]
            rgb_images = results['rgb_images']  # [S, 3, H, W]
            depth_conf = results['depth_conf']  # [S, H, W, 1]
            extrinsics = results['extrinsics']  # [S, 3, 4] or [S, 4, 4]

            if i < point_map.shape[0] and i < human_masks_data.shape[1]:
                # Get current frame data
                points_3d = point_map[i]  # [H, W, 3] - in camera coordinates
                conf_map = depth_conf[i].squeeze(-1)  # [H, W]
                conf_mask_frame = conf_map > conf_thres

                # Get camera-to-world transformation for this frame
                extr = extrinsics[i].numpy()  # [3, 4] or [4, 4]
                if extr.shape[0] == 3:  # Convert [3, 4] to [4, 4] if needed
                    extr = np.vstack([extr, [0, 0, 0, 1]])

                # Get camera-to-world transformation
                cam_to_world_extr = closed_form_inverse_se3(extr[None])[0]
                R_cam_to_world = cam_to_world_extr[:3, :3]
                t_cam_to_world = cam_to_world_extr[:3, 3]

                # Extract human points using masks
                # Single human processing
                human_idx = 0
                if human_idx < human_masks_data.shape[0]:
                    human_mask = human_masks_data[human_idx, i]  # [H, W]

                    # Resize mask if needed to match point cloud resolution
                    if human_mask.shape != conf_mask_frame.shape:
                        human_mask_np = human_mask.cpu().numpy().astype(np.uint8)
                        target_h, target_w = conf_mask_frame.shape
                        human_mask_resized = cv2.resize(
                            human_mask_np, (target_w, target_h), interpolation=cv2.INTER_NEAREST)
                        human_mask = torch.from_numpy(
                            human_mask_resized.astype(bool))

                    # Create human mask (valid points AND human regions)
                    human_point_mask = conf_mask_frame & human_mask.cpu()
                    # [N_human, 3] - camera coordinates
                    human_points_cam = points_3d[human_point_mask]

                    if len(human_points_cam) > 0:
                        # Transform human points to world coordinates (same as scene points)
                        human_points_cam_np = human_points_cam.cpu().numpy()
                        human_points_world = np.dot(
                            human_points_cam_np, R_cam_to_world.T) + t_cam_to_world

                        # Create human point cloud in world coordinates
                        human_pcd = o3d.geometry.PointCloud()
                        human_pcd.points = o3d.utility.Vector3dVector(
                            human_points_world)

                        # Add colors from RGB image
                        if i < rgb_images.shape[0]:
                            rgb_frame = rgb_images[i]  # [3, H, W]
                            if rgb_frame.dim() == 3 and rgb_frame.shape[0] == 3:
                                # Convert from [3, H, W] to [H, W, 3] and normalize
                                rgb_frame = rgb_frame.permute(
                                    1, 2, 0)  # [H, W, 3]
                                rgb_frame = rgb_frame.cpu().numpy()
                                if rgb_frame.max() > 1.0:
                                    # Normalize to [0, 1]
                                    rgb_frame = rgb_frame / 255.0

                                # Get colors for human points
                                # [N_human, 3]
                                human_colors = rgb_frame[human_point_mask]
                                human_pcd.colors = o3d.utility.Vector3dVector(
                                    human_colors)
                            else:
                                # Default red color for human points
                                num_points = len(human_points_cam)
                                human_colors = np.zeros((num_points, 3))
                                human_colors[:, 0] = 0.8  # Red
                                human_colors[:, 1] = 0.2  # Green
                                human_colors[:, 2] = 0.2  # Blue
                                human_pcd.colors = o3d.utility.Vector3dVector(
                                    human_colors)
                        else:
                            # Default red color for human points
                            num_points = len(human_points_cam)
                            human_colors = np.zeros((num_points, 3))
                            human_colors[:, 0] = 0.8  # Red
                            human_colors[:, 1] = 0.2  # Green
                            human_colors[:, 2] = 0.2  # Blue
                            human_pcd.colors = o3d.utility.Vector3dVector(
                                human_colors)

                        render.scene.add_geometry(
                            f"human_pointcloud_{i}_human_{human_idx}", human_pcd, point_mat)

        # Render complete visualization
        complete_img = render.render_to_image()
        complete_img_array = np.asarray(complete_img)

        # Flip vertically and horizontally if using fixed camera mode as they come out upside down and flipped
        if not use_predicted_camera:
            complete_img_array = np.flipud(complete_img_array)
            complete_img_array = np.fliplr(complete_img_array)

        complete_img_bgr = cv2.cvtColor(complete_img_array, cv2.COLOR_RGB2BGR)

        # Save complete frame
        scene_human_frame_path = os.path.join(
            scene_human_frames_folder, f"scene_human_frame_{i:04d}.png")
        cv2.imwrite(scene_human_frame_path, complete_img_bgr)
        scene_human_frames.append(complete_img_array)

        # === Type 2: Scene-only point clouds + SMPL meshes ===
        render.scene.clear_geometry()
        # Ensure white background is set for each frame
        render.scene.set_background([1.0, 1.0, 1.0, 1.0])

        # Add scene-only point cloud
        current_scene_only_pcd = scene_only_point_clouds[i]
        if len(current_scene_only_pcd.points) > 0:
            render.scene.add_geometry(
                f"scene_only_pointcloud_{i}", current_scene_only_pcd, point_mat)

        # Add SMPL meshes (same as complete visualization)
        if i < len(smpl_meshes):
            frame_meshes = smpl_meshes[i]
            if isinstance(frame_meshes, list):
                for human_idx, mesh in enumerate(frame_meshes):
                    if hasattr(mesh, 'vertices') and len(mesh.vertices) > 0:
                        render.scene.add_geometry(
                            f"smpl_mesh_{i}_human_{human_idx}", mesh, mesh_mat)
            else:
                if hasattr(frame_meshes, 'vertices') and len(frame_meshes.vertices) > 0:
                    render.scene.add_geometry(
                        f"smpl_mesh_{i}", frame_meshes, mesh_mat)

        # Render scene-only visualization
        scene_only_img = render.render_to_image()
        scene_only_img_array = np.asarray(scene_only_img)

        # Flip vertically and horizontally if using fixed camera mode as they come out upside down and flipped
        if not use_predicted_camera:
            scene_only_img_array = np.flipud(scene_only_img_array)
            scene_only_img_array = np.fliplr(scene_only_img_array)

        scene_only_img_bgr = cv2.cvtColor(
            scene_only_img_array, cv2.COLOR_RGB2BGR)

        # Save scene-only frame
        scene_smpl_frame_path = os.path.join(
            scene_smpl_frames_folder, f"scene_smpl_frame_{i:04d}.png")
        cv2.imwrite(scene_smpl_frame_path, scene_only_img_bgr)
        scene_smpl_frames.append(scene_only_img_array)

        # Save bbox frame if available
        if human_boxes is not None and rgb_images is not None and i < len(rgb_images):
            # Convert tensor to numpy array for OpenCV operations
            bbox_frame_tensor = rgb_images[i].clone()
            if bbox_frame_tensor.dim() == 3 and bbox_frame_tensor.shape[0] == 3:
                # Convert from [3, H, W] to [H, W, 3]
                bbox_frame_tensor = bbox_frame_tensor.permute(1, 2, 0)

            bbox_frame = bbox_frame_tensor.cpu().numpy()
            if bbox_frame.max() <= 1.0:
                bbox_frame = (bbox_frame * 255).astype(np.uint8)
            else:
                bbox_frame = bbox_frame.astype(np.uint8)

            # Ensure the array is contiguous for OpenCV
            bbox_frame = np.ascontiguousarray(bbox_frame)

            # Draw bounding boxes for single human (using correct indexing)
            img_height, img_width = bbox_frame.shape[:2]
            
            human_idx = 0
            if human_idx < human_boxes.shape[0]:
                # Get normalized bbox: [x1, y1, x2, y2] in [0,1] range
                x1, y1, x2, y2 = human_boxes[human_idx, i]

                # Convert to pixel coordinates
                x1_pixel = int(x1 * img_width)
                y1_pixel = int(y1 * img_height)
                x2_pixel = int(x2 * img_width)
                y2_pixel = int(y2 * img_height)

                # Clamp to image boundaries
                x1_pixel = max(0, min(x1_pixel, img_width))
                y1_pixel = max(0, min(y1_pixel, img_height))
                x2_pixel = max(0, min(x2_pixel, img_width))
                y2_pixel = max(0, min(y2_pixel, img_height))

                # Choose color for each human (single color for now)
                color = (0, 255, 0) # Green

                # Draw bounding box
                cv2.rectangle(bbox_frame, (x1_pixel, y1_pixel),
                              (x2_pixel, y2_pixel), color, 2)

                # Add human ID label
                label = f"Human {human_idx}"
                label_size = cv2.getTextSize(
                    label, cv2.FONT_HERSHEY_SIMPLEX, 0.5, 1)[0]
                cv2.rectangle(bbox_frame, (x1_pixel, y1_pixel - label_size[1] - 5),
                              (x1_pixel + label_size[0], y1_pixel), color, -1)
                cv2.putText(bbox_frame, label, (x1_pixel, y1_pixel - 5),
                            cv2.FONT_HERSHEY_SIMPLEX, 0.5, (255, 255, 255), 1)

            bbox_frame_path = os.path.join(
                bbox_frames_folder, f"bbox_frame_{i:04d}.png")
            cv2.imwrite(bbox_frame_path, cv2.cvtColor(
                bbox_frame, cv2.COLOR_RGB2BGR))
            bbox_frames.append(bbox_frame)

        # Save input frame
        if rgb_images is not None and i < len(rgb_images):
            input_frame_path = os.path.join(
                input_frames_folder, f"input_frame_{i:04d}.png")
            # Ensure the frame is a valid numpy array
            frame = rgb_images[i]
            if isinstance(frame, np.ndarray) and frame.size > 0:
                cv2.imwrite(input_frame_path, cv2.cvtColor(
                    frame, cv2.COLOR_RGB2BGR))
                input_gif_frames.append(frame)
            elif isinstance(frame, torch.Tensor):
                # Convert tensor to numpy with proper shape handling
                frame_np = frame.cpu().numpy()

                # Handle different tensor formats
                if frame_np.ndim == 3:
                    if frame_np.shape[0] == 3:  # [3, H, W] format
                        frame_np = frame_np.transpose(
                            1, 2, 0)  # Convert to [H, W, 3]
                    # else: already in [H, W, 3] format
                # [1, 3, H, W] format
                elif frame_np.ndim == 4 and frame_np.shape[0] == 1:
                    frame_np = frame_np.squeeze(0).transpose(
                        1, 2, 0)  # Convert to [H, W, 3]

                # Ensure proper data type and range
                if frame_np.max() <= 1.0:
                    frame_np = (frame_np * 255).astype(np.uint8)
                else:
                    frame_np = frame_np.astype(np.uint8)

                # Ensure frame has 3 channels for RGB
                if frame_np.shape[-1] == 3:
                    cv2.imwrite(input_frame_path, cv2.cvtColor(
                        frame_np, cv2.COLOR_RGB2BGR))
                    input_gif_frames.append(frame_np)
                else:
                    print(
                        f"Warning: Frame has {frame_np.shape[-1]} channels, expected 3. Skipping frame at index {i}")
                    print(
                        f"Frame shape: {frame_np.shape}, dtype: {frame_np.dtype}")
                    print(f"Original tensor shape: {frame.shape}")
                    continue
            else:
                print(
                    f"Warning: Skipping invalid frame at index {i}: {type(frame)}")

    # Create videos for both visualizations
    print("Creating videos...")
    fourcc = cv2.VideoWriter_fourcc(*'mp4v')

    # Complete visualization video
    print("  - Scene point clouds + human point clouds video...")
    scene_human_video_writer = cv2.VideoWriter(
        scene_human_video_path, fourcc, FPS, (RENDER_WIDTH, RENDER_HEIGHT))
    for frame in scene_human_frames:
        frame_bgr = cv2.cvtColor(frame, cv2.COLOR_RGB2BGR)
        scene_human_video_writer.write(frame_bgr)
    scene_human_video_writer.release()

    # Scene-only visualization video
    print("  - Scene point clouds + SMPL meshes video...")
    scene_smpl_video_writer = cv2.VideoWriter(
        scene_smpl_video_path, fourcc, FPS, (RENDER_WIDTH, RENDER_HEIGHT))
    for frame in scene_smpl_frames:
        frame_bgr = cv2.cvtColor(frame, cv2.COLOR_RGB2BGR)
        scene_smpl_video_writer.write(frame_bgr)
    scene_smpl_video_writer.release()

    # Create GIFs and MP4s for both visualizations
    print("Creating GIFs and MP4s...")

    # Scene-human visualization GIF and MP4
    print("  - Scene point clouds + human point clouds GIF...")
    scene_human_frames_pil = [Image.fromarray(frame) for frame in scene_human_frames]
    scene_human_frames_pil[0].save(
        scene_human_gif_path,
        save_all=True,
        append_images=scene_human_frames_pil[1:],
        duration=1000//FPS,
        loop=0
    )
    print("  - Scene point clouds + human point clouds MP4...")
    create_mp4_from_frames(scene_human_frames, scene_human_gif_mp4_path, FPS)

    # Scene-SMPL visualization GIF and MP4
    print("  - Scene point clouds + SMPL meshes GIF...")
    scene_smpl_frames_pil = [Image.fromarray(
        frame) for frame in scene_smpl_frames]
    scene_smpl_frames_pil[0].save(
        scene_smpl_gif_path,
        save_all=True,
        append_images=scene_smpl_frames_pil[1:],
        duration=1000//FPS,
        loop=0
    )
    print("  - Scene point clouds + SMPL meshes MP4...")
    create_mp4_from_frames(scene_smpl_frames, scene_smpl_gif_mp4_path, FPS)

    if input_gif_frames:
        print("Creating input frames GIF...")
        input_frames_pil = [Image.fromarray(frame)
                            for frame in input_gif_frames]
        input_frames_pil[0].save(
            input_gif_path,
            save_all=True,
            append_images=input_frames_pil[1:],
            duration=1000//FPS,
            loop=0
        )
        print("Creating input frames MP4...")
        create_mp4_from_frames(input_gif_frames, input_gif_mp4_path, FPS)

    # Create chunk GIFs and MP4s for both visualizations
    print("Creating chunk GIFs and MP4s...")

    # Scene-human visualization chunk GIFs and MP4s
    print("  - Scene point clouds + human point clouds chunk GIFs and MP4s...")
    scene_human_chunk_gifs_folder = os.path.join(scene_human_gifs_folder, "chunks")
    os.makedirs(scene_human_chunk_gifs_folder, exist_ok=True)

    for chunk_idx in range(0, total_frames, chunk_size):
        end_idx = min(chunk_idx + chunk_size, total_frames)
        chunk_frames = scene_human_frames[chunk_idx:end_idx]

        if chunk_frames:
            chunk_gif_path = os.path.join(
                scene_human_chunk_gifs_folder, f"scene_human_chunk_{chunk_idx//chunk_size:02d}_frames_{chunk_idx:04d}-{end_idx-1:04d}.gif")
            chunk_mp4_path = os.path.join(
                scene_human_chunk_gifs_folder, f"scene_human_chunk_{chunk_idx//chunk_size:02d}_frames_{chunk_idx:04d}-{end_idx-1:04d}.mp4")
            chunk_frames_pil = [Image.fromarray(
                frame) for frame in chunk_frames]
            chunk_frames_pil[0].save(
                chunk_gif_path,
                save_all=True,
                append_images=chunk_frames_pil[1:],
                duration=1000//FPS,
                loop=0
            )
            create_mp4_from_frames(chunk_frames, chunk_mp4_path, FPS)

    # Scene-SMPL visualization chunk GIFs and MP4s
    print("  - Scene point clouds + SMPL meshes chunk GIFs and MP4s...")
    scene_smpl_chunk_gifs_folder = os.path.join(
        scene_smpl_gifs_folder, "chunks")
    os.makedirs(scene_smpl_chunk_gifs_folder, exist_ok=True)

    for chunk_idx in range(0, total_frames, chunk_size):
        end_idx = min(chunk_idx + chunk_size, total_frames)
        chunk_frames = scene_smpl_frames[chunk_idx:end_idx]

        if chunk_frames:
            chunk_gif_path = os.path.join(
                scene_smpl_chunk_gifs_folder, f"scene_smpl_chunk_{chunk_idx//chunk_size:02d}_frames_{chunk_idx:04d}-{end_idx-1:04d}.gif")
            chunk_mp4_path = os.path.join(
                scene_smpl_chunk_gifs_folder, f"scene_smpl_chunk_{chunk_idx//chunk_size:02d}_frames_{chunk_idx:04d}-{end_idx-1:04d}.mp4")
            chunk_frames_pil = [Image.fromarray(
                frame) for frame in chunk_frames]
            chunk_frames_pil[0].save(
                chunk_gif_path,
                save_all=True,
                append_images=chunk_frames_pil[1:],
                duration=1000//FPS,
                loop=0
            )
            create_mp4_from_frames(chunk_frames, chunk_mp4_path, FPS)

    # Create input chunk GIFs and MP4s if available
    if input_gif_frames:
        print("Creating input frames chunk GIFs and MP4s...")
        input_chunk_gifs_folder = os.path.join(
            viz_folder, "input_chunk_gifs")
        os.makedirs(input_chunk_gifs_folder, exist_ok=True)

        for chunk_idx in range(0, len(input_gif_frames), chunk_size):
            end_idx = min(chunk_idx + chunk_size, len(input_gif_frames))
            chunk_input_frames = input_gif_frames[chunk_idx:end_idx]

            if chunk_input_frames:
                chunk_input_gif_path = os.path.join(
                    input_chunk_gifs_folder, f"input_chunk_{chunk_idx//chunk_size:02d}_frames_{chunk_idx:04d}-{end_idx-1:04d}.gif")
                chunk_input_mp4_path = os.path.join(
                    input_chunk_gifs_folder, f"input_chunk_{chunk_idx//chunk_size:02d}_frames_{chunk_idx:04d}-{end_idx-1:04d}.mp4")
                chunk_input_frames_pil = [Image.fromarray(
                    frame) for frame in chunk_input_frames]
                chunk_input_frames_pil[0].save(
                    chunk_input_gif_path,
                    save_all=True,
                    append_images=chunk_input_frames_pil[1:],
                    duration=1000//FPS,
                    loop=0
                )
                create_mp4_from_frames(
                    chunk_input_frames, chunk_input_mp4_path, FPS)
                print(f"  - Input chunk GIF saved: {chunk_input_gif_path}")
                print(f"  - Input chunk MP4 saved: {chunk_input_mp4_path}")

    print(f"Visualization completed!")
