import argparse
import os
import torch
import numpy as np
import random
import logging
from unish.utils.inference_utils import *

def setup_seed(seed):
    torch.manual_seed(seed)
    torch.cuda.manual_seed_all(seed)
    np.random.seed(seed)
    random.seed(seed)
    torch.backends.cudnn.deterministic = True

def setup_logging(output_dir):
    os.makedirs(output_dir, exist_ok=True)
    
    # Create logger
    logger = logging.getLogger()
    logger.setLevel(logging.INFO)
    
    # Create handlers
    c_handler = logging.StreamHandler()
    f_handler = logging.FileHandler(os.path.join(output_dir, 'inference.log'), mode='w')
    
    # Create formatters and add it to handlers
    c_format = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
    f_format = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
    c_handler.setFormatter(c_format)
    f_handler.setFormatter(f_format)
    
    # Add handlers to the logger
    logger.addHandler(c_handler)
    logger.addHandler(f_handler)
    
    return logger

def main():
    parser = argparse.ArgumentParser(description="Video Inference Script")
    parser.add_argument("--video_path", type=str, required=True,
                        help="Path to the input video file or directory containing images")
    parser.add_argument("--fps", type=float, default=6.0,
                        help="Target FPS for frame extraction (default: 6.0)")
    parser.add_argument("--original_fps", type=float, default=30.0,
                        help="Original FPS of the image sequence (default: 30.0, used only for directory input)")
    parser.add_argument("--target_size", type=int, default=518,
                        help="Target size for frame processing (default: 518)")
    parser.add_argument("--checkpoint", type=str, default="checkpoints/unish_release.safetensors",
                        help="Path to the model checkpoint")
    parser.add_argument("--output_dir", type=str, default="inference_results_video",
                        help="Output directory for results")
    parser.add_argument("--body_models_path", type=str, default="body_models/",
                        help="Path to SMPL body models")
    parser.add_argument("--device", type=str, default="cuda",
                        help="Device to run inference on")
    parser.add_argument("--save_results", action="store_true", default=True,
                        help="Save additional results including smpl_points_for_camera (default: True)")
    parser.add_argument("--chunk_size", type=int, default=30,
                        help="Number of frames to process in each chunk during inference (default: 30)")
    parser.add_argument("--gpu_id", type=int, default=0,
                        help="GPU ID to use for inference (default: 0)")
    parser.add_argument("--camera_mode", type=str, default="fixed",
                        choices=["predicted", "fixed"],
                        help="Camera mode: 'predicted' uses model-predicted camera parameters, "
                             "'fixed' uses a fixed camera angle (default: predicted)")
    parser.add_argument("--human_idx", type=int, default=0,
                        help="Human index to process (default: 0)")
    parser.add_argument("--start_idx", type=int, default=None,
                        help="Start frame index for processing (default: None, process from beginning)")
    parser.add_argument("--end_idx", type=int, default=None,
                        help="End frame index for processing (default: None, process to end)")
    parser.add_argument("--bbox_scale", type=float, default=1.0,
                        help="Scale factor for bounding box size (default: 1.0)")
    parser.add_argument("--conf_thres", type=float, default=0.1,
                        help="Confidence threshold for point cloud generation (default: 0.1)")
    
    # New arguments
    parser.add_argument("--seed", type=int, default=42, help="Random seed for reproducibility")
    parser.add_argument("--yolo_ckpt", type=str, default="ckpts/yolo11n.pt", help="Path to YOLO checkpoint")
    parser.add_argument("--sam2_model", type=str, default="facebook/sam2-hiera-large", help="SAM2 model name or path")

    args = parser.parse_args()

    # Setup seed
    setup_seed(args.seed)

    # Setup logging
    logger = setup_logging(args.output_dir)

    # Setup device
    if torch.cuda.is_available():
        if args.device == "cuda":
            # Use specified GPU ID
            device = torch.device(f"cuda:{args.gpu_id}")
            # Set the current CUDA device
            torch.cuda.set_device(args.gpu_id)
            logger.info(
                f"Using GPU {args.gpu_id}: {torch.cuda.get_device_name(args.gpu_id)}")
        else:
            device = torch.device(args.device)
    else:
        device = torch.device("cpu")
        logger.info("CUDA not available, using CPU")

    logger.info(f"Using device: {device}")

    # Load model
    logger.info("Loading model...")
    model = load_model(args.checkpoint)
    model = model.to(device)
    model.eval()

    # Process video
    logger.info(f"Processing video: {args.video_path}")
    data_dict = process_video(
        args.video_path, args.fps, args.human_idx, args.target_size,
        bbox_scale=args.bbox_scale, start_idx=args.start_idx, end_idx=args.end_idx, 
        original_fps=args.original_fps,
        yolo_ckpt=args.yolo_ckpt, sam2_model=args.sam2_model
    )

    # Run inference
    results = run_inference(model, data_dict, device, args.chunk_size)

    # Create output directory
    os.makedirs(args.output_dir, exist_ok=True)

    viz_scene_point_clouds, viz_smpl_meshes, viz_scene_only_point_clouds, smpl_points_for_camera = generate_mixed_geometries_in_memory(
        results, args.body_models_path, fps=args.fps, conf_thres=args.conf_thres
    )

    # Determine camera mode based on arguments
    use_predicted_camera = (args.camera_mode == "predicted")
    logger.info(f"Using {args.camera_mode} camera mode")

    original_rgb_images = results['rgb_images']

    if original_rgb_images is not None:
        if hasattr(original_rgb_images, 'permute'):  # It's a torch tensor
            original_rgb_images = original_rgb_images.permute(
                0, 2, 3, 1).cpu().numpy()  # [S, H, W, 3]
        elif not isinstance(original_rgb_images, np.ndarray):
            original_rgb_images = np.array(original_rgb_images)

        # Ensure proper data type and range
        if original_rgb_images.max() <= 1.0:
            original_rgb_images = (
                original_rgb_images * 255).astype(np.uint8)

    original_human_boxes = data_dict['human_boxes']

    run_visualization(viz_scene_point_clouds, viz_smpl_meshes, smpl_points_for_camera,
                                    args.output_dir, results['seq_name'],
                                    fps=args.fps,  # Use original fps
                                    rgb_images=original_rgb_images,
                                    human_boxes=original_human_boxes,
                                    chunk_size=args.chunk_size,  # Use original chunk size
                                    results=results,
                                    use_predicted_camera=use_predicted_camera,
                                    scene_only_point_clouds=viz_scene_only_point_clouds,
                                    conf_thres=args.conf_thres)

    if args.save_results:

        logger.info("Creating SMPL meshes per frame...")
        save_smpl_meshes_per_frame(
            results, args.output_dir, args.body_models_path)

        logger.info("Saving scene point clouds (without human)...")
        save_scene_only_point_clouds(
            viz_scene_only_point_clouds, args.output_dir, results['seq_name'])

        logger.info("Saving human point clouds...")
        save_human_point_clouds(viz_scene_point_clouds,
                                viz_scene_only_point_clouds, args.output_dir, results['seq_name'], results)

        logger.info("Saving camera parameters per frame...")
        save_camera_parameters_per_frame(
            results, args.output_dir, results['seq_name'])

    logger.info(f"Inference completed! Results saved to {args.output_dir}")


if __name__ == "__main__":
    main()
