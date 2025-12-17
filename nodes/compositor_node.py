"""
Main compositor node - receives inputs and sends to frontend
"""
import json
import base64
import os
import time
import numpy as np
from pathlib import Path

# Project storage directory (relative to this file's location)
PROJECTS_DIR = Path(__file__).parent.parent / "projects"


class CompositorEditorNode:
    """
    Main node that opens the compositor UI and receives depth/image inputs
    """

    CATEGORY = "Weyl/Compositor"
    RETURN_TYPES = ("MASK", "IMAGE")
    RETURN_NAMES = ("text_matte", "preview")
    FUNCTION = "process"

    # Store compositor data between executions
    _compositor_data = {}

    @classmethod
    def INPUT_TYPES(cls):
        return {
            "required": {
                "source_image": ("IMAGE",),
                "depth_map": ("IMAGE",),
            },
            "optional": {
                "frame_count": ("INT", {
                    "default": 81,
                    "min": 1,
                    "max": 241,
                    "step": 4  # Wan uses 4N+1 pattern
                }),
            },
            "hidden": {
                "unique_id": "UNIQUE_ID",
            }
        }

    def process(self, source_image, depth_map, frame_count=81, unique_id=None):
        """
        Process inputs and send to frontend via WebSocket
        """
        # Lazy import to avoid issues when ComfyUI isn't available
        try:
            from server import PromptServer

            # Convert tensors to base64 for frontend
            source_b64 = self._tensor_to_base64(source_image)
            depth_b64 = self._tensor_to_base64(depth_map)

            # Get dimensions
            _, height, width, _ = source_image.shape

            # Send to frontend
            PromptServer.instance.send_sync(
                "weyl.compositor.inputs_ready",
                {
                    "node_id": unique_id,
                    "source_image": source_b64,
                    "depth_map": depth_b64,
                    "width": width,
                    "height": height,
                    "frame_count": frame_count
                }
            )
        except ImportError:
            # Running outside ComfyUI context
            pass

        # Check if we have compositor output ready
        if unique_id in self._compositor_data:
            matte_data = self._compositor_data[unique_id]
            # Convert back to tensors
            matte_tensor = self._base64_to_tensor(matte_data['matte'])
            preview_tensor = self._base64_to_tensor(matte_data['preview'])
            return (matte_tensor, preview_tensor)

        # Return placeholder if no compositor data yet
        import torch
        _, height, width, _ = source_image.shape
        empty_mask = torch.zeros((frame_count, height, width), dtype=torch.float32)
        empty_image = torch.zeros((frame_count, height, width, 3), dtype=torch.float32)

        return (empty_mask, empty_image)

    def _tensor_to_base64(self, tensor):
        """Convert image tensor to base64 PNG"""
        import torch
        from PIL import Image
        import io

        # Take first frame if batch
        if len(tensor.shape) == 4:
            tensor = tensor[0]

        # Convert to numpy and scale to 0-255
        np_image = (tensor.cpu().numpy() * 255).astype(np.uint8)

        # Create PIL image
        pil_image = Image.fromarray(np_image)

        # Encode to base64
        buffer = io.BytesIO()
        pil_image.save(buffer, format='PNG')
        return base64.b64encode(buffer.getvalue()).decode('utf-8')

    def _base64_to_tensor(self, b64_string):
        """Convert base64 PNG to tensor"""
        import torch
        from PIL import Image
        import io

        image_data = base64.b64decode(b64_string)
        pil_image = Image.open(io.BytesIO(image_data))
        np_image = np.array(pil_image).astype(np.float32) / 255.0

        return torch.from_numpy(np_image)


# Register custom routes when running in ComfyUI
try:
    from server import PromptServer
    from aiohttp import web

    routes = PromptServer.instance.routes

    @routes.post('/weyl/compositor/set_output')
    async def set_compositor_output(request):
        """Receive matte data from frontend"""
        data = await request.json()
        node_id = data.get('node_id')

        if node_id:
            CompositorEditorNode._compositor_data[node_id] = {
                'matte': data.get('matte'),
                'preview': data.get('preview')
            }
            return web.json_response({"status": "success"})

        return web.json_response({"status": "error", "message": "No node_id"}, status=400)

    @routes.post('/weyl/compositor/save_project')
    async def save_project(request):
        """Save compositor project state"""
        try:
            data = await request.json()

            # Ensure projects directory exists
            PROJECTS_DIR.mkdir(parents=True, exist_ok=True)

            # Get project ID or generate one
            project_id = data.get('project_id')
            if not project_id:
                # Generate ID from project name and timestamp
                name = data.get('project', {}).get('meta', {}).get('name', 'untitled')
                safe_name = "".join(c if c.isalnum() or c in '-_' else '_' for c in name)
                project_id = f"{safe_name}_{int(time.time())}"

            # Save project JSON
            project_path = PROJECTS_DIR / f"{project_id}.json"
            with open(project_path, 'w', encoding='utf-8') as f:
                json.dump(data.get('project', data), f, indent=2)

            return web.json_response({
                "status": "success",
                "project_id": project_id,
                "path": str(project_path)
            })
        except Exception as e:
            return web.json_response({
                "status": "error",
                "message": str(e)
            }, status=500)

    @routes.get('/weyl/compositor/load_project/{project_id}')
    async def load_project(request):
        """Load compositor project state"""
        try:
            project_id = request.match_info['project_id']

            # Find project file
            project_path = PROJECTS_DIR / f"{project_id}.json"
            if not project_path.exists():
                return web.json_response({
                    "status": "error",
                    "message": f"Project not found: {project_id}"
                }, status=404)

            # Load and return project
            with open(project_path, 'r', encoding='utf-8') as f:
                project = json.load(f)

            return web.json_response({
                "status": "success",
                "project": project,
                "project_id": project_id
            })
        except Exception as e:
            return web.json_response({
                "status": "error",
                "message": str(e)
            }, status=500)

    @routes.get('/weyl/compositor/list_projects')
    async def list_projects(request):
        """List all saved compositor projects"""
        try:
            # Ensure projects directory exists
            PROJECTS_DIR.mkdir(parents=True, exist_ok=True)

            projects = []
            for path in PROJECTS_DIR.glob("*.json"):
                try:
                    with open(path, 'r', encoding='utf-8') as f:
                        project = json.load(f)

                    projects.append({
                        "id": path.stem,
                        "name": project.get('meta', {}).get('name', path.stem),
                        "created": project.get('meta', {}).get('created'),
                        "modified": project.get('meta', {}).get('modified'),
                        "path": str(path)
                    })
                except (json.JSONDecodeError, KeyError):
                    # Skip invalid project files
                    projects.append({
                        "id": path.stem,
                        "name": path.stem,
                        "error": "Invalid project file"
                    })

            # Sort by modified date, newest first
            projects.sort(key=lambda p: p.get('modified', ''), reverse=True)

            return web.json_response({
                "status": "success",
                "projects": projects
            })
        except Exception as e:
            return web.json_response({
                "status": "error",
                "message": str(e)
            }, status=500)

    @routes.delete('/weyl/compositor/delete_project/{project_id}')
    async def delete_project(request):
        """Delete a compositor project"""
        try:
            project_id = request.match_info['project_id']

            project_path = PROJECTS_DIR / f"{project_id}.json"
            if not project_path.exists():
                return web.json_response({
                    "status": "error",
                    "message": f"Project not found: {project_id}"
                }, status=404)

            project_path.unlink()

            return web.json_response({
                "status": "success",
                "message": f"Deleted project: {project_id}"
            })
        except Exception as e:
            return web.json_response({
                "status": "error",
                "message": str(e)
            }, status=500)

    # =========================================================================
    # Segmentation Endpoint - SAM2/MatSeg for layer creation
    # =========================================================================

    # Lazy-loaded segmentation model
    _segmentation_model = None
    _segmentation_model_type = None

    def _load_segmentation_model(model_type='sam2'):
        """Lazy load segmentation model"""
        global _segmentation_model, _segmentation_model_type

        if _segmentation_model is not None and _segmentation_model_type == model_type:
            return _segmentation_model

        try:
            if model_type == 'sam2':
                # Try to load SAM2 from ComfyUI's model system
                from segment_anything import sam_model_registry, SamPredictor
                import torch
                import folder_paths

                # Look for SAM2 checkpoint
                sam_checkpoint = None
                model_folder = folder_paths.get_folder_paths("checkpoints")[0] if hasattr(folder_paths, 'get_folder_paths') else "models"

                for name in ['sam_vit_h_4b8939.pth', 'sam_vit_l_0b3195.pth', 'sam_vit_b_01ec64.pth']:
                    check_path = os.path.join(model_folder, 'sam', name)
                    if os.path.exists(check_path):
                        sam_checkpoint = check_path
                        model_type_sam = 'vit_h' if 'vit_h' in name else ('vit_l' if 'vit_l' in name else 'vit_b')
                        break

                if sam_checkpoint:
                    device = "cuda" if torch.cuda.is_available() else "cpu"
                    sam = sam_model_registry[model_type_sam](checkpoint=sam_checkpoint)
                    sam.to(device=device)
                    _segmentation_model = SamPredictor(sam)
                    _segmentation_model_type = model_type
                    return _segmentation_model
                else:
                    raise FileNotFoundError("No SAM checkpoint found")

            elif model_type == 'matseg':
                # MatSeg for material segmentation
                # This would load a material segmentation model
                raise NotImplementedError("MatSeg not yet implemented - use sam2")

        except Exception as e:
            print(f"[Weyl] Failed to load {model_type} model: {e}")
            return None

        return None

    def _segment_with_points(image_np, points, labels, model):
        """Run SAM2 segmentation with point prompts"""
        import torch

        model.set_image(image_np)

        points_np = np.array(points)
        labels_np = np.array(labels)

        masks, scores, logits = model.predict(
            point_coords=points_np,
            point_labels=labels_np,
            multimask_output=True,
        )

        # Return the mask with the highest score
        best_idx = np.argmax(scores)
        return masks[best_idx]

    def _segment_with_box(image_np, box, model):
        """Run SAM2 segmentation with box prompt"""
        import torch

        model.set_image(image_np)

        box_np = np.array(box)  # [x1, y1, x2, y2]

        masks, scores, logits = model.predict(
            box=box_np,
            multimask_output=True,
        )

        # Return the mask with the highest score
        best_idx = np.argmax(scores)
        return masks[best_idx]

    def _segment_auto(image_np, model):
        """Run automatic segmentation to find all objects"""
        from segment_anything import SamAutomaticMaskGenerator

        # Create automatic mask generator
        mask_generator = SamAutomaticMaskGenerator(model.model)

        # Generate all masks
        masks = mask_generator.generate(image_np)

        # Return list of masks with metadata
        return [{
            'mask': mask['segmentation'],
            'area': mask['area'],
            'bbox': mask['bbox'],  # [x, y, w, h]
            'score': mask['predicted_iou'],
            'stability': mask['stability_score']
        } for mask in masks]

    @routes.post('/weyl/segment')
    async def segment_image(request):
        """
        Segment image using SAM2 or MatSeg.

        Request body:
        {
            "image": "base64_encoded_png",
            "mode": "point" | "box" | "auto",
            "model": "sam2" | "matseg",
            "points": [[x, y], ...],      // For point mode
            "labels": [1, 0, ...],         // 1=foreground, 0=background
            "box": [x1, y1, x2, y2],       // For box mode
            "min_area": 100,               // For auto mode - minimum mask area
            "max_masks": 20                // For auto mode - maximum masks to return
        }

        Returns:
        {
            "status": "success",
            "masks": [
                {
                    "mask": "base64_encoded_png",
                    "bounds": {"x": 0, "y": 0, "width": 100, "height": 100},
                    "area": 1234,
                    "score": 0.95
                }
            ]
        }
        """
        try:
            data = await request.json()

            # Decode input image
            image_b64 = data.get('image')
            if not image_b64:
                return web.json_response({
                    "status": "error",
                    "message": "No image provided"
                }, status=400)

            from PIL import Image
            import io

            # Decode base64 image
            image_data = base64.b64decode(image_b64)
            pil_image = Image.open(io.BytesIO(image_data)).convert('RGB')
            image_np = np.array(pil_image)

            mode = data.get('mode', 'point')
            model_type = data.get('model', 'sam2')

            # Load segmentation model
            model = _load_segmentation_model(model_type)
            if model is None:
                # Fallback to simple threshold-based segmentation
                return _simple_segment(data, image_np)

            results = []

            if mode == 'point':
                points = data.get('points', [])
                labels = data.get('labels', [1] * len(points))

                if not points:
                    return web.json_response({
                        "status": "error",
                        "message": "No points provided for point mode"
                    }, status=400)

                mask = _segment_with_points(image_np, points, labels, model)
                mask_b64, bounds = _mask_to_base64_with_bounds(mask)

                results.append({
                    "mask": mask_b64,
                    "bounds": bounds,
                    "area": int(np.sum(mask)),
                    "score": 1.0
                })

            elif mode == 'box':
                box = data.get('box')
                if not box or len(box) != 4:
                    return web.json_response({
                        "status": "error",
                        "message": "Invalid box format - expected [x1, y1, x2, y2]"
                    }, status=400)

                mask = _segment_with_box(image_np, box, model)
                mask_b64, bounds = _mask_to_base64_with_bounds(mask)

                results.append({
                    "mask": mask_b64,
                    "bounds": bounds,
                    "area": int(np.sum(mask)),
                    "score": 1.0
                })

            elif mode == 'auto':
                min_area = data.get('min_area', 100)
                max_masks = data.get('max_masks', 20)

                auto_masks = _segment_auto(image_np, model)

                # Filter by minimum area
                auto_masks = [m for m in auto_masks if m['area'] >= min_area]

                # Sort by area (largest first) and take top N
                auto_masks.sort(key=lambda m: m['area'], reverse=True)
                auto_masks = auto_masks[:max_masks]

                for mask_data in auto_masks:
                    mask_b64, bounds = _mask_to_base64_with_bounds(mask_data['mask'])
                    results.append({
                        "mask": mask_b64,
                        "bounds": bounds,
                        "area": mask_data['area'],
                        "score": mask_data['score']
                    })

            else:
                return web.json_response({
                    "status": "error",
                    "message": f"Unknown segmentation mode: {mode}"
                }, status=400)

            return web.json_response({
                "status": "success",
                "masks": results
            })

        except Exception as e:
            import traceback
            traceback.print_exc()
            return web.json_response({
                "status": "error",
                "message": str(e)
            }, status=500)

    def _mask_to_base64_with_bounds(mask):
        """Convert binary mask to base64 PNG and calculate bounds"""
        from PIL import Image
        import io

        # Convert boolean mask to uint8
        mask_uint8 = (mask.astype(np.uint8) * 255)

        # Find bounding box of non-zero region
        rows = np.any(mask, axis=1)
        cols = np.any(mask, axis=0)

        if not np.any(rows) or not np.any(cols):
            # Empty mask
            bounds = {"x": 0, "y": 0, "width": mask.shape[1], "height": mask.shape[0]}
        else:
            rmin, rmax = np.where(rows)[0][[0, -1]]
            cmin, cmax = np.where(cols)[0][[0, -1]]
            bounds = {
                "x": int(cmin),
                "y": int(rmin),
                "width": int(cmax - cmin + 1),
                "height": int(rmax - rmin + 1)
            }

        # Convert to PIL and encode
        pil_mask = Image.fromarray(mask_uint8, mode='L')

        buffer = io.BytesIO()
        pil_mask.save(buffer, format='PNG')
        mask_b64 = base64.b64encode(buffer.getvalue()).decode('utf-8')

        return mask_b64, bounds

    def _simple_segment(data, image_np):
        """Fallback segmentation without AI model - uses color/luminance thresholding"""
        from PIL import Image
        import io

        mode = data.get('mode', 'point')

        if mode == 'box':
            # Simple box selection - just create a rectangular mask
            box = data.get('box', [0, 0, image_np.shape[1], image_np.shape[0]])
            x1, y1, x2, y2 = [int(v) for v in box]

            mask = np.zeros((image_np.shape[0], image_np.shape[1]), dtype=bool)
            mask[y1:y2, x1:x2] = True

            mask_b64, bounds = _mask_to_base64_with_bounds(mask)

            return web.json_response({
                "status": "success",
                "masks": [{
                    "mask": mask_b64,
                    "bounds": bounds,
                    "area": int(np.sum(mask)),
                    "score": 1.0
                }],
                "fallback": True,
                "message": "Using simple box selection (SAM2 not available)"
            })

        elif mode == 'point':
            # Simple flood-fill like selection based on color similarity
            points = data.get('points', [])
            if not points:
                return web.json_response({
                    "status": "error",
                    "message": "No points provided"
                }, status=400)

            # Use first point as seed, do color-based region growing
            px, py = int(points[0][0]), int(points[0][1])
            py = min(py, image_np.shape[0] - 1)
            px = min(px, image_np.shape[1] - 1)

            seed_color = image_np[py, px].astype(np.float32)
            tolerance = data.get('tolerance', 30)

            # Color distance
            color_diff = np.sqrt(np.sum((image_np.astype(np.float32) - seed_color) ** 2, axis=2))
            mask = color_diff < tolerance

            mask_b64, bounds = _mask_to_base64_with_bounds(mask)

            return web.json_response({
                "status": "success",
                "masks": [{
                    "mask": mask_b64,
                    "bounds": bounds,
                    "area": int(np.sum(mask)),
                    "score": 0.5
                }],
                "fallback": True,
                "message": "Using color-based selection (SAM2 not available)"
            })

        else:
            return web.json_response({
                "status": "error",
                "message": f"Auto mode requires SAM2 model"
            }, status=400)

    # =========================================================================
    # Depth Estimation Endpoint - DepthAnything V3
    # =========================================================================

    _depth_model = None

    def _load_depth_model(model_name='DA3-LARGE-1.1'):
        """Lazy load Depth Anything V3 model"""
        global _depth_model

        if _depth_model is not None:
            return _depth_model

        try:
            import torch

            # Try loading from depth_anything_3 package (official)
            try:
                from depth_anything_3.api import DepthAnything3
                _depth_model = DepthAnything3.from_pretrained(f"depth-anything/{model_name}")
                device = "cuda" if torch.cuda.is_available() else "cpu"
                _depth_model = _depth_model.to(device=torch.device(device))
                print(f"[Weyl] Loaded DepthAnything V3 ({model_name}) on {device}")
                return _depth_model
            except ImportError:
                pass

            # Try ComfyUI custom nodes path
            try:
                import folder_paths
                da3_path = os.path.join(folder_paths.get_folder_paths("custom_nodes")[0],
                                       "ComfyUI-DepthAnythingV3")
                if os.path.exists(da3_path):
                    import sys
                    sys.path.insert(0, da3_path)
                    from depth_anything_v3 import DepthAnythingV3
                    _depth_model = DepthAnythingV3(model_name)
                    print(f"[Weyl] Loaded DepthAnything V3 from ComfyUI custom nodes")
                    return _depth_model
            except Exception as e:
                print(f"[Weyl] Failed to load from custom nodes: {e}")

            raise ImportError("DepthAnything V3 not available")

        except Exception as e:
            print(f"[Weyl] Failed to load DepthAnything V3: {e}")
            return None

    @routes.post('/weyl/depth')
    async def generate_depth(request):
        """
        Generate depth map using DepthAnything V3.

        Request body:
        {
            "image": "base64_encoded_png",
            "model": "DA3-LARGE-1.1" | "DA3-GIANT-1.1" | "DA3NESTED-GIANT-LARGE-1.1",
            "return_confidence": false,
            "return_intrinsics": false
        }

        Returns:
        {
            "status": "success",
            "depth": "base64_encoded_png",  // Grayscale depth map
            "confidence": "base64_encoded_png",  // Optional confidence map
            "intrinsics": [[fx, 0, cx], [0, fy, cy], [0, 0, 1]],  // Optional camera intrinsics
            "metadata": {
                "model": "DA3-LARGE-1.1",
                "width": 1024,
                "height": 768
            }
        }
        """
        try:
            data = await request.json()

            # Decode input image
            image_b64 = data.get('image')
            if not image_b64:
                return web.json_response({
                    "status": "error",
                    "message": "No image provided"
                }, status=400)

            from PIL import Image
            import io
            import torch

            # Decode base64 image
            image_data = base64.b64decode(image_b64)
            pil_image = Image.open(io.BytesIO(image_data)).convert('RGB')

            model_name = data.get('model', 'DA3-LARGE-1.1')
            return_confidence = data.get('return_confidence', False)
            return_intrinsics = data.get('return_intrinsics', False)

            # Try to load and run the model
            model = _load_depth_model(model_name)

            if model is not None:
                # Save temp image for inference
                temp_path = '/tmp/weyl_depth_input.png'
                pil_image.save(temp_path)

                # Run inference
                result = model.inference([temp_path])

                # Get depth map
                depth_np = result['depth'][0]  # [H, W] float32

                # Normalize to 0-255 for PNG export
                depth_min = depth_np.min()
                depth_max = depth_np.max()
                depth_normalized = ((depth_np - depth_min) / (depth_max - depth_min + 1e-6) * 255).astype(np.uint8)

                # Convert to base64
                depth_pil = Image.fromarray(depth_normalized, mode='L')
                buffer = io.BytesIO()
                depth_pil.save(buffer, format='PNG')
                depth_b64 = base64.b64encode(buffer.getvalue()).decode('utf-8')

                response = {
                    "status": "success",
                    "depth": depth_b64,
                    "metadata": {
                        "model": model_name,
                        "width": pil_image.width,
                        "height": pil_image.height,
                        "depth_min": float(depth_min),
                        "depth_max": float(depth_max)
                    }
                }

                # Optional confidence map
                if return_confidence and 'conf' in result:
                    conf_np = result['conf'][0]
                    conf_normalized = (conf_np * 255).astype(np.uint8)
                    conf_pil = Image.fromarray(conf_normalized, mode='L')
                    buffer = io.BytesIO()
                    conf_pil.save(buffer, format='PNG')
                    response['confidence'] = base64.b64encode(buffer.getvalue()).decode('utf-8')

                # Optional camera intrinsics
                if return_intrinsics and 'intrinsics' in result:
                    response['intrinsics'] = result['intrinsics'][0].tolist()

                return web.json_response(response)

            else:
                # Fallback: Simple MiDaS-style depth estimation
                return _fallback_depth_estimation(pil_image)

        except Exception as e:
            import traceback
            traceback.print_exc()
            return web.json_response({
                "status": "error",
                "message": str(e)
            }, status=500)

    def _fallback_depth_estimation(pil_image):
        """Fallback depth estimation using grayscale luminance"""
        from PIL import Image
        import io

        # Simple fallback: convert to grayscale (not real depth, but placeholder)
        gray = pil_image.convert('L')

        buffer = io.BytesIO()
        gray.save(buffer, format='PNG')
        depth_b64 = base64.b64encode(buffer.getvalue()).decode('utf-8')

        return web.json_response({
            "status": "success",
            "depth": depth_b64,
            "fallback": True,
            "message": "Using grayscale fallback (DepthAnything V3 not available)",
            "metadata": {
                "model": "fallback",
                "width": pil_image.width,
                "height": pil_image.height
            }
        })

    # =========================================================================
    # Normal Map Endpoint - NormalCrafter or algebraic depth-to-normal
    # =========================================================================

    _normal_model = None

    def _load_normal_model():
        """Lazy load NormalCrafter model"""
        global _normal_model

        if _normal_model is not None:
            return _normal_model

        try:
            # Try loading NormalCrafter from ComfyUI custom nodes
            import folder_paths
            nc_path = os.path.join(folder_paths.get_folder_paths("custom_nodes")[0],
                                   "ComfyUI-NormalCrafterWrapper")
            if os.path.exists(nc_path):
                import sys
                sys.path.insert(0, nc_path)
                # NormalCrafter loading would go here
                print(f"[Weyl] Found NormalCrafter at {nc_path}")
                # For now, we'll use algebraic depth-to-normal
                return None

        except Exception as e:
            print(f"[Weyl] Failed to load NormalCrafter: {e}")

        return None

    def _depth_to_normal_algebraic(depth_np):
        """
        Convert depth map to normal map using Sobel gradients.
        This is a fast algebraic approach that doesn't require a neural network.
        """
        from scipy import ndimage

        # Normalize depth to 0-1
        depth = depth_np.astype(np.float32)
        if depth.max() > 1:
            depth = depth / 255.0

        # Compute gradients using Sobel filters
        dz_dx = ndimage.sobel(depth, axis=1)  # Horizontal gradient
        dz_dy = ndimage.sobel(depth, axis=0)  # Vertical gradient

        # Construct normal vectors: N = normalize([-dz/dx, -dz/dy, 1])
        normal = np.zeros((*depth.shape, 3), dtype=np.float32)
        normal[..., 0] = -dz_dx
        normal[..., 1] = -dz_dy
        normal[..., 2] = 1.0

        # Normalize
        norm = np.linalg.norm(normal, axis=2, keepdims=True)
        normal = normal / (norm + 1e-6)

        # Convert from [-1, 1] to [0, 255] for PNG
        normal_uint8 = ((normal + 1) * 0.5 * 255).astype(np.uint8)

        return normal_uint8

    @routes.post('/weyl/normal')
    async def generate_normal(request):
        """
        Generate normal map from image or depth map.

        Request body:
        {
            "image": "base64_encoded_png",  // RGB image
            "depth": "base64_encoded_png",  // Optional: pre-computed depth map
            "method": "algebraic" | "normalcrafter",
            "depth_model": "DA3-LARGE-1.1"  // If depth not provided
        }

        Returns:
        {
            "status": "success",
            "normal": "base64_encoded_png",  // RGB normal map
            "depth": "base64_encoded_png",   // Depth map used (if generated)
            "metadata": {...}
        }
        """
        try:
            data = await request.json()

            from PIL import Image
            import io

            method = data.get('method', 'algebraic')

            # Get or generate depth map
            depth_np = None

            if 'depth' in data and data['depth']:
                # Use provided depth map
                depth_data = base64.b64decode(data['depth'])
                depth_pil = Image.open(io.BytesIO(depth_data)).convert('L')
                depth_np = np.array(depth_pil)

            elif 'image' in data and data['image']:
                # Generate depth from image
                image_data = base64.b64decode(data['image'])
                pil_image = Image.open(io.BytesIO(image_data)).convert('RGB')

                # Try DepthAnything V3
                model = _load_depth_model(data.get('depth_model', 'DA3-LARGE-1.1'))

                if model is not None:
                    temp_path = '/tmp/weyl_normal_input.png'
                    pil_image.save(temp_path)
                    result = model.inference([temp_path])
                    depth_np = result['depth'][0]
                else:
                    # Fallback to grayscale
                    depth_np = np.array(pil_image.convert('L'))

            else:
                return web.json_response({
                    "status": "error",
                    "message": "No image or depth map provided"
                }, status=400)

            # Generate normal map
            if method == 'normalcrafter':
                model = _load_normal_model()
                if model is not None:
                    # Use NormalCrafter (not yet implemented)
                    pass

            # Default: algebraic depth-to-normal
            normal_np = _depth_to_normal_algebraic(depth_np)

            # Convert to base64 PNG
            normal_pil = Image.fromarray(normal_np, mode='RGB')
            buffer = io.BytesIO()
            normal_pil.save(buffer, format='PNG')
            normal_b64 = base64.b64encode(buffer.getvalue()).decode('utf-8')

            # Also return depth if we generated it
            depth_b64 = None
            if depth_np is not None:
                depth_normalized = depth_np
                if depth_np.max() > 1:
                    depth_normalized = depth_np
                else:
                    depth_normalized = (depth_np * 255).astype(np.uint8)

                if depth_normalized.dtype != np.uint8:
                    depth_normalized = depth_normalized.astype(np.uint8)

                depth_pil = Image.fromarray(depth_normalized, mode='L')
                buffer = io.BytesIO()
                depth_pil.save(buffer, format='PNG')
                depth_b64 = base64.b64encode(buffer.getvalue()).decode('utf-8')

            return web.json_response({
                "status": "success",
                "normal": normal_b64,
                "depth": depth_b64,
                "method": method,
                "metadata": {
                    "width": normal_np.shape[1],
                    "height": normal_np.shape[0]
                }
            })

        except Exception as e:
            import traceback
            traceback.print_exc()
            return web.json_response({
                "status": "error",
                "message": str(e)
            }, status=500)

    # =========================================================================
    # Point Cloud Endpoint - Generate 3D point cloud from depth
    # =========================================================================

    @routes.post('/weyl/pointcloud')
    async def generate_pointcloud(request):
        """
        Generate 3D point cloud from image + depth map.

        Request body:
        {
            "image": "base64_encoded_png",   // RGB image for colors
            "depth": "base64_encoded_png",   // Depth map
            "intrinsics": [[fx, 0, cx], [0, fy, cy], [0, 0, 1]],  // Optional camera intrinsics
            "format": "ply" | "json" | "npy",
            "subsample": 1  // Take every Nth point (for performance)
        }

        Returns:
        {
            "status": "success",
            "pointcloud": "base64_encoded_ply" or JSON array,
            "num_points": 1000000,
            "bounds": {"min": [x,y,z], "max": [x,y,z]}
        }
        """
        try:
            data = await request.json()

            from PIL import Image
            import io

            # Decode image and depth
            if 'image' not in data or 'depth' not in data:
                return web.json_response({
                    "status": "error",
                    "message": "Both image and depth are required"
                }, status=400)

            image_data = base64.b64decode(data['image'])
            depth_data = base64.b64decode(data['depth'])

            image_pil = Image.open(io.BytesIO(image_data)).convert('RGB')
            depth_pil = Image.open(io.BytesIO(depth_data)).convert('L')

            image_np = np.array(image_pil)
            depth_np = np.array(depth_pil).astype(np.float32)

            # Normalize depth to 0-1 range
            if depth_np.max() > 1:
                depth_np = depth_np / 255.0

            height, width = depth_np.shape
            output_format = data.get('format', 'json')
            subsample = max(1, data.get('subsample', 1))

            # Get or estimate camera intrinsics
            intrinsics = data.get('intrinsics')
            if intrinsics is None:
                # Estimate reasonable intrinsics
                fx = fy = max(width, height)  # Assume ~90 degree FOV
                cx, cy = width / 2, height / 2
                intrinsics = [[fx, 0, cx], [0, fy, cy], [0, 0, 1]]

            fx, fy = intrinsics[0][0], intrinsics[1][1]
            cx, cy = intrinsics[0][2], intrinsics[1][2]

            # Generate point cloud
            points = []
            colors = []

            for y in range(0, height, subsample):
                for x in range(0, width, subsample):
                    z = depth_np[y, x]
                    if z > 0.01:  # Skip near-zero depth
                        # Back-project to 3D
                        x3d = (x - cx) * z / fx
                        y3d = (y - cy) * z / fy
                        z3d = z

                        points.append([x3d, y3d, z3d])
                        colors.append(image_np[y, x].tolist())

            points_np = np.array(points, dtype=np.float32)
            colors_np = np.array(colors, dtype=np.uint8)

            # Calculate bounds
            if len(points_np) > 0:
                bounds = {
                    "min": points_np.min(axis=0).tolist(),
                    "max": points_np.max(axis=0).tolist()
                }
            else:
                bounds = {"min": [0, 0, 0], "max": [0, 0, 0]}

            # Format output
            if output_format == 'json':
                return web.json_response({
                    "status": "success",
                    "points": points_np.tolist(),
                    "colors": colors_np.tolist(),
                    "num_points": len(points),
                    "bounds": bounds
                })

            elif output_format == 'ply':
                # Generate PLY file
                ply_header = f"""ply
format ascii 1.0
element vertex {len(points)}
property float x
property float y
property float z
property uchar red
property uchar green
property uchar blue
end_header
"""
                ply_data = []
                for i, (pt, col) in enumerate(zip(points_np, colors_np)):
                    ply_data.append(f"{pt[0]:.6f} {pt[1]:.6f} {pt[2]:.6f} {col[0]} {col[1]} {col[2]}")

                ply_content = ply_header + "\n".join(ply_data)
                ply_b64 = base64.b64encode(ply_content.encode('utf-8')).decode('utf-8')

                return web.json_response({
                    "status": "success",
                    "pointcloud": ply_b64,
                    "format": "ply",
                    "num_points": len(points),
                    "bounds": bounds
                })

            elif output_format == 'npy':
                # Generate NPY binary
                combined = np.hstack([points_np, colors_np.astype(np.float32) / 255.0])

                buffer = io.BytesIO()
                np.save(buffer, combined)
                npy_b64 = base64.b64encode(buffer.getvalue()).decode('utf-8')

                return web.json_response({
                    "status": "success",
                    "pointcloud": npy_b64,
                    "format": "npy",
                    "num_points": len(points),
                    "bounds": bounds
                })

            else:
                return web.json_response({
                    "status": "error",
                    "message": f"Unknown format: {output_format}"
                }, status=400)

        except Exception as e:
            import traceback
            traceback.print_exc()
            return web.json_response({
                "status": "error",
                "message": str(e)
            }, status=500)

except ImportError:
    # Running outside ComfyUI context
    pass
