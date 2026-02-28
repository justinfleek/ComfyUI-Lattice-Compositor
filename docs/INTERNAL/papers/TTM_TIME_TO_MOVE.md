# Time-to-Move: Training-Free Motion Controlled Video Generation via Dual-Clock Denoising

**Authors:** Assaf Singer¹*, Noam Rotstein¹*, Amir Mann¹, Ron Kimmel¹, Or Litany¹,²

¹ Technion – Israel Institute of Technology
² NVIDIA

*Equal contribution

**arXiv:** 2511.08633v1 [cs.CV] 9 Nov 2025

---

## Abstract

Diffusion-based video generation can create realistic videos, yet existing image- and text-based conditioning fails to offer precise motion control. Prior methods for motion-conditioned synthesis typically require model-specific fine-tuning, which is computationally expensive and restrictive. We introduce **Time-to-Move (TTM)**, a training-free, plug-and-play framework for motion- and appearance-controlled video generation with image-to-video (I2V) diffusion models.

Our key insight is to use crude reference animations obtained through user-friendly manipulations such as cut-and-drag or depth-based reprojection. Motivated by SDEdit's use of coarse layout cues for image editing, we treat the crude animations as coarse motion cues and adapt the mechanism to the video domain.

We preserve appearance with image conditioning and introduce **dual-clock denoising**, a region-dependent strategy that enforces strong alignment in motion-specified regions while allowing flexibility elsewhere, balancing fidelity to user intent with natural dynamics.

This lightweight modification of the sampling process incurs no additional training or runtime cost and is compatible with any backbone. Extensive experiments on object and camera motion benchmarks show that TTM matches or exceeds existing training-based baselines in realism and motion control. Beyond this, TTM introduces a unique capability: precise appearance control through pixel-level conditioning, exceeding the limits of text-only prompting.

## 1. Introduction

Diffusion-based video generators have recently achieved remarkable visual quality, yet their controllability remains limited. Image-to-video (I2V) models partially alleviate this limitation by conditioning on a single input frame, which gives users direct control over the appearance of the generated video. However, motion control remains largely prompt-driven which is often unreliable, coarse, and insufficiently fine-grained for interactive use.

To address this gap, a practical generative video system should provide an interface that defines both **what moves** and **where it moves**, ensuring realistic, temporally coherent motion while preserving the appearance of the input image. Such fine-grained control would enable interactive content authoring, post-production, and animation prototyping, where creators require precise, local adjustments with fast feedback.

Existing approaches for controllable motion in generation typically encode user intent through auxiliary control signals such as optical flow or point-trajectories and then heavily fine-tune a generator to ingest this motion conditioning. Such methods are computationally expensive to train, often compromise the quality of the original model, and remain model-specific, requiring architectural modifications to incorporate the controls. This motivates a framework that can be applied to off-the-shelf video diffusion backbones without expensive tuning or additional data.

We introduce **Time-to-Move (TTM)**, a training-free, architecture-agnostic, plug-and-play inference procedure for video diffusion models that matches the speed of standard generation.

### Key Observations

We observe that crude animation inputs, such as those created by simple cut-and-drag manipulation or by straightforward reprojection of the image into novel views using estimated monocular depth, can serve as a useful proxy for the intended target. Such references capture coarse structure and convey the desired motion, while remaining easy to produce and flexible enough to be made as specific or detailed as the user intends.

To transform these crude signals into realistic videos, we draw on **SDEdit**, which shows that coarse structure can be imposed by adding noise to the timestep where the layout is determined. By analogy, we hypothesize that noising the synthetic reference video to the point where motion is established by the video diffusion model can embed the intended dynamics.

Indeed, this strategy successfully injects motion, but at this noise level fidelity to the reference appearance is lost. To mitigate this, we turn to **image-conditioned video diffusion models**, which preserve the identity and scene details of the initial frame and thereby maintain appearance consistency throughout the generated sequence.

### Region-Dependent Dual-Clock Denoising

Even with appearance preserved, motion cues remain uneven across regions. In the synthetic guiding reference video, some regions, such as dragged objects, may contain strong user-specified dynamics, while others remain unspecified. These unconstrained regions are not meant to stay static, but rather to adapt naturally in support of the intended movement.

To this end, we introduce a novel **region-dependent dual-clock denoising** process, which assigns one of two distinct SDE timesteps to different regions across frames:
- **Strong alignment** for user-specified motion
- **Weaker alignment** for unconstrained areas

This allows spatially varying conditioning strength. To realize this effect without retraining the model, we employ a simple yet effective diffusion blending strategy. This allows the model to adhere closely to a specified motion where it exists while allowing greater freedom to invent plausible dynamics elsewhere.

### Joint Motion and Appearance Control

Unlike prior approaches that rely solely on (either sparse or dense) displacement fields as a guiding signal, our method is conditioned directly on the reference video itself. This provides a richer supervisory signal: In regions where alignment is strongly enforced, we not only constrain motion, but can also dictate appearance attributes such as color, shape, or style. As a result, TTM enables **joint control of motion and appearance**, extending the conditioning space beyond motion-only interfaces.

### Contributions

1. **Training-free motion control using crude animations.** We show that simple user-provided animations (e.g., cut-and-drag manipulations or depth-based reprojections) serve as effective motion proxies. Adapting SDEdit-style noise injection to video diffusion and anchoring appearance with image conditioning converts these coarse inputs into realistic motion without training.

2. **Region-dependent dual-clock denoising.** We propose a denoising process that operates with two distinct noise schedules—strong alignment in motion-specified regions and weaker alignment elsewhere—enabling spatially varying conditioning without retraining.

3. **Joint motion-appearance control.** Conditioning on full reference frames, rather than on motion trajectories alone, enables simultaneous control of both motion and appearance, a capability previously limited to ambiguous text prompts.

Extensive experiments show that TTM consistently ranks among the best performing methods on both object and camera motion benchmarks, outperforming even training-based baselines. The approach is training-free and plug-and-play, validated across three I2V backbones, and matches the efficiency of standard video sampling.

## 2. Related Work

Video generation has recently shown great progress, achieving high visual quality and temporal coherence. However, relying solely on a prompt or a single starting frame provides limited control, particularly in specifying accurate motion.

### 2.1 Learning Motion Control in Video Generation

A common strategy in motion control is to learn a trajectory-conditioned representation and fuse it throughout the network:

- **Multi-scale fusion:** Inject user trajectories via multi-scale fusion of trajectory maps in U-Net blocks
- **LoRA modules:** Parameter-efficient LoRA modules that decouple camera and object motion
- **Motion-patch tokens:** Integrated across transformer blocks
- **ATI:** Encodes point tracks as Gaussian-weighted latent features
- **TrackGo:** Inserts auxiliary branches into SVD's temporal self-attention
- **MotionPro:** Uses region-wise trajectories plus a motion mask to distinguish object vs. camera motion

Other methods, like ours, incorporate explicit motion-based cues rather than relying solely on learned injection:
- **DragAnything:** Extracts entity representations from first-frame diffusion features and injects trajectory conditioning via a ControlNet-style branch
- **Motion Prompting:** Conditions a video diffusion model on point-track "motion prompts" via a track-conditioned ControlNet
- **GEN3C:** Constructs a depth-lifted 3D cache and conditions generation on projected renders along the target camera path
- **Go-with-the-Flow (GWTF):** Warps diffusion noise to align with the intended motion (but extensively fine-tunes the base model)

### 2.2 Training-Free Motion-Controllable Video Generation

Several approaches avoid additional training by reusing pretrained models:

**Text-to-Video (T2V) approaches manipulating attention:**
- **TrailBlazer:** Modifies spatial and temporal attention early in denoising
- **PEEKABOO:** Gates regions using masked spatio-temporal attention
- **FreeTraj:** Shapes low-frequency noise with attention biases to follow bounding boxes

However, these models tie bounding boxes to text, limiting part-level motion and preventing precise appearance control or in-place animation of a given image.

**Motion transfer methods:** Synthesize videos by applying motion from a driving sequence to a still image, yet depend on a suitable reference video that is difficult to obtain.

**SG-I2V:** Enforces cross-frame consistency by replacing each frame's spatial self-attention keys/values with those of the first, then optimizes the latent with a box-restricted similarity loss. Demonstrated on SVD-specific layers, so generality for other backbones is unclear.

### 2.3 Heterogeneous Denoising

Asynchronous denoising has been explored in several contexts:

- **RAD:** Reformulates inpainting with element-wise noise schedules and spatial timestep embedding, enabling region-asynchronous denoising while adapting a pretrained model via LoRA
- **SVNR:** Addresses spatially variant sensor noise by training with per-pixel timesteps
- **Diffusion Forcing (DF):** Introduces temporal heterogeneity by assigning each token its own noise level during training

In contrast to RAD, SVNR, and DF, **our approach is training-free**: We impose region-specific schedules directly at inference.

- **RePaint:** Also training-free, but repeatedly re-noises unmasked regions and denoises solely the mask, so only part of the image is actively denoised. Our method heterogeneously denoises the entire image, eliminating RePaint's resampling loops since no region is excluded.

## 3. Method

Our goal is to enable precise motion control in generative video models. Inspired by SDEdit, which injects coarse edits into images via noising and denoising, we treat a crude warped animation as the video analogue of such edits and adapt SDEdit to inject intended motion into video diffusion.

To avoid the loss of identity that occurs when noising alone drives the process—an inherent limitation of SDEdit—we opt for image conditioning, anchoring the generation to the clean first frame so that the appearance is preserved throughout the sequence.

Building on these foundations, we introduce a novel **dual-clock denoising process** that assigns different noise levels to distinct regions, allowing spatially varying motion guidance.

### Problem Formulation

Our method takes as input:
1. **A single image** I ∈ ℝ^(3×H×W)
2. **A coarse, user-specified warped reference video** with F frames, V^w ∈ ℝ^(F×3×H×W)
3. **A binary mask video** M ∈ {0, 1}^(F×H×W) indicating, for each frame, the regions where motion guidance is provided by the reference video

**Objective:** Generate a realistic video x₀ ∈ ℝ^(F×3×H×W) that maintains fidelity to the input image while accurately following the prescribed motion.

### 3.1 Motion Signal

We begin by describing how the motion signal V^w is generated.

To facilitate user-friendly interaction:
1. The user selects a region in the first frame to produce an initial binary mask M₀
2. Then specifies a coarse motion by dragging this region along a trajectory, yielding the sequence M

This defines a **piecewise-smooth displacement field** within the masked region, which induces per-frame warps of the input image. The warped video V^w is obtained by forward warping I, with identity mapping outside the mask.

**Handling Disocclusions:** Forward warping naturally introduces disocclusions where previously occluded background becomes visible; these holes are filled using a simple nearest-neighbor inpainting strategy.

Although presented here as dragging, both V^w and M can be constructed in multiple ways. For example, V^w can also be produced by pixel-wise warping of the input image according to monocular depth estimation. Additional interactions such as rotation and scaling of the selected region integrate seamlessly into the same formulation.

**Key Insight:** While such warped animations are visually unrealistic, they faithfully capture the user-intended object placement and temporal structure. We exploit these properties by using them as a guiding signal for the video diffusion model during generation. Note that V^w can also encode appearance modifications, such as color changes, within the same framework.

### 3.2 SDEdit Adaptation for Motion Injection

Inspired by the use of coarsely edited images as structural priors in SDEdit, we adapt the method to videos by using the crudely warped video V^w itself as a coarse yet explicit motion instruction.

We initialize sampling from a noisy version of the warped reference:
```
x_t* ~ q(x_t* | V^w)
```

Previous publications show that coarse motion is determined early in the denoising trajectory. By noising V^w to t*, the intended dynamics are injected at precisely this stage.

**Problem with Text-Conditioned Models:** If we were to apply this procedure in a text-conditioned video diffusion model, the fidelity to the input image would be quickly lost. The model's only knowledge of appearance comes from the noised V^w, so fine details cannot be preserved.

**Solution:** We instead opt for an **image-conditioned video diffusion model**, which anchors generation to the clean first frame I. The resulting sampling process:
```
x₀ ~ p_θ(x₀ | x_t*, I)
```
faithfully integrates the motion guidance from V^w while preserving identity and appearance throughout the generated sequence.

### 3.3 Region-Dependent Dual-Clock Denoising

SDEdit employs a single noising timestep t* to corrupt the reference signal before denoising. In our setting, this creates a trade-off:

The warped video V^w contains:
- **Masked regions:** Where motion is explicitly specified
- **Unmasked regions:** Without explicit instruction

**Requirements:**
- For masked regions: The generated video should closely follow the prescribed motion
- For unmasked areas: We do not want them to stay static; instead, they should adapt naturally to support the motion

**The Trade-off Problem:**
- If t* is **small**: The denoised video adheres closely to the warped signal but inherits artifacts such as frozen backgrounds
- If t* is **large**: The results look realistic but drift away from the intended motion

We therefore conjecture that different regions require different effective noising levels:
- **Masked regions:** Demand strong adherence to the motion signal (achieved with less noising: t_strong)
- **Unmasked regions:** Benefit from weaker enforcement (achieved with increased noising: t_weak)

### The Dual-Clock Algorithm

The challenge is that standard pretrained diffusion models, which assume inputs are corrupted by a single uniform noise level, cannot directly accommodate region-dependent noise.

**Our Solution - Dual-Clock Denoising:**

Given a mask M:
1. Noise the warped video reference V^w to timestep t_weak
2. Initialize the denoising process
3. At each denoising step t with t_strong ≤ t < t_weak:
   - Override the masked region with the corresponding region of the warped video noised to t − 1
4. This constrains the masked regions to follow the intended trajectory, while the background is free to denoise more aggressively and achieve realism
5. Once t = t_strong, stop overriding and continue the standard sampling process, allowing the model to refine both regions for a coherent result

**Update Rule:**
Let x_t denote the noisy sample at timestep t, and x̂_{t−1}(x_t, t) the denoiser prediction:
```
x_{t−1} ← (1 − M) ⊙ x̂_{t−1}(x_t, t, I) + M ⊙ x^w_{t−1}
```
where x^w_{t−1} is the warped reference video noised to timestep t − 1.

### Algorithm: Dual-Clock Denoising

```python
def dual_clock_denoise(
    model,           # I2V diffusion model
    I,               # Input image (first frame)
    V_w,             # Warped reference video [F, 3, H, W]
    M,               # Binary mask video [F, H, W]
    t_weak,          # Weak alignment timestep (higher noise)
    t_strong,        # Strong alignment timestep (lower noise)
    T=50             # Total denoising steps
):
    """
    Region-dependent dual-clock denoising for motion control.
    
    Key insight: Different regions need different noise levels:
    - Masked regions (user-specified motion): low noise for strong adherence
    - Unmasked regions (background): high noise for natural adaptation
    """
    
    # Step 1: Encode warped video to latent space
    z_w = model.encode(V_w)  # [F, C, h, w] in latent space
    
    # Step 2: Downsample mask to latent resolution
    M_latent = downsample_mask(M, model.latent_scale)  # nearest-neighbor
    
    # Step 3: Initialize from noisy warped reference at t_weak
    # This is where we inject the coarse motion structure
    x_t = add_noise(z_w, timestep=t_weak)
    
    # Step 4: Denoising loop with dual-clock strategy
    for t in range(t_weak, 0, -1):
        
        # Standard denoising step with image conditioning
        x_hat = model.denoise_step(x_t, t, image_condition=I)
        
        if t > t_strong:
            # DUAL-CLOCK REGION: Override masked areas with noisy reference
            # This enforces motion adherence in specified regions
            x_w_prev = add_noise(z_w, timestep=t-1)
            
            # Blend: background from denoiser, foreground from warped reference
            x_t = (1 - M_latent) * x_hat + M_latent * x_w_prev
        else:
            # UNIFIED REGION: Standard denoising for all pixels
            # Model refines both regions together for coherence
            x_t = x_hat
    
    # Step 5: Decode to pixel space
    output_video = model.decode(x_t)
    
    return output_video
```

### Hyperparameters

| Backbone | T (total steps) | t_weak | t_strong |
|----------|-----------------|--------|----------|
| SVD (1.5B params) | 50 | 36 | 25 |
| CogVideoX (5B params) | 50 | 46 | 41 |
| WAN 2.2 (14B params) | 50 | ~similar ratios | ~similar ratios |

**Intuition for hyperparameter selection:**
- `t_weak` ≈ 70-90% of T: High enough to allow background to deviate naturally
- `t_strong` ≈ 50-80% of T: Low enough to preserve motion, high enough to allow refinement
- The gap `t_weak - t_strong` controls how long the dual-clock regime operates

### Motion Signal Generation

```python
def generate_motion_signal(
    I,                    # Input image [3, H, W]
    mask_0,               # Initial object mask [H, W]
    trajectory,           # List of (dx, dy) displacements per frame
    num_frames=16
):
    """
    Generate warped reference video from cut-and-drag interaction.
    """
    V_w = []
    M = []
    
    for f in range(num_frames):
        # Compute cumulative displacement up to frame f
        dx, dy = trajectory[f]
        
        # Forward warp the image
        frame_warped = forward_warp(I, mask_0, dx, dy)
        
        # Update mask position
        mask_f = translate_mask(mask_0, dx, dy)
        
        # Inpaint disoccluded regions (simple nearest-neighbor)
        frame_warped = inpaint_holes(frame_warped, mask_f)
        
        V_w.append(frame_warped)
        M.append(mask_f)
    
    return stack(V_w), stack(M)


def forward_warp(image, mask, dx, dy):
    """
    Warp masked region by displacement (dx, dy).
    Pixels outside mask remain in place (identity mapping).
    """
    H, W = image.shape[1:]
    output = image.clone()
    
    # Create coordinate grids
    y, x = torch.meshgrid(torch.arange(H), torch.arange(W))
    
    # Source coordinates for masked region
    src_y = y[mask] 
    src_x = x[mask]
    
    # Target coordinates after displacement
    tgt_y = (src_y + dy).clamp(0, H-1).long()
    tgt_x = (src_x + dx).clamp(0, W-1).long()
    
    # Forward scatter (may create holes)
    output[:, tgt_y, tgt_x] = image[:, src_y, src_x]
    
    # Mark original positions as holes (disoccluded)
    output[:, src_y, src_x] = float('nan')  # mark for inpainting
    
    return output


def inpaint_holes(frame, mask):
    """
    Simple nearest-neighbor inpainting for disoccluded regions.
    """
    holes = torch.isnan(frame[0])
    
    if not holes.any():
        return frame
    
    # For each hole pixel, find nearest valid pixel
    valid_coords = torch.stack(torch.where(~holes), dim=1)
    hole_coords = torch.stack(torch.where(holes), dim=1)
    
    # Compute distances and find nearest
    dists = torch.cdist(hole_coords.float(), valid_coords.float())
    nearest_idx = dists.argmin(dim=1)
    
    # Fill holes
    for i, (hy, hx) in enumerate(hole_coords):
        vy, vx = valid_coords[nearest_idx[i]]
        frame[:, hy, hx] = frame[:, vy, vx]
    
    return frame
```

### Camera Motion via Depth Reprojection

```python
def generate_camera_motion_signal(
    I,                    # Input image [3, H, W]
    camera_trajectory,    # List of camera extrinsics [F, 4, 4]
    depth_estimator       # e.g., DepthPro
):
    """
    Generate warped reference video for camera motion control.
    """
    # Step 1: Estimate metric depth
    depth = depth_estimator(I)  # [H, W]
    
    # Step 2: Back-project to 3D point cloud
    K = get_camera_intrinsics(I.shape)
    points_3d = backproject_to_3d(I, depth, K)  # [H*W, 3]
    colors = I.reshape(3, -1).T  # [H*W, 3]
    
    V_w = []
    M = []
    
    for f, extrinsic in enumerate(camera_trajectory):
        # Step 3: Reproject point cloud to new viewpoint
        points_2d = project_3d_to_2d(points_3d, extrinsic, K)
        
        # Step 4: Render to image with z-buffering
        frame, valid_mask = render_point_cloud(
            points_2d, colors, depth, (H, W)
        )
        
        # Step 5: Inpaint disoccluded regions
        frame = inpaint_holes(frame, valid_mask)
        
        V_w.append(frame)
        M.append(valid_mask)  # Valid pixels = guidance regions
    
    return stack(V_w), stack(M)
```

### Mask Handling for Latent Space Models

```python
def downsample_mask(M, latent_scale):
    """
    Project binary mask to latent resolution.
    
    For SVD: spatial only (8x downscale)
    For CogVideoX: spatial + temporal (8x spatial, 4x temporal)
    """
    # Spatial downsampling with nearest-neighbor
    M_spatial = F.interpolate(
        M.float().unsqueeze(1),
        scale_factor=1/latent_scale.spatial,
        mode='nearest'
    ).squeeze(1)
    
    # Temporal downsampling if needed (CogVideoX)
    if hasattr(latent_scale, 'temporal') and latent_scale.temporal > 1:
        # Subsample frames
        M_spatial = M_spatial[::latent_scale.temporal]
    
    return M_spatial > 0.5  # Back to binary
```

### Efficiency and Applicability

- **Lightweight modification** to standard sampling
- **No extra computation** or latency over regular video diffusion
- **Entirely training-free** and plug-and-play for image-conditioned I2V models
- Validated across **three I2V backbones** (SVD, CogVideoX, WAN 2.2)

## 4. Experiments

## 5. Conclusions

## References

## Appendix
