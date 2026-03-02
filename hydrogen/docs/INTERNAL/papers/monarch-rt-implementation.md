# MonarchRT: Implementation

**Parent:** [monarch-rt-real-time-video.md](monarch-rt-real-time-video.md)

---

## 4. Triton Kernel Implementation

### 4.1 Kernel Overview

MonarchRT's performance comes from fused Triton kernels:

1. **`_al_cl_y_fwd`** — Stage 1 forward: computes aL, cL, y for each block pair
2. **`_z_fwd`** — Stage 2 forward: combines across blocks to produce final output  
3. **`_al_cl_y_bwd` / `_z_bwd`** — Backward passes for training

### 4.2 Stage 1 Kernel: Block-Local Attention

```python
@triton.autotune(configs=[...], key=["A_CHUNK", "F_CHUNK", "block_b1", "block_b2", "HEAD_DIM"])
@triton.jit
def _al_cl_y_fwd(Z, H, A, F, a_start, f_start, curr_num_a, curr_num_f,
                 ar_ptr, k_ptr, v_ptr, al_ptr, cl_ptr, y_ptr, out_lse_ptr,
                 sm_scale_sqrt, A_CHUNK, F_CHUNK, block_b1, block_b2,
                 HEAD_DIM, CAUSAL_BLOCK_SIZE, BLOCK_J, BLOCK_L):
    """
    Compute Stage 1 outputs for one (query_block, key_block) pair.
    Grid: (ceil(block_b2/BLOCK_J), batch*heads, curr_q_frames*curr_kv_frames*block_b1)
    """
    start_j = tl.program_id(0) * BLOCK_J
    off_hz = tl.program_id(1)
    off_z = off_hz // H
    off_h = off_hz % H
    off_afk = tl.program_id(2)
    
    # Causal masking: skip if query block precedes key block
    if CAUSAL_BLOCK_SIZE > 0:
        if (off_a // CAUSAL_BLOCK_SIZE) < (off_f // CAUSAL_BLOCK_SIZE):
            return
    
    # Initialize accumulators
    al_acc = tl.zeros([BLOCK_J, HEAD_DIM], dtype=tl.float32)
    y_acc = tl.zeros([BLOCK_J, HEAD_DIM], dtype=tl.float32)
    m_j = tl.full([BLOCK_J], dtype=tl.float32, value=float("-inf"))
    
    ar_j = load_tensor_desc(ar_ptr, ...).reshape(BLOCK_J, HEAD_DIM) * sm_scale_sqrt
    
    # Iterate over key positions in tiles
    for l in tl.static_range(0, block_b2, BLOCK_L):
        k_l = load_tensor_desc(k_ptr, ...).reshape(BLOCK_L, HEAD_DIM) * sm_scale_sqrt
        v_l = load_tensor_desc(v_ptr, ...).reshape(BLOCK_L, HEAD_DIM)
        
        br_jl = tl.dot(ar_j, k_l.T) * 1.44269504  # log2(e) for exp2
        
        # Online softmax update
        m_jl = tl.maximum(m_j, tl.max(br_jl, 1))
        p = tl.math.exp2(br_jl - m_jl[:, None])
        alpha = tl.math.exp2(m_j - m_jl)
        
        al_acc = al_acc * alpha[:, None] + tl.dot(p.to(dtype), k_l)
        y_acc = y_acc * alpha[:, None] + tl.dot(p.to(dtype), v_l)
        m_j = m_jl
    
    # Normalize and store
    al_acc = al_acc / l_j[:, None]
    y_acc = y_acc / l_j[:, None]
    store_tensor_desc(al_ptr, ..., al_acc)
    store_tensor_desc(y_ptr, ..., y_acc)
```

### 4.3 Stage 2 Kernel: Cross-Block Combination

```python
@triton.autotune(configs=[...], key=["A_CHUNK", "F_CHUNK", "block_b1", "block_b2", "HEAD_DIM"])
@triton.jit
def _z_fwd(Z, H, A, F, a_start, f_start, curr_num_a, curr_num_f,
           al_ptr, cl_ptr, q_ptr, y_ptr, z_ptr, out_lse_ptr, sm_scale_sqrt,
           IS_FIRST_ITER, A_CHUNK, F_CHUNK, block_b1, block_b2, HEAD_DIM,
           CAUSAL_BLOCK_SIZE, BLOCK_K, BLOCK_I):
    """
    Combine Stage 1 outputs across key blocks.
    """
    start_i = tl.program_id(0) * BLOCK_I
    
    if IS_FIRST_ITER:
        z_acc = tl.zeros([BLOCK_I, HEAD_DIM], dtype=tl.float32)
        m_i = tl.full([BLOCK_I], dtype=tl.float32, value=float("-inf"))
    else:
        z_acc = load_tensor_desc(z_ptr, ...).to(tl.float32)
        m_i = tl.load(lse_ptr, ...)
    
    q_i = load_tensor_desc(q_ptr, ...).reshape(BLOCK_I, HEAD_DIM) * sm_scale_sqrt
    
    # Iterate over key blocks
    for f in tl.range(0, f_lim):
        for k in tl.static_range(0, block_b1, BLOCK_K):
            al_k = load_tensor_desc(al_ptr, ...).reshape(BLOCK_K, HEAD_DIM)
            cl_k = load_tensor_desc(cl_ptr, ...).reshape(BLOCK_K)
            y_k = load_tensor_desc(y_ptr, ...).reshape(BLOCK_K, HEAD_DIM)
            
            # Second-stage attention: Q @ aL^T - cL
            bl_ik = tl.dot(q_i, al_k.T) * 1.44269504
            z_ik = bl_ik - cl_k[None, :]
            
            m_ik = tl.maximum(m_i, tl.max(z_ik, 1))
            p = tl.math.exp2(z_ik - m_ik[:, None])
            alpha = tl.math.exp2(m_i - m_ik)
            z_acc = z_acc * alpha[:, None] + tl.dot(p.to(dtype), y_k)
            m_i = m_ik
    
    z_acc = z_acc / l_i[:, None]
    store_tensor_desc(z_ptr, ..., z_acc)
```

### 4.4 Memory Layout and Tensor Descriptors

MonarchRT uses Triton's **tensor descriptors** (TMA on Hopper+):

```python
def _init_al_cl_y_fwd_descs(Z, H, A, F, A_CHUNK, F_CHUNK, HEAD_DIM, block_b1, block_b2, aR, k, v, aL, y):
    """
    Tensor descriptors enable:
    - Hardware-accelerated address computation
    - Coalesced memory access patterns
    - Async copy overlap with compute
    
    Layout for aL and y: [Z, A_CHUNK, F_CHUNK, block_b2, block_b1, H, HEAD_DIM]
    """
    if supports_host_descriptor:  # SM90+ (Hopper)
        return SimpleNamespace(
            aR = TensorDescriptor(aR, shape=[...], strides=[...], block_shape=[...]),
            k = TensorDescriptor(k, shape=[...], strides=[...], block_shape=[...]),
            # ...
        )
    else:
        return SimpleNamespace(aR=aR, k=k, v=v, aL=aL, y=y)
```

### 4.5 Autotuning Configuration

```python
configs = [
    triton.Config({'BLOCK_J': BJ, 'BLOCK_L': BL}, num_stages=s, num_warps=w,
                  pre_hook=_al_cl_y_fwd_pre_hook)
    for BJ in [16, 32, 64, 128]
    for BL in [16, 32, 64, 128]
    for s in [2, 3, 4]
    for w in [4, 8]
]

def keep(conf):
    """Filter configs that don't work well on specific hardware."""
    BLOCK_J = conf.kwargs["BLOCK_J"]
    BLOCK_L = conf.kwargs["BLOCK_L"]
    # Hopper (SM90) needs larger tiles for efficiency
    return not (torch.cuda.get_device_capability()[0] == 9 
                and BLOCK_J * BLOCK_L < 128 * 128 and conf.num_warps == 8)
```

## 5. Training Pipeline

### 5.1 Training-Free MonarchRT

MonarchRT can be applied **without any training** by replacing attention at inference:

```python
def apply_monarch_training_free(model, monarch_args):
    """
    Drop-in replacement for inference.
    Quality: ~0.5-1.0 VBench points below dense
    Speedup: 2.1× over FlashAttention
    """
    for layer in model.transformer_blocks:
        layer.attn = MonarchAttention(
            dim=layer.attn.dim, num_heads=layer.attn.num_heads, monarch_args=monarch_args)
        layer.attn.qkv.load_state_dict(layer.attn.qkv.state_dict())
        layer.attn.proj.load_state_dict(layer.attn.proj.state_dict())
```

### 5.2 Fine-Tuning for Quality Recovery

Brief fine-tuning (~600 iterations) recovers quality to match dense:

```yaml
# configs/self_forcing_monarch_dmd.yaml
generator_ckpt: checkpoints/ode_init.pt
monarch_args:
  enable: true
  num_iters: 1
  f_tied: 1
  h_reduce: 1
  w_reduce: 1
denoising_step_list: [1000, 750, 500, 250]
distribution_loss: dmd
lr: 2.0e-6
num_training_iters: 600
```

### 5.3 Self-Forcing Integration

MonarchRT integrates with Self-Forcing's autoregressive training:

```python
class SelfForcingModelWithMonarch(SelfForcingModel):
    """
    Training pipeline:
    1. Backward simulation with consistency sampling
    2. DMD distillation for few-step generation
    3. Monarch attention for sub-quadratic complexity
    
    Result: 4-step autoregressive video at 16 FPS
    """
    def _run_generator(self, image_or_video_shape, conditional_dict, initial_latent=None):
        noise = torch.randn(noise_shape, device=self.device, dtype=self.dtype)
        pred_video, timestep_from, timestep_to = self._consistency_backward_simulation(
            noise=noise, **conditional_dict)
        
        if pred_video.shape[1] > 21:
            with torch.no_grad():
                pixels = self.vae.decoder(pred_video[:, :-20, ...])
                frame = pixels[:, -1:, ...].to(self.dtype)
                image_latent = self.vae.encoder(rearrange(frame, "b t c h w -> b c t h w"))
            pred_video = torch.cat([image_latent, pred_video[:, -20:, ...]], dim=1)
        return pred_video, gradient_mask, timestep_from, timestep_to
```

### 5.4 Causal Initialization (Optional)

For maximum quality, train Monarch from scratch during causal initialization:

```bash
# Stage 1: Causal initialization with Monarch
torchrun --nnodes=8 --nproc_per_node=8 train.py \
  --config_path configs/wan_monarch_causal_training.yaml \
  --logdir logs/wan_monarch_causal

# Stage 2: Self-Forcing DMD with Monarch
torchrun --nnodes=8 --nproc_per_node=8 train.py \
  --config_path configs/self_forcing_monarch_from_monarch_dmd.yaml \
  --logdir logs/self_forcing_monarch_from_monarch_dmd
```

---

*Part of MonarchRT paper synthesis.*
