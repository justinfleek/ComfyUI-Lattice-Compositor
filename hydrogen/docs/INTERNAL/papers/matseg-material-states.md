# Learning Zero-Shot Material States Segmentation by Implanting Natural Image Patterns in Synthetic Data

**Authors:** Sagi Eppel¹²*, Jolina Yining Li²*, Manuel S. Drehwald², Alan Aspuru-Guzik¹²

¹Vector Institute, ²University of Toronto
*Equal contributions

**Published:** NeurIPS 2024 (Datasets and Benchmarks Track)

**arXiv:** 2403.03309v6 [cs.CV] 1 Aug 2025

---

## Abstract

Visual recognition of materials and their states is essential for understanding the physical world, from identifying wet regions on surfaces or stains on fabrics to detecting infected areas on plants or minerals in rocks.

**The Problem:**
- Collecting data capturing this variability is complex due to scattered and gradual nature of material states
- Manual annotation of real-world images is constrained by cost and precision
- Synthetic data, although accurate and inexpensive, lacks real-world diversity

**The Solution:**
This work bridges this gap by **infusing patterns automatically extracted from real-world images into synthetic data**. Patterns collected from natural images are used to generate and map materials into synthetic scenes. This unsupervised approach captures the complexity of the real world while maintaining the precision and scalability of synthetic data.

**Contributions:**
1. First comprehensive benchmark for zero-shot material state segmentation (1,220 real-world images)
2. Domains: food, soils, construction, plants, liquids, etc.
3. States: wet, dry, infected, cooked, burned, and many others
4. Annotation includes partial similarity between regions and hard segmentation of identical material states
5. Top foundation models (SAM, Materialistic) perform poorly — nets trained on infused data perform significantly better
6. 300,000 extracted textures and SVBRDF/PBR materials shared publicly

---

## 1. Introduction

Materials and their states form a vast array of patterns and textures that define the physical and visual world:
- Minerals in rocks
- Sediment in soil
- Dust on surfaces
- Infection on leaves
- Stains on fruits
- Foam in liquids

Segmenting these states in images is fundamental to comprehension of the world — essential for cooking, cleaning, construction, laboratory work, and countless other tasks.

### 1.1 Procedural Imitation: Core Method

**Key Hypothesis:** Simple image properties (value, hue, saturation, R/G/B channels) are often correlated with material regions or properties within a material texture.

Examples:
- Dry part of a leaf → often darker/brighter than surroundings
- Stains on fabrics → different brightness
- Pollution in water → different color channel values

**The Method:**
1. Extract maps from broad range of images (brightness, hue, etc.)
2. Use these maps in synthetic scenes where original correlation doesn't apply
3. Patterns learned in general form, not tied to specific correlation

**Why it works:** Patterns extracted in simple cases with strong correlation (material ↔ image property) are rendered and learned in other scenes where this correlation doesn't occur. Neural nets are effective at learning from noisy data (cf. CLIP, GPT).

### 1.2 Zero-Shot Material State Segmentation Benchmark

**Benchmark Properties:**
- 1,220 real-world images
- Wide range of materials and domains
- Class-agnostic evaluation
- Point-based annotation (handles scattered shapes, fuzzy boundaries)
- Partial similarity annotation (handles gradual transitions)

**Key Result:** Top segmentation models (SAM, Materialistic) perform poorly, exposing major gaps in standard data collection approaches.

### 1.3 Summary of Main Contributions

1. **First general material state segmentation benchmark** — enables training and evaluation on this fundamental task

2. **Unsupervised pattern extraction method** — infuses real-world patterns into synthetic scenes, outperforms top methods on zero-shot benchmarks

3. **300,000+ extracted textures and PBR materials** — shared for future dataset generation

---

## 2. Related Works

### Unsupervised Texture Segmentation and Extraction
Classical methods (last 50 years) using simple image features:
- Connected regions with uniform color/shades
- Grid cells with similar statistical distributions
- Mostly discarded in favor of deep learning

**This work's insight:** These "ancient" methods capture patterns missing from leading data generation methods.

### Synthetic Data and Domain Gap
- CGI images commonly used for training (games, movies approach)
- Human-made assets, scans, simulations, procedural generation
- **Problem:** Fail to capture real-world diversity → domain gap
- Domain adaptation (GANs) adjusts images but not underlying scene
- Procedural rules still limited by generation rules

### Materials in Synthetic Scenes (PBR/SVBRDF)
- Materials represented as property maps: albedo, reflectance, normals, roughness, transparency
- Maps wrapped around objects
- **Current limitation:** Only a few thousand publicly available PBR materials
- Neural net generation trained on existing repositories → unclear if generalizes beyond training distribution

### Zero-Shot and Class-Agnostic Segmentation
- Receives query or point → outputs corresponding region
- Previous methods: project multiple textures into image, train on known segmentation maps
- **Limitation:** Random or limited pre-made asset distribution, not tested on material states

---

## 3. Data Generation: Patterns Extraction and Infusion

Two main applications:
1. Map existing materials into synthetic scenes
2. Extract texture maps and PBR/SVBRDF materials from images

### 3.1 Unsupervised Extraction of Maps from Images

```python
def extract_material_map(image):
    """
    Extract material distribution map from natural image.
    
    Key insight: Material regions often correlate with simple 
    image properties (brightness, hue, saturation, RGB channels).
    """
    # Step 1: Select random image property channel
    channels = ['R', 'G', 'B', 'H', 'S', 'V']  # RGB or HSV
    selected_channel = random.choice(channels)
    
    if selected_channel in ['R', 'G', 'B']:
        channel_map = image[:, :, {'R': 0, 'G': 1, 'B': 2}[selected_channel]]
    else:
        hsv = rgb_to_hsv(image)
        channel_map = hsv[:, :, {'H': 0, 'S': 1, 'V': 2}[selected_channel]]
    
    # Step 2: Apply fuzzy threshold (color ramp)
    # Creates soft binary map with distinct segments + gradual transitions
    threshold_low = random.uniform(0, 0.5)
    threshold_high = random.uniform(0.5, 1.0)
    
    material_map = fuzzy_threshold(channel_map, threshold_low, threshold_high)
    
    return material_map


def fuzzy_threshold(channel_map, t_low, t_high):
    """
    Fuzzy threshold creating soft boundaries.
    
    - Below t_low: 0
    - Above t_high: 1
    - Between: linear interpolation
    """
    result = np.zeros_like(channel_map)
    
    # Below threshold
    result[channel_map <= t_low] = 0
    
    # Above threshold
    result[channel_map >= t_high] = 1
    
    # Linear interpolation in between
    mask = (channel_map > t_low) & (channel_map < t_high)
    result[mask] = (channel_map[mask] - t_low) / (t_high - t_low)
    
    return result
```

### Creating 2D Scenes

```python
def create_2d_scene(source_image, textures, background):
    """
    Generate 2D synthetic scene with material mapping.
    """
    # Step 1: Extract material map from source image
    material_map = extract_material_map(source_image)
    
    # Step 2: Create multi-region map (repeat extraction for multiple regions)
    num_regions = random.randint(2, 5)
    region_maps = [extract_material_map(source_image) for _ in range(num_regions)]
    
    # Step 3: Assign textures to regions
    scene = np.zeros_like(background)
    annotation = np.zeros(background.shape[:2], dtype=int)
    
    for i, (region_map, texture) in enumerate(zip(region_maps, textures)):
        # Tile texture to match scene size
        tiled_texture = tile_texture(texture, scene.shape[:2])
        
        # Blend based on region map (soft mixing)
        scene = scene * (1 - region_map[:, :, None]) + tiled_texture * region_map[:, :, None]
        annotation[region_map > 0.5] = i + 1
    
    # Step 4: Add shadow effects using another extracted map
    shadow_map = extract_material_map(source_image)
    scene = scene * (0.5 + 0.5 * shadow_map[:, :, None])
    
    # Step 5: Overlay on background
    final_scene = composite_on_background(scene, background)
    
    return final_scene, annotation
```

### Creating 3D Scenes (Blender)

```python
def create_3d_scene(source_image, pbr_materials, hdri_background):
    """
    Generate 3D synthetic scene with PBR materials.
    
    Uses Blender with Cycles rendering engine.
    """
    # Step 1: Load random 3D objects (ShapeNet)
    objects = load_random_objects(num_objects=random.randint(1, 5))
    
    # Step 2: Extract material maps from source image
    material_maps = [extract_material_map(source_image) for _ in range(len(pbr_materials))]
    
    # Step 3: UV map materials onto object surfaces
    for obj in objects:
        # Wrap extracted maps around object surface
        uv_map = generate_uv_mapping(obj, material_maps)
        
        # Assign PBR materials to each map region
        for i, (pbr_material, region) in enumerate(zip(pbr_materials, material_maps)):
            assign_material_to_region(obj, pbr_material, region, uv_map)
    
    # Step 4: Set up scene
    set_hdri_background(hdri_background)  # Illumination + background
    add_ground_plane()
    add_random_occluders()
    set_random_camera_position()
    
    # Step 5: Render with Cycles (physics-based rendering)
    rendered_image = render_scene()
    annotation_mask = render_material_ids()
    
    return rendered_image, annotation_mask
```

### 3.2 Extracting Textures and Materials

#### 3.2.1 Unsupervised Texture Extraction

```python
def extract_uniform_texture(image, cell_size=40, min_region_size=6):
    """
    Find regions with uniform texture distribution.
    
    Uniform texture implies uniform material.
    """
    H, W = image.shape[:2]
    grid_h, grid_w = H // cell_size, W // cell_size
    
    # Step 1: Compute distribution for each cell
    cell_distributions = {}
    for i in range(grid_h):
        for j in range(grid_w):
            cell = image[i*cell_size:(i+1)*cell_size, j*cell_size:(j+1)*cell_size]
            
            # Distribution of RGB values and gradients
            rgb_hist = compute_rgb_histogram(cell)
            gradient_hist = compute_gradient_histogram(cell)
            
            cell_distributions[(i, j)] = {
                'rgb': rgb_hist,
                'gradient': gradient_hist
            }
    
    # Step 2: Find connected regions with similar distributions
    uniform_regions = []
    visited = set()
    
    for start_cell in cell_distributions:
        if start_cell in visited:
            continue
        
        # BFS to find connected similar cells
        region = flood_fill_similar(
            start_cell, 
            cell_distributions,
            similarity_threshold=0.5,  # Jensen-Shannon distance
            visited=visited
        )
        
        if len(region) >= min_region_size * min_region_size:
            uniform_regions.append(region)
    
    # Step 3: Extract texture from largest valid region
    for region in sorted(uniform_regions, key=len, reverse=True):
        texture = extract_region_as_texture(image, region, cell_size)
        
        # Filter: skip too-uniform (textureless) regions
        if not is_textureless(texture):
            return texture
    
    return None


def compute_cell_similarity(dist1, dist2):
    """
    Jensen-Shannon distance between cell distributions.
    Computed separately for each RGB channel and gradients.
    """
    js_distances = []
    
    for channel in ['R', 'G', 'B']:
        js = jensen_shannon_distance(dist1['rgb'][channel], dist2['rgb'][channel])
        js_distances.append(js)
    
    for channel in ['R', 'G', 'B']:
        js = jensen_shannon_distance(dist1['gradient'][channel], dist2['gradient'][channel])
        js_distances.append(js)
    
    return max(js_distances)  # All must be similar
```

#### 3.2.2 Generating PBR Material Property Maps

```python
def generate_pbr_from_texture(texture_image):
    """
    Generate PBR/SVBRDF material from RGB texture.
    
    Key insight: Material properties (reflectivity, roughness, transparency)
    often correlate with simple image properties in some settings.
    """
    pbr_material = {}
    
    # Albedo: use the texture directly (with possible augmentation)
    pbr_material['albedo'] = augment_texture(texture_image)
    
    # For each property map, randomly select an image channel
    property_channels = ['R', 'G', 'B', 'H', 'S', 'V']
    
    for prop in ['roughness', 'metallic', 'height', 'transmission']:
        # Option 1: Use random channel from texture
        if random.random() > 0.3:
            channel = random.choice(property_channels)
            prop_map = extract_channel(texture_image, channel)
            
            # Apply random transformations
            prop_map = apply_threshold(prop_map)
            prop_map = random_scale_shift(prop_map)
            
            pbr_material[prop] = prop_map
        else:
            # Option 2: Uniform random value
            pbr_material[prop] = np.full_like(texture_image[:, :, 0], 
                                               random.uniform(0, 1))
    
    # Normal map: gradient of height map
    pbr_material['normal'] = height_to_normal(pbr_material['height'])
    
    return pbr_material


def height_to_normal(height_map, strength=1.0):
    """
    Convert height/bump map to normal map via gradient.
    """
    # Sobel gradients
    dx = cv2.Sobel(height_map, cv2.CV_32F, 1, 0, ksize=3)
    dy = cv2.Sobel(height_map, cv2.CV_32F, 0, 1, ksize=3)
    
    # Construct normal vectors
    normal_map = np.zeros((*height_map.shape, 3), dtype=np.float32)
    normal_map[:, :, 0] = -dx * strength  # X
    normal_map[:, :, 1] = -dy * strength  # Y
    normal_map[:, :, 2] = 1.0             # Z
    
    # Normalize
    norm = np.linalg.norm(normal_map, axis=2, keepdims=True)
    normal_map = normal_map / (norm + 1e-8)
    
    # Convert to 0-1 range for storage
    normal_map = (normal_map + 1) / 2
    
    return normal_map
```

### PBR Material Mixing

```python
def mix_pbr_materials(material_a, material_b, mixing_mode='per_property'):
    """
    Create new PBR material by mixing two existing materials.
    
    Args:
        mixing_mode: 'per_material' (same weight for all) or 
                     'per_property' (different weight per property)
    """
    mixed = {}
    
    if mixing_mode == 'per_material':
        weight = random.uniform(0, 1)
        weights = {prop: weight for prop in material_a.keys()}
    else:
        weights = {prop: random.uniform(0, 1) for prop in material_a.keys()}
    
    for prop in material_a.keys():
        w = weights[prop]
        mixed[prop] = w * material_a[prop] + (1 - w) * material_b[prop]
    
    return mixed
```

---

## 4. Material State Segmentation Benchmark

**Goal:** Test general material state segmentation beyond specific materials/domains.

**Requirements:**
- Real-world images
- Wide range of material states, environments, domains
- Capture scattered/sparse shapes
- Handle mixtures and gradual transitions

### Image Collection

**1,220 images** manually collected from real-world scenes:

| Domain | Examples |
|--------|----------|
| Food | Different cooking levels |
| Liquids | Solutes, foams, precipitates |
| Plants | Infection, dry regions |
| Rocks | Minerals, sediments |
| Grounds/Landscapes | Various soil states |
| Construction | Metals, relics |
| Metals | Corrosion, wear |
| Fabrics | Stains, wetness |
| Labs | Cooking, wetting, rotting processes |

### Point-Based Annotation

**Why points instead of polygons?**
- Scattered shapes with soft boundaries often impossible to fully segment
- Points allow focusing on clear regions while sampling complex areas
- Avoids annotating areas where segmentation is unclear

**Annotation Procedure:**

```
1. Pick points representing distribution of each material state
2. Group points by material state (same label = identical material)
3. Assign relative similarity between groups:
   - If B is transition between A and C:
     - B partially similar to A and C
     - A and C not similar to each other
```

### 4.1 Evaluation Metric: Triplet Accuracy

```python
def triplet_evaluation(predictions, ground_truth):
    """
    Evaluate segmentation using triplet metric.
    
    For any segmentation method (soft or hard), can be converted
    to similarity prediction between two points.
    """
    correct = 0
    total = 0
    
    # For all triplets of annotated points
    for anchor, point_a, point_b in generate_triplets(ground_truth):
        # Ground truth: which point is more similar to anchor?
        gt_sim_a = ground_truth.similarity(anchor, point_a)
        gt_sim_b = ground_truth.similarity(anchor, point_b)
        
        if gt_sim_a == gt_sim_b:
            continue  # Skip identical similarity (ambiguous)
        
        gt_closer = 'a' if gt_sim_a > gt_sim_b else 'b'
        
        # Prediction: which point is more similar to anchor?
        pred_sim_a = predictions.similarity(anchor, point_a)
        pred_sim_b = predictions.similarity(anchor, point_b)
        pred_closer = 'a' if pred_sim_a > pred_sim_b else 'b'
        
        if gt_closer == pred_closer:
            correct += 1
        total += 1
    
    return correct / total  # 50% = random, 100% = perfect


def hard_segmentation_to_similarity(segmentation, point_a, point_b):
    """
    Convert hard segmentation to binary similarity.
    """
    label_a = segmentation[point_a]
    label_b = segmentation[point_b]
    return 1.0 if label_a == label_b else 0.0
```

### 4.2 Additional Benchmarks

Cross-validation on specialized benchmarks:

| Benchmark | Field | Characteristics |
|-----------|-------|-----------------|
| Cu dataset | Mineral/Ore | Scattered |
| FeM dataset | Mineral/Ore | Scattered |
| corrosao-segment | Corrosion/Metals | Scattered + Gradual |
| Leaf diseases | Plants/Disease | Scattered + Gradual |
| URDE | Dust | Gradual |
| Soil-type-class-2 | Soil States | Gradual |
| Soil type classification | Soil/Rocks | Standard |
| NuInsSeg | Microscopy | Scattered + Gradual |
| CryoNuSeg | Microscopy | Scattered + Gradual |
| Materialistic | General | Smooth boundaries |
| LabPics Chemistry | Chemistry/Phases | Standard |
| LabPics Medical | Lab/Liquids | Standard |

---

## 5. Segment Anything Model (SAM) and Materialistic

### SAM (Segment Anything Model)
- Leading foundation model for image segmentation
- Trained on 11M real images, 1B segments (semi-manual annotation)
- Input: positive points (inside target) + negative points (outside)
- Evaluated with 2, 4, and 8 input points

### Materialistic
- Latest approach for material segmentation based on visual similarity
- Zero-shot: finds regions of same material using input point
- Trained on 3D synthetic data
- **Key difference from MatSeg:** All assets based on existing (mostly manual) repositories

**Comparing Materialistic vs MatSeg isolates the effect of the pattern infusion method.**

---

## 6. Results

### MatSeg Benchmark Results (Triplet Accuracy)

| Method | Points | All | Soft Cases |
|--------|--------|-----|------------|
| **MatSeg (Mixed 2D+3D)** | 1 | **0.92** | **0.84** |
| MatSeg (3D only) | 1 | 0.90 | 0.83 |
| MatSeg (2D only) | 1 | 0.91 | 0.84 |
| Materialistic | 1 | 0.76 | 0.72 |
| SAM | 1 | 0.69 | 0.63 |
| SAM | 2 | 0.70 | 0.62 |
| SAM | 4 | 0.72 | 0.64 |
| SAM | 8 | 0.74 | 0.65 |

**Note:** 50% = random guess, 100% = perfect

**Key Findings:**
- MatSeg significantly outperforms SAM and Materialistic
- Learns scattered patterns, soft/gradual transitions across diverse domains
- Mitigates reflections and shadows
- SAM and Materialistic search for bulk regions with smooth boundaries
- SAM fails even with 8 guiding points → suggests fundamental gap in training data

### Results on Other Benchmarks (IOU)

| Dataset | Field | S/G | MatSeg | Materialistic | SAM (8pt) |
|---------|-------|-----|--------|---------------|-----------|
| Cu dataset | Mineral/Ore | S | **0.52** | 0.36 | 0.69 |
| FeM dataset | Mineral/Ore | S | **0.62** | 0.37 | 0.67 |
| corrosao-segment | Corrosion | SG | **0.69** | 0.49 | 0.56 |
| Leaf diseases | Plants | SG | **0.56** | 0.47 | 0.54 |
| URDE | Dust | G | **0.50** | 0.47 | 0.52 |
| Soil-type-class-2 | Soil States | G | 0.62 | 0.53 | **0.72** |
| Soil type class | Soil/Rocks | - | 0.69 | 0.71 | **0.88** |
| NuInsSeg | Microscopy | SG | **0.38** | 0.17 | 0.32 |
| CryoNuSeg | Microscopy | SG | **0.45** | 0.28 | 0.28 |
| Materialistic | General | - | 0.75 | **0.87** | 0.85 |
| LabPics Chemistry | Chemistry | - | 0.62 | 0.63 | **0.75** |
| LabPics Medical | Lab/Liquids | - | **0.71** | 0.68 | 0.72 |

**S = Scattered shapes, G = Gradual transitions**

**Pattern:**
- **MatSeg wins** on: scattered segments, soft/gradual boundaries, similar states (dust, diseases, corrosion, microscopy)
- **SAM/Materialistic win** on: bulk smooth boundaries, single shapes, object-correlated, no gradual transitions

**Conclusion:** The infusion method taps a fundamentally different distribution missed by both manual annotations and standard synthetic data generation.

### 6.2 Conclusion

The results suggest:

1. **Data infusion captures missing patterns** — real-world complexity that standard approaches miss
2. **Neural nets learn from noisy data** — unsupervised extraction captures signal despite noise
3. **Significant gap remains** — all methods have limited accuracy, substantial room for improvement
4. **Different methods excel at different types** — MatSeg for material states, SAM for object-aligned segments

---

## Appendix

### A. Net Architecture and Training

**Architecture:**
- Standard U-net
- Encoder: Pretrained ConvNext base
- PSP layer
- 3 skip connections with upsampling
- Output: 128-dimensional descriptor per pixel

**Training Procedure:**

```python
def matseg_training_step(model, batch):
    """
    Training with material descriptor embeddings.
    """
    images, gt_masks = batch
    
    # Step 1: Forward pass → descriptor map (128 channels per pixel)
    descriptor_map = model(images)  # [B, 128, H, W]
    descriptor_map = F.normalize(descriptor_map, dim=1)  # L2 normalize
    
    # Step 2: Compute average descriptor per material
    material_descriptors = []
    for material_id in unique_materials(gt_masks):
        mask = (gt_masks == material_id)
        avg_descriptor = descriptor_map[:, :, mask].mean(dim=-1)
        material_descriptors.append(avg_descriptor)
    
    # Step 3: Compute similarity maps (cosine similarity)
    similarity_maps = []
    for mat_desc in material_descriptors:
        # [B, H, W] cosine similarity to this material
        sim = torch.einsum('bchw,bc->bhw', descriptor_map, mat_desc)
        similarity_maps.append(sim)
    
    # Step 4: Softmax over materials (temperature=0.2)
    similarity_stack = torch.stack(similarity_maps, dim=1)  # [B, M, H, W]
    probabilities = F.softmax(similarity_stack / 0.2, dim=1)
    
    # Step 5: Cross-entropy loss
    # Convert soft GT to hard (highest concentration per pixel)
    gt_hard = gt_masks.argmax(dim=1)
    loss = F.cross_entropy(probabilities, gt_hard)
    
    return loss
```

**Training Parameters:**
- Optimizer: AdamW
- Learning rate: 1e-5
- Hardware: Single RTX 3090
- Image size: Random crop/resize 250-900 pixels

**Augmentation:**
- Darkening/lightening
- Gaussian blur
- Partial and full decoloring
- White noise addition

### B. 3D Scene Building (Blender)

```python
def build_3d_scene():
    """
    3D scene creation in Blender with Cycles.
    """
    # 1. Load random 3D objects (ShapeNet, Objaverse-XL)
    objects = load_random_objects()
    
    # 2. Generate material map from natural image
    source_image = load_random_image()  # Open Images v7
    material_map = extract_material_map(source_image)
    
    # 3. Load PBR materials and map to object surfaces
    for obj in objects:
        uv_map = generate_uv(obj, material_map)
        assign_pbr_materials(obj, uv_map)
    
    # 4. Set up environment
    load_hdri_background()  # HDRI Haven (600 panoramic images)
    add_ground_plane()
    add_random_objects()  # Shadows and occlusion
    add_random_lights()  # Optional additional lights
    
    # 5. Camera and render
    set_random_camera()
    render_with_cycles()
```

### C. Hardware Requirements

| Task | Hardware |
|------|----------|
| 2D scene generation | CPU (i7) |
| Texture extraction | CPU (i7) |
| 3D rendering | RTX 3090 (accelerated) |
| Training | RTX 3090 |

### D. Asset Sources

| Asset | Source | License |
|-------|--------|---------|
| Images | Open Images v7 | Apache |
| 3D Objects | ShapeNet | GNU |
| HDRIs | HDRI Haven | CC0 |
| Rendering | Blender 4 + Cycles | GPL |

### E. Shared Resources

**Available publicly:**
- 300,000+ extracted textures
- 200,000+ generated SVBRDF/PBR materials
- MatSeg dataset (1,220 annotated images)
- Trained models and weights
- Generation scripts
- Python readers and evaluation code

**License:** CC0 1.0 Universal (Public Domain)

