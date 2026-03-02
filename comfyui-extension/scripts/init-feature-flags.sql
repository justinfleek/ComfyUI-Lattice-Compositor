-- Feature Flags Initialization Script
-- Run: duckdb .lattice/database.duckdb < scripts/init-feature-flags.sql

-- Insert default feature flags
INSERT INTO feature_flags (id, name, description, enabled_by_default, category, created_at, updated_at) VALUES
    ('ff-ui-particles', 'UI: Particles', 'Show particle system UI', true, 'ui', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-ui-physics', 'UI: Physics', 'Show physics UI', true, 'ui', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-ui-camera', 'UI: Camera', 'Show camera UI', true, 'ui', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-ui-audio', 'UI: Audio', 'Show audio panel', true, 'ui', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-ui-ai-chat', 'UI: AI Chat', 'Show AI chat panel', true, 'ui', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-ui-timeline', 'UI: Timeline', 'Show timeline panel', true, 'ui', strftime('%s', 'now'), strftime('%s', 'now')),
    
    ('ff-engine-webgpu', 'Engine: WebGPU', 'Use WebGPU renderer', true, 'engine', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-engine-webgl', 'Engine: WebGL', 'Use WebGL renderer (fallback)', true, 'engine', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-engine-motion-blur', 'Engine: Motion Blur', 'Enable motion blur', false, 'engine', strftime('%s', 'now'), strftime('%s', 'now')),
    
    ('ff-export-h264', 'Export: H.264', 'Enable H.264 export', true, 'export', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-export-prores', 'Export: ProRes', 'Enable ProRes export', false, 'export', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-export-webm', 'Export: WebM', 'Enable WebM export', true, 'export', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-export-camera', 'Export: Camera', 'Enable camera export formats', true, 'export', strftime('%s', 'now'), strftime('%s', 'now')),
    
    ('ff-ai-chat', 'AI: Chat', 'Enable AI chat', true, 'ai', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-ai-generation', 'AI: Generation', 'Enable AI generation', true, 'ai', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-ai-segmentation', 'AI: Segmentation', 'Enable AI segmentation', true, 'ai', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-ai-vectorization', 'AI: Vectorization', 'Enable AI vectorization', true, 'ai', strftime('%s', 'now'), strftime('%s', 'now')),
    
    ('ff-particles-enabled', 'Particles: Enabled', 'Enable particle systems', true, 'particles', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-particles-gpu', 'Particles: GPU', 'Use GPU acceleration', true, 'particles', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-particles-sph', 'Particles: SPH', 'Enable SPH fluid simulation', false, 'particles', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-particles-flocking', 'Particles: Flocking', 'Enable flocking behavior', true, 'particles', strftime('%s', 'now'), strftime('%s', 'now')),
    
    ('ff-physics-enabled', 'Physics: Enabled', 'Enable physics simulation', true, 'physics', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-physics-ragdoll', 'Physics: Ragdoll', 'Enable ragdoll physics', false, 'physics', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-physics-joints', 'Physics: Joints', 'Enable joint system', true, 'physics', strftime('%s', 'now'), strftime('%s', 'now')),
    
    ('ff-experimental-mesh-warp', 'Experimental: Mesh Warp', 'Enable mesh warp deformation', false, 'experimental', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-experimental-gaussian-splatting', 'Experimental: Gaussian Splatting', 'Enable Gaussian splatting', false, 'experimental', strftime('%s', 'now'), strftime('%s', 'now')),
    ('ff-experimental-depthflow', 'Experimental: Depth Flow', 'Enable depth flow', false, 'experimental', strftime('%s', 'now'), strftime('%s', 'now'));
