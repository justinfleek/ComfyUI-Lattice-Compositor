//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                           // hydrogen // runtime // renderer
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! WebGPU renderer for Hydrogen command buffers.

use std::collections::HashMap;

use web_sys::HtmlCanvasElement;
use wgpu::util::DeviceExt;

use crate::commands::{CommandBuffer, DrawCommand, GlyphInstancePayload, PathDataHeader};
use crate::shaders;
use crate::tessellate::{tessellate_contours, tessellate_path_commands, TessellatedPath};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // vertex types
// ═══════════════════════════════════════════════════════════════════════════════

/// Vertex for rect rendering.
#[repr(C)]
#[derive(Copy, Clone, Debug, bytemuck::Pod, bytemuck::Zeroable)]
struct RectVertex {
    position: [f32; 2],
    rect: [f32; 4],
    color: [f32; 4],
    radii: [f32; 4],
    depth_pick: [f32; 2],
}

impl RectVertex {
    const ATTRIBS: [wgpu::VertexAttribute; 5] = wgpu::vertex_attr_array![
        0 => Float32x2,  // position
        1 => Float32x4,  // rect
        2 => Float32x4,  // color
        3 => Float32x4,  // radii
        4 => Float32x2,  // depth_pick
    ];
    
    fn desc() -> wgpu::VertexBufferLayout<'static> {
        wgpu::VertexBufferLayout {
            array_stride: std::mem::size_of::<RectVertex>() as wgpu::BufferAddress,
            step_mode: wgpu::VertexStepMode::Vertex,
            attributes: &Self::ATTRIBS,
        }
    }
}

/// Vertex for path rendering (typography as geometry).
#[repr(C)]
#[derive(Copy, Clone, Debug, bytemuck::Pod, bytemuck::Zeroable)]
struct PathVertex {
    position: [f32; 2],      // vertex position from tessellation
    transform: [f32; 4],     // position.xy, scale.xy
    rotation: [f32; 3],      // rotation.xyz (degrees)
    _pad: f32,               // padding for alignment
    color: [f32; 4],         // r, g, b, a
    depth_pick: [f32; 2],    // depth, pick_id
}

impl PathVertex {
    const ATTRIBS: [wgpu::VertexAttribute; 5] = wgpu::vertex_attr_array![
        0 => Float32x2,  // position
        1 => Float32x4,  // transform
        2 => Float32x3,  // rotation
        3 => Float32x4,  // color (note: skips padding via offset)
        4 => Float32x2,  // depth_pick
    ];
    
    fn desc() -> wgpu::VertexBufferLayout<'static> {
        wgpu::VertexBufferLayout {
            array_stride: std::mem::size_of::<PathVertex>() as wgpu::BufferAddress,
            step_mode: wgpu::VertexStepMode::Vertex,
            attributes: &Self::ATTRIBS,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // path data cache
// ═══════════════════════════════════════════════════════════════════════════════

/// Cached tessellated path data for instanced rendering.
#[derive(Debug)]
struct CachedPathData {
    tessellated: TessellatedPath,
    header: PathDataHeader,
}

/// Cache for path data definitions.
#[derive(Debug, Default)]
struct PathDataCache {
    entries: HashMap<u32, CachedPathData>,
}

impl PathDataCache {
    fn new() -> Self {
        PathDataCache {
            entries: HashMap::new(),
        }
    }
    
    fn insert(&mut self, id: u32, header: PathDataHeader, tessellated: TessellatedPath) {
        self.entries.insert(id, CachedPathData { tessellated, header });
    }
    
    fn get(&self, id: u32) -> Option<&CachedPathData> {
        self.entries.get(&id)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // uniforms
// ═══════════════════════════════════════════════════════════════════════════════

#[repr(C)]
#[derive(Copy, Clone, Debug, bytemuck::Pod, bytemuck::Zeroable)]
struct Uniforms {
    resolution: [f32; 2],
    _padding: [f32; 2],
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // renderer
// ═══════════════════════════════════════════════════════════════════════════════

/// The WebGPU renderer.
pub struct Renderer {
    device: wgpu::Device,
    queue: wgpu::Queue,
    surface: wgpu::Surface<'static>,
    surface_config: wgpu::SurfaceConfiguration,
    rect_pipeline: wgpu::RenderPipeline,
    path_pipeline: wgpu::RenderPipeline,
    uniform_buffer: wgpu::Buffer,
    uniform_bind_group: wgpu::BindGroup,
    bind_group_layout: wgpu::BindGroupLayout,
    width: u32,
    height: u32,
    path_data_cache: PathDataCache,
}

impl Renderer {
    /// Create a new renderer attached to a canvas.
    pub async fn new(canvas: HtmlCanvasElement) -> Result<Self, String> {
        let width = canvas.width();
        let height = canvas.height();
        
        // Create WebGPU instance
        let instance = wgpu::Instance::new(wgpu::InstanceDescriptor {
            backends: wgpu::Backends::BROWSER_WEBGPU,
            ..Default::default()
        });
        
        // Create surface from canvas
        #[cfg(target_arch = "wasm32")]
        let surface = instance
            .create_surface(wgpu::SurfaceTarget::Canvas(canvas))
            .map_err(|e| format!("Failed to create surface: {}", e))?;
        
        #[cfg(not(target_arch = "wasm32"))]
        let surface = {
            // For native testing, create a dummy surface
            // In production, this code path won't be used
            return Err("Native rendering not supported - use WASM target".to_string());
        };
        
        // Request adapter
        let adapter = instance
            .request_adapter(&wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::HighPerformance,
                compatible_surface: Some(&surface),
                force_fallback_adapter: false,
            })
            .await
            .ok_or("Failed to find GPU adapter")?;
        
        // Request device
        let (device, queue) = adapter
            .request_device(
                &wgpu::DeviceDescriptor {
                    label: Some("Hydrogen Device"),
                    required_features: wgpu::Features::empty(),
                    required_limits: wgpu::Limits::downlevel_webgl2_defaults(),
                },
                None,
            )
            .await
            .map_err(|e| format!("Failed to create device: {}", e))?;
        
        // Configure surface
        let surface_caps = surface.get_capabilities(&adapter);
        let surface_format = surface_caps
            .formats
            .iter()
            .copied()
            .find(|f| f.is_srgb())
            .unwrap_or(surface_caps.formats[0]);
        
        let surface_config = wgpu::SurfaceConfiguration {
            usage: wgpu::TextureUsages::RENDER_ATTACHMENT,
            format: surface_format,
            width,
            height,
            present_mode: wgpu::PresentMode::Fifo,
            alpha_mode: surface_caps.alpha_modes[0],
            view_formats: vec![],
            desired_maximum_frame_latency: 2,
        };
        surface.configure(&device, &surface_config);
        
        // Create uniform buffer
        let uniforms = Uniforms {
            resolution: [width as f32, height as f32],
            _padding: [0.0, 0.0],
        };
        
        let uniform_buffer = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("Uniform Buffer"),
            contents: bytemuck::cast_slice(&[uniforms]),
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
        });
        
        // Create bind group layout
        let bind_group_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("Uniform Bind Group Layout"),
            entries: &[wgpu::BindGroupLayoutEntry {
                binding: 0,
                visibility: wgpu::ShaderStages::VERTEX | wgpu::ShaderStages::FRAGMENT,
                ty: wgpu::BindingType::Buffer {
                    ty: wgpu::BufferBindingType::Uniform,
                    has_dynamic_offset: false,
                    min_binding_size: None,
                },
                count: None,
            }],
        });
        
        let uniform_bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("Uniform Bind Group"),
            layout: &bind_group_layout,
            entries: &[wgpu::BindGroupEntry {
                binding: 0,
                resource: uniform_buffer.as_entire_binding(),
            }],
        });
        
        // Create rect pipeline
        let rect_shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("Rect Shader"),
            source: wgpu::ShaderSource::Wgsl(shaders::RECT_SHADER.into()),
        });
        
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("Rect Pipeline Layout"),
            bind_group_layouts: &[&bind_group_layout],
            push_constant_ranges: &[],
        });
        
        let rect_pipeline = device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("Rect Pipeline"),
            layout: Some(&pipeline_layout),
            vertex: wgpu::VertexState {
                module: &rect_shader,
                entry_point: "vs_main",
                buffers: &[RectVertex::desc()],
            },
            fragment: Some(wgpu::FragmentState {
                module: &rect_shader,
                entry_point: "fs_main",
                targets: &[Some(wgpu::ColorTargetState {
                    format: surface_format,
                    blend: Some(wgpu::BlendState::ALPHA_BLENDING),
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            primitive: wgpu::PrimitiveState {
                topology: wgpu::PrimitiveTopology::TriangleList,
                strip_index_format: None,
                front_face: wgpu::FrontFace::Ccw,
                cull_mode: None,
                polygon_mode: wgpu::PolygonMode::Fill,
                unclipped_depth: false,
                conservative: false,
            },
            depth_stencil: None,
            multisample: wgpu::MultisampleState::default(),
            multiview: None,
        });
        
        // Create path pipeline for typography as geometry
        let path_shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("Path Shader"),
            source: wgpu::ShaderSource::Wgsl(shaders::PATH_SHADER.into()),
        });
        
        let path_pipeline = device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("Path Pipeline"),
            layout: Some(&pipeline_layout),
            vertex: wgpu::VertexState {
                module: &path_shader,
                entry_point: "vs_main",
                buffers: &[PathVertex::desc()],
            },
            fragment: Some(wgpu::FragmentState {
                module: &path_shader,
                entry_point: "fs_main",
                targets: &[Some(wgpu::ColorTargetState {
                    format: surface_format,
                    blend: Some(wgpu::BlendState::ALPHA_BLENDING),
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            primitive: wgpu::PrimitiveState {
                topology: wgpu::PrimitiveTopology::TriangleList,
                strip_index_format: None,
                front_face: wgpu::FrontFace::Ccw,
                cull_mode: None,
                polygon_mode: wgpu::PolygonMode::Fill,
                unclipped_depth: false,
                conservative: false,
            },
            depth_stencil: None,
            multisample: wgpu::MultisampleState::default(),
            multiview: None,
        });
        
        Ok(Renderer {
            device,
            queue,
            surface,
            surface_config,
            rect_pipeline,
            path_pipeline,
            uniform_buffer,
            uniform_bind_group,
            bind_group_layout,
            width,
            height,
            path_data_cache: PathDataCache::new(),
        })
    }
    
    /// Render a command buffer.
    pub fn render(&mut self, buffer: &CommandBuffer) -> Result<(), String> {
        // First pass: process DefinePathData commands to populate cache
        self.process_path_definitions(buffer);
        
        // Get current frame
        let output = self
            .surface
            .get_current_texture()
            .map_err(|e| format!("Failed to get surface texture: {}", e))?;
        
        let view = output.texture.create_view(&wgpu::TextureViewDescriptor::default());
        
        // Collect rect commands
        let rects: Vec<_> = buffer
            .commands
            .iter()
            .filter_map(|cmd| match cmd {
                DrawCommand::Rect(r) => Some(*r),
                _ => None,
            })
            .collect();
        
        // Collect glyph instance commands
        let glyph_instances: Vec<_> = buffer
            .commands
            .iter()
            .filter_map(|cmd| match cmd {
                DrawCommand::GlyphInstance(g) => Some(*g),
                _ => None,
            })
            .collect();
        
        // Build rect vertex buffer
        let rect_vertices = self.build_rect_vertices(&rects);
        
        // Build path vertex buffer for glyph instances
        let path_vertices = self.build_path_vertices(&glyph_instances);
        
        // Check if there's anything to draw
        if rect_vertices.is_empty() && path_vertices.is_empty() {
            output.present();
            return Ok(());
        }
        
        // Create buffers before render pass so they live long enough
        let rect_buffer = if !rect_vertices.is_empty() {
            Some(self.device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("Rect Vertex Buffer"),
                contents: bytemuck::cast_slice(&rect_vertices),
                usage: wgpu::BufferUsages::VERTEX,
            }))
        } else {
            None
        };
        
        let path_buffer = if !path_vertices.is_empty() {
            Some(self.device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("Path Vertex Buffer"),
                contents: bytemuck::cast_slice(&path_vertices),
                usage: wgpu::BufferUsages::VERTEX,
            }))
        } else {
            None
        };
        
        // Create command encoder
        let mut encoder = self.device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
            label: Some("Render Encoder"),
        });
        
        // Render pass
        {
            let mut render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                label: Some("Main Render Pass"),
                color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                    view: &view,
                    resolve_target: None,
                    ops: wgpu::Operations {
                        load: wgpu::LoadOp::Clear(wgpu::Color::BLACK),
                        store: wgpu::StoreOp::Store,
                    },
                })],
                depth_stencil_attachment: None,
                timestamp_writes: None,
                occlusion_query_set: None,
            });
            
            // Draw rectangles
            if let Some(ref buffer) = rect_buffer {
                render_pass.set_pipeline(&self.rect_pipeline);
                render_pass.set_bind_group(0, &self.uniform_bind_group, &[]);
                render_pass.set_vertex_buffer(0, buffer.slice(..));
                render_pass.draw(0..rect_vertices.len() as u32, 0..1);
            }
            
            // Draw path geometry (glyph instances)
            if let Some(ref buffer) = path_buffer {
                render_pass.set_pipeline(&self.path_pipeline);
                render_pass.set_bind_group(0, &self.uniform_bind_group, &[]);
                render_pass.set_vertex_buffer(0, buffer.slice(..));
                render_pass.draw(0..path_vertices.len() as u32, 0..1);
            }
        }
        
        // Submit and present
        self.queue.submit(std::iter::once(encoder.finish()));
        output.present();
        
        Ok(())
    }
    
    /// Process DefinePathData commands and cache tessellated geometry.
    fn process_path_definitions(&mut self, buffer: &CommandBuffer) {
        for cmd in &buffer.commands {
            match cmd {
                DrawCommand::PathData { header, commands } => {
                    // Only tessellate if not already cached
                    if self.path_data_cache.get(header.path_data_id).is_none() {
                        let tessellated = tessellate_path_commands(commands);
                        self.path_data_cache.insert(header.path_data_id, *header, tessellated);
                    }
                }
                DrawCommand::GlyphPath { header, contours } => {
                    // Cache glyph paths using glyph_id as the path_data_id
                    if self.path_data_cache.get(header.glyph_id).is_none() {
                        let tessellated = tessellate_contours(contours);
                        // Create a PathDataHeader from GlyphPathHeader
                        let path_header = PathDataHeader {
                            path_data_id: header.glyph_id,
                            command_count: 0, // Not used for cached data
                            bounds: header.bounds,
                        };
                        self.path_data_cache.insert(header.glyph_id, path_header, tessellated);
                    }
                }
                _ => {}
            }
        }
    }
    
    /// Build rect vertices from rect payloads.
    fn build_rect_vertices(&self, rects: &[crate::commands::RectPayload]) -> Vec<RectVertex> {
        let mut vertices = Vec::with_capacity(rects.len() * 6);
        
        for rect in rects {
            let quad_positions: [[f32; 2]; 6] = [
                [0.0, 0.0], [1.0, 0.0], [1.0, 1.0],
                [0.0, 0.0], [1.0, 1.0], [0.0, 1.0],
            ];
            
            for pos in quad_positions {
                vertices.push(RectVertex {
                    position: pos,
                    rect: [rect.x, rect.y, rect.width, rect.height],
                    color: [rect.color.r, rect.color.g, rect.color.b, rect.color.a],
                    radii: [
                        rect.radii.top_left,
                        rect.radii.top_right,
                        rect.radii.bottom_right,
                        rect.radii.bottom_left,
                    ],
                    depth_pick: [rect.depth, rect.pick_id as f32],
                });
            }
        }
        
        vertices
    }
    
    /// Build path vertices from glyph instance payloads.
    fn build_path_vertices(&self, instances: &[GlyphInstancePayload]) -> Vec<PathVertex> {
        let mut vertices = Vec::new();
        
        for instance in instances {
            // Look up cached tessellated path data
            if let Some(cached) = self.path_data_cache.get(instance.path_data_id) {
                let tess = &cached.tessellated;
                
                // Convert color from u8 to f32
                let color = [
                    instance.color.r as f32 / 255.0,
                    instance.color.g as f32 / 255.0,
                    instance.color.b as f32 / 255.0,
                    instance.color.a as f32 / 255.0,
                ];
                
                let transform = [
                    instance.pos_x,
                    instance.pos_y,
                    instance.scale_x,
                    instance.scale_y,
                ];
                
                let rotation = [instance.rot_x, instance.rot_y, instance.rot_z];
                let depth_pick = [instance.depth, instance.pick_id as f32];
                
                // Create vertices for each triangle
                for i in (0..tess.indices.len()).step_by(3) {
                    for j in 0..3 {
                        let idx = tess.indices[i + j] as usize;
                        let vx = tess.vertices[idx * 2];
                        let vy = tess.vertices[idx * 2 + 1];
                        
                        vertices.push(PathVertex {
                            position: [vx, vy],
                            transform,
                            rotation,
                            _pad: 0.0,
                            color,
                            depth_pick,
                        });
                    }
                }
            }
        }
        
        vertices
    }
    
    /// Pick the element at screen coordinates.
    pub fn pick(&self, _x: u32, _y: u32) -> u32 {
        // Simplified: full implementation would render to pick buffer
        // and read back the pixel value
        0
    }
    
    /// Resize the renderer.
    pub fn resize(&mut self, width: u32, height: u32) {
        if width == 0 || height == 0 {
            return;
        }
        
        self.width = width;
        self.height = height;
        
        self.surface_config.width = width;
        self.surface_config.height = height;
        self.surface.configure(&self.device, &self.surface_config);
        
        // Update uniforms
        let uniforms = Uniforms {
            resolution: [width as f32, height as f32],
            _padding: [0.0, 0.0],
        };
        self.queue.write_buffer(&self.uniform_buffer, 0, bytemuck::cast_slice(&[uniforms]));
    }
}
