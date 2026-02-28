//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                              // hydrogen // runtime // wasm
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Hydrogen WebGPU Runtime
//!
//! This is the WASM runtime that consumes Hydrogen's binary command format
//! and renders via WebGPU. No JavaScript in the render path.
//!
//! ## Architecture
//!
//! ```text
//! PureScript (Hydrogen)
//!     ↓ Binary.serialize
//! Command Buffer (bytes)
//!     ↓ WASM boundary
//! Rust (this crate)
//!     ↓ parse + render
//! WebGPU
//! ```
//!
//! ## Usage from JavaScript
//!
//! ```javascript
//! import init, { Runtime } from 'hydrogen-runtime';
//!
//! await init();
//! const runtime = await Runtime.new(canvas);
//! runtime.render(commandBytes);
//! ```

mod binary;
mod commands;
mod renderer;
mod shaders;
mod tessellate;

use wasm_bindgen::prelude::*;
use web_sys::HtmlCanvasElement;

pub use binary::parse_command_buffer;
pub use commands::{CommandBuffer, DrawCommand, Header};
pub use renderer::Renderer;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // wasm entry
// ═══════════════════════════════════════════════════════════════════════════════

/// Initialize panic hook for better error messages in browser console.
#[wasm_bindgen(start)]
pub fn init() {
    #[cfg(feature = "console_error_panic_hook")]
    console_error_panic_hook::set_once();
    
    console_log::init_with_level(log::Level::Info).expect("Failed to init logger");
    log::info!("Hydrogen Runtime initialized");
}

/// The main runtime interface exposed to JavaScript/PureScript.
#[wasm_bindgen]
pub struct Runtime {
    renderer: Renderer,
}

#[wasm_bindgen]
impl Runtime {
    /// Create a new runtime attached to a canvas element.
    #[wasm_bindgen(constructor)]
    pub async fn new(canvas: HtmlCanvasElement) -> Result<Runtime, JsValue> {
        let renderer = Renderer::new(canvas)
            .await
            .map_err(|e| JsValue::from_str(&e))?;
        
        Ok(Runtime { renderer })
    }
    
    /// Render a command buffer.
    ///
    /// Takes raw bytes from Hydrogen's Binary.serialize output.
    #[wasm_bindgen]
    pub fn render(&mut self, bytes: &[u8]) -> Result<(), JsValue> {
        let buffer = parse_command_buffer(bytes)
            .map_err(|e| JsValue::from_str(&format!("Parse error: {}", e)))?;
        
        self.renderer
            .render(&buffer)
            .map_err(|e| JsValue::from_str(&format!("Render error: {}", e)))?;
        
        Ok(())
    }
    
    /// Get the pick ID at screen coordinates.
    ///
    /// Returns 0 if no interactive element at that position.
    #[wasm_bindgen]
    pub fn pick(&self, x: u32, y: u32) -> u32 {
        self.renderer.pick(x, y)
    }
    
    /// Resize the renderer to match canvas size.
    #[wasm_bindgen]
    pub fn resize(&mut self, width: u32, height: u32) {
        self.renderer.resize(width, height);
    }
}
