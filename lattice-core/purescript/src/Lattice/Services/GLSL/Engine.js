// @ts-check
/**
 * Lattice GLSL Engine FFI
 *
 * WebGL2 shader engine with Shadertoy-compatible uniforms.
 * Provides GPU-accelerated image processing for effects pipeline.
 */

// ────────────────────────────────────────────────────────────────────────────
// Engine Singleton
// ────────────────────────────────────────────────────────────────────────────

/** @type {GLSLEngine | null} */
let engineSingleton = null;

/**
 * @typedef {Object} GLSLEngine
 * @property {WebGL2RenderingContext} gl
 * @property {HTMLCanvasElement} canvas
 * @property {WebGLProgram | null} currentProgram
 * @property {string} currentShaderSource
 * @property {WebGLBuffer | null} vertexBuffer
 * @property {WebGLBuffer | null} texCoordBuffer
 * @property {WebGLTexture | null} inputTexture
 * @property {Object} uniformLocations
 */

// ────────────────────────────────────────────────────────────────────────────
// Vertex Shader (constant)
// ────────────────────────────────────────────────────────────────────────────

const VERTEX_SHADER = `#version 300 es
in vec2 a_position;
in vec2 a_texCoord;
out vec2 v_texCoord;
out vec2 fragCoord;
uniform vec3 iResolution;

void main() {
  gl_Position = vec4(a_position, 0.0, 1.0);
  v_texCoord = a_texCoord;
  fragCoord = a_texCoord * iResolution.xy;
}
`;

// ────────────────────────────────────────────────────────────────────────────
// Implementation Functions
// ────────────────────────────────────────────────────────────────────────────

/**
 * Check if WebGL2 is available
 * @returns {boolean}
 */
export function isWebGLAvailableImpl() {
  try {
    const canvas = document.createElement("canvas");
    return !!canvas.getContext("webgl2");
  } catch (e) {
    return false;
  }
}

/**
 * Create a new GLSL engine
 * @param {Object} options
 * @param {boolean} options.preserveDrawingBuffer
 * @param {boolean} options.alpha
 * @param {boolean} options.premultipliedAlpha
 * @returns {GLSLEngine}
 */
export function createEngineImpl(options) {
  return () => {
    const canvas = document.createElement("canvas");
    canvas.width = 1920;
    canvas.height = 1080;

    const gl = canvas.getContext("webgl2", {
      preserveDrawingBuffer: options.preserveDrawingBuffer,
      alpha: options.alpha,
      premultipliedAlpha: options.premultipliedAlpha,
      antialias: false,
      depth: false,
      stencil: false,
    });

    if (!gl) {
      throw new Error("WebGL2 not available");
    }

    // Create vertex buffer (fullscreen quad)
    const vertexBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, vertexBuffer);
    gl.bufferData(
      gl.ARRAY_BUFFER,
      new Float32Array([-1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1]),
      gl.STATIC_DRAW,
    );

    // Create texture coordinate buffer
    const texCoordBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, texCoordBuffer);
    gl.bufferData(
      gl.ARRAY_BUFFER,
      new Float32Array([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1]),
      gl.STATIC_DRAW,
    );

    /** @type {GLSLEngine} */
    const engine = {
      gl,
      canvas,
      currentProgram: null,
      currentShaderSource: "",
      vertexBuffer,
      texCoordBuffer,
      inputTexture: null,
      uniformLocations: {},
    };

    return engine;
  };
}

/**
 * Dispose of engine resources
 * @param {GLSLEngine} engine
 * @returns {function(): void}
 */
export function disposeEngineImpl(engine) {
  return () => {
    const gl = engine.gl;
    if (engine.currentProgram) {
      gl.deleteProgram(engine.currentProgram);
    }
    if (engine.vertexBuffer) {
      gl.deleteBuffer(engine.vertexBuffer);
    }
    if (engine.texCoordBuffer) {
      gl.deleteBuffer(engine.texCoordBuffer);
    }
    if (engine.inputTexture) {
      gl.deleteTexture(engine.inputTexture);
    }
    // Lose context
    const ext = gl.getExtension("WEBGL_lose_context");
    if (ext) {
      ext.loseContext();
    }
  };
}

/**
 * Check if context is lost
 * @param {GLSLEngine} engine
 * @returns {function(): boolean}
 */
export function isContextLostImpl(engine) {
  return () => engine.gl.isContextLost();
}

/**
 * Compile a shader program
 * @param {GLSLEngine} engine
 * @param {string} fragmentSource
 * @param {string} header
 * @param {string} footer
 * @param {string} library
 * @param {boolean} includeLibrary
 * @returns {function(): Object}
 */
export function compileShaderImpl(engine) {
  return (fragmentSource) =>
    (header) =>
    (footer) =>
    (library) =>
    (includeLibrary) =>
    () => {
      const gl = engine.gl;

      // Compile vertex shader
      const vertexShader = gl.createShader(gl.VERTEX_SHADER);
      if (!vertexShader) {
        return {
          success: false,
          error: { value0: "Failed to create vertex shader" },
          errorLine: { value0: 0 },
        };
      }
      gl.shaderSource(vertexShader, VERTEX_SHADER);
      gl.compileShader(vertexShader);

      if (!gl.getShaderParameter(vertexShader, gl.COMPILE_STATUS)) {
        const log = gl.getShaderInfoLog(vertexShader) || "Unknown error";
        gl.deleteShader(vertexShader);
        return {
          success: false,
          error: { value0: "Vertex: " + log },
          errorLine: { value0: 0 },
        };
      }

      // Build fragment shader source
      const fragPrefix = `#version 300 es
precision highp float;
out vec4 fragColor;
`;
      const libSource = includeLibrary ? library : "";
      const fullSource =
        fragPrefix + header + libSource + fragmentSource + footer;

      // Compile fragment shader
      const fragmentShader = gl.createShader(gl.FRAGMENT_SHADER);
      if (!fragmentShader) {
        gl.deleteShader(vertexShader);
        return {
          success: false,
          error: { value0: "Failed to create fragment shader" },
          errorLine: { value0: 0 },
        };
      }
      gl.shaderSource(fragmentShader, fullSource);
      gl.compileShader(fragmentShader);

      if (!gl.getShaderParameter(fragmentShader, gl.COMPILE_STATUS)) {
        const log = gl.getShaderInfoLog(fragmentShader) || "Unknown error";
        gl.deleteShader(vertexShader);
        gl.deleteShader(fragmentShader);

        // Parse error line
        const match = log.match(/ERROR:\s*\d+:(\d+)/);
        const errorLine = match ? parseInt(match[1], 10) : 0;

        return {
          success: false,
          error: { value0: log },
          errorLine: { value0: errorLine },
        };
      }

      // Link program
      const program = gl.createProgram();
      if (!program) {
        gl.deleteShader(vertexShader);
        gl.deleteShader(fragmentShader);
        return {
          success: false,
          error: { value0: "Failed to create program" },
          errorLine: { value0: 0 },
        };
      }

      gl.attachShader(program, vertexShader);
      gl.attachShader(program, fragmentShader);
      gl.linkProgram(program);

      // Shaders can be deleted after linking
      gl.deleteShader(vertexShader);
      gl.deleteShader(fragmentShader);

      if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
        const log = gl.getProgramInfoLog(program) || "Unknown link error";
        gl.deleteProgram(program);
        return {
          success: false,
          error: { value0: log },
          errorLine: { value0: 0 },
        };
      }

      // Store the program
      if (engine.currentProgram) {
        gl.deleteProgram(engine.currentProgram);
      }
      engine.currentProgram = program;
      engine.currentShaderSource = fragmentSource;

      // Cache uniform locations
      gl.useProgram(program);
      engine.uniformLocations = {
        iResolution: gl.getUniformLocation(program, "iResolution"),
        iTime: gl.getUniformLocation(program, "iTime"),
        iTimeDelta: gl.getUniformLocation(program, "iTimeDelta"),
        iFrame: gl.getUniformLocation(program, "iFrame"),
        iMouse: gl.getUniformLocation(program, "iMouse"),
        iDate: gl.getUniformLocation(program, "iDate"),
        iSampleRate: gl.getUniformLocation(program, "iSampleRate"),
        iChannel0: gl.getUniformLocation(program, "iChannel0"),
      };

      return { success: true, error: null, errorLine: null };
    };
}

/**
 * Set shader (only recompiles if source changed)
 * @param {GLSLEngine} engine
 * @param {string} fragmentSource
 * @param {string} header
 * @param {string} footer
 * @param {string} library
 * @param {boolean} includeLibrary
 * @returns {function(): Object}
 */
export function setShaderImpl(engine) {
  return (fragmentSource) =>
    (header) =>
    (footer) =>
    (library) =>
    (includeLibrary) =>
    () => {
      // Skip if same shader
      if (
        engine.currentShaderSource === fragmentSource &&
        engine.currentProgram
      ) {
        return { success: true, error: null, errorLine: null };
      }
      // Compile new shader
      return compileShaderImpl(engine)(fragmentSource)(header)(footer)(library)(
        includeLibrary,
      )();
    };
}

/**
 * Set uniforms on current shader
 * @param {GLSLEngine} engine
 * @param {Object} uniforms
 * @returns {function(): void}
 */
export function setUniformsImpl(engine) {
  return (uniforms) => () => {
    const gl = engine.gl;
    const locs = engine.uniformLocations;

    if (!engine.currentProgram) return;

    gl.useProgram(engine.currentProgram);

    if (locs.iResolution && uniforms.iResolution) {
      gl.uniform3f(
        locs.iResolution,
        uniforms.iResolution.x,
        uniforms.iResolution.y,
        uniforms.iResolution.z,
      );
    }
    if (locs.iTime != null) {
      gl.uniform1f(locs.iTime, uniforms.iTime);
    }
    if (locs.iTimeDelta != null) {
      gl.uniform1f(locs.iTimeDelta, uniforms.iTimeDelta);
    }
    if (locs.iFrame != null) {
      gl.uniform1i(locs.iFrame, uniforms.iFrame);
    }
    if (locs.iMouse && uniforms.iMouse) {
      gl.uniform4f(
        locs.iMouse,
        uniforms.iMouse.x,
        uniforms.iMouse.y,
        uniforms.iMouse.z,
        uniforms.iMouse.w,
      );
    }
    if (locs.iDate && uniforms.iDate) {
      gl.uniform4f(
        locs.iDate,
        uniforms.iDate.x,
        uniforms.iDate.y,
        uniforms.iDate.z,
        uniforms.iDate.w,
      );
    }
    if (locs.iSampleRate != null) {
      gl.uniform1f(locs.iSampleRate, uniforms.iSampleRate);
    }
  };
}

/**
 * Render with current shader
 * @param {GLSLEngine} engine
 * @param {string} inputCanvasId
 * @param {number} width
 * @param {number} height
 * @returns {function(function(Error): void, function(HTMLCanvasElement): void): function(): void}
 */
export function renderImpl(engine) {
  return (inputCanvasId) => (width) => (height) => (onError, onSuccess) => {
    try {
      const gl = engine.gl;
      const canvas = engine.canvas;

      // Resize canvas if needed
      if (canvas.width !== width || canvas.height !== height) {
        canvas.width = width;
        canvas.height = height;
      }

      gl.viewport(0, 0, width, height);
      gl.clearColor(0, 0, 0, 0);
      gl.clear(gl.COLOR_BUFFER_BIT);

      if (!engine.currentProgram) {
        onError(new Error("No shader program compiled"));
        return () => {};
      }

      gl.useProgram(engine.currentProgram);

      // Get input canvas if specified
      if (inputCanvasId) {
        const inputCanvas = document.getElementById(inputCanvasId);
        if (
          inputCanvas &&
          (inputCanvas instanceof HTMLCanvasElement ||
            inputCanvas instanceof HTMLImageElement)
        ) {
          // Create or update texture
          if (!engine.inputTexture) {
            engine.inputTexture = gl.createTexture();
          }
          gl.activeTexture(gl.TEXTURE0);
          gl.bindTexture(gl.TEXTURE_2D, engine.inputTexture);
          gl.texImage2D(
            gl.TEXTURE_2D,
            0,
            gl.RGBA,
            gl.RGBA,
            gl.UNSIGNED_BYTE,
            inputCanvas,
          );
          gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
          gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
          gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
          gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);

          if (engine.uniformLocations.iChannel0 != null) {
            gl.uniform1i(engine.uniformLocations.iChannel0, 0);
          }
        }
      }

      // Set resolution uniform
      if (engine.uniformLocations.iResolution) {
        gl.uniform3f(engine.uniformLocations.iResolution, width, height, 1.0);
      }

      // Setup vertex attributes
      const posLoc = gl.getAttribLocation(engine.currentProgram, "a_position");
      const texLoc = gl.getAttribLocation(engine.currentProgram, "a_texCoord");

      gl.bindBuffer(gl.ARRAY_BUFFER, engine.vertexBuffer);
      gl.enableVertexAttribArray(posLoc);
      gl.vertexAttribPointer(posLoc, 2, gl.FLOAT, false, 0, 0);

      gl.bindBuffer(gl.ARRAY_BUFFER, engine.texCoordBuffer);
      gl.enableVertexAttribArray(texLoc);
      gl.vertexAttribPointer(texLoc, 2, gl.FLOAT, false, 0, 0);

      // Draw
      gl.drawArrays(gl.TRIANGLES, 0, 6);

      onSuccess(canvas);
    } catch (e) {
      onError(e instanceof Error ? e : new Error(String(e)));
    }

    return () => {}; // Canceler
  };
}

/**
 * Render with uniforms
 * @param {GLSLEngine} engine
 * @param {string} inputCanvasId
 * @param {number} width
 * @param {number} height
 * @param {Object} uniforms
 * @returns {function(function(Error): void, function(HTMLCanvasElement): void): function(): void}
 */
export function renderWithUniformsImpl(engine) {
  return (inputCanvasId) =>
    (width) =>
    (height) =>
    (uniforms) =>
    (onError, onSuccess) => {
      setUniformsImpl(engine)(uniforms)();
      return renderImpl(engine)(inputCanvasId)(width)(height)(
        onError,
        onSuccess,
      );
    };
}

/**
 * Get singleton engine instance
 * @returns {function(): GLSLEngine}
 */
export function getEngineImpl() {
  return () => {
    if (!engineSingleton) {
      engineSingleton = createEngineImpl({
        preserveDrawingBuffer: true,
        alpha: true,
        premultipliedAlpha: false,
      })();
    }
    return engineSingleton;
  };
}
