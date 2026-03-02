// FFI bindings for Lattice.Services.GLSL.Engine
// WebGL shader engine implementation

// Default vertex shader
const DEFAULT_VERTEX_SHADER = `
attribute vec2 a_position;
attribute vec2 a_texCoord;
varying vec2 v_texCoord;
varying vec2 fragCoord;
uniform vec3 iResolution;

void main() {
  gl_Position = vec4(a_position, 0.0, 1.0);
  v_texCoord = a_texCoord;
  fragCoord = a_texCoord * iResolution.xy;
}
`;

// Singleton instance
let engineInstance = null;

// Check if WebGL is available
export const isWebGLAvailableImpl = () => () => {
  try {
    const testCanvas = document.createElement("canvas");
    testCanvas.width = 1;
    testCanvas.height = 1;
    const gl = testCanvas.getContext("webgl") || testCanvas.getContext("experimental-webgl");
    return gl !== null;
  } catch {
    return false;
  }
};

// Create a new GLSL engine
export const createEngineImpl = (options) => () => {
  return {
    options,
    canvas: null,
    gl: null,
    program: null,
    positionBuffer: null,
    texCoordBuffer: null,
    inputTexture: null,
    framebuffer: null,
    outputTexture: null,
    currentWidth: 0,
    currentHeight: 0,
    uniformLocations: new Map(),
    currentShaderSource: "",
    contextLost: false
  };
};

// Get singleton instance
export const getEngineImpl = () => () => {
  if (!engineInstance) {
    engineInstance = createEngineImpl({
      preserveDrawingBuffer: true,
      alpha: true,
      premultipliedAlpha: false
    })();
  }
  return engineInstance;
};

// Dispose of engine resources
export const disposeEngineImpl = (engine) => () => {
  if (engine.gl) {
    if (engine.program) engine.gl.deleteProgram(engine.program);
    if (engine.inputTexture) engine.gl.deleteTexture(engine.inputTexture);
    if (engine.outputTexture) engine.gl.deleteTexture(engine.outputTexture);
    if (engine.positionBuffer) engine.gl.deleteBuffer(engine.positionBuffer);
    if (engine.texCoordBuffer) engine.gl.deleteBuffer(engine.texCoordBuffer);
    if (engine.framebuffer) engine.gl.deleteFramebuffer(engine.framebuffer);
  }
  engine.gl = null;
  engine.canvas = null;
  engine.program = null;
  engine.uniformLocations.clear();
  engine.contextLost = false;

  if (engine === engineInstance) {
    engineInstance = null;
  }
};

// Check if context is lost
export const isContextLostImpl = (engine) => () => {
  return engine.contextLost;
};

// Initialize WebGL context
function initGL(engine, width, height) {
  if (engine.contextLost) return false;

  // Create or resize canvas
  if (!engine.canvas) {
    engine.canvas = document.createElement("canvas");
    engine.canvas.addEventListener("webglcontextlost", (e) => {
      e.preventDefault();
      engine.contextLost = true;
      engine.gl = null;
      engine.program = null;
      engine.uniformLocations.clear();
    });
    engine.canvas.addEventListener("webglcontextrestored", () => {
      engine.contextLost = false;
    });
  }

  if (engine.currentWidth !== width || engine.currentHeight !== height) {
    engine.canvas.width = width;
    engine.canvas.height = height;
    engine.currentWidth = width;
    engine.currentHeight = height;
    engine.outputTexture = null;
  }

  // Get WebGL context
  if (!engine.gl) {
    engine.gl = engine.canvas.getContext("webgl", {
      alpha: engine.options.alpha !== false,
      premultipliedAlpha: engine.options.premultipliedAlpha || false,
      preserveDrawingBuffer: engine.options.preserveDrawingBuffer !== false
    });

    if (!engine.gl) return false;

    const gl = engine.gl;

    // Create position buffer
    engine.positionBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, engine.positionBuffer);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([
      -1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1
    ]), gl.STATIC_DRAW);

    // Create texture coordinate buffer
    engine.texCoordBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, engine.texCoordBuffer);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([
      0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1
    ]), gl.STATIC_DRAW);

    // Create framebuffer
    engine.framebuffer = gl.createFramebuffer();
  }

  // Create output texture if needed
  if (!engine.outputTexture) {
    const gl = engine.gl;
    engine.outputTexture = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, engine.outputTexture);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, width, height, 0, gl.RGBA, gl.UNSIGNED_BYTE, null);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  }

  return true;
}

// Compile shader
export const compileShaderImpl =
  (engine) => (fragmentSource) => (header) => (footer) => (library) => (includeLibrary) => () => {
    if (!initGL(engine, 1, 1)) {
      return { success: false, error: "WebGL not available", errorLine: null };
    }

    const gl = engine.gl;

    // Build full source
    let fullSource = header;
    if (includeLibrary) {
      fullSource += library;
    }
    fullSource += fragmentSource;
    fullSource += footer;

    // Compile vertex shader
    const vertexShader = gl.createShader(gl.VERTEX_SHADER);
    gl.shaderSource(vertexShader, DEFAULT_VERTEX_SHADER);
    gl.compileShader(vertexShader);

    if (!gl.getShaderParameter(vertexShader, gl.COMPILE_STATUS)) {
      const error = gl.getShaderInfoLog(vertexShader) || "Unknown vertex shader error";
      gl.deleteShader(vertexShader);
      return { success: false, error: "Vertex shader: " + error, errorLine: null };
    }

    // Compile fragment shader
    const fragmentShader = gl.createShader(gl.FRAGMENT_SHADER);
    gl.shaderSource(fragmentShader, fullSource);
    gl.compileShader(fragmentShader);

    if (!gl.getShaderParameter(fragmentShader, gl.COMPILE_STATUS)) {
      const error = gl.getShaderInfoLog(fragmentShader) || "Unknown fragment shader error";
      gl.deleteShader(vertexShader);
      gl.deleteShader(fragmentShader);

      const lineMatch = error.match(/ERROR: \d+:(\d+)/);
      const errorLine = lineMatch ? parseInt(lineMatch[1], 10) : null;

      return { success: false, error, errorLine };
    }

    // Create program
    const program = gl.createProgram();
    gl.attachShader(program, vertexShader);
    gl.attachShader(program, fragmentShader);
    gl.linkProgram(program);

    gl.deleteShader(vertexShader);
    gl.deleteShader(fragmentShader);

    if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
      const error = gl.getProgramInfoLog(program) || "Unknown program link error";
      gl.deleteProgram(program);
      return { success: false, error, errorLine: null };
    }

    // Store program
    if (engine.program) {
      gl.deleteProgram(engine.program);
    }
    engine.program = program;
    engine.currentShaderSource = fragmentSource;
    engine.uniformLocations.clear();

    return { success: true, error: null, errorLine: null };
  };

// Set shader (compile if changed)
export const setShaderImpl =
  (engine) => (fragmentSource) => (header) => (footer) => (library) => (includeLibrary) => () => {
    if (engine.currentShaderSource === fragmentSource && engine.program) {
      return { success: true, error: null, errorLine: null };
    }
    return compileShaderImpl(engine)(fragmentSource)(header)(footer)(library)(includeLibrary)();
  };

// Get uniform location with caching
function getUniformLocation(engine, name) {
  if (!engine.gl || !engine.program) return null;

  if (engine.uniformLocations.has(name)) {
    return engine.uniformLocations.get(name);
  }

  const location = engine.gl.getUniformLocation(engine.program, name);
  if (location) {
    engine.uniformLocations.set(name, location);
  }
  return location;
}

// Set uniforms
export const setUniformsImpl = (engine) => (uniforms) => () => {
  if (!engine.gl || !engine.program) return;

  const gl = engine.gl;
  gl.useProgram(engine.program);

  // iResolution
  const resLoc = getUniformLocation(engine, "iResolution");
  if (resLoc) {
    gl.uniform3f(resLoc, uniforms.iResolution.x, uniforms.iResolution.y, uniforms.iResolution.z);
  }

  // iTime
  const timeLoc = getUniformLocation(engine, "iTime");
  if (timeLoc) {
    gl.uniform1f(timeLoc, uniforms.iTime);
  }

  // iTimeDelta
  const deltaLoc = getUniformLocation(engine, "iTimeDelta");
  if (deltaLoc) {
    gl.uniform1f(deltaLoc, uniforms.iTimeDelta);
  }

  // iFrame
  const frameLoc = getUniformLocation(engine, "iFrame");
  if (frameLoc) {
    gl.uniform1i(frameLoc, uniforms.iFrame);
  }

  // iMouse
  const mouseLoc = getUniformLocation(engine, "iMouse");
  if (mouseLoc) {
    gl.uniform4f(mouseLoc, uniforms.iMouse.x, uniforms.iMouse.y, uniforms.iMouse.z, uniforms.iMouse.w);
  }

  // iDate
  const dateLoc = getUniformLocation(engine, "iDate");
  if (dateLoc) {
    gl.uniform4f(dateLoc, uniforms.iDate.x, uniforms.iDate.y, uniforms.iDate.z, uniforms.iDate.w);
  }

  // iSampleRate
  const rateLoc = getUniformLocation(engine, "iSampleRate");
  if (rateLoc) {
    gl.uniform1f(rateLoc, uniforms.iSampleRate);
  }
};

// Render implementation
export const renderImpl = (engine) => (inputCanvasId) => (width) => (height) => () =>
  new Promise((resolve, reject) => {
    if (!initGL(engine, width, height) || !engine.program) {
      reject(new Error("WebGL not initialized or no program"));
      return;
    }

    const gl = engine.gl;
    const inputCanvas = document.getElementById(inputCanvasId);

    if (!inputCanvas) {
      reject(new Error(`Input canvas not found: ${inputCanvasId}`));
      return;
    }

    try {
      // Set viewport
      gl.viewport(0, 0, width, height);
      gl.useProgram(engine.program);

      // Set up attributes
      const positionLoc = gl.getAttribLocation(engine.program, "a_position");
      const texCoordLoc = gl.getAttribLocation(engine.program, "a_texCoord");

      gl.bindBuffer(gl.ARRAY_BUFFER, engine.positionBuffer);
      gl.enableVertexAttribArray(positionLoc);
      gl.vertexAttribPointer(positionLoc, 2, gl.FLOAT, false, 0, 0);

      gl.bindBuffer(gl.ARRAY_BUFFER, engine.texCoordBuffer);
      gl.enableVertexAttribArray(texCoordLoc);
      gl.vertexAttribPointer(texCoordLoc, 2, gl.FLOAT, false, 0, 0);

      // Upload input texture
      if (!engine.inputTexture) {
        engine.inputTexture = gl.createTexture();
      }
      gl.activeTexture(gl.TEXTURE0);
      gl.bindTexture(gl.TEXTURE_2D, engine.inputTexture);
      gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, inputCanvas);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);

      // Set iChannel0 uniform
      const channel0Loc = getUniformLocation(engine, "iChannel0");
      if (channel0Loc) {
        gl.uniform1i(channel0Loc, 0);
      }

      // Render to framebuffer
      gl.bindFramebuffer(gl.FRAMEBUFFER, engine.framebuffer);
      gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, engine.outputTexture, 0);

      gl.clearColor(0, 0, 0, 0);
      gl.clear(gl.COLOR_BUFFER_BIT);
      gl.drawArrays(gl.TRIANGLES, 0, 6);

      // Read back result
      const pixels = new Uint8Array(width * height * 4);
      gl.readPixels(0, 0, width, height, gl.RGBA, gl.UNSIGNED_BYTE, pixels);

      gl.bindFramebuffer(gl.FRAMEBUFFER, null);

      // Create output canvas (flip Y)
      const outputCanvas = document.createElement("canvas");
      outputCanvas.width = width;
      outputCanvas.height = height;
      const ctx = outputCanvas.getContext("2d");
      const imageData = ctx.createImageData(width, height);

      for (let y = 0; y < height; y++) {
        const srcRow = (height - 1 - y) * width * 4;
        const dstRow = y * width * 4;
        for (let x = 0; x < width * 4; x++) {
          imageData.data[dstRow + x] = pixels[srcRow + x];
        }
      }

      ctx.putImageData(imageData, 0, 0);
      resolve(outputCanvas);
    } catch (error) {
      reject(error);
    }
  });

// Render with uniforms
export const renderWithUniformsImpl =
  (engine) => (inputCanvasId) => (width) => (height) => (uniforms) => () =>
    new Promise((resolve, reject) => {
      setUniformsImpl(engine)(uniforms)();
      renderImpl(engine)(inputCanvasId)(width)(height)()
        .then(resolve)
        .catch(reject);
    });
