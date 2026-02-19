let sesReady = false;
let Compartment = null;
let harden = null;
async function initSES() {
  if (sesReady) return true;
  try {
    await import('./assets/index-DIa_xRYn.js');
    if (!globalThis.lockdown) {
      return false;
    }
    globalThis.lockdown({
      consoleTaming: "unsafe",
      errorTaming: "unsafe",
      stackFiltering: "verbose",
      overrideTaming: "severe",
      localeTaming: "unsafe",
      domainTaming: "unsafe"
    });
    Compartment = globalThis.Compartment !== null && globalThis.Compartment !== void 0 && typeof globalThis.Compartment === "function" ? globalThis.Compartment : null;
    harden = globalThis.harden !== null && globalThis.harden !== void 0 && typeof globalThis.harden === "function" ? globalThis.harden : null;
    if (!Compartment || !harden) {
      return false;
    }
    sesReady = true;
    return true;
  } catch (e) {
    console.error("[ExpressionWorker] SES init failed:", e);
    return false;
  }
}
const safeMath = {
  abs: Math.abs,
  acos: Math.acos,
  asin: Math.asin,
  atan: Math.atan,
  atan2: Math.atan2,
  ceil: Math.ceil,
  cos: Math.cos,
  exp: Math.exp,
  floor: Math.floor,
  log: Math.log,
  max: Math.max,
  min: Math.min,
  pow: Math.pow,
  round: Math.round,
  sin: Math.sin,
  sqrt: Math.sqrt,
  tan: Math.tan,
  PI: Math.PI,
  E: Math.E
};
function createSeededRandom(frame) {
  return (seed) => {
    const s = seed !== void 0 ? seed : frame;
    const x = Math.sin(s * 12.9898) * 43758.5453;
    return x - Math.floor(x);
  };
}
async function evaluate(req) {
  try {
    if (!sesReady) {
      const ok = await initSES();
      if (!ok) {
        throw new Error(`[ExpressionWorker] SES not available. Secure Evaluator initialization failed.`);
      }
    }
    const frame = typeof req.context.frame === "number" ? req.context.frame : 0;
    if (harden === null) {
      throw new Error("[ExpressionWorker] harden not available");
    }
    const seededRandom = harden(createSeededRandom(frame));
    const globals = {
      ...safeMath,
      random: seededRandom,
      //                                                                  // security
      // Even though SES sandboxes these, we block them for defense-in-depth
      Function: void 0,
      eval: void 0,
      globalThis: void 0,
      window: void 0,
      document: void 0,
      setTimeout: void 0,
      setInterval: void 0,
      setImmediate: void 0,
      fetch: void 0,
      XMLHttpRequest: void 0,
      WebSocket: void 0,
      Worker: void 0,
      importScripts: void 0,
      require: void 0,
      process: void 0,
      Deno: void 0,
      Bun: void 0
    };
    for (const [key, value] of Object.entries(req.context)) {
      if (typeof value === "number" || typeof value === "string" || typeof value === "boolean") {
        globals[key] = value;
      }
    }
    if (Compartment === null || harden === null) {
      throw new Error("[ExpressionWorker] SES not properly initialized");
    }
    const compartment = new Compartment(harden(globals));
    const result = compartment.evaluate(req.code);
    if (typeof result !== "number" || !Number.isFinite(result)) {
      return { id: req.id, success: true, result: 0 };
    }
    return { id: req.id, success: true, result };
  } catch (e) {
    const errorMessage = e instanceof Error ? e.message : String(e);
    return {
      id: req.id,
      success: false,
      error: errorMessage
    };
  }
}
self.onmessage = async (e) => {
  const response = await evaluate(e.data);
  self.postMessage(response);
};
self.postMessage({ type: "ready" });
