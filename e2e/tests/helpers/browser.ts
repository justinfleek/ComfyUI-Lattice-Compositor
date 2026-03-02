/**
 * Browser test helpers for Puppeteer E2E tests
 * Provides browser lifecycle management, page utilities, and common operations
 */

import { type ChildProcess, execSync, spawn } from "child_process";
import puppeteer, { Browser, type LaunchOptions, Page } from "puppeteer";

const BASE_URL = "http://localhost:8080";
const HEADLESS = process.env.PUPPETEER_HEADLESS !== "false";
const SLOWMO = parseInt(process.env.PUPPETEER_SLOWMO || "0", 10);

let browser: Browser | null = null;
let server: ChildProcess | null = null;

/**
 * Find Chrome/Chromium executable on the system (NixOS compatible)
 */
function findChromePath(): string | undefined {
  const candidates = [
    process.env.PUPPETEER_EXECUTABLE_PATH,
    process.env.CHROME_PATH,
    "/home/justin/.nix-profile/bin/chromium",
    "/run/current-system/sw/bin/chromium",
    "/usr/bin/chromium",
    "/usr/bin/chromium-browser",
    "/usr/bin/google-chrome",
    "/usr/bin/google-chrome-stable",
  ];

  for (const path of candidates) {
    if (path) {
      try {
        execSync(`test -x "${path}"`, { stdio: "ignore" });
        return path;
      } catch {
        // Not executable, try next
      }
    }
  }

  try {
    const result = execSync(
      "which chromium 2>/dev/null || which chromium-browser 2>/dev/null || which google-chrome 2>/dev/null",
      { encoding: "utf-8" },
    );
    return result.trim() || undefined;
  } catch {
    return undefined;
  }
}

/**
 * Launch browser with WebGL support
 */
export async function launchBrowser(): Promise<Browser> {
  if (browser) return browser;

  const chromePath = findChromePath();

  const options: LaunchOptions = {
    headless: HEADLESS,
    slowMo: SLOWMO,
    executablePath: chromePath,
    args: [
      "--no-sandbox",
      "--disable-setuid-sandbox",
      "--disable-dev-shm-usage",
      "--disable-accelerated-2d-canvas",
      "--disable-gpu-sandbox",
      // WebGL support
      "--use-gl=swiftshader",
      "--enable-webgl",
      "--enable-webgl2",
      // Larger viewport for testing
      "--window-size=1920,1080",
      // Disable throttling for performance tests
      "--disable-backgrounding-occluded-windows",
      "--disable-renderer-backgrounding",
    ],
    defaultViewport: {
      width: 1920,
      height: 1080,
      deviceScaleFactor: 1,
    },
  };

  browser = await puppeteer.launch(options);
  return browser;
}

/**
 * Close browser instance
 */
export async function closeBrowser(): Promise<void> {
  if (browser) {
    await browser.close();
    browser = null;
  }
}

/**
 * Start the dev server
 */
export async function startServer(): Promise<void> {
  return new Promise((resolve, reject) => {
    server = spawn("python3", ["-m", "http.server", "8080"], {
      cwd: "../lattice-core/purescript/public",
      stdio: "pipe",
    });

    server.stderr?.on("data", (data) => {
      const msg = data.toString();
      if (msg.includes("Serving HTTP")) {
        resolve();
      }
    });

    server.on("error", reject);

    // Give it a moment to start
    setTimeout(resolve, 1000);
  });
}

/**
 * Stop the dev server
 */
export function stopServer(): void {
  if (server) {
    server.kill("SIGTERM");
    server = null;
  }
}

/**
 * Create a new page with standard configuration
 */
export async function createPage(): Promise<Page> {
  const b = await launchBrowser();
  const page = await b.newPage();

  // Enable JavaScript console logging in tests
  page.on("console", (msg) => {
    if (process.env.DEBUG) {
      console.log(`[Browser Console] ${msg.type()}: ${msg.text()}`);
    }
  });

  // Capture page errors
  page.on("pageerror", (error) => {
    console.error(`[Page Error] ${error.message}`);
  });

  return page;
}

/**
 * Navigate to a route and wait for app to initialize
 */
export async function navigateTo(
  page: Page,
  path: string = "/",
): Promise<void> {
  await page.goto(`${BASE_URL}${path}`, { waitUntil: "networkidle0" });
  // Wait for the app to initialize
  await page.waitForSelector("#lattice-root", { timeout: 10000 });
}

/**
 * Wait for WebGL canvas to be ready
 */
export async function waitForCanvas(page: Page): Promise<void> {
  await page.waitForSelector("#lattice-webgl", { timeout: 10000 });
  // Give WebGL context time to initialize
  await page.waitForFunction(
    () => {
      const canvas = document.querySelector(
        "#lattice-webgl",
      ) as HTMLCanvasElement | null;
      if (!canvas) return false;
      const gl = canvas.getContext("webgl2") || canvas.getContext("webgl");
      return gl !== null;
    },
    { timeout: 10000 },
  );
}

/**
 * Get canvas pixel data for comparison
 */
export async function getCanvasPixels(
  page: Page,
  canvasSelector: string = "#lattice-webgl",
): Promise<Buffer> {
  const dataUrl = await page.evaluate((selector) => {
    const canvas = document.querySelector(selector) as HTMLCanvasElement | null;
    if (!canvas) throw new Error(`Canvas not found: ${selector}`);
    return canvas.toDataURL("image/png");
  }, canvasSelector);

  // Convert data URL to buffer
  const base64 = dataUrl.replace(/^data:image\/png;base64,/, "");
  return Buffer.from(base64, "base64");
}

/**
 * Get WebGL context info for verification
 */
export async function getWebGLInfo(
  page: Page,
  canvasSelector: string = "#lattice-webgl",
): Promise<{
  vendor: string;
  renderer: string;
  version: string;
  shadingLanguageVersion: string;
}> {
  return page.evaluate((selector) => {
    const canvas = document.querySelector(selector) as HTMLCanvasElement | null;
    if (!canvas) throw new Error(`Canvas not found: ${selector}`);

    const gl = canvas.getContext("webgl2") || canvas.getContext("webgl");
    if (!gl) throw new Error("WebGL context not available");

    const debugInfo = gl.getExtension("WEBGL_debug_renderer_info");

    return {
      vendor: debugInfo
        ? gl.getParameter(debugInfo.UNMASKED_VENDOR_WEBGL)
        : gl.getParameter(gl.VENDOR),
      renderer: debugInfo
        ? gl.getParameter(debugInfo.UNMASKED_RENDERER_WEBGL)
        : gl.getParameter(gl.RENDERER),
      version: gl.getParameter(gl.VERSION),
      shadingLanguageVersion: gl.getParameter(gl.SHADING_LANGUAGE_VERSION),
    };
  }, canvasSelector);
}

/**
 * Measure frame render time
 */
export async function measureFrameTime(
  page: Page,
  frames: number = 60,
): Promise<{
  avgFrameTime: number;
  minFrameTime: number;
  maxFrameTime: number;
  fps: number;
}> {
  return page.evaluate((frameCount) => {
    return new Promise((resolve) => {
      const frameTimes: number[] = [];
      let lastTime = performance.now();
      let count = 0;

      function measureFrame() {
        const now = performance.now();
        frameTimes.push(now - lastTime);
        lastTime = now;
        count++;

        if (count < frameCount) {
          requestAnimationFrame(measureFrame);
        } else {
          const sorted = frameTimes.slice().sort((a, b) => a - b);
          const avg = frameTimes.reduce((a, b) => a + b, 0) / frameTimes.length;
          resolve({
            avgFrameTime: avg,
            minFrameTime: sorted[0],
            maxFrameTime: sorted[sorted.length - 1],
            fps: 1000 / avg,
          });
        }
      }

      requestAnimationFrame(measureFrame);
    });
  }, frames);
}

/**
 * Get memory usage metrics
 */
export async function getMemoryUsage(page: Page): Promise<{
  usedJSHeapSize: number;
  totalJSHeapSize: number;
  jsHeapSizeLimit: number;
}> {
  const metrics = await page.metrics();
  return {
    usedJSHeapSize: metrics.JSHeapUsedSize ?? 0,
    totalJSHeapSize: metrics.JSHeapTotalSize ?? 0,
    jsHeapSizeLimit: 0, // Not available via puppeteer metrics
  };
}

/**
 * Simulate keyboard shortcut
 */
export async function pressKeys(page: Page, ...keys: string[]): Promise<void> {
  // Hold all modifier keys first
  for (const key of keys.slice(0, -1)) {
    await page.keyboard.down(key);
  }
  // Press the final key
  await page.keyboard.press(keys[keys.length - 1]);
  // Release modifiers
  for (const key of keys.slice(0, -1).reverse()) {
    await page.keyboard.up(key);
  }
}

/**
 * Wait for a specific number of animation frames
 */
export async function waitFrames(page: Page, count: number): Promise<void> {
  await page.evaluate((frameCount) => {
    return new Promise<void>((resolve) => {
      let remaining = frameCount;
      function tick() {
        remaining--;
        if (remaining <= 0) {
          resolve();
        } else {
          requestAnimationFrame(tick);
        }
      }
      requestAnimationFrame(tick);
    });
  }, count);
}

/**
 * Take a screenshot for visual regression
 */
export async function takeScreenshot(
  page: Page,
  name: string,
): Promise<Buffer> {
  const screenshot = await page.screenshot({
    type: "png",
    fullPage: false,
  });
  return screenshot;
}

/**
 * Inject test data into the app
 */
export async function injectTestData(
  page: Page,
  data: Record<string, unknown>,
): Promise<void> {
  await page.evaluate((testData) => {
    (
      window as unknown as { __LATTICE_TEST_DATA__: Record<string, unknown> }
    ).__LATTICE_TEST_DATA__ = testData;
  }, data);
}

/**
 * Get app state for assertions
 */
export async function getAppState(
  page: Page,
): Promise<Record<string, unknown>> {
  return page.evaluate(() => {
    return (
      (window as unknown as { __LATTICE_APP_STATE__?: Record<string, unknown> })
        .__LATTICE_APP_STATE__ ?? {}
    );
  });
}

export { BASE_URL };
