/**
 * Motion Intent Resolver
 *
 * Analyzes user prompts and scene context using vision models
 * to generate structured motion intents.
 *
 * PRINCIPLE: This service runs at AUTHORING time only.
 * It is NEVER called during frame evaluation.
 *
 * SECURITY: API calls are routed through the backend proxy at:
 * - /lattice/api/vision/openai - OpenAI GPT-4V/GPT-4o
 * - /lattice/api/vision/anthropic - Claude Vision
 * - /lattice/api/status - Check which API keys are configured
 *
 * API keys are stored server-side in environment variables
 * (OPENAI_API_KEY, ANTHROPIC_API_KEY) and never exposed to the browser.
 */

import { createLogger } from "@/utils/logger";
import type {
  CameraMotionIntent,
  ControlPoint,
  MotionIntentResult,
  ParticleMotionIntent,
  SceneContext,
  SplineMotionIntent,
  VisionModelConfig,
  VisionModelId,
} from "./types";

const logger = createLogger("MotionIntentResolver");

// ============================================================================
// PROMPT TEMPLATES
// ============================================================================

const SYSTEM_PROMPT = `You are a motion graphics expert analyzing images for camera movements and animation paths.

Given an image, suggest motion paths and camera trajectories that would create compelling visual effects.

ALWAYS respond in valid JSON format with this structure:
{
  "description": "Brief description of suggested motion",
  "confidence": 0.0-1.0,
  "cameraIntents": [...],
  "splineIntents": [...],
  "particleIntents": [...],
  "layerIntents": [...]
}

For spline/path suggestions, provide control points as:
{
  "suggestedPoints": [
    { "id": "p1", "x": 100, "y": 200, "depth": 0.5, "handleIn": null, "handleOut": null, "type": "smooth" }
  ]
}

Consider:
- Depth information if available (closer = lower depth values)
- Subject positions and focal points
- Natural motion paths that follow scene geometry
- Parallax opportunities based on depth layers
`;

const PATH_SUGGESTION_PROMPT = `Analyze this image and suggest camera/motion paths.

Consider:
1. Main subjects and their positions
2. Depth layers (foreground, midground, background)
3. Natural movement paths that would be visually interesting
4. Points of interest to orbit around or move between

Suggest 2-3 different trajectory options with varying complexity.`;

// ============================================================================
// MOTION INTENT RESOLVER
// ============================================================================

export class MotionIntentResolver {
  private config: VisionModelConfig;
  private lastResult: MotionIntentResult | null = null;

  constructor(config?: Partial<VisionModelConfig>) {
    this.config = {
      modelId: config?.modelId ?? "rule-based",
      apiEndpoint: config?.apiEndpoint,
      apiKey: config?.apiKey,
      maxTokens: config?.maxTokens ?? 2048,
      temperature: config?.temperature ?? 0.7,
    };
  }

  /**
   * Resolve a user prompt into structured motion intents
   */
  async resolve(
    prompt: string,
    context: SceneContext,
    modelOverride?: VisionModelId,
  ): Promise<MotionIntentResult> {
    const modelId = modelOverride ?? this.config.modelId;

    logger.info(`Resolving motion intent with ${modelId}:`, prompt);

    try {
      let result: MotionIntentResult;

      switch (modelId) {
        case "rule-based":
          result = await this.resolveWithRules(prompt, context);
          break;
        case "gpt-4v":
        case "gpt-4o":
          result = await this.resolveWithOpenAI(prompt, context, modelId);
          break;
        case "claude-vision":
          result = await this.resolveWithClaude(prompt, context);
          break;
        case "qwen-vl":
        case "qwen2-vl":
        case "llava":
        case "local-vlm":
          result = await this.resolveWithLocalVLM(prompt, context, modelId);
          break;
        default:
          result = await this.resolveWithRules(prompt, context);
      }

      this.lastResult = result;
      return result;
    } catch (error) {
      logger.error("Motion intent resolution failed:", error);
      // Fall back to rule-based
      return this.resolveWithRules(prompt, context);
    }
  }

  /**
   * Suggest paths based on image analysis
   * This is the main entry point for "suggest trajectories across image"
   */
  async suggestPaths(
    context: SceneContext,
    modelOverride?: VisionModelId,
  ): Promise<MotionIntentResult> {
    return this.resolve(PATH_SUGGESTION_PROMPT, context, modelOverride);
  }

  // ============================================================================
  // RULE-BASED FALLBACK
  // ============================================================================

  private async resolveWithRules(
    prompt: string,
    context: SceneContext,
  ): Promise<MotionIntentResult> {
    const lowerPrompt = prompt.toLowerCase();
    const intents: MotionIntentResult = {
      description: "Rule-based motion suggestion",
      confidence: 0.6,
      cameraIntents: [],
      splineIntents: [],
      particleIntents: [],
      layerIntents: [],
    };

    // Analyze prompt for camera motion keywords
    const cameraIntents: CameraMotionIntent[] = [];

    if (
      lowerPrompt.includes("dolly") ||
      lowerPrompt.includes("push in") ||
      lowerPrompt.includes("pull out")
    ) {
      cameraIntents.push({
        type: "dolly",
        intensity: this.extractIntensity(lowerPrompt),
        axis: "z",
        durationFrames: context.frameCount,
        suggestedEasing: "easeInOut",
      });
    }

    if (lowerPrompt.includes("pan") || lowerPrompt.includes("sweep")) {
      cameraIntents.push({
        type: "pan",
        intensity: this.extractIntensity(lowerPrompt),
        axis: "y",
        durationFrames: context.frameCount,
        suggestedEasing: "easeInOut",
      });
    }

    if (lowerPrompt.includes("orbit") || lowerPrompt.includes("around")) {
      cameraIntents.push({
        type: "orbit",
        intensity: this.extractIntensity(lowerPrompt),
        durationFrames: context.frameCount,
        orbitCenter: { x: context.width / 2, y: context.height / 2, z: 0 },
        suggestedEasing: "linear",
      });
    }

    if (
      lowerPrompt.includes("drift") ||
      lowerPrompt.includes("float") ||
      lowerPrompt.includes("subtle")
    ) {
      cameraIntents.push({
        type: "drift",
        intensity: "very_subtle",
        durationFrames: context.frameCount,
        suggestedEasing: "easeInOut",
      });
    }

    if (lowerPrompt.includes("handheld") || lowerPrompt.includes("shake")) {
      cameraIntents.push({
        type: "handheld",
        intensity: this.extractIntensity(lowerPrompt),
        noiseAmount: lowerPrompt.includes("light") ? 0.3 : 0.6,
        durationFrames: context.frameCount,
      });
    }

    // Generate path suggestions based on depth map if available
    const splineIntents: SplineMotionIntent[] = [];

    if (
      context.depthMap ||
      lowerPrompt.includes("path") ||
      lowerPrompt.includes("trajectory")
    ) {
      // Generate a default path through the scene
      const defaultPath = this.generateDefaultPath(context);
      splineIntents.push({
        usage: "camera_path",
        smoothness: 0.8,
        complexity: defaultPath.length,
        worldSpace: true,
        suggestedPoints: defaultPath,
        closed: false,
      });

      // If depth map available, suggest depth-based path
      if (context.depthMap) {
        const depthPath = this.generateDepthBasedPath(context);
        splineIntents.push({
          usage: "camera_path",
          smoothness: 0.9,
          complexity: depthPath.length,
          worldSpace: true,
          suggestedPoints: depthPath,
          closed: false,
        });
      }
    }

    // Particle suggestions
    const particleIntents: ParticleMotionIntent[] = [];

    if (
      lowerPrompt.includes("particle") ||
      lowerPrompt.includes("dust") ||
      lowerPrompt.includes("snow")
    ) {
      particleIntents.push({
        behavior: lowerPrompt.includes("snow")
          ? "snow"
          : lowerPrompt.includes("dust")
            ? "dust"
            : "drift",
        intensity: 0.5,
        spread: 45,
        lifetime: 120,
      });
    }

    return {
      ...intents,
      cameraIntents,
      splineIntents,
      particleIntents,
    };
  }

  private extractIntensity(
    prompt: string,
  ): "very_subtle" | "subtle" | "medium" | "strong" | "dramatic" {
    if (prompt.includes("very subtle") || prompt.includes("barely"))
      return "very_subtle";
    if (
      prompt.includes("subtle") ||
      prompt.includes("gentle") ||
      prompt.includes("soft")
    )
      return "subtle";
    if (
      prompt.includes("dramatic") ||
      prompt.includes("intense") ||
      prompt.includes("strong")
    )
      return "dramatic";
    if (prompt.includes("bold") || prompt.includes("dynamic")) return "strong";
    return "medium";
  }

  private generateDefaultPath(context: SceneContext): ControlPoint[] {
    const { width, height } = context;
    const padding = Math.min(width, height) * 0.1;

    // Simple S-curve through the frame
    return [
      this.createControlPoint("p1", padding, height / 2, 0),
      this.createControlPoint("p2", width * 0.33, height * 0.3, 0.3),
      this.createControlPoint("p3", width * 0.66, height * 0.7, 0.6),
      this.createControlPoint("p4", width - padding, height / 2, 1),
    ];
  }

  private generateDepthBasedPath(context: SceneContext): ControlPoint[] {
    const { width, height, depthMap } = context;

    if (!depthMap) {
      return this.generateDefaultPath(context);
    }

    // Sample depth at key points and create path that moves through depth layers
    const points: ControlPoint[] = [];
    const numPoints = 5;

    for (let i = 0; i < numPoints; i++) {
      const t = i / (numPoints - 1);
      const x = width * (0.2 + t * 0.6); // 20% to 80% of width
      const y = height * (0.3 + Math.sin(t * Math.PI) * 0.4); // Arc pattern

      // Sample depth at this position
      const pixelIndex = Math.floor(y) * width + Math.floor(x);
      const depth = depthMap[pixelIndex] ?? 0.5;

      points.push(this.createControlPoint(`dp${i}`, x, y, depth));
    }

    return points;
  }

  private createControlPoint(
    id: string,
    x: number,
    y: number,
    depth: number,
  ): ControlPoint {
    return {
      id,
      x,
      y,
      depth,
      handleIn: null,
      handleOut: null,
      type: "smooth",
    };
  }

  // ============================================================================
  // OPENAI GPT-4V / GPT-4o
  // ============================================================================

  private async resolveWithOpenAI(
    prompt: string,
    context: SceneContext,
    model: "gpt-4v" | "gpt-4o",
  ): Promise<MotionIntentResult> {
    const imageBase64 = context.frameImage
      ? this.imageDataToBase64(context.frameImage)
      : null;

    const messages = [
      { role: "system", content: SYSTEM_PROMPT },
      {
        role: "user",
        content: imageBase64
          ? [
              { type: "text", text: prompt },
              {
                type: "image_url",
                image_url: { url: `data:image/png;base64,${imageBase64}` },
              },
            ]
          : prompt,
      },
    ];

    try {
      // Use backend proxy (API key handled server-side)
      const response = await fetch("/lattice/api/vision/openai", {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
        },
        body: JSON.stringify({
          model: model === "gpt-4o" ? "gpt-4o" : "gpt-4-vision-preview",
          messages,
          max_tokens: this.config.maxTokens,
          temperature: this.config.temperature,
        }),
      });

      const result = await response.json();

      if (result.status !== "success") {
        throw new Error(
          result.message || `OpenAI API error: ${response.status}`,
        );
      }

      const content = result.data.choices[0]?.message?.content;

      return this.parseAIResponse(content, prompt);
    } catch (error) {
      logger.error("OpenAI API call failed:", error);
      return this.resolveWithRules(prompt, context);
    }
  }

  // ============================================================================
  // CLAUDE VISION
  // ============================================================================

  private async resolveWithClaude(
    prompt: string,
    context: SceneContext,
  ): Promise<MotionIntentResult> {
    const imageBase64 = context.frameImage
      ? this.imageDataToBase64(context.frameImage)
      : null;

    const content = imageBase64
      ? [
          {
            type: "image",
            source: {
              type: "base64",
              media_type: "image/png",
              data: imageBase64,
            },
          },
          { type: "text", text: prompt },
        ]
      : [{ type: "text", text: prompt }];

    try {
      // Use backend proxy (API key handled server-side)
      const response = await fetch("/lattice/api/vision/anthropic", {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
        },
        body: JSON.stringify({
          model: "claude-3-5-sonnet-20241022",
          max_tokens: this.config.maxTokens,
          messages: [
            {
              role: "user",
              content:
                SYSTEM_PROMPT +
                "\n\nUser request: " +
                (typeof content === "string"
                  ? content
                  : JSON.stringify(content)),
            },
          ],
        }),
      });

      const result = await response.json();

      if (result.status !== "success") {
        throw new Error(
          result.message || `Anthropic API error: ${response.status}`,
        );
      }

      const responseContent = result.data.content[0]?.text;

      return this.parseAIResponse(responseContent, prompt);
    } catch (error) {
      logger.error("Anthropic API call failed:", error);
      return this.resolveWithRules(prompt, context);
    }
  }

  // ============================================================================
  // LOCAL VLM (via ComfyUI or local endpoint)
  // ============================================================================

  private async resolveWithLocalVLM(
    prompt: string,
    context: SceneContext,
    model: VisionModelId,
  ): Promise<MotionIntentResult> {
    // Use ComfyUI's lattice endpoint (relative path works when running in ComfyUI)
    const endpoint = this.config.apiEndpoint ?? "/lattice/vlm";

    const imageBase64 = context.frameImage
      ? this.imageDataToBase64(context.frameImage)
      : null;

    try {
      const response = await fetch(endpoint, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          model,
          prompt: `${SYSTEM_PROMPT}\n\nUser request: ${prompt}`,
          image: imageBase64,
          max_tokens: this.config.maxTokens,
        }),
      });

      if (!response.ok) {
        throw new Error(`Local VLM API error: ${response.status}`);
      }

      const data = await response.json();
      return this.parseAIResponse(
        data.response ?? data.text ?? data.content,
        prompt,
      );
    } catch (error) {
      logger.error("Local VLM API call failed:", error);
      return this.resolveWithRules(prompt, context);
    }
  }

  // ============================================================================
  // RESPONSE PARSING
  // ============================================================================

  private parseAIResponse(
    content: string,
    _originalPrompt: string,
  ): MotionIntentResult {
    try {
      // Try to extract JSON from response
      const jsonMatch = content.match(/\{[\s\S]*\}/);
      if (jsonMatch) {
        const parsed = JSON.parse(jsonMatch[0]);
        return {
          description: parsed.description ?? "AI-generated motion suggestion",
          confidence: parsed.confidence ?? 0.8,
          cameraIntents: parsed.cameraIntents ?? [],
          splineIntents: parsed.splineIntents ?? [],
          particleIntents: parsed.particleIntents ?? [],
          layerIntents: parsed.layerIntents ?? [],
          rawResponse: content,
        };
      }
    } catch (error) {
      logger.warn("Failed to parse AI response as JSON:", error);
    }

    // Fallback: create basic intent from description
    return {
      description: content.slice(0, 200),
      confidence: 0.5,
      cameraIntents: [],
      splineIntents: [],
      particleIntents: [],
      layerIntents: [],
      rawResponse: content,
    };
  }

  // ============================================================================
  // UTILITIES
  // ============================================================================

  private imageDataToBase64(imageData: ImageData): string {
    const canvas = document.createElement("canvas");
    canvas.width = imageData.width;
    canvas.height = imageData.height;
    const ctx = canvas.getContext("2d")!;
    ctx.putImageData(imageData, 0, 0);
    return canvas.toDataURL("image/png").split(",")[1];
  }

  /**
   * Get last resolution result
   */
  getLastResult(): MotionIntentResult | null {
    return this.lastResult;
  }

  /**
   * Update configuration
   */
  setConfig(config: Partial<VisionModelConfig>): void {
    this.config = { ...this.config, ...config };
  }
}

// Singleton instance
export const motionIntentResolver = new MotionIntentResolver();
