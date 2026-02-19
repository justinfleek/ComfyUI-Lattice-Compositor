/**
 * LLM-Powered Depth Estimation Service
 *
 * Uses vision-capable LLMs (GPT-4o, Claude) to analyze decomposed image layers
 * and estimate their relative depths for automatic z-space placement.
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import { createLogger } from "@/utils/logger";

const logger = createLogger("DepthEstimation");

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Types
// ═══════════════════════════════════════════════════════════════════════════

export interface LayerDepthEstimate {
  layerIndex: number;
  layerName: string;
  estimatedDepth: number; // 0 (nearest) to 100 (farthest)
  confidence: number; // 0-1
  reasoning: string; // LLM explanation
  suggestedZPosition: number; // Compositor z-space units
  contentDescription: string; // What the layer contains
}

export interface DepthEstimationResult {
  layers: LayerDepthEstimate[];
  sceneDescription: string;
  depthRange: { near: number; far: number };
  success: boolean;
  error?: string;
}

export interface LayerAnalysisInput {
  index: number;
  label: string;
  imageDataUrl: string;
  alphaCoverage?: number;
  bounds?: { x: number; y: number; width: number; height: number };
  centroid?: { x: number; y: number };
}

export type LLMProvider = "openai" | "anthropic";

export interface DepthEstimationOptions {
  provider?: LLMProvider;
  zSpaceScale?: number; // Max z-space distance (default 500)
  includeReasoning?: boolean; // Include LLM reasoning (default true)
}

/**
 * Parsed layer structure from LLM depth estimation response
 */
interface ParsedDepthLayer {
  index?: number;
  depth?: number;
  content?: string;
  confidence?: number;
  reasoning?: string;
}

/**
 * Parsed depth estimation response structure
 */
interface ParsedDepthResponse {
  sceneDescription?: string;
  layers?: ParsedDepthLayer[];
}

// ═══════════════════════════════════════════════════════════════════════════
// System Prompts
// ═══════════════════════════════════════════════════════════════════════════

const DEPTH_ESTIMATION_SYSTEM_PROMPT = `You are an expert depth estimation system for VFX compositing. Your task is to analyze decomposed image layers and estimate their relative depths in a scene.

## Your Task
Given a set of image layers with transparency (extracted from a single photograph), estimate the relative depth of each layer from the camera's perspective.

## Depth Scale
- 0 = Closest to camera (foreground objects, items being held)
- 100 = Farthest from camera (sky, distant mountains, horizon)

## Guidelines

### Typical Depth Ranges
- Sky/clouds: 95-100
- Distant mountains/buildings: 80-95
- Far background trees/structures: 60-80
- Mid-ground elements (trees, cars, people at distance): 30-60
- Foreground elements (close people, objects): 10-30
- Very close objects (items in hand, camera-near): 0-10

### Analysis Cues
1. **Occlusion**: Objects in front occlude objects behind
2. **Size perspective**: Smaller = farther (for same-type objects)
3. **Position**: Lower in frame often = closer (ground plane perspective)
4. **Blur/detail**: Less detail often indicates distance
5. **Atmospheric perspective**: Distant objects appear hazier/bluer
6. **Semantic knowledge**: Sky is always far, floors are near, etc.

### Common Patterns
- Layer 1 (first) is typically the background/sky
- Last layer is typically the main foreground subject
- Middle layers represent intermediate depth planes

## Response Format
You MUST respond with valid JSON in this exact format:
{
  "sceneDescription": "Brief description of the overall scene",
  "layers": [
    {
      "index": 0,
      "depth": 95,
      "content": "blue sky with clouds",
      "confidence": 0.95,
      "reasoning": "Sky is always the farthest element in outdoor scenes"
    }
  ]
}

Be precise and consistent. Your estimates directly control 3D layer placement in a compositor.`;

// ═══════════════════════════════════════════════════════════════════════════
// LLM Depth Estimation Class
// ═══════════════════════════════════════════════════════════════════════════

export class LLMDepthEstimator {
  private baseUrl: string;

  constructor(serverAddress?: string) {
    // Use the AI proxy endpoint
    this.baseUrl = serverAddress ? `http://${serverAddress}` : "";
  }

  /**
   * Estimate depths for a set of decomposed layers
   */
  async estimateDepths(
    layers: LayerAnalysisInput[],
    options: DepthEstimationOptions = {},
  ): Promise<DepthEstimationResult> {
    const {
      provider = "openai",
      zSpaceScale = 500,
      includeReasoning = true,
    } = options;

    if (layers.length === 0) {
      throw new Error(`[DepthEstimation] No layers provided. At least one layer is required for depth estimation.`);
    }

    try {
      logger.info(
        `Estimating depths for ${layers.length} layers using ${provider}`,
      );

      // Build the prompt with layer information
      const userPrompt = this.buildUserPrompt(layers);

      // Call the AI API
      const response = await this.callVisionAPI(layers, userPrompt, provider);

      // Parse the response
      const parsed = this.parseResponse(response);

      // Map depths to z-space positions
      const result = this.mapToZSpace(
        parsed,
        layers,
        zSpaceScale,
        includeReasoning,
      );

      logger.info(
        `Depth estimation complete: ${result.layers.length} layers analyzed`,
      );
      return result;
    } catch (error) {
      const errorMsg = error instanceof Error ? error.message : "Unknown error";
      logger.error("Depth estimation failed:", error);
      throw new Error(`[DepthEstimation] Depth estimation failed: ${errorMsg}. Check AI provider availability and layer data.`);
    }
  }

  /**
   * Build the user prompt with layer metadata
   */
  private buildUserPrompt(layers: LayerAnalysisInput[]): string {
    const layerDescriptions = layers
      .map((layer, i) => {
        let desc = `Layer ${i + 1} "${layer.label}"`;

        if (layer.alphaCoverage !== undefined) {
          desc += `\n  - Alpha coverage: ${(layer.alphaCoverage * 100).toFixed(1)}%`;
        }
        if (layer.centroid) {
          desc += `\n  - Center position: (${layer.centroid.x.toFixed(0)}, ${layer.centroid.y.toFixed(0)})`;
        }
        if (layer.bounds) {
          desc += `\n  - Size: ${layer.bounds.width}x${layer.bounds.height} pixels`;
        }

        return desc;
      })
      .join("\n\n");

    return `Analyze these ${layers.length} image layers extracted from a single photograph.
Each layer has transparency (RGBA) and represents a different depth plane in the scene.

## Layer Information
${layerDescriptions}

Please estimate the relative depth (0-100) for each layer, where 0 is closest to camera and 100 is farthest.
Respond with JSON only.`;
  }

  /**
   * Call the vision-capable LLM API
   */
  private async callVisionAPI(
    layers: LayerAnalysisInput[],
    prompt: string,
    provider: LLMProvider,
  ): Promise<string> {
    // Build the request for the AI proxy endpoint
    const messages = [
      {
        role: "system",
        content: DEPTH_ESTIMATION_SYSTEM_PROMPT,
      },
      {
        role: "user",
        content: [
          { type: "text", text: prompt },
          // Include layer images for vision analysis
          ...layers.slice(0, 5).map((layer) => ({
            type: "image_url",
            image_url: {
              url: layer.imageDataUrl,
              detail: "low", // Use low detail to reduce tokens
            },
          })),
        ],
      },
    ];

    const requestBody = {
      model: provider === "openai" ? "gpt-4o" : "claude-sonnet",
      messages,
      max_tokens: 2048,
      temperature: 0.2, // Low temperature for consistent results
    };

    const response = await fetch(`${this.baseUrl}/lattice/api/ai/agent`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(requestBody),
    });

    if (!response.ok) {
      throw new Error(
        `API request failed: ${response.status} ${response.statusText}`,
      );
    }

    const result = await response.json();

    if (result.error) {
      throw new Error(result.error);
    }

    // Extract the text content from the response
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const choices = (result != null && typeof result === "object" && "choices" in result && result.choices != null && Array.isArray(result.choices) && result.choices.length > 0) ? result.choices : undefined;
    const firstChoice = choices != null ? choices[0] : undefined;
    const message = (firstChoice != null && typeof firstChoice === "object" && "message" in firstChoice && firstChoice.message != null && typeof firstChoice.message === "object") ? firstChoice.message : undefined;
    const messageContent = (message != null && typeof message === "object" && "content" in message && typeof message.content === "string") ? message.content : undefined;
    
    const contentArray = (result != null && typeof result === "object" && "content" in result && result.content != null && Array.isArray(result.content) && result.content.length > 0) ? result.content : undefined;
    const firstContent = contentArray != null ? contentArray[0] : undefined;
    const contentText = (firstContent != null && typeof firstContent === "object" && "text" in firstContent && typeof firstContent.text === "string") ? firstContent.text : undefined;
    
    const responseValue = (result != null && typeof result === "object" && "response" in result && typeof result.response === "string") ? result.response : undefined;
    
    const content = messageContent != null ? messageContent : (contentText != null ? contentText : responseValue);

    if (!content) {
      throw new Error("Empty response from LLM");
    }

    return content;
  }

  /**
   * Parse the LLM response JSON
   */
  private parseResponse(response: string): {
    sceneDescription: string;
    layers: Array<{
      index: number;
      depth: number;
      content: string;
      confidence: number;
      reasoning: string;
    }>;
  } {
    // Extract JSON from the response (may be wrapped in markdown code blocks)
    let jsonStr = response;

    // Try to extract from code blocks
    const jsonMatch = response.match(/```(?:json)?\s*([\s\S]*?)```/);
    if (jsonMatch) {
      jsonStr = jsonMatch[1].trim();
    }

    // Try to find JSON object directly
    const objectMatch = jsonStr.match(/\{[\s\S]*\}/);
    if (objectMatch) {
      jsonStr = objectMatch[0];
    }

    try {
      const parsed = JSON.parse(jsonStr) as ParsedDepthResponse;

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
      const layersRaw = parsed.layers;
      const layersArray = (layersRaw !== null && layersRaw !== undefined && Array.isArray(layersRaw)) ? layersRaw : [];
      return {
        sceneDescription: parsed.sceneDescription || "Scene analyzed",
        layers: layersArray.map((layer: ParsedDepthLayer) => ({
          // Type proof: index ∈ ℕ ∪ {undefined} → ℕ
          index: (() => {
            const indexValue = layer.index;
            return isFiniteNumber(indexValue) && Number.isInteger(indexValue) && indexValue >= 0 ? indexValue : 0;
          })(),
          // Type proof: depth ∈ ℝ ∪ {undefined} → ℝ (clamped to [0, 100])
          depth: Math.max(0, Math.min(100, (() => {
            const depthValue = layer.depth;
            return isFiniteNumber(depthValue) ? depthValue : 50;
          })())),
          content: layer.content || "Unknown",
          // Type proof: confidence ∈ ℝ ∪ {undefined} → ℝ (clamped to [0, 1])
          confidence: Math.max(0, Math.min(1, (() => {
            const confidenceValue = layer.confidence;
            return isFiniteNumber(confidenceValue) ? confidenceValue : 0.5;
          })())),
          reasoning: layer.reasoning || "",
        })),
      };
    } catch (parseError) {
      logger.error("Failed to parse LLM response:", parseError, response);
      throw new Error("Failed to parse depth estimation response");
    }
  }

  /**
   * Map depth estimates to z-space positions
   */
  private mapToZSpace(
    parsed: ReturnType<typeof this.parseResponse>,
    layers: LayerAnalysisInput[],
    zSpaceScale: number,
    includeReasoning: boolean,
  ): DepthEstimationResult {
    const layerEstimates: LayerDepthEstimate[] = layers.map((layer, i) => {
      // Find matching estimate from LLM
      const estimate = parsed.layers.find((e) => e.index === i) ||
        parsed.layers[i] || {
          depth: 50,
          content: layer.label,
          confidence: 0.5,
          reasoning: "No estimate",
        };

      // Convert depth (0-100) to z-space
      // Higher depth = farther = more negative z (or we can use positive z going away)
      const normalizedDepth = estimate.depth / 100;
      const suggestedZ = normalizedDepth * zSpaceScale;

      return {
        layerIndex: i,
        layerName: layer.label,
        estimatedDepth: estimate.depth,
        confidence: estimate.confidence,
        reasoning: includeReasoning ? estimate.reasoning : "",
        suggestedZPosition: suggestedZ,
        contentDescription: estimate.content,
      };
    });

    // Calculate depth range
    const depths = layerEstimates.map((e) => e.estimatedDepth);
    const depthRange = {
      near: Math.min(...depths),
      far: Math.max(...depths),
    };

    return {
      layers: layerEstimates,
      sceneDescription: parsed.sceneDescription,
      depthRange,
      success: true,
    };
  }

  /**
   * Generate fallback estimates when LLM fails
   */
  private generateFallbackEstimates(
    layers: LayerAnalysisInput[],
    zSpaceScale: number,
  ): LayerDepthEstimate[] {
    return layers.map((layer, i) => {
      // Simple heuristic: first layer is background, last is foreground
      const position = i / (layers.length - 1 || 1);
      const depth = Math.round((1 - position) * 100); // Invert so first layer is far

      return {
        layerIndex: i,
        layerName: layer.label,
        estimatedDepth: depth,
        confidence: 0.3, // Low confidence for fallback
        reasoning: "Fallback: estimated by layer order",
        suggestedZPosition: (depth / 100) * zSpaceScale,
        contentDescription: layer.label,
      };
    });
  }
}

// ═══════════════════════════════════════════════════════════════════════════
// Singleton Instance
// ═══════════════════════════════════════════════════════════════════════════

let defaultEstimator: LLMDepthEstimator | null = null;

export function getLLMDepthEstimator(
  serverAddress?: string,
): LLMDepthEstimator {
  if (!defaultEstimator) {
    defaultEstimator = new LLMDepthEstimator(serverAddress);
  }
  return defaultEstimator;
}

// ═══════════════════════════════════════════════════════════════════════════
// Utility Functions
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Quick depth estimation without LLM (uses heuristics only)
 */
export function estimateDepthsHeuristic(
  layers: LayerAnalysisInput[],
  zSpaceScale: number = 500,
): DepthEstimationResult {
  const estimates: LayerDepthEstimate[] = layers.map((layer, i) => {
    let depth: number;
    let confidence: number;
    let reasoning: string;

    // Heuristics based on layer properties
    const label = layer.label.toLowerCase();

    // Check for semantic keywords
    if (label.includes("sky") || label.includes("background")) {
      depth = 95;
      confidence = 0.8;
      reasoning = "Label indicates background/sky";
    } else if (label.includes("foreground") || label.includes("subject")) {
      depth = 15;
      confidence = 0.8;
      reasoning = "Label indicates foreground";
    } else if (label.includes("mid") || label.includes("middle")) {
      depth = 50;
      confidence = 0.6;
      reasoning = "Label indicates midground";
    } else if (layer.alphaCoverage !== undefined) {
      // Use alpha coverage as a heuristic
      // High coverage = likely background, low coverage = likely foreground detail
      if (layer.alphaCoverage > 0.8) {
        depth = 90;
        confidence = 0.5;
        reasoning = "High alpha coverage suggests background";
      } else if (layer.alphaCoverage < 0.2) {
        depth = 20;
        confidence = 0.5;
        reasoning = "Low alpha coverage suggests foreground detail";
      } else {
        depth = 50;
        confidence = 0.4;
        reasoning = "Medium alpha coverage";
      }
    } else {
      // Fall back to layer order
      const position = i / (layers.length - 1 || 1);
      depth = Math.round((1 - position) * 100);
      confidence = 0.3;
      reasoning = "Estimated by layer order";
    }

    return {
      layerIndex: i,
      layerName: layer.label,
      estimatedDepth: depth,
      confidence,
      reasoning,
      suggestedZPosition: (depth / 100) * zSpaceScale,
      contentDescription: layer.label,
    };
  });

  const depths = estimates.map((e) => e.estimatedDepth);

  return {
    layers: estimates,
    sceneDescription: "Scene analyzed using heuristics",
    depthRange: {
      near: Math.min(...depths),
      far: Math.max(...depths),
    },
    success: true,
  };
}
