/**
 * Frontend Text Generation Service for Lattice Compositor
 *
 * Client-side service for COMPASS text generation integration.
 * Calls backend API for content generation.
 */

export interface GenerateTextContentRequest {
  content_type: string;
  topic: string;
  platform?: string;
  brand_voice?: {
    personality?: string[];
    key_phrases?: string[];
  };
  max_tokens?: number;
}

export interface GenerateTextContentResponse {
  success: boolean;
  text: string;
  word_count: number;
  character_count: number;
  metadata?: Record<string, unknown>;
}

export interface GenerateSocialMediaRequest {
  platform: string;
  topic: string;
  style?: string;
  include_hashtags?: boolean;
}

export interface GenerateAdCopyRequest {
  platform: string;
  product: string;
  target_audience?: string;
  ad_type?: string;
}

/**
 * Generate text content using COMPASS engine
 */
export async function generateTextContent(
  request: GenerateTextContentRequest
): Promise<GenerateTextContentResponse> {
  const response = await fetch("/lattice/api/content/generate", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(request),
  });

  if (!response.ok) {
    const error = await response.json().catch(() => ({ message: "Unknown error" }));
    throw new Error(`Text generation failed: ${error.message || "Unknown error"}`);
  }

  return response.json();
}

/**
 * Generate social media post
 */
export async function generateSocialMediaPost(
  request: GenerateSocialMediaRequest
): Promise<GenerateTextContentResponse> {
  const response = await fetch("/lattice/api/content/generate-social", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(request),
  });

  if (!response.ok) {
    const error = await response.json().catch(() => ({ message: "Unknown error" }));
    throw new Error(`Social media generation failed: ${error.message || "Unknown error"}`);
  }

  return response.json();
}

/**
 * Generate ad copy
 */
export async function generateAdCopy(
  request: GenerateAdCopyRequest
): Promise<GenerateTextContentResponse> {
  const response = await fetch("/lattice/api/content/generate-ad", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(request),
  });

  if (!response.ok) {
    const error = await response.json().catch(() => ({ message: "Unknown error" }));
    throw new Error(`Ad copy generation failed: ${error.message || "Unknown error"}`);
  }

  return response.json();
}
