/**
 * ColorProfileService - Color Management System
 *
 * Phase 6: Color Management Implementation
 *
 * Features:
 * - ICC profile parsing and embedding
 * - Color space conversions (sRGB, Wide-Gamut RGB, Display P3, ProPhoto RGB)
 * - Linear RGB workflow support
 * - Working color space setting
 * - View transforms for preview
 */

import { createLogger } from "@/utils/logger";
import { isFiniteNumber } from "@/utils/typeGuards";

const logger = createLogger("ColorProfile");

// ============================================================================
// TYPES
// ============================================================================

export type ColorSpace =
  | "sRGB"
  | "linear-sRGB"
  | "Wide-Gamut-RGB"
  | "Display-P3"
  | "ProPhoto-RGB"
  | "ACEScg"
  | "Rec709"
  | "Rec2020";

export type ViewTransform =
  | "sRGB"
  | "Display-P3"
  | "Rec709"
  | "ACES-sRGB"
  | "Filmic";

export interface ColorSpaceInfo {
  name: string;
  description: string;
  gamut: "narrow" | "wide" | "ultra-wide";
  gamma: number | "linear";
  whitePoint: [number, number]; // xy chromaticity
  primaries: {
    red: [number, number];
    green: [number, number];
    blue: [number, number];
  };
}

export interface ColorSettings {
  /** Working color space for compositing */
  workingColorSpace: ColorSpace;
  /** View transform for preview */
  viewTransform: ViewTransform;
  /** Export color space */
  exportColorSpace: ColorSpace | "source";
  /** Enable linear RGB compositing */
  linearCompositing: boolean;
  /** Display gamma correction */
  displayGamma: number;
}

export interface ICCProfile {
  /** Profile name */
  name: string;
  /** Color space */
  colorSpace: ColorSpace | "unknown";
  /** Profile class (input, display, output, etc.) */
  profileClass: string;
  /** Profile data as ArrayBuffer */
  data: ArrayBuffer;
  /** White point */
  whitePoint: [number, number, number];
  /** Primaries if available */
  primaries?: {
    red: [number, number, number];
    green: [number, number, number];
    blue: [number, number, number];
  };
}

export type RGB = [number, number, number];
export type XYZ = [number, number, number];

// ============================================================================
// COLOR SPACE DEFINITIONS
// ============================================================================

export const COLOR_SPACES: Record<ColorSpace, ColorSpaceInfo> = {
  sRGB: {
    name: "sRGB",
    description: "Standard RGB (web/most displays)",
    gamut: "narrow",
    gamma: 2.2,
    whitePoint: [0.3127, 0.329], // D65
    primaries: {
      red: [0.64, 0.33],
      green: [0.3, 0.6],
      blue: [0.15, 0.06],
    },
  },
  "linear-sRGB": {
    name: "Linear sRGB",
    description: "sRGB without gamma (for compositing)",
    gamut: "narrow",
    gamma: "linear",
    whitePoint: [0.3127, 0.329],
    primaries: {
      red: [0.64, 0.33],
      green: [0.3, 0.6],
      blue: [0.15, 0.06],
    },
  },
  "Wide-Gamut-RGB": {
    name: "Wide-Gamut RGB (1998)",
    description: "Wide gamut for print",
    gamut: "wide",
    gamma: 2.2,
    whitePoint: [0.3127, 0.329],
    primaries: {
      red: [0.64, 0.33],
      green: [0.21, 0.71],
      blue: [0.15, 0.06],
    },
  },
  "Display-P3": {
    name: "Display P3",
    description: "Apple/DCI wide gamut",
    gamut: "wide",
    gamma: 2.2,
    whitePoint: [0.3127, 0.329],
    primaries: {
      red: [0.68, 0.32],
      green: [0.265, 0.69],
      blue: [0.15, 0.06],
    },
  },
  "ProPhoto-RGB": {
    name: "ProPhoto RGB",
    description: "Ultra-wide gamut for photography",
    gamut: "ultra-wide",
    gamma: 1.8,
    whitePoint: [0.3457, 0.3585], // D50
    primaries: {
      red: [0.7347, 0.2653],
      green: [0.1596, 0.8404],
      blue: [0.0366, 0.0001],
    },
  },
  ACEScg: {
    name: "ACEScg",
    description: "ACES working space (linear, wide)",
    gamut: "ultra-wide",
    gamma: "linear",
    whitePoint: [0.32168, 0.33767], // ACES white
    primaries: {
      red: [0.713, 0.293],
      green: [0.165, 0.83],
      blue: [0.128, 0.044],
    },
  },
  Rec709: {
    name: "Rec. 709",
    description: "HDTV standard",
    gamut: "narrow",
    gamma: 2.4,
    whitePoint: [0.3127, 0.329],
    primaries: {
      red: [0.64, 0.33],
      green: [0.3, 0.6],
      blue: [0.15, 0.06],
    },
  },
  Rec2020: {
    name: "Rec. 2020",
    description: "UHD/HDR standard",
    gamut: "ultra-wide",
    gamma: 2.4,
    whitePoint: [0.3127, 0.329],
    primaries: {
      red: [0.708, 0.292],
      green: [0.17, 0.797],
      blue: [0.131, 0.046],
    },
  },
};

// ============================================================================
// TRANSFER FUNCTIONS (Gamma)
// ============================================================================

/**
 * sRGB transfer function (linearize)
 */
export function sRGBToLinear(value: number): number {
  if (value <= 0.04045) {
    return value / 12.92;
  }
  return ((value + 0.055) / 1.055) ** 2.4;
}

/**
 * sRGB inverse transfer function (apply gamma)
 */
export function linearToSRGB(value: number): number {
  if (value <= 0.0031308) {
    return value * 12.92;
  }
  return 1.055 * value ** (1 / 2.4) - 0.055;
}

/**
 * Simple gamma transfer function
 */
export function gammaToLinear(value: number, gamma: number): number {
  return Math.max(0, value) ** gamma;
}

/**
 * Simple gamma inverse transfer function
 */
export function linearToGamma(value: number, gamma: number): number {
  return Math.max(0, value) ** (1 / gamma);
}

/**
 * Linearize RGB based on color space
 */
export function linearizeRGB(rgb: RGB, colorSpace: ColorSpace): RGB {
  const info = COLOR_SPACES[colorSpace];

  if (info.gamma === "linear") {
    return rgb;
  }

  if (colorSpace === "sRGB" || colorSpace === "linear-sRGB") {
    return [sRGBToLinear(rgb[0]), sRGBToLinear(rgb[1]), sRGBToLinear(rgb[2])];
  }

  const gamma = info.gamma;
  return [
    gammaToLinear(rgb[0], gamma),
    gammaToLinear(rgb[1], gamma),
    gammaToLinear(rgb[2], gamma),
  ];
}

/**
 * Apply gamma to linear RGB
 */
export function applyGammaRGB(rgb: RGB, colorSpace: ColorSpace): RGB {
  const info = COLOR_SPACES[colorSpace];

  if (info.gamma === "linear") {
    return rgb;
  }

  if (colorSpace === "sRGB") {
    return [linearToSRGB(rgb[0]), linearToSRGB(rgb[1]), linearToSRGB(rgb[2])];
  }

  const gamma = info.gamma;
  return [
    linearToGamma(rgb[0], gamma),
    linearToGamma(rgb[1], gamma),
    linearToGamma(rgb[2], gamma),
  ];
}

// ============================================================================
// COLOR SPACE CONVERSION MATRICES
// ============================================================================

/**
 * 3x3 matrix for RGB to XYZ conversion
 */
type Matrix3x3 = [
  [number, number, number],
  [number, number, number],
  [number, number, number],
];

// sRGB to XYZ (D65)
const SRGB_TO_XYZ: Matrix3x3 = [
  [0.4124564, 0.3575761, 0.1804375],
  [0.2126729, 0.7151522, 0.072175],
  [0.0193339, 0.119192, 0.9503041],
];

// XYZ to sRGB (D65)
const XYZ_TO_SRGB: Matrix3x3 = [
  [3.2404542, -1.5371385, -0.4985314],
  [-0.969266, 1.8760108, 0.041556],
  [0.0556434, -0.2040259, 1.0572252],
];

// Display P3 to XYZ (D65)
const P3_TO_XYZ: Matrix3x3 = [
  [0.4865709, 0.2656677, 0.1982173],
  [0.2289746, 0.6917385, 0.0792869],
  [0.0, 0.0451134, 1.0439444],
];

// XYZ to Display P3 (D65)
const XYZ_TO_P3: Matrix3x3 = [
  [2.4934969, -0.9313836, -0.4027108],
  [-0.829489, 1.7626641, 0.0236247],
  [0.0358458, -0.0761724, 0.9568845],
];

// Wide-Gamut RGB to XYZ (D65)
const WIDEGAMUT_TO_XYZ: Matrix3x3 = [
  [0.5767309, 0.185554, 0.1881852],
  [0.2973769, 0.6273491, 0.0752741],
  [0.0270343, 0.0706872, 0.9911085],
];

// XYZ to Wide-Gamut RGB (D65)
const XYZ_TO_WIDEGAMUT: Matrix3x3 = [
  [2.041369, -0.5649464, -0.3446944],
  [-0.969266, 1.8760108, 0.041556],
  [0.0134474, -0.1183897, 1.0154096],
];

/**
 * Matrix-vector multiplication
 */
function matrixMultiply(
  m: Matrix3x3,
  v: [number, number, number],
): [number, number, number] {
  return [
    m[0][0] * v[0] + m[0][1] * v[1] + m[0][2] * v[2],
    m[1][0] * v[0] + m[1][1] * v[1] + m[1][2] * v[2],
    m[2][0] * v[0] + m[2][1] * v[1] + m[2][2] * v[2],
  ];
}

// ============================================================================
// COLOR SPACE CONVERSIONS
// ============================================================================

/**
 * Convert RGB to XYZ color space
 */
export function rgbToXYZ(rgb: RGB, colorSpace: ColorSpace): XYZ {
  // First linearize
  const linear = linearizeRGB(rgb, colorSpace);

  // Then apply matrix based on source color space
  switch (colorSpace) {
    case "sRGB":
    case "linear-sRGB":
    case "Rec709":
      return matrixMultiply(SRGB_TO_XYZ, linear);
    case "Display-P3":
      return matrixMultiply(P3_TO_XYZ, linear);
    case "Wide-Gamut-RGB":
      return matrixMultiply(WIDEGAMUT_TO_XYZ, linear);
    default:
      // Default to sRGB matrix
      return matrixMultiply(SRGB_TO_XYZ, linear);
  }
}

/**
 * Convert XYZ to RGB color space
 */
export function xyzToRGB(xyz: XYZ, colorSpace: ColorSpace): RGB {
  let linear: RGB;

  // Apply inverse matrix based on target color space
  switch (colorSpace) {
    case "sRGB":
    case "linear-sRGB":
    case "Rec709":
      linear = matrixMultiply(XYZ_TO_SRGB, xyz);
      break;
    case "Display-P3":
      linear = matrixMultiply(XYZ_TO_P3, xyz);
      break;
    case "Wide-Gamut-RGB":
      linear = matrixMultiply(XYZ_TO_WIDEGAMUT, xyz);
      break;
    default:
      linear = matrixMultiply(XYZ_TO_SRGB, xyz);
  }

  // Apply gamma
  return applyGammaRGB(linear, colorSpace);
}

/**
 * Convert RGB from one color space to another
 */
export function convertColorSpace(
  rgb: RGB,
  from: ColorSpace,
  to: ColorSpace,
): RGB {
  if (from === to) return rgb;

  // Handle linear conversions directly
  if (from === "linear-sRGB" && to === "sRGB") {
    return applyGammaRGB(rgb, "sRGB");
  }
  if (from === "sRGB" && to === "linear-sRGB") {
    return linearizeRGB(rgb, "sRGB");
  }

  // General conversion via XYZ
  const xyz = rgbToXYZ(rgb, from);
  return xyzToRGB(xyz, to);
}

// ============================================================================
// ICC PROFILE PARSING
// ============================================================================

/**
 * Parse basic ICC profile information
 * Note: This is a simplified parser for common profiles
 */
export function parseICCProfile(data: ArrayBuffer): ICCProfile {
  try {
    const view = new DataView(data);

    // Check signature "acsp"
    const signature = String.fromCharCode(
      view.getUint8(36),
      view.getUint8(37),
      view.getUint8(38),
      view.getUint8(39),
    );

    if (signature !== "acsp") {
      throw new Error(`[ColorProfileService] Invalid ICC profile signature: Expected "acsp", got "${signature}"`);
    }

    // Profile size
    const size = view.getUint32(0);
    if (size !== data.byteLength) {
      logger.warn("ICC profile size mismatch");
    }

    // Color space type (offset 16)
    const colorSpaceType = String.fromCharCode(
      view.getUint8(16),
      view.getUint8(17),
      view.getUint8(18),
      view.getUint8(19),
    ).trim();

    // Profile class (offset 12)
    const profileClass = String.fromCharCode(
      view.getUint8(12),
      view.getUint8(13),
      view.getUint8(14),
      view.getUint8(15),
    ).trim();

    // Parse description tag to get name
    // Tag table starts at offset 128
    const tagCount = view.getUint32(128);
    let name = "Unknown Profile";

    for (let i = 0; i < tagCount; i++) {
      const tagOffset = 132 + i * 12;
      const tagSig = String.fromCharCode(
        view.getUint8(tagOffset),
        view.getUint8(tagOffset + 1),
        view.getUint8(tagOffset + 2),
        view.getUint8(tagOffset + 3),
      );

      if (tagSig === "desc") {
        const dataOffset = view.getUint32(tagOffset + 4);
        const _dataSize = view.getUint32(tagOffset + 8);

        // Read description string (simplified)
        const descType = String.fromCharCode(
          view.getUint8(dataOffset),
          view.getUint8(dataOffset + 1),
          view.getUint8(dataOffset + 2),
          view.getUint8(dataOffset + 3),
        );

        if (descType === "desc") {
          const strLen = view.getUint32(dataOffset + 8);
          const strBytes = new Uint8Array(
            data,
            dataOffset + 12,
            Math.min(strLen - 1, 100),
          );
          name = new TextDecoder("ascii").decode(strBytes);
        }
        break;
      }
    }

    // Determine color space
    let colorSpace: ColorSpace | "unknown" = "unknown";
    if (colorSpaceType === "RGB") {
      // Try to identify specific RGB space from name
      const nameLower = name.toLowerCase();
      if (nameLower.includes("srgb")) {
        colorSpace = "sRGB";
      } else if (nameLower.includes("display p3") || nameLower.includes("p3")) {
        colorSpace = "Display-P3";
      } else if (
        nameLower.includes("wide-gamut rgb") ||
        nameLower.includes("widegamut")
      ) {
        colorSpace = "Wide-Gamut-RGB";
      } else if (nameLower.includes("prophoto")) {
        colorSpace = "ProPhoto-RGB";
      } else {
        colorSpace = "sRGB"; // Default assumption
      }
    }

    return {
      name,
      colorSpace,
      profileClass,
      data,
      whitePoint: [0.9505, 1.0, 1.089], // D65 default
    };
  } catch (error) {
    if (error instanceof Error && error.message.startsWith("[ColorProfileService]")) {
      throw error;
    }
    throw new Error(`[ColorProfileService] Failed to parse ICC profile: ${error instanceof Error ? error.message : String(error)}`);
  }
}

/**
 * Extract ICC profile from image file
 * 
 * System F/Omega proof: Explicit validation of image format and ICC profile existence
 * Type proof: imageData ∈ ArrayBuffer → ICCProfile (non-nullable)
 * Mathematical proof: Image format must be supported (PNG/JPEG) and ICC profile must exist
 * Pattern proof: Unsupported format or missing profile is an explicit failure condition, not a lazy null return
 */
export async function extractICCFromImage(
  imageData: ArrayBuffer,
): Promise<ICCProfile> {
  // System F/Omega proof: Explicit validation of image data existence
  // Type proof: imageData ∈ ArrayBuffer
  // Mathematical proof: Image data must exist and have sufficient bytes to check format
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
  if (!imageData || imageData.byteLength < 8) {
    const byteLength = (imageData !== null && imageData !== undefined && typeof imageData === "object" && "byteLength" in imageData && typeof imageData.byteLength === "number" && Number.isFinite(imageData.byteLength)) ? imageData.byteLength : 0;
    throw new Error(
      `[ColorProfileService] Cannot extract ICC profile: Image data is invalid or too small. ` +
      `Image data byteLength: ${byteLength}, minimum required: 8 bytes. ` +
      `Image data must contain at least 8 bytes to identify format (PNG signature: 8 bytes, JPEG signature: 2 bytes).`
    );
  }

  try {
    const view = new DataView(imageData);

    // Check for PNG
    if (view.getUint32(0) === 0x89504e47) {
      return extractICCFromPNG(imageData);
    }

    // Check for JPEG
    if (view.getUint16(0) === 0xffd8) {
      return extractICCFromJPEG(imageData);
    }

    // System F/Omega proof: Unsupported image format
    // Type proof: Format signature ∈ number → format ∈ {PNG, JPEG} | undefined
    // Mathematical proof: Image format must be PNG or JPEG to extract ICC profile
    // Pattern proof: Unsupported format is an explicit failure condition
    const firstBytes = Array.from(new Uint8Array(imageData.slice(0, 8)))
      .map((b) => `0x${b.toString(16).padStart(2, "0")}`)
      .join(" ");
    throw new Error(
      `[ColorProfileService] Cannot extract ICC profile: Unsupported image format. ` +
      `Image data first 8 bytes: ${firstBytes}. ` +
      `Supported formats: PNG (signature: 0x89 0x50 0x4e 0x47), JPEG (signature: 0xff 0xd8). ` +
      `Image must be PNG or JPEG format to extract ICC profile. Wrap in try/catch if "no profile" is an expected state.`
    );
  } catch (error) {
    // System F/Omega proof: Re-throw with context if it's already our error
    if (error instanceof Error && error.message.startsWith("[ColorProfileService]")) {
      throw error;
    }
    // System F/Omega proof: Wrap unexpected errors with context
    // Type proof: error ∈ Error | unknown
    // Mathematical proof: ICC profile extraction failed for unknown reason
    const errorMessage = error instanceof Error ? error.message : String(error);
    throw new Error(
      `[ColorProfileService] Cannot extract ICC profile: Extraction failed. ` +
      `Image data byteLength: ${imageData.byteLength}. ` +
      `Original error: ${errorMessage}. ` +
      `ICC profile extraction may have failed due to corrupted image data, unsupported format, or parsing error. ` +
      `Wrap in try/catch if "no profile" is an expected state.`
    );
  }
}

/**
 * Extract ICC profile from PNG
 */
function extractICCFromPNG(data: ArrayBuffer): ICCProfile {
  const view = new DataView(data);
  let offset = 8; // Skip PNG signature

  while (offset < data.byteLength) {
    const chunkLength = view.getUint32(offset);
    const chunkType = String.fromCharCode(
      view.getUint8(offset + 4),
      view.getUint8(offset + 5),
      view.getUint8(offset + 6),
      view.getUint8(offset + 7),
    );

    if (chunkType === "iCCP") {
      // ICC Profile chunk found
      // Skip to profile data (after null-terminated name and compression method)
      let nameEnd = offset + 8;
      while (
        view.getUint8(nameEnd) !== 0 &&
        nameEnd < offset + 8 + chunkLength
      ) {
        nameEnd++;
      }

      // Compression method byte
      const compressionMethod = view.getUint8(nameEnd + 1);

      if (compressionMethod === 0) {
        // Deflate compressed - TODO: implement decompression
        throw new Error(`[ColorProfileService] Cannot extract ICC profile from PNG: Compressed iCCP chunk found but decompression not implemented. Use uncompressed ICC profile or implement pako.inflate`);
      } else {
        // Uncompressed ICC profile (compressionMethod === 1 or other)
        const profileData = data.slice(nameEnd + 2, offset + 8 + chunkLength);
        return parseICCProfile(profileData);
      }
    }

    // Move to next chunk
    offset += 12 + chunkLength;
  }

  throw new Error(`[ColorProfileService] Cannot extract ICC profile from PNG: No iCCP chunk found`);
}

/**
 * Extract ICC profile from JPEG
 */
function extractICCFromJPEG(data: ArrayBuffer): ICCProfile {
  const view = new DataView(data);
  let offset = 2; // Skip SOI marker

  const profileChunks: ArrayBuffer[] = [];

  while (offset < data.byteLength) {
    const marker = view.getUint16(offset);

    if (marker === 0xffd9) break; // EOI

    if ((marker & 0xff00) !== 0xff00) {
      offset++;
      continue;
    }

    const segmentLength = view.getUint16(offset + 2);

    // APP2 marker with ICC_PROFILE
    if (marker === 0xffe2) {
      const iccSignature = String.fromCharCode(
        view.getUint8(offset + 4),
        view.getUint8(offset + 5),
        view.getUint8(offset + 6),
        view.getUint8(offset + 7),
        view.getUint8(offset + 8),
        view.getUint8(offset + 9),
        view.getUint8(offset + 10),
        view.getUint8(offset + 11),
      );

      if (iccSignature === "ICC_PROF") {
        // const chunkNum = view.getUint8(offset + 14);
        // const totalChunks = view.getUint8(offset + 15);
        const profileData = data.slice(offset + 18, offset + 2 + segmentLength);
        profileChunks.push(profileData);
      }
    }

    offset += 2 + segmentLength;
  }

  if (profileChunks.length > 0) {
    // Concatenate chunks
    const totalSize = profileChunks.reduce(
      (sum, chunk) => sum + chunk.byteLength,
      0,
    );
    const combined = new Uint8Array(totalSize);
    let pos = 0;
    for (const chunk of profileChunks) {
      combined.set(new Uint8Array(chunk), pos);
      pos += chunk.byteLength;
    }

    return parseICCProfile(combined.buffer);
  }

  throw new Error(`[ColorProfileService] Cannot extract ICC profile from JPEG: No APP2 ICC profile segments found`);
}

// ============================================================================
// COLOR PROFILE SERVICE CLASS
// ============================================================================

export class ColorProfileService {
  private settings: ColorSettings;
  private loadedProfiles: Map<string, ICCProfile> = new Map();

  constructor(settings?: Partial<ColorSettings>) {
    // Type proof: workingColorSpace ∈ ColorSpace | undefined → ColorSpace
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const settingsWorkingColorSpace = (settings != null && typeof settings === "object" && "workingColorSpace" in settings && typeof settings.workingColorSpace === "string") ? settings.workingColorSpace : undefined;
    const workingColorSpace = (settingsWorkingColorSpace != null &&
      (settingsWorkingColorSpace === "sRGB" ||
        settingsWorkingColorSpace === "linear-sRGB" ||
        settingsWorkingColorSpace === "Wide-Gamut-RGB" ||
        settingsWorkingColorSpace === "Display-P3" ||
        settingsWorkingColorSpace === "ProPhoto-RGB" ||
        settingsWorkingColorSpace === "ACEScg" ||
        settingsWorkingColorSpace === "Rec709" ||
        settingsWorkingColorSpace === "Rec2020"))
      ? settingsWorkingColorSpace
      : "sRGB";
    // Type proof: viewTransform ∈ ViewTransform | undefined → ViewTransform
    const settingsViewTransform = (settings != null && typeof settings === "object" && "viewTransform" in settings && typeof settings.viewTransform === "string") ? settings.viewTransform : undefined;
    const viewTransform = (settingsViewTransform != null &&
      (settingsViewTransform === "sRGB" ||
        settingsViewTransform === "Display-P3" ||
        settingsViewTransform === "Rec709" ||
        settingsViewTransform === "ACES-sRGB" ||
        settingsViewTransform === "Filmic"))
      ? settingsViewTransform
      : "sRGB";
    // Type proof: exportColorSpace ∈ ColorSpace | "source" | undefined → ColorSpace | "source"
    const settingsExportColorSpace = (settings != null && typeof settings === "object" && "exportColorSpace" in settings && typeof settings.exportColorSpace === "string") ? settings.exportColorSpace : undefined;
    const exportColorSpace = (settingsExportColorSpace != null &&
      (settingsExportColorSpace === "source" ||
        settingsExportColorSpace === "sRGB" ||
        settingsExportColorSpace === "linear-sRGB" ||
        settingsExportColorSpace === "Wide-Gamut-RGB" ||
        settingsExportColorSpace === "Display-P3" ||
        settingsExportColorSpace === "ProPhoto-RGB" ||
        settingsExportColorSpace === "ACEScg" ||
        settingsExportColorSpace === "Rec709" ||
        settingsExportColorSpace === "Rec2020"))
      ? settingsExportColorSpace
      : "sRGB";
    // Type proof: linearCompositing ∈ boolean | undefined → boolean
    const settingsLinearCompositing = (settings != null && typeof settings === "object" && "linearCompositing" in settings && typeof settings.linearCompositing === "boolean") ? settings.linearCompositing : undefined;
    const linearCompositing = (settingsLinearCompositing != null)
      ? settingsLinearCompositing
      : false;
    // Type proof: displayGamma ∈ number | undefined → number
    const settingsDisplayGamma = (settings != null && typeof settings === "object" && "displayGamma" in settings && typeof settings.displayGamma === "number") ? settings.displayGamma : undefined;
    const displayGamma = isFiniteNumber(settingsDisplayGamma) &&
      settingsDisplayGamma > 0
      ? settingsDisplayGamma
      : 2.2;

    this.settings = {
      workingColorSpace,
      viewTransform,
      exportColorSpace,
      linearCompositing,
      displayGamma,
    };
  }

  // ============================================================================
  // SETTINGS
  // ============================================================================

  getSettings(): ColorSettings {
    return { ...this.settings };
  }

  updateSettings(settings: Partial<ColorSettings>): void {
    Object.assign(this.settings, settings);
    logger.debug("Color settings updated:", this.settings);
  }

  setWorkingColorSpace(colorSpace: ColorSpace): void {
    this.settings.workingColorSpace = colorSpace;
  }

  setViewTransform(transform: ViewTransform): void {
    this.settings.viewTransform = transform;
  }

  setLinearCompositing(enabled: boolean): void {
    this.settings.linearCompositing = enabled;
  }

  // ============================================================================
  // PROFILE MANAGEMENT
  // ============================================================================

  async loadProfile(
    name: string,
    data: ArrayBuffer,
  ): Promise<ICCProfile> {
    const profile = parseICCProfile(data);
    this.loadedProfiles.set(name, profile);
    logger.debug(`Loaded ICC profile: ${profile.name}`);
    return profile;
  }

  getProfile(name: string): ICCProfile | undefined {
    return this.loadedProfiles.get(name);
  }

  async extractProfileFromImage(
    imageData: ArrayBuffer,
  ): Promise<ICCProfile> {
    return extractICCFromImage(imageData);
  }

  // ============================================================================
  // COLOR CONVERSION
  // ============================================================================

  /**
   * Convert RGB to working color space
   */
  toWorkingSpace(rgb: RGB, sourceSpace: ColorSpace): RGB {
    return convertColorSpace(rgb, sourceSpace, this.settings.workingColorSpace);
  }

  /**
   * Convert from working color space to export space
   */
  toExportSpace(rgb: RGB): RGB {
    const exportSpace =
      this.settings.exportColorSpace === "source"
        ? this.settings.workingColorSpace
        : this.settings.exportColorSpace;
    return convertColorSpace(rgb, this.settings.workingColorSpace, exportSpace);
  }

  /**
   * Apply view transform for preview
   */
  applyViewTransform(rgb: RGB): RGB {
    // For now, just convert to display color space
    // In production, you'd implement ACES view transforms
    switch (this.settings.viewTransform) {
      case "Display-P3":
        return convertColorSpace(
          rgb,
          this.settings.workingColorSpace,
          "Display-P3",
        );
      case "Rec709":
        return convertColorSpace(
          rgb,
          this.settings.workingColorSpace,
          "Rec709",
        );
      default:
        return convertColorSpace(rgb, this.settings.workingColorSpace, "sRGB");
    }
  }

  /**
   * Linearize for compositing
   */
  linearize(rgb: RGB): RGB {
    if (!this.settings.linearCompositing) return rgb;
    return linearizeRGB(rgb, this.settings.workingColorSpace);
  }

  /**
   * Apply gamma after compositing
   */
  delinearize(rgb: RGB): RGB {
    if (!this.settings.linearCompositing) return rgb;
    return applyGammaRGB(rgb, this.settings.workingColorSpace);
  }

  // ============================================================================
  // CANVAS OPERATIONS
  // ============================================================================

  /**
   * Convert ImageData to working color space
   */
  convertImageToWorkingSpace(
    imageData: ImageData,
    sourceSpace: ColorSpace,
  ): ImageData {
    if (sourceSpace === this.settings.workingColorSpace) return imageData;

    const data = imageData.data;
    const result = new Uint8ClampedArray(data.length);

    for (let i = 0; i < data.length; i += 4) {
      const rgb: RGB = [data[i] / 255, data[i + 1] / 255, data[i + 2] / 255];
      const converted = this.toWorkingSpace(rgb, sourceSpace);

      result[i] = Math.round(converted[0] * 255);
      result[i + 1] = Math.round(converted[1] * 255);
      result[i + 2] = Math.round(converted[2] * 255);
      result[i + 3] = data[i + 3]; // Preserve alpha
    }

    return new ImageData(result, imageData.width, imageData.height);
  }

  /**
   * Convert ImageData for export
   */
  convertImageForExport(imageData: ImageData): ImageData {
    if (this.settings.exportColorSpace === "source") return imageData;

    const data = imageData.data;
    const result = new Uint8ClampedArray(data.length);

    for (let i = 0; i < data.length; i += 4) {
      const rgb: RGB = [data[i] / 255, data[i + 1] / 255, data[i + 2] / 255];
      const converted = this.toExportSpace(rgb);

      result[i] = Math.round(converted[0] * 255);
      result[i + 1] = Math.round(converted[1] * 255);
      result[i + 2] = Math.round(converted[2] * 255);
      result[i + 3] = data[i + 3];
    }

    return new ImageData(result, imageData.width, imageData.height);
  }
}

// ============================================================================
// SINGLETON INSTANCE
// ============================================================================

let serviceInstance: ColorProfileService | null = null;

export function getColorProfileService(): ColorProfileService {
  if (!serviceInstance) {
    serviceInstance = new ColorProfileService();
  }
  return serviceInstance;
}

export function initializeColorManagement(
  settings?: Partial<ColorSettings>,
): ColorProfileService {
  serviceInstance = new ColorProfileService(settings);
  return serviceInstance;
}

// ============================================================================
// UTILITY EXPORTS
// ============================================================================

export const colorUtils = {
  sRGBToLinear,
  linearToSRGB,
  gammaToLinear,
  linearToGamma,
  linearizeRGB,
  applyGammaRGB,
  rgbToXYZ,
  xyzToRGB,
  convertColorSpace,
};
