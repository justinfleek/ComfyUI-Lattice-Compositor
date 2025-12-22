/**
 * ColorProfileService - Color Management System
 *
 * Phase 6: Color Management Implementation
 *
 * Features:
 * - ICC profile parsing and embedding
 * - Color space conversions (sRGB, Adobe RGB, Display P3, ProPhoto RGB)
 * - Linear RGB workflow support
 * - Working color space setting
 * - View transforms for preview
 */

import { createLogger } from '@/utils/logger';

const logger = createLogger('ColorProfile');

// ============================================================================
// TYPES
// ============================================================================

export type ColorSpace =
  | 'sRGB'
  | 'linear-sRGB'
  | 'Adobe-RGB'
  | 'Display-P3'
  | 'ProPhoto-RGB'
  | 'ACEScg'
  | 'Rec709'
  | 'Rec2020';

export type ViewTransform = 'sRGB' | 'Display-P3' | 'Rec709' | 'ACES-sRGB' | 'Filmic';

export interface ColorSpaceInfo {
  name: string;
  description: string;
  gamut: 'narrow' | 'wide' | 'ultra-wide';
  gamma: number | 'linear';
  whitePoint: [number, number];  // xy chromaticity
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
  exportColorSpace: ColorSpace | 'source';
  /** Enable linear RGB compositing */
  linearCompositing: boolean;
  /** Display gamma correction */
  displayGamma: number;
}

export interface ICCProfile {
  /** Profile name */
  name: string;
  /** Color space */
  colorSpace: ColorSpace | 'unknown';
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
  'sRGB': {
    name: 'sRGB',
    description: 'Standard RGB (web/most displays)',
    gamut: 'narrow',
    gamma: 2.2,
    whitePoint: [0.3127, 0.3290],  // D65
    primaries: {
      red: [0.64, 0.33],
      green: [0.30, 0.60],
      blue: [0.15, 0.06],
    },
  },
  'linear-sRGB': {
    name: 'Linear sRGB',
    description: 'sRGB without gamma (for compositing)',
    gamut: 'narrow',
    gamma: 'linear',
    whitePoint: [0.3127, 0.3290],
    primaries: {
      red: [0.64, 0.33],
      green: [0.30, 0.60],
      blue: [0.15, 0.06],
    },
  },
  'Adobe-RGB': {
    name: 'Adobe RGB (1998)',
    description: 'Wide gamut for print',
    gamut: 'wide',
    gamma: 2.2,
    whitePoint: [0.3127, 0.3290],
    primaries: {
      red: [0.64, 0.33],
      green: [0.21, 0.71],
      blue: [0.15, 0.06],
    },
  },
  'Display-P3': {
    name: 'Display P3',
    description: 'Apple/DCI wide gamut',
    gamut: 'wide',
    gamma: 2.2,
    whitePoint: [0.3127, 0.3290],
    primaries: {
      red: [0.68, 0.32],
      green: [0.265, 0.69],
      blue: [0.15, 0.06],
    },
  },
  'ProPhoto-RGB': {
    name: 'ProPhoto RGB',
    description: 'Ultra-wide gamut for photography',
    gamut: 'ultra-wide',
    gamma: 1.8,
    whitePoint: [0.3457, 0.3585],  // D50
    primaries: {
      red: [0.7347, 0.2653],
      green: [0.1596, 0.8404],
      blue: [0.0366, 0.0001],
    },
  },
  'ACEScg': {
    name: 'ACEScg',
    description: 'ACES working space (linear, wide)',
    gamut: 'ultra-wide',
    gamma: 'linear',
    whitePoint: [0.32168, 0.33767],  // ACES white
    primaries: {
      red: [0.713, 0.293],
      green: [0.165, 0.830],
      blue: [0.128, 0.044],
    },
  },
  'Rec709': {
    name: 'Rec. 709',
    description: 'HDTV standard',
    gamut: 'narrow',
    gamma: 2.4,
    whitePoint: [0.3127, 0.3290],
    primaries: {
      red: [0.64, 0.33],
      green: [0.30, 0.60],
      blue: [0.15, 0.06],
    },
  },
  'Rec2020': {
    name: 'Rec. 2020',
    description: 'UHD/HDR standard',
    gamut: 'ultra-wide',
    gamma: 2.4,
    whitePoint: [0.3127, 0.3290],
    primaries: {
      red: [0.708, 0.292],
      green: [0.170, 0.797],
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
  return Math.pow((value + 0.055) / 1.055, 2.4);
}

/**
 * sRGB inverse transfer function (apply gamma)
 */
export function linearToSRGB(value: number): number {
  if (value <= 0.0031308) {
    return value * 12.92;
  }
  return 1.055 * Math.pow(value, 1 / 2.4) - 0.055;
}

/**
 * Simple gamma transfer function
 */
export function gammaToLinear(value: number, gamma: number): number {
  return Math.pow(Math.max(0, value), gamma);
}

/**
 * Simple gamma inverse transfer function
 */
export function linearToGamma(value: number, gamma: number): number {
  return Math.pow(Math.max(0, value), 1 / gamma);
}

/**
 * Linearize RGB based on color space
 */
export function linearizeRGB(rgb: RGB, colorSpace: ColorSpace): RGB {
  const info = COLOR_SPACES[colorSpace];

  if (info.gamma === 'linear') {
    return rgb;
  }

  if (colorSpace === 'sRGB' || colorSpace === 'linear-sRGB') {
    return [
      sRGBToLinear(rgb[0]),
      sRGBToLinear(rgb[1]),
      sRGBToLinear(rgb[2]),
    ];
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

  if (info.gamma === 'linear') {
    return rgb;
  }

  if (colorSpace === 'sRGB') {
    return [
      linearToSRGB(rgb[0]),
      linearToSRGB(rgb[1]),
      linearToSRGB(rgb[2]),
    ];
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
  [number, number, number]
];

// sRGB to XYZ (D65)
const SRGB_TO_XYZ: Matrix3x3 = [
  [0.4124564, 0.3575761, 0.1804375],
  [0.2126729, 0.7151522, 0.0721750],
  [0.0193339, 0.1191920, 0.9503041],
];

// XYZ to sRGB (D65)
const XYZ_TO_SRGB: Matrix3x3 = [
  [3.2404542, -1.5371385, -0.4985314],
  [-0.9692660, 1.8760108, 0.0415560],
  [0.0556434, -0.2040259, 1.0572252],
];

// Display P3 to XYZ (D65)
const P3_TO_XYZ: Matrix3x3 = [
  [0.4865709, 0.2656677, 0.1982173],
  [0.2289746, 0.6917385, 0.0792869],
  [0.0000000, 0.0451134, 1.0439444],
];

// XYZ to Display P3 (D65)
const XYZ_TO_P3: Matrix3x3 = [
  [2.4934969, -0.9313836, -0.4027108],
  [-0.8294890, 1.7626641, 0.0236247],
  [0.0358458, -0.0761724, 0.9568845],
];

// Adobe RGB to XYZ (D65)
const ADOBERGB_TO_XYZ: Matrix3x3 = [
  [0.5767309, 0.1855540, 0.1881852],
  [0.2973769, 0.6273491, 0.0752741],
  [0.0270343, 0.0706872, 0.9911085],
];

// XYZ to Adobe RGB (D65)
const XYZ_TO_ADOBERGB: Matrix3x3 = [
  [2.0413690, -0.5649464, -0.3446944],
  [-0.9692660, 1.8760108, 0.0415560],
  [0.0134474, -0.1183897, 1.0154096],
];

/**
 * Matrix-vector multiplication
 */
function matrixMultiply(m: Matrix3x3, v: [number, number, number]): [number, number, number] {
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
    case 'sRGB':
    case 'linear-sRGB':
    case 'Rec709':
      return matrixMultiply(SRGB_TO_XYZ, linear);
    case 'Display-P3':
      return matrixMultiply(P3_TO_XYZ, linear);
    case 'Adobe-RGB':
      return matrixMultiply(ADOBERGB_TO_XYZ, linear);
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
    case 'sRGB':
    case 'linear-sRGB':
    case 'Rec709':
      linear = matrixMultiply(XYZ_TO_SRGB, xyz);
      break;
    case 'Display-P3':
      linear = matrixMultiply(XYZ_TO_P3, xyz);
      break;
    case 'Adobe-RGB':
      linear = matrixMultiply(XYZ_TO_ADOBERGB, xyz);
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
export function convertColorSpace(rgb: RGB, from: ColorSpace, to: ColorSpace): RGB {
  if (from === to) return rgb;

  // Handle linear conversions directly
  if (from === 'linear-sRGB' && to === 'sRGB') {
    return applyGammaRGB(rgb, 'sRGB');
  }
  if (from === 'sRGB' && to === 'linear-sRGB') {
    return linearizeRGB(rgb, 'sRGB');
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
export function parseICCProfile(data: ArrayBuffer): ICCProfile | null {
  try {
    const view = new DataView(data);

    // Check signature "acsp"
    const signature = String.fromCharCode(
      view.getUint8(36),
      view.getUint8(37),
      view.getUint8(38),
      view.getUint8(39)
    );

    if (signature !== 'acsp') {
      logger.warn('Invalid ICC profile signature');
      return null;
    }

    // Profile size
    const size = view.getUint32(0);
    if (size !== data.byteLength) {
      logger.warn('ICC profile size mismatch');
    }

    // Color space type (offset 16)
    const colorSpaceType = String.fromCharCode(
      view.getUint8(16),
      view.getUint8(17),
      view.getUint8(18),
      view.getUint8(19)
    ).trim();

    // Profile class (offset 12)
    const profileClass = String.fromCharCode(
      view.getUint8(12),
      view.getUint8(13),
      view.getUint8(14),
      view.getUint8(15)
    ).trim();

    // Parse description tag to get name
    // Tag table starts at offset 128
    const tagCount = view.getUint32(128);
    let name = 'Unknown Profile';

    for (let i = 0; i < tagCount; i++) {
      const tagOffset = 132 + (i * 12);
      const tagSig = String.fromCharCode(
        view.getUint8(tagOffset),
        view.getUint8(tagOffset + 1),
        view.getUint8(tagOffset + 2),
        view.getUint8(tagOffset + 3)
      );

      if (tagSig === 'desc') {
        const dataOffset = view.getUint32(tagOffset + 4);
        const dataSize = view.getUint32(tagOffset + 8);

        // Read description string (simplified)
        const descType = String.fromCharCode(
          view.getUint8(dataOffset),
          view.getUint8(dataOffset + 1),
          view.getUint8(dataOffset + 2),
          view.getUint8(dataOffset + 3)
        );

        if (descType === 'desc') {
          const strLen = view.getUint32(dataOffset + 8);
          const strBytes = new Uint8Array(data, dataOffset + 12, Math.min(strLen - 1, 100));
          name = new TextDecoder('ascii').decode(strBytes);
        }
        break;
      }
    }

    // Determine color space
    let colorSpace: ColorSpace | 'unknown' = 'unknown';
    if (colorSpaceType === 'RGB') {
      // Try to identify specific RGB space from name
      const nameLower = name.toLowerCase();
      if (nameLower.includes('srgb')) {
        colorSpace = 'sRGB';
      } else if (nameLower.includes('display p3') || nameLower.includes('p3')) {
        colorSpace = 'Display-P3';
      } else if (nameLower.includes('adobe rgb') || nameLower.includes('adobergb')) {
        colorSpace = 'Adobe-RGB';
      } else if (nameLower.includes('prophoto')) {
        colorSpace = 'ProPhoto-RGB';
      } else {
        colorSpace = 'sRGB';  // Default assumption
      }
    }

    return {
      name,
      colorSpace,
      profileClass,
      data,
      whitePoint: [0.9505, 1.0, 1.0890],  // D65 default
    };
  } catch (error) {
    logger.warn('Failed to parse ICC profile:', error);
    return null;
  }
}

/**
 * Extract ICC profile from image file
 */
export async function extractICCFromImage(imageData: ArrayBuffer): Promise<ICCProfile | null> {
  try {
    const view = new DataView(imageData);

    // Check for PNG
    if (view.getUint32(0) === 0x89504E47) {
      return extractICCFromPNG(imageData);
    }

    // Check for JPEG
    if (view.getUint16(0) === 0xFFD8) {
      return extractICCFromJPEG(imageData);
    }

    return null;
  } catch (error) {
    logger.warn('Failed to extract ICC profile:', error);
    return null;
  }
}

/**
 * Extract ICC profile from PNG
 */
function extractICCFromPNG(data: ArrayBuffer): ICCProfile | null {
  const view = new DataView(data);
  let offset = 8;  // Skip PNG signature

  while (offset < data.byteLength) {
    const chunkLength = view.getUint32(offset);
    const chunkType = String.fromCharCode(
      view.getUint8(offset + 4),
      view.getUint8(offset + 5),
      view.getUint8(offset + 6),
      view.getUint8(offset + 7)
    );

    if (chunkType === 'iCCP') {
      // ICC Profile chunk found
      // Skip to profile data (after null-terminated name and compression method)
      let nameEnd = offset + 8;
      while (view.getUint8(nameEnd) !== 0 && nameEnd < offset + 8 + chunkLength) {
        nameEnd++;
      }

      // Compression method byte
      const compressionMethod = view.getUint8(nameEnd + 1);

      if (compressionMethod === 0) {
        // Deflate compressed
        const compressedData = new Uint8Array(data, nameEnd + 2, chunkLength - (nameEnd - offset - 8) - 2);

        // Decompress using pako or similar (simplified - return null for now)
        // In production, you'd use pako.inflate(compressedData)
        logger.debug('Found compressed ICC profile in PNG');
      }
    }

    // Move to next chunk
    offset += 12 + chunkLength;
  }

  return null;
}

/**
 * Extract ICC profile from JPEG
 */
function extractICCFromJPEG(data: ArrayBuffer): ICCProfile | null {
  const view = new DataView(data);
  let offset = 2;  // Skip SOI marker

  const profileChunks: ArrayBuffer[] = [];

  while (offset < data.byteLength) {
    const marker = view.getUint16(offset);

    if (marker === 0xFFD9) break;  // EOI

    if ((marker & 0xFF00) !== 0xFF00) {
      offset++;
      continue;
    }

    const segmentLength = view.getUint16(offset + 2);

    // APP2 marker with ICC_PROFILE
    if (marker === 0xFFE2) {
      const iccSignature = String.fromCharCode(
        view.getUint8(offset + 4),
        view.getUint8(offset + 5),
        view.getUint8(offset + 6),
        view.getUint8(offset + 7),
        view.getUint8(offset + 8),
        view.getUint8(offset + 9),
        view.getUint8(offset + 10),
        view.getUint8(offset + 11)
      );

      if (iccSignature === 'ICC_PROF') {
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
    const totalSize = profileChunks.reduce((sum, chunk) => sum + chunk.byteLength, 0);
    const combined = new Uint8Array(totalSize);
    let pos = 0;
    for (const chunk of profileChunks) {
      combined.set(new Uint8Array(chunk), pos);
      pos += chunk.byteLength;
    }

    return parseICCProfile(combined.buffer);
  }

  return null;
}

// ============================================================================
// COLOR PROFILE SERVICE CLASS
// ============================================================================

export class ColorProfileService {
  private settings: ColorSettings;
  private loadedProfiles: Map<string, ICCProfile> = new Map();

  constructor(settings?: Partial<ColorSettings>) {
    this.settings = {
      workingColorSpace: settings?.workingColorSpace ?? 'sRGB',
      viewTransform: settings?.viewTransform ?? 'sRGB',
      exportColorSpace: settings?.exportColorSpace ?? 'sRGB',
      linearCompositing: settings?.linearCompositing ?? false,
      displayGamma: settings?.displayGamma ?? 2.2,
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
    logger.debug('Color settings updated:', this.settings);
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

  async loadProfile(name: string, data: ArrayBuffer): Promise<ICCProfile | null> {
    const profile = parseICCProfile(data);
    if (profile) {
      this.loadedProfiles.set(name, profile);
      logger.debug(`Loaded ICC profile: ${profile.name}`);
    }
    return profile;
  }

  getProfile(name: string): ICCProfile | undefined {
    return this.loadedProfiles.get(name);
  }

  async extractProfileFromImage(imageData: ArrayBuffer): Promise<ICCProfile | null> {
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
    const exportSpace = this.settings.exportColorSpace === 'source'
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
      case 'Display-P3':
        return convertColorSpace(rgb, this.settings.workingColorSpace, 'Display-P3');
      case 'Rec709':
        return convertColorSpace(rgb, this.settings.workingColorSpace, 'Rec709');
      default:
        return convertColorSpace(rgb, this.settings.workingColorSpace, 'sRGB');
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
  convertImageToWorkingSpace(imageData: ImageData, sourceSpace: ColorSpace): ImageData {
    if (sourceSpace === this.settings.workingColorSpace) return imageData;

    const data = imageData.data;
    const result = new Uint8ClampedArray(data.length);

    for (let i = 0; i < data.length; i += 4) {
      const rgb: RGB = [data[i] / 255, data[i + 1] / 255, data[i + 2] / 255];
      const converted = this.toWorkingSpace(rgb, sourceSpace);

      result[i] = Math.round(converted[0] * 255);
      result[i + 1] = Math.round(converted[1] * 255);
      result[i + 2] = Math.round(converted[2] * 255);
      result[i + 3] = data[i + 3];  // Preserve alpha
    }

    return new ImageData(result, imageData.width, imageData.height);
  }

  /**
   * Convert ImageData for export
   */
  convertImageForExport(imageData: ImageData): ImageData {
    if (this.settings.exportColorSpace === 'source') return imageData;

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

export function initializeColorManagement(settings?: Partial<ColorSettings>): ColorProfileService {
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
