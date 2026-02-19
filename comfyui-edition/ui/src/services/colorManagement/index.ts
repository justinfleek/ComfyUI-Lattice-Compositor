/**
 * Color Management Module
 *
 * ICC profile parsing, color space conversions, and linear RGB workflow
 */

export {
  applyGammaRGB,
  // Constants
  COLOR_SPACES,
  ColorProfileService,
  type ColorSettings,
  // Types
  type ColorSpace,
  type ColorSpaceInfo,
  colorUtils,
  convertColorSpace,
  extractICCFromImage,
  gammaToLinear,
  getColorProfileService,
  type ICCProfile,
  initializeColorManagement,
  linearizeRGB,
  linearToGamma,
  linearToSRGB,
  parseICCProfile,
  type RGB,
  rgbToXYZ,
  // Functions
  sRGBToLinear,
  type ViewTransform,
  type XYZ,
  xyzToRGB,
} from "./ColorProfileService";
