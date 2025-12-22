/**
 * Color Management Module
 *
 * ICC profile parsing, color space conversions, and linear RGB workflow
 */

export {
  ColorProfileService,
  getColorProfileService,
  initializeColorManagement,
  colorUtils,
  // Types
  type ColorSpace,
  type ViewTransform,
  type ColorSpaceInfo,
  type ColorSettings,
  type ICCProfile,
  type RGB,
  type XYZ,
  // Constants
  COLOR_SPACES,
  // Functions
  sRGBToLinear,
  linearToSRGB,
  gammaToLinear,
  linearToGamma,
  linearizeRGB,
  applyGammaRGB,
  rgbToXYZ,
  xyzToRGB,
  convertColorSpace,
  parseICCProfile,
  extractICCFromImage,
} from './ColorProfileService';
