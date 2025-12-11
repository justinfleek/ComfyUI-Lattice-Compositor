// Professional Control Components
export { default as ScrubableNumber } from './ScrubableNumber.vue';
export { default as SliderInput } from './SliderInput.vue';
export { default as ColorPicker } from './ColorPicker.vue';
export { default as AngleDial } from './AngleDial.vue';
export { default as PositionXY } from './PositionXY.vue';
export { default as CurveEditor } from './CurveEditor.vue';

// Easing presets for CurveEditor
export const EASING_PRESETS = {
  linear: { cp1x: 0, cp1y: 0, cp2x: 1, cp2y: 1 },
  easeIn: { cp1x: 0.42, cp1y: 0, cp2x: 1, cp2y: 1 },
  easeOut: { cp1x: 0, cp1y: 0, cp2x: 0.58, cp2y: 1 },
  easeInOut: { cp1x: 0.42, cp1y: 0, cp2x: 0.58, cp2y: 1 },
  easeInQuad: { cp1x: 0.55, cp1y: 0.085, cp2x: 0.68, cp2y: 0.53 },
  easeOutQuad: { cp1x: 0.25, cp1y: 0.46, cp2x: 0.45, cp2y: 0.94 },
  easeInOutQuad: { cp1x: 0.455, cp1y: 0.03, cp2x: 0.515, cp2y: 0.955 },
  easeInCubic: { cp1x: 0.55, cp1y: 0.055, cp2x: 0.675, cp2y: 0.19 },
  easeOutCubic: { cp1x: 0.215, cp1y: 0.61, cp2x: 0.355, cp2y: 1 },
  easeInOutCubic: { cp1x: 0.645, cp1y: 0.045, cp2x: 0.355, cp2y: 1 },
  easeInExpo: { cp1x: 0.95, cp1y: 0.05, cp2x: 0.795, cp2y: 0.035 },
  easeOutExpo: { cp1x: 0.19, cp1y: 1, cp2x: 0.22, cp2y: 1 },
  easeInOutExpo: { cp1x: 1, cp1y: 0, cp2x: 0, cp2y: 1 },
  easeInBack: { cp1x: 0.6, cp1y: -0.28, cp2x: 0.735, cp2y: 0.045 },
  easeOutBack: { cp1x: 0.175, cp1y: 0.885, cp2x: 0.32, cp2y: 1.275 },
  easeInOutBack: { cp1x: 0.68, cp1y: -0.55, cp2x: 0.265, cp2y: 1.55 },
};
