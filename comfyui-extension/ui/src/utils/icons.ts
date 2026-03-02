/**
 * Icon Utilities
 *
 * Centralized icon mapping using Phosphor Icons.
 * All icons are from @phosphor-icons/vue
 */

// Icon name mappings for common UI elements
// These map semantic names to Phosphor icon component names
export const ICON_NAMES = {
  // Tools
  pen: "PhPen",
  pencil: "PhPencilSimple",
  hand: "PhHand",
  magnifyingGlass: "PhMagnifyingGlass",
  sparkle: "PhSparkle",
  star: "PhStar",
  starFilled: "PhStarFill",
  cursor: "PhCursor",

  // Files & Folders
  folder: "PhFolder",
  folderOpen: "PhFolderOpen",
  file: "PhFile",
  fileText: "PhFileText",
  fileImage: "PhFileImage",
  fileVideo: "PhFileVideo",
  fileAudio: "PhFileAudio",
  download: "PhDownloadSimple",
  upload: "PhUploadSimple",
  export: "PhExport",
  import: "PhDownload",

  // Media
  image: "PhImage",
  video: "PhVideoCamera",
  film: "PhFilmStrip",
  filmSlate: "PhFilmSlate",
  camera: "PhCamera",
  speaker: "PhSpeakerHigh",
  speakerMute: "PhSpeakerSlash",
  microphone: "PhMicrophone",
  music: "PhMusicNote",
  musicNotes: "PhMusicNotes",
  waveform: "PhWaveform",

  // Audio/Music specific
  piano: "PhPiano",
  guitar: "PhGuitar",
  drums: "PhDrum",
  vocals: "PhMicrophone",

  // Controls
  play: "PhPlay",
  pause: "PhPause",
  stop: "PhStop",
  skipBack: "PhSkipBack",
  skipForward: "PhSkipForward",
  rewind: "PhRewind",
  fastForward: "PhFastForward",
  loop: "PhRepeat",
  shuffle: "PhShuffle",

  // Visibility & Lock
  eye: "PhEye",
  eyeSlash: "PhEyeSlash",
  lock: "PhLock",
  lockOpen: "PhLockOpen",
  lockKey: "PhLockKey",

  // Actions
  check: "PhCheck",
  x: "PhX",
  plus: "PhPlus",
  minus: "PhMinus",
  trash: "PhTrash",
  copy: "PhCopy",
  paste: "PhClipboard",
  cut: "PhScissors",
  undo: "PhArrowCounterClockwise",
  redo: "PhArrowClockwise",
  refresh: "PhArrowsClockwise",

  // UI Elements
  gear: "PhGear",
  gearSix: "PhGearSix",
  sliders: "PhSliders",
  faders: "PhFaders",
  warning: "PhWarning",
  info: "PhInfo",
  question: "PhQuestion",
  link: "PhLink",
  linkBreak: "PhLinkBreak",
  chain: "PhChain",

  // Shapes & Graphics
  square: "PhSquare",
  circle: "PhCircle",
  triangle: "PhTriangle",
  polygon: "PhPolygon",
  rectangle: "PhRectangle",
  path: "PhPath",
  bezierCurve: "PhBezierCurve",
  vectorTwo: "PhVectorTwo",

  // 3D & Layers
  cube: "PhCube",
  cubeTransparent: "PhCubeTransparent",
  stack: "PhStack",
  stackSimple: "PhStackSimple",
  layers: "PhStackSimple",

  // Text
  textT: "PhTextT",
  textAa: "PhTextAa",
  textAlignLeft: "PhTextAlignLeft",

  // Navigation
  arrowUp: "PhArrowUp",
  arrowDown: "PhArrowDown",
  arrowLeft: "PhArrowLeft",
  arrowRight: "PhArrowRight",
  caretUp: "PhCaretUp",
  caretDown: "PhCaretDown",
  caretLeft: "PhCaretLeft",
  caretRight: "PhCaretRight",

  // Timeline specific
  keyframe: "PhDiamond",
  marker: "PhMapPin",
  ruler: "PhRuler",
  clock: "PhClock",
  timer: "PhTimer",

  // Effects & Magic
  magic: "PhMagicWand",
  sparkles: "PhSparkle",
  lightning: "PhLightning",
  fire: "PhFire",
  drop: "PhDrop",
  wind: "PhWind",
  cloud: "PhCloud",
  sun: "PhSun",
  sunDim: "PhSunDim",
  moon: "PhMoon",

  // Data & Charts
  chartLine: "PhChartLine",
  chartLineUp: "PhChartLineUp",
  chartBar: "PhChartBar",
  activity: "PhActivity",
  pulse: "PhPulse",

  // Misc
  robot: "PhRobot",
  package: "PhPackage",
  compass: "PhCompass",
  waves: "PhWaves",
  monitor: "PhMonitor",
  desktop: "PhDesktop",
  palette: "PhPalette",
  paintBrush: "PhPaintBrush",
  atom: "PhAtom",
  circuitry: "PhCircuitry",
  globe: "PhGlobeSimple",
  target: "PhTarget",
  crosshair: "PhCrosshair",

  // Light
  lightbulb: "PhLightbulb",
  lamp: "PhLamp",
  flashlight: "PhFlashlight",

  // Special
  eyedropper: "PhEyedropper",
  selection: "PhSelection",
  selectionAll: "PhSelectionAll",
  boundingBox: "PhBoundingBox",
  dice: "PhDice",

  // Collapse/Expand
  caretDoubleUp: "PhCaretDoubleUp",
  caretDoubleDown: "PhCaretDoubleDown",
  arrowsOut: "PhArrowsOut",
  arrowsIn: "PhArrowsIn",
  cornersOut: "PhCornersOut",
  cornersIn: "PhCornersIn",
} as const;

// Layer type to icon mapping
export const LAYER_TYPE_ICONS: Record<string, string> = {
  image: "PhImage",
  video: "PhFilmStrip",
  text: "PhTextT",
  solid: "PhSquare",
  shape: "PhPath",
  spline: "PhBezierCurve",
  null: "PhCrosshair",
  camera: "PhCamera",
  light: "PhLightbulb",
  particles: "PhSparkle",
  audio: "PhSpeakerHigh",
  precomp: "PhPackage",
  nestedComp: "PhPackage",
  adjustment: "PhSliders",
  model: "PhCube",
  pointcloud: "PhCloud",
  depth: "PhWaves",
  normal: "PhCompass",
  generated: "PhRobot",
  group: "PhFolder",
  control: "PhCrosshair",
  matte: "PhSelection",
  path: "PhPath",
  pose: "PhPerson",
};

// Asset type to icon mapping
export const ASSET_TYPE_ICONS: Record<string, string> = {
  composition: "PhFilmSlate",
  footage: "PhFilmStrip",
  image: "PhImage",
  audio: "PhSpeakerHigh",
  folder: "PhFolder",
  data: "PhChartBar",
  svg: "PhVectorTwo",
  environment: "PhSun",
  model: "PhCube",
};

// Stem type to icon mapping
export const STEM_TYPE_ICONS: Record<string, string> = {
  vocals: "PhMicrophone",
  drums: "PhDrum",
  bass: "PhWaveSquare",
  other: "PhMusicNote",
  guitar: "PhGuitar",
  piano: "PhPiano",
};

// Effect category icons
export const EFFECT_CATEGORY_ICONS: Record<string, string> = {
  blur: "PhCircleHalf",
  color: "PhPalette",
  distort: "PhWaveSine",
  generate: "PhSparkle",
  stylize: "PhPaintBrush",
  time: "PhClock",
  audio: "PhWaveform",
  "3d": "PhCube",
};
