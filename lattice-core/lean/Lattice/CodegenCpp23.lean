/-
  Lattice.CodegenCpp23 - C++23 code generation
  
  Generates C++23 headers from Lean types with proofs.
  Uses modern C++23 features: concepts, std::expected, etc.
  
  Every emitted type has a corresponding Extractable instance
  with a proven roundtrip theorem.
-/

import Lattice.Codegen
import Lattice.Primitives
import Lattice.Enums
import Lattice.Events
import Lattice.Metrics
import Lattice.Triggers
import Lattice.Actions
import Lattice.Entities

namespace Lattice.CodegenCpp23

open Lattice.Codegen
open Lattice.Primitives
open Lattice.Enums
open Lattice.Events
open Lattice.Metrics
open Lattice.Triggers
open Lattice.Actions
open Lattice.Entities

/-! ## C++23 Type Emission -/

/-- C++23 type declaration for an Extractable type -/
class EmitCpp23 (α : Type _) where
  typeName : String
  typeDecl : String

/-! ## Layer 0 Primitives - C++23 Instances -/

instance : EmitCpp23 NonEmptyString where
  typeName := "NonEmptyString"
  typeDecl := """struct NonEmptyString {
    std::string value;
    
    // Constructor ensures non-empty invariant
    explicit NonEmptyString(std::string_view s) 
        : value(s) {
        if (value.empty()) {
            throw std::invalid_argument("NonEmptyString cannot be empty");
        }
    }
    
    // Accessor
    [[nodiscard]] const std::string& get() const noexcept { return value; }
    
    // Comparison operators
    bool operator==(const NonEmptyString& other) const noexcept {
        return value == other.value;
    }
};"""

instance : EmitCpp23 PositiveInt where
  typeName := "PositiveInt"
  typeDecl := """struct PositiveInt {
    std::uint64_t value;
    
    // Constructor ensures positive invariant
    explicit PositiveInt(std::uint64_t n) 
        : value(n) {
        if (value == 0) {
            throw std::invalid_argument("PositiveInt must be > 0");
        }
    }
    
    // Accessor
    [[nodiscard]] std::uint64_t get() const noexcept { return value; }
    
    // Comparison operators
    bool operator==(const PositiveInt& other) const noexcept {
        return value == other.value;
    }
};"""

instance : EmitCpp23 PositiveFloat where
  typeName := "PositiveFloat"
  typeDecl := """struct PositiveFloat {
    float value;
    
    // Constructor ensures positive and finite invariant
    explicit PositiveFloat(float f) 
        : value(f) {
        if (!std::isfinite(value) || value <= 0.0f) {
            throw std::invalid_argument("PositiveFloat must be finite and > 0");
        }
    }
    
    // Accessor
    [[nodiscard]] float get() const noexcept { return value; }
    
    // Comparison operators
    bool operator==(const PositiveFloat& other) const noexcept {
        return value == other.value;
    }
};"""

instance : EmitCpp23 NonNegativeFloat where
  typeName := "NonNegativeFloat"
  typeDecl := """struct NonNegativeFloat {
    float value;
    
    // Constructor ensures non-negative and finite invariant
    explicit NonNegativeFloat(float f) 
        : value(f) {
        if (!std::isfinite(value) || value < 0.0f) {
            throw std::invalid_argument("NonNegativeFloat must be finite and >= 0");
        }
    }
    
    // Accessor
    [[nodiscard]] float get() const noexcept { return value; }
    
    // Comparison operators
    bool operator==(const NonNegativeFloat& other) const noexcept {
        return value == other.value;
    }
};"""

instance : EmitCpp23 Percentage where
  typeName := "Percentage"
  typeDecl := """struct Percentage {
    float value;
    
    // Constructor ensures 0 <= value <= 100 and finite invariant
    explicit Percentage(float f) 
        : value(f) {
        if (!std::isfinite(value) || value < 0.0f || value > 100.0f) {
            throw std::invalid_argument("Percentage must be finite and in [0, 100]");
        }
    }
    
    // Accessor
    [[nodiscard]] float get() const noexcept { return value; }
    
    // Comparison operators
    bool operator==(const Percentage& other) const noexcept {
        return value == other.value;
    }
};"""

instance : EmitCpp23 NormalizedValue where
  typeName := "NormalizedValue"
  typeDecl := """struct NormalizedValue {
    float value;
    
    // Constructor ensures 0 <= value <= 1 and finite invariant
    explicit NormalizedValue(float f) 
        : value(f) {
        if (!std::isfinite(value) || value < 0.0f || value > 1.0f) {
            throw std::invalid_argument("NormalizedValue must be finite and in [0, 1]");
        }
    }
    
    // Accessor
    [[nodiscard]] float get() const noexcept { return value; }
    
    // Comparison operators
    bool operator==(const NormalizedValue& other) const noexcept {
        return value == other.value;
    }
};"""

instance : EmitCpp23 FrameNumber where
  typeName := "FrameNumber"
  typeDecl := """struct FrameNumber {
    std::uint64_t value;
    
    // Constructor
    explicit FrameNumber(std::uint64_t n) noexcept : value(n) {}
    
    // Accessor
    [[nodiscard]] std::uint64_t get() const noexcept { return value; }
    
    // Comparison operators
    bool operator==(const FrameNumber& other) const noexcept {
        return value == other.value;
    }
    
    bool operator<(const FrameNumber& other) const noexcept {
        return value < other.value;
    }
};"""

instance : EmitCpp23 Vec2 where
  typeName := "Vec2"
  typeDecl := """struct Vec2 {
    float x;
    float y;
    
    // Constructor ensures all components are finite
    Vec2(float x_val, float y_val) 
        : x(x_val), y(y_val) {
        if (!std::isfinite(x) || !std::isfinite(y)) {
            throw std::invalid_argument("Vec2 components must be finite");
        }
    }
    
    // Comparison operators
    bool operator==(const Vec2& other) const noexcept {
        return x == other.x && y == other.y;
    }
};"""

instance : EmitCpp23 Vec3 where
  typeName := "Vec3"
  typeDecl := """struct Vec3 {
    float x;
    float y;
    float z;
    
    // Constructor ensures all components are finite
    Vec3(float x_val, float y_val, float z_val) 
        : x(x_val), y(y_val), z(z_val) {
        if (!std::isfinite(x) || !std::isfinite(y) || !std::isfinite(z)) {
            throw std::invalid_argument("Vec3 components must be finite");
        }
    }
    
    // Comparison operators
    bool operator==(const Vec3& other) const noexcept {
        return x == other.x && y == other.y && z == other.z;
    }
};"""

instance : EmitCpp23 Vec4 where
  typeName := "Vec4"
  typeDecl := """struct Vec4 {
    float x;
    float y;
    float z;
    float w;
    
    // Constructor ensures all components are finite
    Vec4(float x_val, float y_val, float z_val, float w_val) 
        : x(x_val), y(y_val), z(z_val), w(w_val) {
        if (!std::isfinite(x) || !std::isfinite(y) || !std::isfinite(z) || !std::isfinite(w)) {
            throw std::invalid_argument("Vec4 components must be finite");
        }
    }
    
    // Comparison operators
    bool operator==(const Vec4& other) const noexcept {
        return x == other.x && y == other.y && z == other.z && w == other.w;
    }
};"""

instance : EmitCpp23 Matrix3x3 where
  typeName := "Matrix3x3"
  typeDecl := """struct Matrix3x3 {
    float m00, m01, m02;
    float m10, m11, m12;
    float m20, m21, m22;
    
    // Constructor ensures all entries are finite
    Matrix3x3(float m00_val, float m01_val, float m02_val,
             float m10_val, float m11_val, float m12_val,
             float m20_val, float m21_val, float m22_val)
        : m00(m00_val), m01(m01_val), m02(m02_val),
          m10(m10_val), m11(m11_val), m12(m12_val),
          m20(m20_val), m21(m21_val), m22(m22_val) {
        if (!std::isfinite(m00) || !std::isfinite(m01) || !std::isfinite(m02) ||
            !std::isfinite(m10) || !std::isfinite(m11) || !std::isfinite(m12) ||
            !std::isfinite(m20) || !std::isfinite(m21) || !std::isfinite(m22)) {
            throw std::invalid_argument("Matrix3x3 entries must be finite");
        }
    }
    
    // Comparison operators
    bool operator==(const Matrix3x3& other) const noexcept {
        return m00 == other.m00 && m01 == other.m01 && m02 == other.m02 &&
               m10 == other.m10 && m11 == other.m11 && m12 == other.m12 &&
               m20 == other.m20 && m21 == other.m21 && m22 == other.m22;
    }
};"""

instance : EmitCpp23 Matrix4x4 where
  typeName := "Matrix4x4"
  typeDecl := """struct Matrix4x4 {
    float m00, m01, m02, m03;
    float m10, m11, m12, m13;
    float m20, m21, m22, m23;
    float m30, m31, m32, m33;
    
    // Constructor ensures all entries are finite
    Matrix4x4(float m00_val, float m01_val, float m02_val, float m03_val,
             float m10_val, float m11_val, float m12_val, float m13_val,
             float m20_val, float m21_val, float m22_val, float m23_val,
             float m30_val, float m31_val, float m32_val, float m33_val)
        : m00(m00_val), m01(m01_val), m02(m02_val), m03(m03_val),
          m10(m10_val), m11(m11_val), m12(m12_val), m13(m13_val),
          m20(m20_val), m21(m21_val), m22(m22_val), m23(m23_val),
          m30(m30_val), m31(m31_val), m32(m32_val), m33(m33_val) {
        if (!std::isfinite(m00) || !std::isfinite(m01) || !std::isfinite(m02) || !std::isfinite(m03) ||
            !std::isfinite(m10) || !std::isfinite(m11) || !std::isfinite(m12) || !std::isfinite(m13) ||
            !std::isfinite(m20) || !std::isfinite(m21) || !std::isfinite(m22) || !std::isfinite(m23) ||
            !std::isfinite(m30) || !std::isfinite(m31) || !std::isfinite(m32) || !std::isfinite(m33)) {
            throw std::invalid_argument("Matrix4x4 entries must be finite");
        }
    }
    
    // Comparison operators
    bool operator==(const Matrix4x4& other) const noexcept {
        return m00 == other.m00 && m01 == other.m01 && m02 == other.m02 && m03 == other.m03 &&
               m10 == other.m10 && m11 == other.m11 && m12 == other.m12 && m13 == other.m13 &&
               m20 == other.m20 && m21 == other.m21 && m22 == other.m22 && m23 == other.m23 &&
               m30 == other.m30 && m31 == other.m31 && m32 == other.m32 && m33 == other.m33;
    }
};"""

/-! ## Layer 1 Enums - C++23 Instances -/

instance : EmitCpp23 LayerType where
  typeName := "LayerType"
  typeDecl := """enum class LayerType {
    shape,
    text,
    image,
    video,
    audio,
    group,
    camera,
    light,
    particle,
    effect
};"""

instance : EmitCpp23 BlendMode where
  typeName := "BlendMode"
  typeDecl := """enum class BlendMode {
    normal,
    multiply,
    screen,
    overlay,
    softLight,
    hardLight,
    colorDodge,
    colorBurn,
    darken,
    lighten,
    difference,
    exclusion,
    hue,
    saturation,
    color,
    luminosity,
    add,
    subtract,
    divide
};"""

instance : EmitCpp23 MaskMode where
  typeName := "MaskMode"
  typeDecl := """enum class MaskMode {
    add,
    subtract,
    intersect,
    difference
};"""

instance : EmitCpp23 LayerStatus where
  typeName := "LayerStatus"
  typeDecl := """enum class LayerStatus {
    active,
    hidden,
    locked,
    disabled
};"""

instance : EmitCpp23 InterpolationType where
  typeName := "InterpolationType"
  typeDecl := """enum class InterpolationType {
    linear,
    bezier,
    hold,
    easeIn,
    easeOut,
    easeInOut,
    custom
};"""

instance : EmitCpp23 EasingType where
  typeName := "EasingType"
  typeDecl := """enum class EasingType {
    linear,
    easeInQuad,
    easeOutQuad,
    easeInOutQuad,
    easeInCubic,
    easeOutCubic,
    easeInOutCubic,
    easeInQuart,
    easeOutQuart,
    easeInOutQuart,
    easeInQuint,
    easeOutQuint,
    easeInOutQuint,
    easeInSine,
    easeOutSine,
    easeInOutSine,
    easeInExpo,
    easeOutExpo,
    easeInOutExpo,
    easeInCirc,
    easeOutCirc,
    easeInOutCirc,
    easeInElastic,
    easeOutElastic,
    easeInOutElastic,
    easeInBack,
    easeOutBack,
    easeInOutBack,
    easeInBounce,
    easeOutBounce,
    easeInOutBounce
};"""

instance : EmitCpp23 KeyframeType where
  typeName := "KeyframeType"
  typeDecl := """enum class KeyframeType {
    linear,
    bezier,
    hold,
    auto
};"""

instance : EmitCpp23 EffectCategory where
  typeName := "EffectCategory"
  typeDecl := """enum class EffectCategory {
    blurSharpen,
    colorCorrection,
    distort,
    generate,
    keying,
    matte,
    noiseGrain,
    perspective,
    stylize,
    time,
    transition,
    utility
};"""

instance : EmitCpp23 EffectStatus where
  typeName := "EffectStatus"
  typeDecl := """enum class EffectStatus {
    active,
    disabled,
    bypassed
};"""

instance : EmitCpp23 ColorSpace where
  typeName := "ColorSpace"
  typeDecl := """enum class ColorSpace {
    sRGB,
    linearSRGB,
    wideGamutRGB,
    displayP3,
    proPhotoRGB,
    acescg,
    rec709,
    rec2020
};"""

instance : EmitCpp23 ColorFormat where
  typeName := "ColorFormat"
  typeDecl := """enum class ColorFormat {
    rgb8,
    rgb16,
    rgba8,
    rgba16,
    hsl,
    hsv,
    lab,
    xyz
};"""

instance : EmitCpp23 TransferFunction where
  typeName := "TransferFunction"
  typeDecl := """enum class TransferFunction {
    linear,
    sRGB,
    gamma,
    log,
    pq,
    hlg
};"""

instance : EmitCpp23 ExportFormat where
  typeName := "ExportFormat"
  typeDecl := """enum class ExportFormat {
    mp4,
    mov,
    avi,
    webm,
    png,
    jpg,
    exr,
    h264,
    h265,
    prores
};"""

instance : EmitCpp23 ExportStatus where
  typeName := "ExportStatus"
  typeDecl := """enum class ExportStatus {
    queued,
    processing,
    completed,
    failed,
    cancelled
};"""

instance : EmitCpp23 CameraType where
  typeName := "CameraType"
  typeDecl := """enum class CameraType {
    perspective,
    orthographic,
    fisheye,
    spherical
};"""

instance : EmitCpp23 ProjectionType where
  typeName := "ProjectionType"
  typeDecl := """enum class ProjectionType {
    perspective,
    orthographic
};"""

instance : EmitCpp23 TextAlign where
  typeName := "TextAlign"
  typeDecl := """enum class TextAlign {
    left,
    center,
    right,
    justify
};"""

instance : EmitCpp23 TextDirection where
  typeName := "TextDirection"
  typeDecl := """enum class TextDirection {
    ltr,
    rtl
};"""

instance : EmitCpp23 FontStyle where
  typeName := "FontStyle"
  typeDecl := """enum class FontStyle {
    normal,
    italic,
    oblique
};"""

instance : EmitCpp23 FontWeight where
  typeName := "FontWeight"
  typeDecl := """enum class FontWeight {
    thin,
    extraLight,
    light,
    regular,
    medium,
    semiBold,
    bold,
    extraBold,
    black
};"""

instance : EmitCpp23 JobStatus where
  typeName := "JobStatus"
  typeDecl := """enum class JobStatus {
    queued,
    running,
    completed,
    failed,
    cancelled
};"""

instance : EmitCpp23 RenderStatus where
  typeName := "RenderStatus"
  typeDecl := """enum class RenderStatus {
    idle,
    rendering,
    paused,
    completed,
    failed
};"""

instance : EmitCpp23 QualityMode where
  typeName := "QualityMode"
  typeDecl := """enum class QualityMode {
    low,
    medium,
    high,
    ultra
};"""

instance : EmitCpp23 ValidationResult where
  typeName := "ValidationResult"
  typeDecl := """enum class ValidationResult {
    valid,
    invalid,
    warning
};"""

instance : EmitCpp23 Severity where
  typeName := "Severity"
  typeDecl := """enum class Severity {
    debug,
    info,
    warning,
    error,
    critical
};"""

instance : EmitCpp23 EffectType where
  typeName := "EffectType"
  typeDecl := """enum class EffectType {
    blur,
    sharpen,
    glow,
    shadow,
    bevel,
    gradientOverlay,
    stroke,
    colorCorrection,
    distort,
    keying,
    matte,
    noise,
    grain,
    motionBlur,
    timewarp,
    transition
};"""

instance : EmitCpp23 EmitterShape where
  typeName := "EmitterShape"
  typeDecl := """enum class EmitterShape {
    point,
    line,
    circle,
    box,
    sphere,
    ring,
    spline,
    depthMap,
    mask,
    cone,
    image,
    depthEdge,
    mesh
};"""

instance : EmitCpp23 ParticleShape where
  typeName := "ParticleShape"
  typeDecl := """enum class ParticleShape {
    point,
    circle,
    square,
    triangle,
    star,
    custom
};"""

instance : EmitCpp23 CollisionType where
  typeName := "CollisionType"
  typeDecl := """enum class CollisionType {
    none,
    boundingBox,
    precise,
    trigger
};"""

instance : EmitCpp23 MaterialType where
  typeName := "MaterialType"
  typeDecl := """enum class MaterialType {
    standard,
    physical,
    toon,
    emissive,
    transparent,
    custom
};"""

instance : EmitCpp23 AudioFormat where
  typeName := "AudioFormat"
  typeDecl := """enum class AudioFormat {
    mp3,
    wav,
    ogg,
    aac,
    flac,
    m4a
};"""

instance : EmitCpp23 AudioChannel where
  typeName := "AudioChannel"
  typeDecl := """enum class AudioChannel {
    mono,
    stereo,
    quad,
    surround51,
    surround71
};"""

instance : EmitCpp23 BeatDetectionMethod where
  typeName := "BeatDetectionMethod"
  typeDecl := """enum class BeatDetectionMethod {
    energy,
    onset,
    spectral,
    tempo,
    custom
};"""

instance : EmitCpp23 ExportTarget where
  typeName := "ExportTarget"
  typeDecl := """enum class ExportTarget {
    wan22I2V,
    wan22T2V,
    wan22FunCamera,
    wan22FirstLast,
    uni3cCamera,
    uni3cMotion,
    motionctrl,
    motionctrlSvd,
    cogvideox,
    controlnetDepth,
    controlnetCanny,
    controlnetLineart,
    controlnetPose,
    animatediffCameractrl,
    customWorkflow,
    lightX,
    wanMove,
    ati,
    ttm,
    ttmWan,
    ttmCogvideox,
    ttmSvd,
    scail,
    cameraComfyui
};"""

instance : EmitCpp23 DepthOfFieldMode where
  typeName := "DepthOfFieldMode"
  typeDecl := """enum class DepthOfFieldMode {
    off,
    gaussian,
    bokeh,
    custom
};"""

instance : EmitCpp23 ModelType where
  typeName := "ModelType"
  typeDecl := """enum class ModelType {
    mesh,
    pointCloud,
    volume,
    procedural
};"""

instance : EmitCpp23 PreprocessorType where
  typeName := "PreprocessorType"
  typeDecl := """enum class PreprocessorType {
    depth,
    normal,
    pose,
    edge,
    lineart,
    scribble,
    segmentation,
    video,
    other
};"""

instance : EmitCpp23 SegmentationMode where
  typeName := "SegmentationMode"
  typeDecl := """enum class SegmentationMode {
    semantic,
    instance,
    panoptic,
    custom
};"""

instance : EmitCpp23 AuditCategory where
  typeName := "AuditCategory"
  typeDecl := """enum class AuditCategory {
    security,
    performance,
    error,
    access,
    modification,
    system
};"""

instance : EmitCpp23 RateLimitScope where
  typeName := "RateLimitScope"
  typeDecl := """enum class RateLimitScope {
    global,
    user,
    ip,
    endpoint,
    custom
};"""

instance : EmitCpp23 SyncStatus where
  typeName := "SyncStatus"
  typeDecl := """enum class SyncStatus {
    synced,
    syncing,
    pending,
    failed,
    conflict
};"""

instance : EmitCpp23 ExpressionType where
  typeName := "ExpressionType"
  typeDecl := """enum class ExpressionType {
    preset,
    custom
};"""

instance : EmitCpp23 TextRangeMode where
  typeName := "TextRangeMode"
  typeDecl := """enum class TextRangeMode {
    percent,
    index
};"""

instance : EmitCpp23 TextRangeBasedOn where
  typeName := "TextRangeBasedOn"
  typeDecl := """enum class TextRangeBasedOn {
    characters,
    charactersExcludingSpaces,
    words,
    lines
};"""

instance : EmitCpp23 TextRangeShape where
  typeName := "TextRangeShape"
  typeDecl := """enum class TextRangeShape {
    square,
    rampUp,
    rampDown,
    triangle,
    round,
    smooth
};"""

/-! ## Layer 2A Events - C++23 Instances -/

instance : EmitCpp23 BaseEvent where
  typeName := "BaseEvent"
  typeDecl := """struct BaseEvent {
    NonEmptyString id;
    PositiveFloat timestamp;
    NonEmptyString eventType;
    
    BaseEvent(NonEmptyString id, PositiveFloat timestamp, NonEmptyString eventType)
        : id(id), timestamp(timestamp), eventType(eventType) {}
};"""

instance : EmitCpp23 CompositionCreated where
  typeName := "CompositionCreated"
  typeDecl := """struct CompositionCreated : BaseEvent {
    NonEmptyString compositionId;
    NonEmptyString compositionName;
    
    CompositionCreated(BaseEvent base, NonEmptyString compositionId, NonEmptyString compositionName)
        : BaseEvent(base), compositionId(compositionId), compositionName(compositionName) {}
};"""

instance : EmitCpp23 CompositionDeleted where
  typeName := "CompositionDeleted"
  typeDecl := """struct CompositionDeleted : BaseEvent {
    NonEmptyString compositionId;
    
    CompositionDeleted(BaseEvent base, NonEmptyString compositionId)
        : BaseEvent(base), compositionId(compositionId) {}
};"""

instance : EmitCpp23 CompositionRendered where
  typeName := "CompositionRendered"
  typeDecl := """struct CompositionRendered : BaseEvent {
    NonEmptyString compositionId;
    FrameNumber frameNumber;
    NonNegativeFloat duration;
    
    CompositionRendered(BaseEvent base, NonEmptyString compositionId, FrameNumber frameNumber, NonNegativeFloat duration)
        : BaseEvent(base), compositionId(compositionId), frameNumber(frameNumber), duration(duration) {}
};"""

instance : EmitCpp23 LayerCreated where
  typeName := "LayerCreated"
  typeDecl := """struct LayerCreated : BaseEvent {
    NonEmptyString layerId;
    NonEmptyString compositionId;
    LayerType layerType;
    
    LayerCreated(BaseEvent base, NonEmptyString layerId, NonEmptyString compositionId, LayerType layerType)
        : BaseEvent(base), layerId(layerId), compositionId(compositionId), layerType(layerType) {}
};"""

instance : EmitCpp23 LayerDeleted where
  typeName := "LayerDeleted"
  typeDecl := """struct LayerDeleted : BaseEvent {
    NonEmptyString layerId;
    NonEmptyString compositionId;
    
    LayerDeleted(BaseEvent base, NonEmptyString layerId, NonEmptyString compositionId)
        : BaseEvent(base), layerId(layerId), compositionId(compositionId) {}
};"""

instance : EmitCpp23 LayerMoved where
  typeName := "LayerMoved"
  typeDecl := """struct LayerMoved : BaseEvent {
    NonEmptyString layerId;
    NonEmptyString compositionId;
    FrameNumber oldIndex;
    FrameNumber newIndex;
    
    LayerMoved(BaseEvent base, NonEmptyString layerId, NonEmptyString compositionId, FrameNumber oldIndex, FrameNumber newIndex)
        : BaseEvent(base), layerId(layerId), compositionId(compositionId), oldIndex(oldIndex), newIndex(newIndex) {}
};"""

instance : EmitCpp23 LayerDuplicated where
  typeName := "LayerDuplicated"
  typeDecl := """struct LayerDuplicated : BaseEvent {
    NonEmptyString sourceLayerId;
    NonEmptyString newLayerId;
    NonEmptyString compositionId;
    
    LayerDuplicated(BaseEvent base, NonEmptyString sourceLayerId, NonEmptyString newLayerId, NonEmptyString compositionId)
        : BaseEvent(base), sourceLayerId(sourceLayerId), newLayerId(newLayerId), compositionId(compositionId) {}
};"""

instance : EmitCpp23 LayerVisibilityChanged where
  typeName := "LayerVisibilityChanged"
  typeDecl := """struct LayerVisibilityChanged : BaseEvent {
    NonEmptyString layerId;
    NonEmptyString compositionId;
    bool visible;
    
    LayerVisibilityChanged(BaseEvent base, NonEmptyString layerId, NonEmptyString compositionId, bool visible)
        : BaseEvent(base), layerId(layerId), compositionId(compositionId), visible(visible) {}
};"""

instance : EmitCpp23 KeyframeAdded where
  typeName := "KeyframeAdded"
  typeDecl := """struct KeyframeAdded : BaseEvent {
    NonEmptyString keyframeId;
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    FrameNumber frameNumber;
    std::string value;
    
    KeyframeAdded(BaseEvent base, NonEmptyString keyframeId, NonEmptyString layerId, NonEmptyString propertyPath, FrameNumber frameNumber, std::string value)
        : BaseEvent(base), keyframeId(keyframeId), layerId(layerId), propertyPath(propertyPath), frameNumber(frameNumber), value(value) {}
};"""

instance : EmitCpp23 KeyframeRemoved where
  typeName := "KeyframeRemoved"
  typeDecl := """struct KeyframeRemoved : BaseEvent {
    NonEmptyString keyframeId;
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    FrameNumber frameNumber;
    
    KeyframeRemoved(BaseEvent base, NonEmptyString keyframeId, NonEmptyString layerId, NonEmptyString propertyPath, FrameNumber frameNumber)
        : BaseEvent(base), keyframeId(keyframeId), layerId(layerId), propertyPath(propertyPath), frameNumber(frameNumber) {}
};"""

instance : EmitCpp23 KeyframeModified where
  typeName := "KeyframeModified"
  typeDecl := """struct KeyframeModified : BaseEvent {
    NonEmptyString keyframeId;
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    FrameNumber frameNumber;
    std::string oldValue;
    std::string newValue;
    
    KeyframeModified(BaseEvent base, NonEmptyString keyframeId, NonEmptyString layerId, NonEmptyString propertyPath, FrameNumber frameNumber, std::string oldValue, std::string newValue)
        : BaseEvent(base), keyframeId(keyframeId), layerId(layerId), propertyPath(propertyPath), frameNumber(frameNumber), oldValue(oldValue), newValue(newValue) {}
};"""

instance : EmitCpp23 KeyframeInterpolationChanged where
  typeName := "KeyframeInterpolationChanged"
  typeDecl := """struct KeyframeInterpolationChanged : BaseEvent {
    NonEmptyString keyframeId;
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    InterpolationType oldInterpolation;
    InterpolationType newInterpolation;
    
    KeyframeInterpolationChanged(BaseEvent base, NonEmptyString keyframeId, NonEmptyString layerId, NonEmptyString propertyPath, InterpolationType oldInterpolation, InterpolationType newInterpolation)
        : BaseEvent(base), keyframeId(keyframeId), layerId(layerId), propertyPath(propertyPath), oldInterpolation(oldInterpolation), newInterpolation(newInterpolation) {}
};"""

instance : EmitCpp23 PropertyAnimated where
  typeName := "PropertyAnimated"
  typeDecl := """struct PropertyAnimated : BaseEvent {
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    PositiveInt keyframeCount;
    
    PropertyAnimated(BaseEvent base, NonEmptyString layerId, NonEmptyString propertyPath, PositiveInt keyframeCount)
        : BaseEvent(base), layerId(layerId), propertyPath(propertyPath), keyframeCount(keyframeCount) {}
};"""

instance : EmitCpp23 PropertyExpressionChanged where
  typeName := "PropertyExpressionChanged"
  typeDecl := """struct PropertyExpressionChanged : BaseEvent {
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    std::string oldExpression;
    std::string newExpression;
    
    PropertyExpressionChanged(BaseEvent base, NonEmptyString layerId, NonEmptyString propertyPath, std::string oldExpression, std::string newExpression)
        : BaseEvent(base), layerId(layerId), propertyPath(propertyPath), oldExpression(oldExpression), newExpression(newExpression) {}
};"""

instance : EmitCpp23 PropertyDriverAdded where
  typeName := "PropertyDriverAdded"
  typeDecl := """struct PropertyDriverAdded : BaseEvent {
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    NonEmptyString driverPropertyPath;
    
    PropertyDriverAdded(BaseEvent base, NonEmptyString layerId, NonEmptyString propertyPath, NonEmptyString driverPropertyPath)
        : BaseEvent(base), layerId(layerId), propertyPath(propertyPath), driverPropertyPath(driverPropertyPath) {}
};"""

instance : EmitCpp23 EffectAdded where
  typeName := "EffectAdded"
  typeDecl := """struct EffectAdded : BaseEvent {
    NonEmptyString effectId;
    NonEmptyString layerId;
    EffectCategory effectCategory;
    
    EffectAdded(BaseEvent base, NonEmptyString effectId, NonEmptyString layerId, EffectCategory effectCategory)
        : BaseEvent(base), effectId(effectId), layerId(layerId), effectCategory(effectCategory) {}
};"""

instance : EmitCpp23 EffectRemoved where
  typeName := "EffectRemoved"
  typeDecl := """struct EffectRemoved : BaseEvent {
    NonEmptyString effectId;
    NonEmptyString layerId;
    
    EffectRemoved(BaseEvent base, NonEmptyString effectId, NonEmptyString layerId)
        : BaseEvent(base), effectId(effectId), layerId(layerId) {}
};"""

instance : EmitCpp23 EffectParameterChanged where
  typeName := "EffectParameterChanged"
  typeDecl := """struct EffectParameterChanged : BaseEvent {
    NonEmptyString effectId;
    NonEmptyString layerId;
    NonEmptyString parameterName;
    std::string oldValue;
    std::string newValue;
    
    EffectParameterChanged(BaseEvent base, NonEmptyString effectId, NonEmptyString layerId, NonEmptyString parameterName, std::string oldValue, std::string newValue)
        : BaseEvent(base), effectId(effectId), layerId(layerId), parameterName(parameterName), oldValue(oldValue), newValue(newValue) {}
};"""

instance : EmitCpp23 ExportStarted where
  typeName := "ExportStarted"
  typeDecl := """struct ExportStarted : BaseEvent {
    NonEmptyString exportId;
    NonEmptyString compositionId;
    ExportFormat exportFormat;
    ExportTarget exportTarget;
    
    ExportStarted(BaseEvent base, NonEmptyString exportId, NonEmptyString compositionId, ExportFormat exportFormat, ExportTarget exportTarget)
        : BaseEvent(base), exportId(exportId), compositionId(compositionId), exportFormat(exportFormat), exportTarget(exportTarget) {}
};"""

instance : EmitCpp23 ExportProgress where
  typeName := "ExportProgress"
  typeDecl := """struct ExportProgress : BaseEvent {
    NonEmptyString exportId;
    NonEmptyString compositionId;
    Percentage progress;
    FrameNumber currentFrame;
    FrameNumber totalFrames;
    
    ExportProgress(BaseEvent base, NonEmptyString exportId, NonEmptyString compositionId, Percentage progress, FrameNumber currentFrame, FrameNumber totalFrames)
        : BaseEvent(base), exportId(exportId), compositionId(compositionId), progress(progress), currentFrame(currentFrame), totalFrames(totalFrames) {}
};"""

instance : EmitCpp23 ExportCompleted where
  typeName := "ExportCompleted"
  typeDecl := """struct ExportCompleted : BaseEvent {
    NonEmptyString exportId;
    NonEmptyString compositionId;
    NonEmptyString outputPath;
    NonNegativeFloat duration;
    
    ExportCompleted(BaseEvent base, NonEmptyString exportId, NonEmptyString compositionId, NonEmptyString outputPath, NonNegativeFloat duration)
        : BaseEvent(base), exportId(exportId), compositionId(compositionId), outputPath(outputPath), duration(duration) {}
};"""

instance : EmitCpp23 ExportFailed where
  typeName := "ExportFailed"
  typeDecl := """struct ExportFailed : BaseEvent {
    NonEmptyString exportId;
    NonEmptyString compositionId;
    NonEmptyString errorMessage;
    
    ExportFailed(BaseEvent base, NonEmptyString exportId, NonEmptyString compositionId, NonEmptyString errorMessage)
        : BaseEvent(base), exportId(exportId), compositionId(compositionId), errorMessage(errorMessage) {}
};"""

instance : EmitCpp23 RenderJobQueued where
  typeName := "RenderJobQueued"
  typeDecl := """struct RenderJobQueued : BaseEvent {
    NonEmptyString jobId;
    NonEmptyString compositionId;
    PositiveInt priority;
    
    RenderJobQueued(BaseEvent base, NonEmptyString jobId, NonEmptyString compositionId, PositiveInt priority)
        : BaseEvent(base), jobId(jobId), compositionId(compositionId), priority(priority) {}
};"""

instance : EmitCpp23 RenderJobCompleted where
  typeName := "RenderJobCompleted"
  typeDecl := """struct RenderJobCompleted : BaseEvent {
    NonEmptyString jobId;
    NonEmptyString compositionId;
    NonNegativeFloat duration;
    
    RenderJobCompleted(BaseEvent base, NonEmptyString jobId, NonEmptyString compositionId, NonNegativeFloat duration)
        : BaseEvent(base), jobId(jobId), compositionId(compositionId), duration(duration) {}
};"""

instance : EmitCpp23 CacheCleared where
  typeName := "CacheCleared"
  typeDecl := """struct CacheCleared : BaseEvent {
    NonEmptyString cacheType;
    FrameNumber sizeBytes;
    
    CacheCleared(BaseEvent base, NonEmptyString cacheType, FrameNumber sizeBytes)
        : BaseEvent(base), cacheType(cacheType), sizeBytes(sizeBytes) {}
};"""

instance : EmitCpp23 ErrorOccurred where
  typeName := "ErrorOccurred"
  typeDecl := """struct ErrorOccurred : BaseEvent {
    Severity severity;
    NonEmptyString errorMessage;
    NonEmptyString errorCode;
    std::string stackTrace;
    
    ErrorOccurred(BaseEvent base, Severity severity, NonEmptyString errorMessage, NonEmptyString errorCode, std::string stackTrace)
        : BaseEvent(base), severity(severity), errorMessage(errorMessage), errorCode(errorCode), stackTrace(stackTrace) {}
};"""

/-! ## Layer 2B Metrics - C++23 Instances -/

instance : EmitCpp23 AggregationType where
  typeName := "AggregationType"
  typeDecl := """enum class AggregationType {
    sum,
    average,
    min,
    max,
    count,
    last
};"""

instance : EmitCpp23 TimeGrain where
  typeName := "TimeGrain"
  typeDecl := """enum class TimeGrain {
    millisecond,
    second,
    minute,
    hour,
    day
};"""

instance : EmitCpp23 MetricDataType where
  typeName := "MetricDataType"
  typeDecl := """enum class MetricDataType {
    float,
    integer,
    percentage,
    duration
};"""

instance : EmitCpp23 MetricCategory where
  typeName := "MetricCategory"
  typeDecl := """enum class MetricCategory {
    rendering,
    performance,
    quality,
    resource,
    user,
    ai
};"""

instance : EmitCpp23 MetricDefinition where
  typeName := "MetricDefinition"
  typeDecl := """struct MetricDefinition {
    NonEmptyString id;
    NonEmptyString name;
    MetricCategory category;
    MetricDataType dataType;
    NonEmptyString unit;
    float minValue;
    float maxValue;
    AggregationType aggregation;
    TimeGrain timeGrain;
    
    MetricDefinition(NonEmptyString id, NonEmptyString name, MetricCategory category, MetricDataType dataType, NonEmptyString unit, float minValue, float maxValue, AggregationType aggregation, TimeGrain timeGrain)
        : id(id), name(name), category(category), dataType(dataType), unit(unit), minValue(minValue), maxValue(maxValue), aggregation(aggregation), timeGrain(timeGrain) {}
};"""

instance : EmitCpp23 FrameRenderTime where
  typeName := "FrameRenderTime"
  typeDecl := """struct FrameRenderTime {
    PositiveFloat value;
    FrameNumber frameNumber;
    
    FrameRenderTime(PositiveFloat value, FrameNumber frameNumber)
        : value(value), frameNumber(frameNumber) {}
};"""

instance : EmitCpp23 TotalRenderTime where
  typeName := "TotalRenderTime"
  typeDecl := """struct TotalRenderTime {
    NonNegativeFloat value;
    FrameNumber frameCount;
    
    TotalRenderTime(NonNegativeFloat value, FrameNumber frameCount)
        : value(value), frameCount(frameCount) {}
};"""

instance : EmitCpp23 MemoryUsage where
  typeName := "MemoryUsage"
  typeDecl := """struct MemoryUsage {
    NonNegativeFloat value;
    
    MemoryUsage(NonNegativeFloat value)
        : value(value) {
        if (!std::isfinite(value.get())) {
            throw std::invalid_argument("MemoryUsage value must be finite");
        }
    }
};"""

instance : EmitCpp23 GpuUsage where
  typeName := "GpuUsage"
  typeDecl := """struct GpuUsage {
    Percentage value;
    
    GpuUsage(Percentage value)
        : value(value) {}
};"""

instance : EmitCpp23 CacheHitRate where
  typeName := "CacheHitRate"
  typeDecl := """struct CacheHitRate {
    Percentage value;
    
    CacheHitRate(Percentage value)
        : value(value) {}
};"""

instance : EmitCpp23 CacheSize where
  typeName := "CacheSize"
  typeDecl := """struct CacheSize {
    NonNegativeFloat value;
    
    CacheSize(NonNegativeFloat value)
        : value(value) {
        if (!std::isfinite(value.get())) {
            throw std::invalid_argument("CacheSize value must be finite");
        }
    }
};"""

instance : EmitCpp23 Fps where
  typeName := "Fps"
  typeDecl := """struct Fps {
    NonNegativeFloat value;
    
    Fps(NonNegativeFloat value)
        : value(value) {
        if (!std::isfinite(value.get())) {
            throw std::invalid_argument("Fps value must be finite");
        }
    }
};"""

instance : EmitCpp23 DroppedFrames where
  typeName := "DroppedFrames"
  typeDecl := """struct DroppedFrames {
    FrameNumber value;
    
    DroppedFrames(FrameNumber value)
        : value(value) {}
};"""

instance : EmitCpp23 PlaybackLatency where
  typeName := "PlaybackLatency"
  typeDecl := """struct PlaybackLatency {
    NonNegativeFloat value;
    
    PlaybackLatency(NonNegativeFloat value)
        : value(value) {
        if (!std::isfinite(value.get())) {
            throw std::invalid_argument("PlaybackLatency value must be finite");
        }
    }
};"""

instance : EmitCpp23 ScrubLatency where
  typeName := "ScrubLatency"
  typeDecl := """struct ScrubLatency {
    NonNegativeFloat value;
    
    ScrubLatency(NonNegativeFloat value)
        : value(value) {
        if (!std::isfinite(value.get())) {
            throw std::invalid_argument("ScrubLatency value must be finite");
        }
    }
};"""

instance : EmitCpp23 CompressionRatio where
  typeName := "CompressionRatio"
  typeDecl := """struct CompressionRatio {
    PositiveFloat value;
    
    CompressionRatio(PositiveFloat value)
        : value(value) {}
};"""

instance : EmitCpp23 Bitrate where
  typeName := "Bitrate"
  typeDecl := """struct Bitrate {
    PositiveFloat value;
    
    Bitrate(PositiveFloat value)
        : value(value) {}
};"""

instance : EmitCpp23 ColorAccuracy where
  typeName := "ColorAccuracy"
  typeDecl := """struct ColorAccuracy {
    Percentage value;
    
    ColorAccuracy(Percentage value)
        : value(value) {}
};"""

instance : EmitCpp23 MotionBlurQuality where
  typeName := "MotionBlurQuality"
  typeDecl := """struct MotionBlurQuality {
    NormalizedValue value;
    
    MotionBlurQuality(NormalizedValue value)
        : value(value) {}
};"""

instance : EmitCpp23 VramUsage where
  typeName := "VramUsage"
  typeDecl := """struct VramUsage {
    NonNegativeFloat value;
    
    VramUsage(NonNegativeFloat value)
        : value(value) {
        if (!std::isfinite(value.get())) {
            throw std::invalid_argument("VramUsage value must be finite");
        }
    }
};"""

instance : EmitCpp23 CpuUsage where
  typeName := "CpuUsage"
  typeDecl := """struct CpuUsage {
    Percentage value;
    
    CpuUsage(Percentage value)
        : value(value) {}
};"""

instance : EmitCpp23 NetworkBandwidth where
  typeName := "NetworkBandwidth"
  typeDecl := """struct NetworkBandwidth {
    NonNegativeFloat value;
    
    NetworkBandwidth(NonNegativeFloat value)
        : value(value) {
        if (!std::isfinite(value.get())) {
            throw std::invalid_argument("NetworkBandwidth value must be finite");
        }
    }
};"""

instance : EmitCpp23 StorageUsed where
  typeName := "StorageUsed"
  typeDecl := """struct StorageUsed {
    NonNegativeFloat value;
    
    StorageUsed(NonNegativeFloat value)
        : value(value) {
        if (!std::isfinite(value.get())) {
            throw std::invalid_argument("StorageUsed value must be finite");
        }
    }
};"""

instance : EmitCpp23 ActionsPerSession where
  typeName := "ActionsPerSession"
  typeDecl := """struct ActionsPerSession {
    FrameNumber value;
    
    ActionsPerSession(FrameNumber value)
        : value(value) {}
};"""

instance : EmitCpp23 ExportCount where
  typeName := "ExportCount"
  typeDecl := """struct ExportCount {
    FrameNumber value;
    
    ExportCount(FrameNumber value)
        : value(value) {}
};"""

instance : EmitCpp23 ProjectCount where
  typeName := "ProjectCount"
  typeDecl := """struct ProjectCount {
    FrameNumber value;
    
    ProjectCount(FrameNumber value)
        : value(value) {}
};"""

instance : EmitCpp23 InferenceTime where
  typeName := "InferenceTime"
  typeDecl := """struct InferenceTime {
    PositiveFloat value;
    
    InferenceTime(PositiveFloat value)
        : value(value) {}
};"""

instance : EmitCpp23 ModelLoadTime where
  typeName := "ModelLoadTime"
  typeDecl := """struct ModelLoadTime {
    PositiveFloat value;
    
    ModelLoadTime(PositiveFloat value)
        : value(value) {}
};"""

instance : EmitCpp23 TokensUsed where
  typeName := "TokensUsed"
  typeDecl := """struct TokensUsed {
    FrameNumber value;
    
    TokensUsed(FrameNumber value)
        : value(value) {}
};"""

instance : EmitCpp23 CostUSD where
  typeName := "CostUSD"
  typeDecl := """struct CostUSD {
    NonNegativeFloat value;
    
    CostUSD(NonNegativeFloat value)
        : value(value) {
        if (!std::isfinite(value.get())) {
            throw std::invalid_argument("CostUSD value must be finite");
        }
    }
};"""

/-! ## Layer 3 Triggers - C++23 Instances -/

instance : EmitCpp23 ComparisonOperator where
  typeName := "ComparisonOperator"
  typeDecl := """enum class ComparisonOperator {
    equals,
    notEquals,
    greaterThan,
    greaterThanOrEqual,
    lessThan,
    lessThanOrEqual
};"""

instance : EmitCpp23 PropertyCondition where
  typeName := "PropertyCondition"
  typeDecl := """struct PropertyCondition {
    NonEmptyString propertyPath;
    ComparisonOperator operator;
    std::string value;
    
    PropertyCondition(NonEmptyString propertyPath, ComparisonOperator operator, std::string value)
        : propertyPath(propertyPath), operator(operator), value(value) {}
};"""

instance : EmitCpp23 FrameCondition where
  typeName := "FrameCondition"
  typeDecl := """struct FrameCondition {
    FrameNumber frame;
    std::optional<std::pair<FrameNumber, FrameNumber>> range;
    std::optional<FrameNumber> modulo;
    
    FrameCondition(FrameNumber frame, std::optional<std::pair<FrameNumber, FrameNumber>> range, std::optional<FrameNumber> modulo)
        : frame(frame), range(range), modulo(modulo) {}
};"""

instance : EmitCpp23 AudioCondition where
  typeName := "AudioCondition"
  typeDecl := """struct AudioCondition {
    std::optional<FrameNumber> beatIndex;
    NormalizedValue peakThreshold;
    std::optional<NormalizedValue> frequency;
    
    AudioCondition(std::optional<FrameNumber> beatIndex, NormalizedValue peakThreshold, std::optional<NormalizedValue> frequency)
        : beatIndex(beatIndex), peakThreshold(peakThreshold), frequency(frequency) {}
};"""

instance : EmitCpp23 TimeCondition where
  typeName := "TimeCondition"
  typeDecl := """struct TimeCondition {
    NonNegativeFloat timecode;
    std::optional<NonNegativeFloat> duration;
    bool loop;
    
    TimeCondition(NonNegativeFloat timecode, std::optional<NonNegativeFloat> duration, bool loop)
        : timecode(timecode), duration(duration), loop(loop) {}
};"""

instance : EmitCpp23 BaseTrigger where
  typeName := "BaseTrigger"
  typeDecl := """struct BaseTrigger {
    NonEmptyString id;
    NonEmptyString triggerType;
    bool enabled;
    NonEmptyString compositionId;
    
    BaseTrigger(NonEmptyString id, NonEmptyString triggerType, bool enabled, NonEmptyString compositionId)
        : id(id), triggerType(triggerType), enabled(enabled), compositionId(compositionId) {}
};"""

instance : EmitCpp23 FrameTrigger where
  typeName := "FrameTrigger"
  typeDecl := """struct FrameTrigger : BaseTrigger {
    FrameCondition condition;
    
    FrameTrigger(BaseTrigger base, FrameCondition condition)
        : BaseTrigger(base), condition(condition) {}
};"""

instance : EmitCpp23 PropertyTrigger where
  typeName := "PropertyTrigger"
  typeDecl := """struct PropertyTrigger : BaseTrigger {
    PropertyCondition condition;
    NonEmptyString layerId;
    
    PropertyTrigger(BaseTrigger base, PropertyCondition condition, NonEmptyString layerId)
        : BaseTrigger(base), condition(condition), layerId(layerId) {}
};"""

instance : EmitCpp23 AudioTrigger where
  typeName := "AudioTrigger"
  typeDecl := """struct AudioTrigger : BaseTrigger {
    AudioCondition condition;
    NonEmptyString layerId;
    
    AudioTrigger(BaseTrigger base, AudioCondition condition, NonEmptyString layerId)
        : BaseTrigger(base), condition(condition), layerId(layerId) {}
};"""

instance : EmitCpp23 TimeTrigger where
  typeName := "TimeTrigger"
  typeDecl := """struct TimeTrigger : BaseTrigger {
    TimeCondition condition;
    
    TimeTrigger(BaseTrigger base, TimeCondition condition)
        : BaseTrigger(base), condition(condition) {}
};"""

instance : EmitCpp23 ExpressionTrigger where
  typeName := "ExpressionTrigger"
  typeDecl := """struct ExpressionTrigger : BaseTrigger {
    NonEmptyString expression;
    NonEmptyString layerId;
    
    ExpressionTrigger(BaseTrigger base, NonEmptyString expression, NonEmptyString layerId)
        : BaseTrigger(base), expression(expression), layerId(layerId) {}
};"""

instance : EmitCpp23 EventTrigger where
  typeName := "EventTrigger"
  typeDecl := """struct EventTrigger : BaseTrigger {
    NonEmptyString eventType;
    
    EventTrigger(BaseTrigger base, NonEmptyString eventType)
        : BaseTrigger(base), eventType(eventType) {}
};"""

instance : EmitCpp23 CompositeOperator where
  typeName := "CompositeOperator"
  typeDecl := """enum class CompositeOperator {
    and,
    or
};"""

instance : EmitCpp23 CompositeTrigger where
  typeName := "CompositeTrigger"
  typeDecl := """struct CompositeTrigger : BaseTrigger {
    CompositeOperator operator;
    std::vector<NonEmptyString> triggers;
    
    CompositeTrigger(BaseTrigger base, CompositeOperator operator, std::vector<NonEmptyString> triggers)
        : BaseTrigger(base), operator(operator), triggers(triggers) {}
};"""

/-! ## Layer 4 Actions - C++23 Instances -/

instance : EmitCpp23 ActionResult where
  typeName := "ActionResult"
  typeDecl := """enum class ActionResult {
    success,
    failure,
    partial
};"""

instance : EmitCpp23 RetryPolicy where
  typeName := "RetryPolicy"
  typeDecl := """struct RetryPolicy {
    FrameNumber maxRetries;
    NonNegativeFloat retryDelay;
    PositiveFloat backoffMultiplier;
    
    RetryPolicy(FrameNumber maxRetries, NonNegativeFloat retryDelay, PositiveFloat backoffMultiplier)
        : maxRetries(maxRetries), retryDelay(retryDelay), backoffMultiplier(backoffMultiplier) {}
};"""

instance : EmitCpp23 BaseAction where
  typeName := "BaseAction"
  typeDecl := """struct BaseAction {
    NonEmptyString id;
    NonEmptyString actionType;
    NonEmptyString target;
    std::string params;
    std::optional<RetryPolicy> retryPolicy;
    
    BaseAction(NonEmptyString id, NonEmptyString actionType, NonEmptyString target, std::string params, std::optional<RetryPolicy> retryPolicy)
        : id(id), actionType(actionType), target(target), params(params), retryPolicy(retryPolicy) {}
};"""

instance : EmitCpp23 CreateLayer where
  typeName := "CreateLayer"
  typeDecl := """struct CreateLayer : BaseAction {
    LayerType layerType;
    NonEmptyString compositionId;
    
    CreateLayer(BaseAction base, LayerType layerType, NonEmptyString compositionId)
        : BaseAction(base), layerType(layerType), compositionId(compositionId) {}
};"""

instance : EmitCpp23 DeleteLayer where
  typeName := "DeleteLayer"
  typeDecl := """struct DeleteLayer : BaseAction {
    NonEmptyString layerId;
    NonEmptyString compositionId;
    
    DeleteLayer(BaseAction base, NonEmptyString layerId, NonEmptyString compositionId)
        : BaseAction(base), layerId(layerId), compositionId(compositionId) {}
};"""

instance : EmitCpp23 DuplicateLayer where
  typeName := "DuplicateLayer"
  typeDecl := """struct DuplicateLayer : BaseAction {
    NonEmptyString sourceLayerId;
    NonEmptyString compositionId;
    
    DuplicateLayer(BaseAction base, NonEmptyString sourceLayerId, NonEmptyString compositionId)
        : BaseAction(base), sourceLayerId(sourceLayerId), compositionId(compositionId) {}
};"""

instance : EmitCpp23 MoveLayer where
  typeName := "MoveLayer"
  typeDecl := """struct MoveLayer : BaseAction {
    NonEmptyString layerId;
    NonEmptyString compositionId;
    FrameNumber newIndex;
    
    MoveLayer(BaseAction base, NonEmptyString layerId, NonEmptyString compositionId, FrameNumber newIndex)
        : BaseAction(base), layerId(layerId), compositionId(compositionId), newIndex(newIndex) {}
};"""

instance : EmitCpp23 SetLayerVisibility where
  typeName := "SetLayerVisibility"
  typeDecl := """struct SetLayerVisibility : BaseAction {
    NonEmptyString layerId;
    NonEmptyString compositionId;
    bool visible;
    
    SetLayerVisibility(BaseAction base, NonEmptyString layerId, NonEmptyString compositionId, bool visible)
        : BaseAction(base), layerId(layerId), compositionId(compositionId), visible(visible) {}
};"""

instance : EmitCpp23 SetLayerOpacity where
  typeName := "SetLayerOpacity"
  typeDecl := """struct SetLayerOpacity : BaseAction {
    NonEmptyString layerId;
    NonEmptyString compositionId;
    NormalizedValue opacity;
    
    SetLayerOpacity(BaseAction base, NonEmptyString layerId, NonEmptyString compositionId, NormalizedValue opacity)
        : BaseAction(base), layerId(layerId), compositionId(compositionId), opacity(opacity) {}
};"""

instance : EmitCpp23 AddKeyframe where
  typeName := "AddKeyframe"
  typeDecl := """struct AddKeyframe : BaseAction {
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    FrameNumber frameNumber;
    std::string value;
    
    AddKeyframe(BaseAction base, NonEmptyString layerId, NonEmptyString propertyPath, FrameNumber frameNumber, std::string value)
        : BaseAction(base), layerId(layerId), propertyPath(propertyPath), frameNumber(frameNumber), value(value) {}
};"""

instance : EmitCpp23 RemoveKeyframe where
  typeName := "RemoveKeyframe"
  typeDecl := """struct RemoveKeyframe : BaseAction {
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    FrameNumber frameNumber;
    
    RemoveKeyframe(BaseAction base, NonEmptyString layerId, NonEmptyString propertyPath, FrameNumber frameNumber)
        : BaseAction(base), layerId(layerId), propertyPath(propertyPath), frameNumber(frameNumber) {}
};"""

instance : EmitCpp23 ModifyKeyframe where
  typeName := "ModifyKeyframe"
  typeDecl := """struct ModifyKeyframe : BaseAction {
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    FrameNumber frameNumber;
    std::string value;
    
    ModifyKeyframe(BaseAction base, NonEmptyString layerId, NonEmptyString propertyPath, FrameNumber frameNumber, std::string value)
        : BaseAction(base), layerId(layerId), propertyPath(propertyPath), frameNumber(frameNumber), value(value) {}
};"""

instance : EmitCpp23 SetInterpolation where
  typeName := "SetInterpolation"
  typeDecl := """struct SetInterpolation : BaseAction {
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    FrameNumber frameNumber;
    InterpolationType interpolation;
    
    SetInterpolation(BaseAction base, NonEmptyString layerId, NonEmptyString propertyPath, FrameNumber frameNumber, InterpolationType interpolation)
        : BaseAction(base), layerId(layerId), propertyPath(propertyPath), frameNumber(frameNumber), interpolation(interpolation) {}
};"""

instance : EmitCpp23 CopyKeyframes where
  typeName := "CopyKeyframes"
  typeDecl := """struct CopyKeyframes : BaseAction {
    NonEmptyString sourceLayerId;
    NonEmptyString sourcePropertyPath;
    NonEmptyString targetLayerId;
    NonEmptyString targetPropertyPath;
    std::optional<std::pair<FrameNumber, FrameNumber>> frameRange;
    
    CopyKeyframes(BaseAction base, NonEmptyString sourceLayerId, NonEmptyString sourcePropertyPath, NonEmptyString targetLayerId, NonEmptyString targetPropertyPath, std::optional<std::pair<FrameNumber, FrameNumber>> frameRange)
        : BaseAction(base), sourceLayerId(sourceLayerId), sourcePropertyPath(sourcePropertyPath), targetLayerId(targetLayerId), targetPropertyPath(targetPropertyPath), frameRange(frameRange) {}
};"""

instance : EmitCpp23 PasteKeyframes where
  typeName := "PasteKeyframes"
  typeDecl := """struct PasteKeyframes : BaseAction {
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    FrameNumber frameNumber;
    
    PasteKeyframes(BaseAction base, NonEmptyString layerId, NonEmptyString propertyPath, FrameNumber frameNumber)
        : BaseAction(base), layerId(layerId), propertyPath(propertyPath), frameNumber(frameNumber) {}
};"""

instance : EmitCpp23 AnimateProperty where
  typeName := "AnimateProperty"
  typeDecl := """struct AnimateProperty : BaseAction {
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    std::string keyframes;
    
    AnimateProperty(BaseAction base, NonEmptyString layerId, NonEmptyString propertyPath, std::string keyframes)
        : BaseAction(base), layerId(layerId), propertyPath(propertyPath), keyframes(keyframes) {}
};"""

instance : EmitCpp23 SetPropertyValue where
  typeName := "SetPropertyValue"
  typeDecl := """struct SetPropertyValue : BaseAction {
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    std::string value;
    
    SetPropertyValue(BaseAction base, NonEmptyString layerId, NonEmptyString propertyPath, std::string value)
        : BaseAction(base), layerId(layerId), propertyPath(propertyPath), value(value) {}
};"""

instance : EmitCpp23 AddExpression where
  typeName := "AddExpression"
  typeDecl := """struct AddExpression : BaseAction {
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    NonEmptyString expression;
    
    AddExpression(BaseAction base, NonEmptyString layerId, NonEmptyString propertyPath, NonEmptyString expression)
        : BaseAction(base), layerId(layerId), propertyPath(propertyPath), expression(expression) {}
};"""

instance : EmitCpp23 RemoveExpression where
  typeName := "RemoveExpression"
  typeDecl := """struct RemoveExpression : BaseAction {
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    
    RemoveExpression(BaseAction base, NonEmptyString layerId, NonEmptyString propertyPath)
        : BaseAction(base), layerId(layerId), propertyPath(propertyPath) {}
};"""

instance : EmitCpp23 AddDriver where
  typeName := "AddDriver"
  typeDecl := """struct AddDriver : BaseAction {
    NonEmptyString layerId;
    NonEmptyString propertyPath;
    NonEmptyString driverPropertyPath;
    
    AddDriver(BaseAction base, NonEmptyString layerId, NonEmptyString propertyPath, NonEmptyString driverPropertyPath)
        : BaseAction(base), layerId(layerId), propertyPath(propertyPath), driverPropertyPath(driverPropertyPath) {}
};"""

instance : EmitCpp23 AddEffect where
  typeName := "AddEffect"
  typeDecl := """struct AddEffect : BaseAction {
    NonEmptyString layerId;
    EffectCategory effectCategory;
    std::string effectParams;
    
    AddEffect(BaseAction base, NonEmptyString layerId, EffectCategory effectCategory, std::string effectParams)
        : BaseAction(base), layerId(layerId), effectCategory(effectCategory), effectParams(effectParams) {}
};"""

instance : EmitCpp23 RemoveEffect where
  typeName := "RemoveEffect"
  typeDecl := """struct RemoveEffect : BaseAction {
    NonEmptyString layerId;
    NonEmptyString effectId;
    
    RemoveEffect(BaseAction base, NonEmptyString layerId, NonEmptyString effectId)
        : BaseAction(base), layerId(layerId), effectId(effectId) {}
};"""

instance : EmitCpp23 ModifyEffect where
  typeName := "ModifyEffect"
  typeDecl := """struct ModifyEffect : BaseAction {
    NonEmptyString layerId;
    NonEmptyString effectId;
    std::string effectParams;
    
    ModifyEffect(BaseAction base, NonEmptyString layerId, NonEmptyString effectId, std::string effectParams)
        : BaseAction(base), layerId(layerId), effectId(effectId), effectParams(effectParams) {}
};"""

instance : EmitCpp23 EnableEffect where
  typeName := "EnableEffect"
  typeDecl := """struct EnableEffect : BaseAction {
    NonEmptyString layerId;
    NonEmptyString effectId;
    
    EnableEffect(BaseAction base, NonEmptyString layerId, NonEmptyString effectId)
        : BaseAction(base), layerId(layerId), effectId(effectId) {}
};"""

instance : EmitCpp23 DisableEffect where
  typeName := "DisableEffect"
  typeDecl := """struct DisableEffect : BaseAction {
    NonEmptyString layerId;
    NonEmptyString effectId;
    
    DisableEffect(BaseAction base, NonEmptyString layerId, NonEmptyString effectId)
        : BaseAction(base), layerId(layerId), effectId(effectId) {}
};"""

instance : EmitCpp23 CreateComposition where
  typeName := "CreateComposition"
  typeDecl := """struct CreateComposition : BaseAction {
    NonEmptyString compositionName;
    PositiveInt width;
    PositiveInt height;
    PositiveFloat fps;
    
    CreateComposition(BaseAction base, NonEmptyString compositionName, PositiveInt width, PositiveInt height, PositiveFloat fps)
        : BaseAction(base), compositionName(compositionName), width(width), height(height), fps(fps) {}
};"""

instance : EmitCpp23 DeleteComposition where
  typeName := "DeleteComposition"
  typeDecl := """struct DeleteComposition : BaseAction {
    NonEmptyString compositionId;
    
    DeleteComposition(BaseAction base, NonEmptyString compositionId)
        : BaseAction(base), compositionId(compositionId) {}
};"""

instance : EmitCpp23 SetCompositionSettings where
  typeName := "SetCompositionSettings"
  typeDecl := """struct SetCompositionSettings : BaseAction {
    NonEmptyString compositionId;
    std::string settings;
    
    SetCompositionSettings(BaseAction base, NonEmptyString compositionId, std::string settings)
        : BaseAction(base), compositionId(compositionId), settings(settings) {}
};"""

instance : EmitCpp23 RenderComposition where
  typeName := "RenderComposition"
  typeDecl := """struct RenderComposition : BaseAction {
    NonEmptyString compositionId;
    FrameNumber startFrame;
    FrameNumber endFrame;
    
    RenderComposition(BaseAction base, NonEmptyString compositionId, FrameNumber startFrame, FrameNumber endFrame)
        : BaseAction(base), compositionId(compositionId), startFrame(startFrame), endFrame(endFrame) {}
};"""

instance : EmitCpp23 StartExport where
  typeName := "StartExport"
  typeDecl := """struct StartExport : BaseAction {
    NonEmptyString compositionId;
    ExportFormat exportFormat;
    ExportTarget exportTarget;
    std::string settings;
    
    StartExport(BaseAction base, NonEmptyString compositionId, ExportFormat exportFormat, ExportTarget exportTarget, std::string settings)
        : BaseAction(base), compositionId(compositionId), exportFormat(exportFormat), exportTarget(exportTarget), settings(settings) {}
};"""

instance : EmitCpp23 CancelExport where
  typeName := "CancelExport"
  typeDecl := """struct CancelExport : BaseAction {
    NonEmptyString exportId;
    
    CancelExport(BaseAction base, NonEmptyString exportId)
        : BaseAction(base), exportId(exportId) {}
};"""

instance : EmitCpp23 PauseExport where
  typeName := "PauseExport"
  typeDecl := """struct PauseExport : BaseAction {
    NonEmptyString exportId;
    
    PauseExport(BaseAction base, NonEmptyString exportId)
        : BaseAction(base), exportId(exportId) {}
};"""

instance : EmitCpp23 ResumeExport where
  typeName := "ResumeExport"
  typeDecl := """struct ResumeExport : BaseAction {
    NonEmptyString exportId;
    
    ResumeExport(BaseAction base, NonEmptyString exportId)
        : BaseAction(base), exportId(exportId) {}
};"""

instance : EmitCpp23 SetExportSettings where
  typeName := "SetExportSettings"
  typeDecl := """struct SetExportSettings : BaseAction {
    NonEmptyString exportId;
    std::string settings;
    
    SetExportSettings(BaseAction base, NonEmptyString exportId, std::string settings)
        : BaseAction(base), exportId(exportId), settings(settings) {}
};"""

instance : EmitCpp23 LoadAudio where
  typeName := "LoadAudio"
  typeDecl := """struct LoadAudio : BaseAction {
    NonEmptyString layerId;
    NonEmptyString audioPath;
    
    LoadAudio(BaseAction base, NonEmptyString layerId, NonEmptyString audioPath)
        : BaseAction(base), layerId(layerId), audioPath(audioPath) {}
};"""

instance : EmitCpp23 AnalyzeAudio where
  typeName := "AnalyzeAudio"
  typeDecl := """struct AnalyzeAudio : BaseAction {
    NonEmptyString layerId;
    BeatDetectionMethod method;
    
    AnalyzeAudio(BaseAction base, NonEmptyString layerId, BeatDetectionMethod method)
        : BaseAction(base), layerId(layerId), method(method) {}
};"""

instance : EmitCpp23 SetAudioReactivity where
  typeName := "SetAudioReactivity"
  typeDecl := """struct SetAudioReactivity : BaseAction {
    NonEmptyString layerId;
    bool enabled;
    std::string reactivityParams;
    
    SetAudioReactivity(BaseAction base, NonEmptyString layerId, bool enabled, std::string reactivityParams)
        : BaseAction(base), layerId(layerId), enabled(enabled), reactivityParams(reactivityParams) {}
};"""

instance : EmitCpp23 SetCameraPosition where
  typeName := "SetCameraPosition"
  typeDecl := """struct SetCameraPosition : BaseAction {
    NonEmptyString layerId;
    Vec3 position;
    
    SetCameraPosition(BaseAction base, NonEmptyString layerId, Vec3 position)
        : BaseAction(base), layerId(layerId), position(position) {}
};"""

instance : EmitCpp23 SetCameraRotation where
  typeName := "SetCameraRotation"
  typeDecl := """struct SetCameraRotation : BaseAction {
    NonEmptyString layerId;
    Vec3 rotation;
    
    SetCameraRotation(BaseAction base, NonEmptyString layerId, Vec3 rotation)
        : BaseAction(base), layerId(layerId), rotation(rotation) {}
};"""

instance : EmitCpp23 SetCameraFOV where
  typeName := "SetCameraFOV"
  typeDecl := """struct SetCameraFOV : BaseAction {
    NonEmptyString layerId;
    PositiveFloat fov;
    
    SetCameraFOV(BaseAction base, NonEmptyString layerId, PositiveFloat fov)
        : BaseAction(base), layerId(layerId), fov(fov) {}
};"""

instance : EmitCpp23 AnimateCamera where
  typeName := "AnimateCamera"
  typeDecl := """struct AnimateCamera : BaseAction {
    NonEmptyString layerId;
    std::string keyframes;
    
    AnimateCamera(BaseAction base, NonEmptyString layerId, std::string keyframes)
        : BaseAction(base), layerId(layerId), keyframes(keyframes) {}
};"""

instance : EmitCpp23 SegmentImage where
  typeName := "SegmentImage"
  typeDecl := """struct SegmentImage : BaseAction {
    NonEmptyString layerId;
    SegmentationMode mode;
    
    SegmentImage(BaseAction base, NonEmptyString layerId, SegmentationMode mode)
        : BaseAction(base), layerId(layerId), mode(mode) {}
};"""

instance : EmitCpp23 VectorizeImage where
  typeName := "VectorizeImage"
  typeDecl := """struct VectorizeImage : BaseAction {
    NonEmptyString layerId;
    std::string vectorizeParams;
    
    VectorizeImage(BaseAction base, NonEmptyString layerId, std::string vectorizeParams)
        : BaseAction(base), layerId(layerId), vectorizeParams(vectorizeParams) {}
};"""

instance : EmitCpp23 DecomposeImage where
  typeName := "DecomposeImage"
  typeDecl := """struct DecomposeImage : BaseAction {
    NonEmptyString layerId;
    std::string components;
    
    DecomposeImage(BaseAction base, NonEmptyString layerId, std::string components)
        : BaseAction(base), layerId(layerId), components(components) {}
};"""

instance : EmitCpp23 GenerateDepth where
  typeName := "GenerateDepth"
  typeDecl := """struct GenerateDepth : BaseAction {
    NonEmptyString layerId;
    PreprocessorType method;
    
    GenerateDepth(BaseAction base, NonEmptyString layerId, PreprocessorType method)
        : BaseAction(base), layerId(layerId), method(method) {}
};"""

instance : EmitCpp23 EstimateNormals where
  typeName := "EstimateNormals"
  typeDecl := """struct EstimateNormals : BaseAction {
    NonEmptyString layerId;
    std::string normalParams;
    
    EstimateNormals(BaseAction base, NonEmptyString layerId, std::string normalParams)
        : BaseAction(base), layerId(layerId), normalParams(normalParams) {}
};"""

instance : EmitCpp23 ClearCache where
  typeName := "ClearCache"
  typeDecl := """struct ClearCache : BaseAction {
    NonEmptyString cacheType;
    
    ClearCache(BaseAction base, NonEmptyString cacheType)
        : BaseAction(base), cacheType(cacheType) {}
};"""

instance : EmitCpp23 OptimizeMemory where
  typeName := "OptimizeMemory"
  typeDecl := """struct OptimizeMemory : BaseAction {
    PositiveFloat targetMemoryMB;
    
    OptimizeMemory(BaseAction base, PositiveFloat targetMemoryMB)
        : BaseAction(base), targetMemoryMB(targetMemoryMB) {}
};"""

instance : EmitCpp23 SaveProject where
  typeName := "SaveProject"
  typeDecl := """struct SaveProject : BaseAction {
    NonEmptyString projectId;
    NonEmptyString filePath;
    
    SaveProject(BaseAction base, NonEmptyString projectId, NonEmptyString filePath)
        : BaseAction(base), projectId(projectId), filePath(filePath) {}
};"""

instance : EmitCpp23 LoadProject where
  typeName := "LoadProject"
  typeDecl := """struct LoadProject : BaseAction {
    NonEmptyString filePath;
    
    LoadProject(BaseAction base, NonEmptyString filePath)
        : BaseAction(base), filePath(filePath) {}
};"""

instance : EmitCpp23 Undo where
  typeName := "Undo"
  typeDecl := """struct Undo : BaseAction {
    NonEmptyString compositionId;
    FrameNumber steps;
    
    Undo(BaseAction base, NonEmptyString compositionId, FrameNumber steps)
        : BaseAction(base), compositionId(compositionId), steps(steps) {}
};"""

instance : EmitCpp23 Redo where
  typeName := "Redo"
  typeDecl := """struct Redo : BaseAction {
    NonEmptyString compositionId;
    FrameNumber steps;
    
    Redo(BaseAction base, NonEmptyString compositionId, FrameNumber steps)
        : BaseAction(base), compositionId(compositionId), steps(steps) {}
};"""

/-! ## Layer 5 Entities - C++23 Instances -/

instance : EmitCpp23 ControlMode where
  typeName := "ControlMode"
  typeDecl := """enum class ControlMode {
    symmetric,
    smooth,
    corner
};"""

instance : EmitCpp23 BezierHandle where
  typeName := "BezierHandle"
  typeDecl := """struct BezierHandle {
    float frame;
    float value;
    bool enabled;
    
    BezierHandle(float frame, float value, bool enabled)
        : frame(frame), value(value), enabled(enabled) {}
};"""

instance : EmitCpp23 Keyframe where
  typeName := "Keyframe"
  typeDecl := """struct Keyframe {
    NonEmptyString id;
    FrameNumber frame;
    std::string value;
    InterpolationType interpolation;
    BezierHandle inHandle;
    BezierHandle outHandle;
    ControlMode controlMode;
    
    Keyframe(NonEmptyString id, FrameNumber frame, std::string value, InterpolationType interpolation, BezierHandle inHandle, BezierHandle outHandle, ControlMode controlMode)
        : id(id), frame(frame), value(value), interpolation(interpolation), inHandle(inHandle), outHandle(outHandle), controlMode(controlMode) {}
};"""

instance : EmitCpp23 PropertyValueType where
  typeName := "PropertyValueType"
  typeDecl := """enum class PropertyValueType {
    number,
    position,
    color,
    enum,
    vector3
};"""

instance : EmitCpp23 PropertyExpression where
  typeName := "PropertyExpression"
  typeDecl := """struct PropertyExpression {
    bool enabled;
    ExpressionType expressionType;
    NonEmptyString name;
    std::string params;
    
    PropertyExpression(bool enabled, ExpressionType expressionType, NonEmptyString name, std::string params)
        : enabled(enabled), expressionType(expressionType), name(name), params(params) {}
};"""

instance : EmitCpp23 AnimatableProperty where
  typeName := "AnimatableProperty"
  typeDecl := """struct AnimatableProperty {
    NonEmptyString id;
    NonEmptyString name;
    PropertyValueType propertyType;
    std::string value;
    bool animated;
    std::vector<NonEmptyString> keyframes;
    std::optional<NonEmptyString> group;
    std::optional<PropertyExpression> expression;
    
    AnimatableProperty(NonEmptyString id, NonEmptyString name, PropertyValueType propertyType, std::string value, bool animated, std::vector<NonEmptyString> keyframes, std::optional<NonEmptyString> group, std::optional<PropertyExpression> expression)
        : id(id), name(name), propertyType(propertyType), value(value), animated(animated), keyframes(keyframes), group(group), expression(expression) {}
};"""

instance : EmitCpp23 CompositionSettings where
  typeName := "CompositionSettings"
  typeDecl := """struct CompositionSettings {
    PositiveInt width;
    PositiveInt height;
    PositiveFloat fps;
    NonNegativeFloat duration;
    NonEmptyString backgroundColor;
    
    CompositionSettings(PositiveInt width, PositiveInt height, PositiveFloat fps, NonNegativeFloat duration, NonEmptyString backgroundColor)
        : width(width), height(height), fps(fps), duration(duration), backgroundColor(backgroundColor) {}
};"""

instance : EmitCpp23 RenderSettings where
  typeName := "RenderSettings"
  typeDecl := """struct RenderSettings {
    QualityMode quality;
    bool motionBlur;
    PositiveInt motionBlurSamples;
    NormalizedValue motionBlurShutterAngle;
    
    RenderSettings(QualityMode quality, bool motionBlur, PositiveInt motionBlurSamples, NormalizedValue motionBlurShutterAngle)
        : quality(quality), motionBlur(motionBlur), motionBlurSamples(motionBlurSamples), motionBlurShutterAngle(motionBlurShutterAngle) {}
};"""

instance : EmitCpp23 Composition where
  typeName := "Composition"
  typeDecl := """struct Composition {
    NonEmptyString id;
    NonNegativeFloat createdAt;
    NonNegativeFloat updatedAt;
    NonEmptyString name;
    CompositionSettings settings;
    RenderSettings renderSettings;
    std::optional<NonEmptyString> mainCompositionId;
    
    Composition(NonEmptyString id, NonNegativeFloat createdAt, NonNegativeFloat updatedAt, NonEmptyString name, CompositionSettings settings, RenderSettings renderSettings, std::optional<NonEmptyString> mainCompositionId)
        : id(id), createdAt(createdAt), updatedAt(updatedAt), name(name), settings(settings), renderSettings(renderSettings), mainCompositionId(mainCompositionId) {}
};"""

-- CreateComposition (Entity Create model)
instance : EmitCpp23 (Lattice.Entities.CreateComposition) where
  typeName := "CreateCompositionEntity"
  typeDecl := """struct CreateCompositionEntity {
    NonEmptyString name;
    CompositionSettings settings;
    RenderSettings renderSettings;
    
    CreateCompositionEntity(NonEmptyString name, CompositionSettings settings, RenderSettings renderSettings)
        : name(name), settings(settings), renderSettings(renderSettings) {}
};"""

-- UpdateComposition
instance : EmitCpp23 (Lattice.Entities.UpdateComposition) where
  typeName := "UpdateComposition"
  typeDecl := """struct UpdateComposition {
    std::optional<NonEmptyString> name;
    std::optional<CompositionSettings> settings;
    std::optional<RenderSettings> renderSettings;
    
    UpdateComposition(std::optional<NonEmptyString> name, std::optional<CompositionSettings> settings, std::optional<RenderSettings> renderSettings)
        : name(name), settings(settings), renderSettings(renderSettings) {}
};"""

-- CreateLayer (Entity Create model)
instance : EmitCpp23 (Lattice.Entities.CreateLayer) where
  typeName := "CreateLayerEntity"
  typeDecl := """struct CreateLayerEntity {
    NonEmptyString name;
    LayerType layerType;
    FrameNumber startFrame;
    FrameNumber endFrame;
    std::optional<NonEmptyString> parentId;
    
    CreateLayerEntity(NonEmptyString name, LayerType layerType, FrameNumber startFrame, FrameNumber endFrame, std::optional<NonEmptyString> parentId)
        : name(name), layerType(layerType), startFrame(startFrame), endFrame(endFrame), parentId(parentId) {}
};"""

-- UpdateLayer
instance : EmitCpp23 (Lattice.Entities.UpdateLayer) where
  typeName := "UpdateLayer"
  typeDecl := """struct UpdateLayer {
    std::optional<NonEmptyString> name;
    std::optional<bool> visible;
    std::optional<bool> locked;
    std::optional<bool> threeD;
    std::optional<bool> motionBlur;
    std::optional<FrameNumber> startFrame;
    std::optional<FrameNumber> endFrame;
    std::optional<NonEmptyString> parentId;
    std::optional<BlendMode> blendMode;
    
    UpdateLayer(std::optional<NonEmptyString> name, std::optional<bool> visible, std::optional<bool> locked, std::optional<bool> threeD, std::optional<bool> motionBlur, std::optional<FrameNumber> startFrame, std::optional<FrameNumber> endFrame, std::optional<NonEmptyString> parentId, std::optional<BlendMode> blendMode)
        : name(name), visible(visible), locked(locked), threeD(threeD), motionBlur(motionBlur), startFrame(startFrame), endFrame(endFrame), parentId(parentId), blendMode(blendMode) {}
};"""

-- CreateEffectInstance
instance : EmitCpp23 (Lattice.Entities.CreateEffectInstance) where
  typeName := "CreateEffectInstance"
  typeDecl := """struct CreateEffectInstance {
    EffectType effectType;
    NonEmptyString layerId;
    
    CreateEffectInstance(EffectType effectType, NonEmptyString layerId)
        : effectType(effectType), layerId(layerId) {}
};"""

-- UpdateEffectInstance
instance : EmitCpp23 (Lattice.Entities.UpdateEffectInstance) where
  typeName := "UpdateEffectInstance"
  typeDecl := """struct UpdateEffectInstance {
    std::optional<bool> enabled;
    std::optional<std::vector<NonEmptyString>> parameters;
    
    UpdateEffectInstance(std::optional<bool> enabled, std::optional<std::vector<NonEmptyString>> parameters)
        : enabled(enabled), parameters(parameters) {}
};"""

-- CreateProject
instance : EmitCpp23 (Lattice.Entities.CreateProject) where
  typeName := "CreateProject"
  typeDecl := """struct CreateProject {
    NonEmptyString name;
    ProjectSettings settings;
    
    CreateProject(NonEmptyString name, ProjectSettings settings)
        : name(name), settings(settings) {}
};"""

-- UpdateProject
instance : EmitCpp23 (Lattice.Entities.UpdateProject) where
  typeName := "UpdateProject"
  typeDecl := """struct UpdateProject {
    std::optional<NonEmptyString> name;
    std::optional<ProjectSettings> settings;
    std::optional<NonEmptyString> mainCompositionId;
    
    UpdateProject(std::optional<NonEmptyString> name, std::optional<ProjectSettings> settings, std::optional<NonEmptyString> mainCompositionId)
        : name(name), settings(settings), mainCompositionId(mainCompositionId) {}
};"""

-- CreateAsset
instance : EmitCpp23 (Lattice.Entities.CreateAsset) where
  typeName := "CreateAsset"
  typeDecl := """struct CreateAsset {
    NonEmptyString name;
    AssetType assetType;
    AssetSource source;
    NonEmptyString data;
    AssetMetadata metadata;
    
    CreateAsset(NonEmptyString name, AssetType assetType, AssetSource source, NonEmptyString data, AssetMetadata metadata)
        : name(name), assetType(assetType), source(source), data(data), metadata(metadata) {}
};"""

-- UpdateAsset
instance : EmitCpp23 (Lattice.Entities.UpdateAsset) where
  typeName := "UpdateAsset"
  typeDecl := """struct UpdateAsset {
    std::optional<NonEmptyString> name;
    std::optional<NonEmptyString> data;
    std::optional<AssetMetadata> metadata;
    
    UpdateAsset(std::optional<NonEmptyString> name, std::optional<NonEmptyString> data, std::optional<AssetMetadata> metadata)
        : name(name), data(data), metadata(metadata) {}
};"""

-- CreateExportJob
instance : EmitCpp23 (Lattice.Entities.CreateExportJob) where
  typeName := "CreateExportJob"
  typeDecl := """struct CreateExportJob {
    NonEmptyString compositionId;
    ExportConfig config;
    
    CreateExportJob(NonEmptyString compositionId, ExportConfig config)
        : compositionId(compositionId), config(config) {}
};"""

-- UpdateExportJob
instance : EmitCpp23 (Lattice.Entities.UpdateExportJob) where
  typeName := "UpdateExportJob"
  typeDecl := """struct UpdateExportJob {
    std::optional<ExportJobStatus> status;
    std::optional<NormalizedValue> progress;
    std::optional<std::string> outputFiles;
    std::optional<NonEmptyString> errorMessage;
    
    UpdateExportJob(std::optional<ExportJobStatus> status, std::optional<NormalizedValue> progress, std::optional<std::string> outputFiles, std::optional<NonEmptyString> errorMessage)
        : status(status), progress(progress), outputFiles(outputFiles), errorMessage(errorMessage) {}
};"""

instance : EmitCpp23 LayerTransform where
  typeName := "LayerTransform"
  typeDecl := """struct LayerTransform {
    Vec2 position;
    float rotation;
    Vec2 scale;
    Vec2 anchor;
    NormalizedValue opacity;
    
    LayerTransform(Vec2 position, float rotation, Vec2 scale, Vec2 anchor, NormalizedValue opacity)
        : position(position), rotation(rotation), scale(scale), anchor(anchor), opacity(opacity) {}
};"""

instance : EmitCpp23 LayerMask where
  typeName := "LayerMask"
  typeDecl := """struct LayerMask {
    NonEmptyString id;
    std::string path;
    MaskMode mode;
    bool inverted;
    
    LayerMask(NonEmptyString id, std::string path, MaskMode mode, bool inverted)
        : id(id), path(path), mode(mode), inverted(inverted) {}
};"""

instance : EmitCpp23 Layer where
  typeName := "Layer"
  typeDecl := """struct Layer {
    NonEmptyString id;
    NonNegativeFloat createdAt;
    NonNegativeFloat updatedAt;
    NonEmptyString name;
    LayerType layerType;
    bool visible;
    bool locked;
    bool threeD;
    bool motionBlur;
    FrameNumber startFrame;
    FrameNumber endFrame;
    std::optional<NonEmptyString> parentId;
    BlendMode blendMode;
    AnimatableProperty opacity;
    LayerTransform transform;
    std::vector<LayerMask> masks;
    std::optional<NonEmptyString> matteType;
    std::vector<NonEmptyString> properties;
    std::vector<NonEmptyString> effects;
    std::optional<NonEmptyString> data;
    
    Layer(NonEmptyString id, NonNegativeFloat createdAt, NonNegativeFloat updatedAt, NonEmptyString name, LayerType layerType, bool visible, bool locked, bool threeD, bool motionBlur, FrameNumber startFrame, FrameNumber endFrame, std::optional<NonEmptyString> parentId, BlendMode blendMode, AnimatableProperty opacity, LayerTransform transform, std::vector<LayerMask> masks, std::optional<NonEmptyString> matteType, std::vector<NonEmptyString> properties, std::vector<NonEmptyString> effects, std::optional<NonEmptyString> data)
        : id(id), createdAt(createdAt), updatedAt(updatedAt), name(name), layerType(layerType), visible(visible), locked(locked), threeD(threeD), motionBlur(motionBlur), startFrame(startFrame), endFrame(endFrame), parentId(parentId), blendMode(blendMode), opacity(opacity), transform(transform), masks(masks), matteType(matteType), properties(properties), effects(effects), data(data) {}
};"""

instance : EmitCpp23 EffectParameter where
  typeName := "EffectParameter"
  typeDecl := """struct EffectParameter {
    NonEmptyString id;
    NonEmptyString name;
    PropertyValueType parameterType;
    std::string value;
    
    EffectParameter(NonEmptyString id, NonEmptyString name, PropertyValueType parameterType, std::string value)
        : id(id), name(name), parameterType(parameterType), value(value) {}
};"""

instance : EmitCpp23 EffectInstance where
  typeName := "EffectInstance"
  typeDecl := """struct EffectInstance {
    NonEmptyString id;
    NonNegativeFloat createdAt;
    NonNegativeFloat updatedAt;
    EffectType effectType;
    bool enabled;
    std::vector<NonEmptyString> parameters;
    
    EffectInstance(NonEmptyString id, NonNegativeFloat createdAt, NonNegativeFloat updatedAt, EffectType effectType, bool enabled, std::vector<NonEmptyString> parameters)
        : id(id), createdAt(createdAt), updatedAt(updatedAt), effectType(effectType), enabled(enabled), parameters(parameters) {}
};"""

instance : EmitCpp23 EffectPreset where
  typeName := "EffectPreset"
  typeDecl := """struct EffectPreset {
    NonEmptyString id;
    NonEmptyString name;
    EffectType effectType;
    std::string parameters;
    
    EffectPreset(NonEmptyString id, NonEmptyString name, EffectType effectType, std::string parameters)
        : id(id), name(name), effectType(effectType), parameters(parameters) {}
};"""

-- ProjectMetadata
instance : EmitCpp23 ProjectMetadata where
  typeName := "ProjectMetadata"
  typeDecl := """struct ProjectMetadata {
    NonEmptyString name;
    NonEmptyString created;
    NonEmptyString modified;
    std::optional<NonEmptyString> author;
    NonEmptyString version;
    
    ProjectMetadata(NonEmptyString name, NonEmptyString created, NonEmptyString modified, std::optional<NonEmptyString> author, NonEmptyString version)
        : name(name), created(created), modified(modified), author(author), version(version) {}
};"""

-- ProjectSettings
instance : EmitCpp23 ProjectSettings where
  typeName := "ProjectSettings"
  typeDecl := """struct ProjectSettings {
    bool autoSave;
    NonNegativeFloat autoSaveInterval;
    CompositionSettings defaultCompositionSettings;
    
    ProjectSettings(bool autoSave, NonNegativeFloat autoSaveInterval, CompositionSettings defaultCompositionSettings)
        : autoSave(autoSave), autoSaveInterval(autoSaveInterval), defaultCompositionSettings(defaultCompositionSettings) {}
};"""

-- Project
instance : EmitCpp23 Project where
  typeName := "Project"
  typeDecl := """struct Project {
    NonEmptyString id;
    NonNegativeFloat createdAt;
    NonNegativeFloat updatedAt;
    NonEmptyString name;
    ProjectMetadata metadata;
    ProjectSettings settings;
    NonEmptyString mainCompositionId;
    std::vector<NonEmptyString> compositionIds;
    std::vector<NonEmptyString> assetIds;
    
    Project(NonEmptyString id, NonNegativeFloat createdAt, NonNegativeFloat updatedAt, NonEmptyString name, ProjectMetadata metadata, ProjectSettings settings, NonEmptyString mainCompositionId, std::vector<NonEmptyString> compositionIds, std::vector<NonEmptyString> assetIds)
        : id(id), createdAt(createdAt), updatedAt(updatedAt), name(name), metadata(metadata), settings(settings), mainCompositionId(mainCompositionId), compositionIds(compositionIds), assetIds(assetIds) {}
};"""

-- AssetType
instance : EmitCpp23 AssetType where
  typeName := "AssetType"
  typeDecl := """enum class AssetType {
    depthMap,
    image,
    video,
    audio,
    model,
    pointcloud,
    texture,
    material,
    hdri,
    svg,
    sprite,
    spritesheet,
    lut
};"""

-- AssetSource
instance : EmitCpp23 AssetSource where
  typeName := "AssetSource"
  typeDecl := """enum class AssetSource {
    comfyuiNode,
    file,
    generated,
    url
};"""

-- AssetMetadata
instance : EmitCpp23 AssetMetadata where
  typeName := "AssetMetadata"
  typeDecl := """struct AssetMetadata {
    PositiveInt width;
    PositiveInt height;
    std::optional<NonEmptyString> filename;
    std::optional<FrameNumber> frameCount;
    std::optional<NonNegativeFloat> duration;
    std::optional<PositiveFloat> fps;
    std::optional<bool> hasAudio;
    std::optional<PositiveInt> audioChannels;
    std::optional<PositiveInt> sampleRate;
    std::optional<NonEmptyString> modelFormat;
    std::optional<FrameNumber> modelMeshCount;
    std::optional<FrameNumber> modelVertexCount;
    std::optional<NonEmptyString> pointCloudFormat;
    std::optional<FrameNumber> pointCount;
    
    AssetMetadata(PositiveInt width, PositiveInt height, std::optional<NonEmptyString> filename, std::optional<FrameNumber> frameCount, std::optional<NonNegativeFloat> duration, std::optional<PositiveFloat> fps, std::optional<bool> hasAudio, std::optional<PositiveInt> audioChannels, std::optional<PositiveInt> sampleRate, std::optional<NonEmptyString> modelFormat, std::optional<FrameNumber> modelMeshCount, std::optional<FrameNumber> modelVertexCount, std::optional<NonEmptyString> pointCloudFormat, std::optional<FrameNumber> pointCount)
        : width(width), height(height), filename(filename), frameCount(frameCount), duration(duration), fps(fps), hasAudio(hasAudio), audioChannels(audioChannels), sampleRate(sampleRate), modelFormat(modelFormat), modelMeshCount(modelMeshCount), modelVertexCount(modelVertexCount), pointCloudFormat(pointCloudFormat), pointCount(pointCount) {}
};"""

-- Asset
instance : EmitCpp23 Asset where
  typeName := "Asset"
  typeDecl := """struct Asset {
    NonEmptyString id;
    NonNegativeFloat createdAt;
    NonNegativeFloat updatedAt;
    NonEmptyString name;
    AssetType assetType;
    AssetSource source;
    NonEmptyString data;
    AssetMetadata metadata;
    std::optional<NonEmptyString> nodeId;
    
    Asset(NonEmptyString id, NonNegativeFloat createdAt, NonNegativeFloat updatedAt, NonEmptyString name, AssetType assetType, AssetSource source, NonEmptyString data, AssetMetadata metadata, std::optional<NonEmptyString> nodeId)
        : id(id), createdAt(createdAt), updatedAt(updatedAt), name(name), assetType(assetType), source(source), data(data), metadata(metadata), nodeId(nodeId) {}
};"""

-- AssetReference
instance : EmitCpp23 AssetReference where
  typeName := "AssetReference"
  typeDecl := """struct AssetReference {
    NonEmptyString id;
    AssetType assetType;
    AssetSource source;
    
    AssetReference(NonEmptyString id, AssetType assetType, AssetSource source)
        : id(id), assetType(assetType), source(source) {}
};"""

-- ExportJobStatus
instance : EmitCpp23 ExportJobStatus where
  typeName := "ExportJobStatus"
  typeDecl := """enum class ExportJobStatus {
    queued,
    processing,
    completed,
    failed,
    cancelled
};"""

-- ExportConfig
instance : EmitCpp23 ExportConfig where
  typeName := "ExportConfig"
  typeDecl := """struct ExportConfig {
    ExportTarget target;
    PositiveInt width;
    PositiveInt height;
    FrameNumber frameCount;
    PositiveFloat fps;
    FrameNumber startFrame;
    FrameNumber endFrame;
    NonEmptyString outputDir;
    NonEmptyString filenamePrefix;
    bool exportDepthMap;
    bool exportControlImages;
    bool exportCameraData;
    bool exportReferenceFrame;
    bool exportLastFrame;
    NonEmptyString prompt;
    NonEmptyString negativePrompt;
    
    ExportConfig(ExportTarget target, PositiveInt width, PositiveInt height, FrameNumber frameCount, PositiveFloat fps, FrameNumber startFrame, FrameNumber endFrame, NonEmptyString outputDir, NonEmptyString filenamePrefix, bool exportDepthMap, bool exportControlImages, bool exportCameraData, bool exportReferenceFrame, bool exportLastFrame, NonEmptyString prompt, NonEmptyString negativePrompt)
        : target(target), width(width), height(height), frameCount(frameCount), fps(fps), startFrame(startFrame), endFrame(endFrame), outputDir(outputDir), filenamePrefix(filenamePrefix), exportDepthMap(exportDepthMap), exportControlImages(exportControlImages), exportCameraData(exportCameraData), exportReferenceFrame(exportReferenceFrame), exportLastFrame(exportLastFrame), prompt(prompt), negativePrompt(negativePrompt) {}
};"""

-- ExportTemplate
instance : EmitCpp23 ExportTemplate where
  typeName := "ExportTemplate"
  typeDecl := """struct ExportTemplate {
    NonEmptyString id;
    NonEmptyString name;
    ExportConfig config;
    
    ExportTemplate(NonEmptyString id, NonEmptyString name, ExportConfig config)
        : id(id), name(name), config(config) {}
};"""

-- ExportJob
instance : EmitCpp23 ExportJob where
  typeName := "ExportJob"
  typeDecl := """struct ExportJob {
    NonEmptyString id;
    NonNegativeFloat createdAt;
    NonNegativeFloat updatedAt;
    NonEmptyString compositionId;
    ExportConfig config;
    ExportJobStatus status;
    NormalizedValue progress;
    std::string outputFiles;
    std::optional<NonEmptyString> errorMessage;
    
    ExportJob(NonEmptyString id, NonNegativeFloat createdAt, NonNegativeFloat updatedAt, NonEmptyString compositionId, ExportConfig config, ExportJobStatus status, NormalizedValue progress, std::string outputFiles, std::optional<NonEmptyString> errorMessage)
        : id(id), createdAt(createdAt), updatedAt(updatedAt), compositionId(compositionId), config(config), status(status), progress(progress), outputFiles(outputFiles), errorMessage(errorMessage) {}
};"""

-- CameraControlType
instance : EmitCpp23 CameraControlType where
  typeName := "CameraControlType"
  typeDecl := """enum class CameraControlType {
    oneNode,
    twoNode
};"""

-- AutoOrientMode
instance : EmitCpp23 AutoOrientMode where
  typeName := "AutoOrientMode"
  typeDecl := """enum class AutoOrientMode {
    off,
    orientAlongPath,
    orientTowardsPoi
};"""

-- DepthOfField
instance : EmitCpp23 DepthOfField where
  typeName := "DepthOfField"
  typeDecl := """struct DepthOfField {
    bool enabled;
    float focusDistance;
    float aperture;
    float fStop;
    NormalizedValue blurLevel;
    bool lockToZoom;
    
    DepthOfField(bool enabled, float focusDistance, float aperture, float fStop, NormalizedValue blurLevel, bool lockToZoom)
        : enabled(enabled), focusDistance(focusDistance), aperture(aperture), fStop(fStop), blurLevel(blurLevel), lockToZoom(lockToZoom) {}
};"""

-- Camera3D
instance : EmitCpp23 Camera3D where
  typeName := "Camera3D"
  typeDecl := """struct Camera3D {
    NonEmptyString id;
    NonEmptyString name;
    CameraControlType cameraControlType;
    CameraType cameraType;
    Vec3 position;
    std::optional<Vec3> pointOfInterest;
    Vec3 orientation;
    float xRotation;
    float yRotation;
    float zRotation;
    PositiveFloat zoom;
    PositiveFloat focalLength;
    PositiveFloat angleOfView;
    PositiveFloat filmSize;
    DepthOfField depthOfField;
    AutoOrientMode autoOrient;
    NonNegativeFloat nearClip;
    NonNegativeFloat farClip;
    
    Camera3D(NonEmptyString id, NonEmptyString name, CameraControlType cameraControlType, CameraType cameraType, Vec3 position, std::optional<Vec3> pointOfInterest, Vec3 orientation, float xRotation, float yRotation, float zRotation, PositiveFloat zoom, PositiveFloat focalLength, PositiveFloat angleOfView, PositiveFloat filmSize, DepthOfField depthOfField, AutoOrientMode autoOrient, NonNegativeFloat nearClip, NonNegativeFloat farClip)
        : id(id), name(name), cameraControlType(cameraControlType), cameraType(cameraType), position(position), pointOfInterest(pointOfInterest), orientation(orientation), xRotation(xRotation), yRotation(yRotation), zRotation(zRotation), zoom(zoom), focalLength(focalLength), angleOfView(angleOfView), filmSize(filmSize), depthOfField(depthOfField), autoOrient(autoOrient), nearClip(nearClip), farClip(farClip) {}
};"""

-- CameraKeyframe
instance : EmitCpp23 CameraKeyframe where
  typeName := "CameraKeyframe"
  typeDecl := """struct CameraKeyframe {
    FrameNumber frame;
    std::optional<Vec3> position;
    std::optional<Vec3> pointOfInterest;
    std::optional<Vec3> orientation;
    std::optional<float> xRotation;
    std::optional<float> yRotation;
    std::optional<float> zRotation;
    std::optional<PositiveFloat> zoom;
    std::optional<PositiveFloat> focalLength;
    
    CameraKeyframe(FrameNumber frame, std::optional<Vec3> position, std::optional<Vec3> pointOfInterest, std::optional<Vec3> orientation, std::optional<float> xRotation, std::optional<float> yRotation, std::optional<float> zRotation, std::optional<PositiveFloat> zoom, std::optional<PositiveFloat> focalLength)
        : frame(frame), position(position), pointOfInterest(pointOfInterest), orientation(orientation), xRotation(xRotation), yRotation(yRotation), zRotation(zRotation), zoom(zoom), focalLength(focalLength) {}
};"""

-- CameraPath
instance : EmitCpp23 CameraPath where
  typeName := "CameraPath"
  typeDecl := """struct CameraPath {
    NonEmptyString id;
    NonEmptyString cameraId;
    std::vector<CameraKeyframe> keyframes;
    
    CameraPath(NonEmptyString id, NonEmptyString cameraId, std::vector<CameraKeyframe> keyframes)
        : id(id), cameraId(cameraId), keyframes(keyframes) {}
};"""

-- FontConfig
instance : EmitCpp23 FontConfig where
  typeName := "FontConfig"
  typeDecl := """struct FontConfig {
    NonEmptyString fontFamily;
    PositiveFloat fontSize;
    FontWeight fontWeight;
    FontStyle fontStyle;
    
    FontConfig(NonEmptyString fontFamily, PositiveFloat fontSize, FontWeight fontWeight, FontStyle fontStyle)
        : fontFamily(fontFamily), fontSize(fontSize), fontWeight(fontWeight), fontStyle(fontStyle) {}
};"""

-- TextAnimatorProperties
instance : EmitCpp23 TextAnimatorProperties where
  typeName := "TextAnimatorProperties"
  typeDecl := """struct TextAnimatorProperties {
    std::optional<Vec2> position;
    std::optional<float> rotation;
    std::optional<Vec2> scale;
    std::optional<NormalizedValue> opacity;
    std::optional<NonEmptyString> fillColor;
    std::optional<NonEmptyString> strokeColor;
    std::optional<NonNegativeFloat> strokeWidth;
    std::optional<float> tracking;
    std::optional<Vec2> blur;
    
    TextAnimatorProperties(std::optional<Vec2> position, std::optional<float> rotation, std::optional<Vec2> scale, std::optional<NormalizedValue> opacity, std::optional<NonEmptyString> fillColor, std::optional<NonEmptyString> strokeColor, std::optional<NonNegativeFloat> strokeWidth, std::optional<float> tracking, std::optional<Vec2> blur)
        : position(position), rotation(rotation), scale(scale), opacity(opacity), fillColor(fillColor), strokeColor(strokeColor), strokeWidth(strokeWidth), tracking(tracking), blur(blur) {}
};"""

-- TextRangeSelector
instance : EmitCpp23 TextRangeSelector where
  typeName := "TextRangeSelector"
  typeDecl := """struct TextRangeSelector {
    TextRangeMode mode;
    NonEmptyString start;
    NonEmptyString end;
    NonEmptyString offset;
    TextRangeBasedOn basedOn;
    TextRangeShape shape;
    bool randomizeOrder;
    FrameNumber randomSeed;
    
    TextRangeSelector(TextRangeMode mode, NonEmptyString start, NonEmptyString end, NonEmptyString offset, TextRangeBasedOn basedOn, TextRangeShape shape, bool randomizeOrder, FrameNumber randomSeed)
        : mode(mode), start(start), end(end), offset(offset), basedOn(basedOn), shape(shape), randomizeOrder(randomizeOrder), randomSeed(randomSeed) {}
};"""

-- TextAnimator
instance : EmitCpp23 TextAnimator where
  typeName := "TextAnimator"
  typeDecl := """struct TextAnimator {
    NonEmptyString id;
    NonEmptyString name;
    bool enabled;
    TextRangeSelector rangeSelector;
    TextAnimatorProperties properties;
    
    TextAnimator(NonEmptyString id, NonEmptyString name, bool enabled, TextRangeSelector rangeSelector, TextAnimatorProperties properties)
        : id(id), name(name), enabled(enabled), rangeSelector(rangeSelector), properties(properties) {}
};"""

-- TextLayerData
instance : EmitCpp23 TextLayerData where
  typeName := "TextLayerData"
  typeDecl := """struct TextLayerData {
    NonEmptyString text;
    FontConfig fontConfig;
    NonEmptyString fill;
    NonEmptyString stroke;
    NonNegativeFloat strokeWidth;
    float tracking;
    float lineSpacing;
    TextAlign textAlign;
    std::optional<NonEmptyString> pathLayerId;
    std::vector<NonEmptyString> animators;
    
    TextLayerData(NonEmptyString text, FontConfig fontConfig, NonEmptyString fill, NonEmptyString stroke, NonNegativeFloat strokeWidth, float tracking, float lineSpacing, TextAlign textAlign, std::optional<NonEmptyString> pathLayerId, std::vector<NonEmptyString> animators)
        : text(text), fontConfig(fontConfig), fill(fill), stroke(stroke), strokeWidth(strokeWidth), tracking(tracking), lineSpacing(lineSpacing), textAlign(textAlign), pathLayerId(pathLayerId), animators(animators) {}
};"""

-- TextShaper
instance : EmitCpp23 TextShaper where
  typeName := "TextShaper"
  typeDecl := """struct TextShaper {
    NonEmptyString id;
    NonEmptyString name;
    bool enabled;
    std::string config;
    
    TextShaper(NonEmptyString id, NonEmptyString name, bool enabled, std::string config)
        : id(id), name(name), enabled(enabled), config(config) {}
};"""

-- BeatData
instance : EmitCpp23 BeatData where
  typeName := "BeatData"
  typeDecl := """struct BeatData {
    FrameNumber frame;
    NormalizedValue amplitude;
    std::optional<NormalizedValue> frequency;
    
    BeatData(FrameNumber frame, NormalizedValue amplitude, std::optional<NormalizedValue> frequency)
        : frame(frame), amplitude(amplitude), frequency(frequency) {}
};"""

-- AudioAnalysis
instance : EmitCpp23 AudioAnalysis where
  typeName := "AudioAnalysis"
  typeDecl := """struct AudioAnalysis {
    NonNegativeFloat duration;
    PositiveInt sampleRate;
    PositiveInt channels;
    std::vector<FrameNumber> beats;
    std::vector<std::pair<FrameNumber, NormalizedValue>> peaks;
    std::string frequencies;
    
    AudioAnalysis(NonNegativeFloat duration, PositiveInt sampleRate, PositiveInt channels, std::vector<FrameNumber> beats, std::vector<std::pair<FrameNumber, NormalizedValue>> peaks, std::string frequencies)
        : duration(duration), sampleRate(sampleRate), channels(channels), beats(beats), peaks(peaks), frequencies(frequencies) {}
};"""

-- AudioReactivity
instance : EmitCpp23 AudioReactivity where
  typeName := "AudioReactivity"
  typeDecl := """struct AudioReactivity {
    bool enabled;
    BeatDetectionMethod method;
    NonEmptyString targetProperty;
    NormalizedValue sensitivity;
    NormalizedValue smoothing;
    
    AudioReactivity(bool enabled, BeatDetectionMethod method, NonEmptyString targetProperty, NormalizedValue sensitivity, NormalizedValue smoothing)
        : enabled(enabled), method(method), targetProperty(targetProperty), sensitivity(sensitivity), smoothing(smoothing) {}
};"""

-- AudioTrack
instance : EmitCpp23 AudioTrack where
  typeName := "AudioTrack"
  typeDecl := """struct AudioTrack {
    NonEmptyString id;
    NonEmptyString name;
    NonEmptyString assetId;
    NormalizedValue volume;
    float pan;
    NonNegativeFloat startTime;
    std::optional<AudioAnalysis> analysis;
    std::optional<AudioReactivity> reactivity;
    
    AudioTrack(NonEmptyString id, NonEmptyString name, NonEmptyString assetId, NormalizedValue volume, float pan, NonNegativeFloat startTime, std::optional<AudioAnalysis> analysis, std::optional<AudioReactivity> reactivity)
        : id(id), name(name), assetId(assetId), volume(volume), pan(pan), startTime(startTime), analysis(analysis), reactivity(reactivity) {}
};"""

-- ParticleEmitter
instance : EmitCpp23 ParticleEmitter where
  typeName := "ParticleEmitter"
  typeDecl := """struct ParticleEmitter {
    NonEmptyString id;
    EmitterShape emitterShape;
    Vec2 position;
    PositiveFloat rate;
    PositiveFloat lifetime;
    PositiveFloat speed;
    float direction;
    float spread;
    std::optional<NonEmptyString> pathLayerId;
    
    ParticleEmitter(NonEmptyString id, EmitterShape emitterShape, Vec2 position, PositiveFloat rate, PositiveFloat lifetime, PositiveFloat speed, float direction, float spread, std::optional<NonEmptyString> pathLayerId)
        : id(id), emitterShape(emitterShape), position(position), rate(rate), lifetime(lifetime), speed(speed), direction(direction), spread(spread), pathLayerId(pathLayerId) {}
};"""

-- ForceType
instance : EmitCpp23 ForceType where
  typeName := "ForceType"
  typeDecl := """enum class ForceType {
    gravity,
    wind,
    attraction,
    explosion,
    buoyancy,
    vortex,
    drag
};"""

-- Force
instance : EmitCpp23 Force where
  typeName := "Force"
  typeDecl := """struct Force {
    NonEmptyString id;
    NonEmptyString name;
    ForceType forceType;
    float strength;
    Vec2 direction;
    std::optional<Vec2> position;
    bool enabled;
    
    Force(NonEmptyString id, NonEmptyString name, ForceType forceType, float strength, Vec2 direction, std::optional<Vec2> position, bool enabled)
        : id(id), name(name), forceType(forceType), strength(strength), direction(direction), position(position), enabled(enabled) {}
};"""

-- CollisionConfig
instance : EmitCpp23 CollisionConfig where
  typeName := "CollisionConfig"
  typeDecl := """struct CollisionConfig {
    bool enabled;
    std::optional<NonEmptyString> depthLayerId;
    NormalizedValue bounciness;
    NormalizedValue friction;
    
    CollisionConfig(bool enabled, std::optional<NonEmptyString> depthLayerId, NormalizedValue bounciness, NormalizedValue friction)
        : enabled(enabled), depthLayerId(depthLayerId), bounciness(bounciness), friction(friction) {}
};"""

-- ParticleRenderer
instance : EmitCpp23 ParticleRenderer where
  typeName := "ParticleRenderer"
  typeDecl := """struct ParticleRenderer {
    PositiveFloat startSize;
    PositiveFloat endSize;
    NonEmptyString startColor;
    NonEmptyString endColor;
    NormalizedValue startOpacity;
    NormalizedValue endOpacity;
    BlendMode blendMode;
    
    ParticleRenderer(PositiveFloat startSize, PositiveFloat endSize, NonEmptyString startColor, NonEmptyString endColor, NormalizedValue startOpacity, NormalizedValue endOpacity, BlendMode blendMode)
        : startSize(startSize), endSize(endSize), startColor(startColor), endColor(endColor), startOpacity(startOpacity), endOpacity(endOpacity), blendMode(blendMode) {}
};"""

-- ParticleSystem
instance : EmitCpp23 ParticleSystem where
  typeName := "ParticleSystem"
  typeDecl := """struct ParticleSystem {
    NonEmptyString id;
    NonEmptyString name;
    NonEmptyString emitter;
    ParticleRenderer renderer;
    std::vector<NonEmptyString> forces;
    std::optional<CollisionConfig> collision;
    bool enabled;
    
    ParticleSystem(NonEmptyString id, NonEmptyString name, NonEmptyString emitter, ParticleRenderer renderer, std::vector<NonEmptyString> forces, std::optional<CollisionConfig> collision, bool enabled)
        : id(id), name(name), emitter(emitter), renderer(renderer), forces(forces), collision(collision), enabled(enabled) {}
};"""

-- BodyType
instance : EmitCpp23 BodyType where
  typeName := "BodyType"
  typeDecl := """enum class BodyType {
    static,
    dynamic,
    kinematic,
    dormant
};"""

-- JointType
instance : EmitCpp23 JointType where
  typeName := "JointType"
  typeDecl := """enum class JointType {
    pivot,
    spring,
    distance,
    piston,
    wheel,
    weld,
    blob,
    rope
};"""

-- PhysicsMaterial
instance : EmitCpp23 PhysicsMaterial where
  typeName := "PhysicsMaterial"
  typeDecl := """struct PhysicsMaterial {
    NormalizedValue restitution;
    NormalizedValue friction;
    
    PhysicsMaterial(NormalizedValue restitution, NormalizedValue friction)
        : restitution(restitution), friction(friction) {}
};"""

-- RigidBody
instance : EmitCpp23 RigidBody where
  typeName := "RigidBody"
  typeDecl := """struct RigidBody {
    NonEmptyString id;
    NonEmptyString layerId;
    BodyType bodyType;
    PositiveFloat mass;
    Vec2 position;
    float rotation;
    PhysicsMaterial material;
    bool enabled;
    
    RigidBody(NonEmptyString id, NonEmptyString layerId, BodyType bodyType, PositiveFloat mass, Vec2 position, float rotation, PhysicsMaterial material, bool enabled)
        : id(id), layerId(layerId), bodyType(bodyType), mass(mass), position(position), rotation(rotation), material(material), enabled(enabled) {}
};"""

-- Joint
instance : EmitCpp23 Joint where
  typeName := "Joint"
  typeDecl := """struct Joint {
    NonEmptyString id;
    NonEmptyString name;
    NonEmptyString bodyA;
    NonEmptyString bodyB;
    JointType jointType;
    Vec2 anchorA;
    Vec2 anchorB;
    bool enabled;
    
    Joint(NonEmptyString id, NonEmptyString name, NonEmptyString bodyA, NonEmptyString bodyB, JointType jointType, Vec2 anchorA, Vec2 anchorB, bool enabled)
        : id(id), name(name), bodyA(bodyA), bodyB(bodyB), jointType(jointType), anchorA(anchorA), anchorB(anchorB), enabled(enabled) {}
};"""

-- PhysicsSpace
instance : EmitCpp23 PhysicsSpace where
  typeName := "PhysicsSpace"
  typeDecl := """struct PhysicsSpace {
    NonEmptyString id;
    NonEmptyString name;
    Vec2 gravity;
    std::vector<NonEmptyString> bodies;
    std::vector<NonEmptyString> joints;
    bool enabled;
    
    PhysicsSpace(NonEmptyString id, NonEmptyString name, Vec2 gravity, std::vector<NonEmptyString> bodies, std::vector<NonEmptyString> joints, bool enabled)
        : id(id), name(name), gravity(gravity), bodies(bodies), joints(joints), enabled(enabled) {}
};"""

-- Ragdoll
instance : EmitCpp23 Ragdoll where
  typeName := "Ragdoll"
  typeDecl := """struct Ragdoll {
    NonEmptyString id;
    NonEmptyString name;
    NonEmptyString rootBody;
    std::vector<NonEmptyString> bodies;
    std::vector<NonEmptyString> joints;
    bool enabled;
    
    Ragdoll(NonEmptyString id, NonEmptyString name, NonEmptyString rootBody, std::vector<NonEmptyString> bodies, std::vector<NonEmptyString> joints, bool enabled)
        : id(id), name(name), rootBody(rootBody), bodies(bodies), joints(joints), enabled(enabled) {}
};"""

-- Cloth
instance : EmitCpp23 Cloth where
  typeName := "Cloth"
  typeDecl := """struct Cloth {
    NonEmptyString id;
    NonEmptyString name;
    NonEmptyString layerId;
    PositiveInt width;
    PositiveInt height;
    NormalizedValue stiffness;
    NormalizedValue damping;
    bool enabled;
    
    Cloth(NonEmptyString id, NonEmptyString name, NonEmptyString layerId, PositiveInt width, PositiveInt height, NormalizedValue stiffness, NormalizedValue damping, bool enabled)
        : id(id), name(name), layerId(layerId), width(width), height(height), stiffness(stiffness), damping(damping), enabled(enabled) {}
};"""

/-! ## Full Module Generation -/

/-! ## C++23 Header Generation -/

def cpp23Header : String :=
  let header := """/*
 * AUTO-GENERATED FROM LEAN TYPE DEFINITIONS
 * DO NOT EDIT - regenerate with `lake exe extract cpp23`
 * 
 * Every type here has a corresponding Extractable instance in Lean
 * with a proven roundtrip theorem. The validation in constructors
 * mirrors the Lean type constraints.
 * 
 * Requires C++23 or later.
 */

#pragma once

#include <cstdint>
#include <cmath>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>
#include <optional>
#include <utility>

namespace Lattice {

"""
  let footer := """
} // namespace Lattice
"""
  let types := [
    -- Layer 0 Primitives
    EmitCpp23.typeDecl (α := NonEmptyString),
    EmitCpp23.typeDecl (α := PositiveInt),
    EmitCpp23.typeDecl (α := PositiveFloat),
    EmitCpp23.typeDecl (α := NonNegativeFloat),
    EmitCpp23.typeDecl (α := Percentage),
    EmitCpp23.typeDecl (α := NormalizedValue),
    EmitCpp23.typeDecl (α := FrameNumber),
    EmitCpp23.typeDecl (α := Vec2),
    EmitCpp23.typeDecl (α := Vec3),
    EmitCpp23.typeDecl (α := Vec4),
    EmitCpp23.typeDecl (α := Matrix3x3),
    EmitCpp23.typeDecl (α := Matrix4x4),
    -- Layer 1 Enums
    EmitCpp23.typeDecl (α := LayerType),
    EmitCpp23.typeDecl (α := BlendMode),
    EmitCpp23.typeDecl (α := MaskMode),
    EmitCpp23.typeDecl (α := LayerStatus),
    EmitCpp23.typeDecl (α := InterpolationType),
    EmitCpp23.typeDecl (α := EasingType),
    EmitCpp23.typeDecl (α := KeyframeType),
    EmitCpp23.typeDecl (α := EffectCategory),
    EmitCpp23.typeDecl (α := EffectStatus),
    EmitCpp23.typeDecl (α := ColorSpace),
    EmitCpp23.typeDecl (α := ColorFormat),
    EmitCpp23.typeDecl (α := TransferFunction),
    EmitCpp23.typeDecl (α := ExportFormat),
    EmitCpp23.typeDecl (α := ExportStatus),
    EmitCpp23.typeDecl (α := CameraType),
    EmitCpp23.typeDecl (α := ProjectionType),
    EmitCpp23.typeDecl (α := TextAlign),
    EmitCpp23.typeDecl (α := TextDirection),
    EmitCpp23.typeDecl (α := FontStyle),
    EmitCpp23.typeDecl (α := FontWeight),
    EmitCpp23.typeDecl (α := JobStatus),
    EmitCpp23.typeDecl (α := RenderStatus),
    EmitCpp23.typeDecl (α := QualityMode),
    EmitCpp23.typeDecl (α := ValidationResult),
    EmitCpp23.typeDecl (α := Severity),
    EmitCpp23.typeDecl (α := EffectType),
    EmitCpp23.typeDecl (α := EmitterShape),
    EmitCpp23.typeDecl (α := ParticleShape),
    EmitCpp23.typeDecl (α := CollisionType),
    EmitCpp23.typeDecl (α := MaterialType),
    EmitCpp23.typeDecl (α := AudioFormat),
    EmitCpp23.typeDecl (α := AudioChannel),
    EmitCpp23.typeDecl (α := BeatDetectionMethod),
    EmitCpp23.typeDecl (α := ExportTarget),
    EmitCpp23.typeDecl (α := DepthOfFieldMode),
    EmitCpp23.typeDecl (α := ModelType),
    EmitCpp23.typeDecl (α := PreprocessorType),
    EmitCpp23.typeDecl (α := SegmentationMode),
    EmitCpp23.typeDecl (α := AuditCategory),
    EmitCpp23.typeDecl (α := RateLimitScope),
    EmitCpp23.typeDecl (α := SyncStatus),
    EmitCpp23.typeDecl (α := ExpressionType),
    EmitCpp23.typeDecl (α := TextRangeMode),
    EmitCpp23.typeDecl (α := TextRangeBasedOn),
    EmitCpp23.typeDecl (α := TextRangeShape),
    -- Layer 2A Events
    EmitCpp23.typeDecl (α := BaseEvent),
    EmitCpp23.typeDecl (α := CompositionCreated),
    EmitCpp23.typeDecl (α := CompositionDeleted),
    EmitCpp23.typeDecl (α := CompositionRendered),
    EmitCpp23.typeDecl (α := LayerCreated),
    EmitCpp23.typeDecl (α := LayerDeleted),
    EmitCpp23.typeDecl (α := LayerMoved),
    EmitCpp23.typeDecl (α := LayerDuplicated),
    EmitCpp23.typeDecl (α := LayerVisibilityChanged),
    EmitCpp23.typeDecl (α := KeyframeAdded),
    EmitCpp23.typeDecl (α := KeyframeRemoved),
    EmitCpp23.typeDecl (α := KeyframeModified),
    EmitCpp23.typeDecl (α := KeyframeInterpolationChanged),
    EmitCpp23.typeDecl (α := PropertyAnimated),
    EmitCpp23.typeDecl (α := PropertyExpressionChanged),
    EmitCpp23.typeDecl (α := PropertyDriverAdded),
    EmitCpp23.typeDecl (α := EffectAdded),
    EmitCpp23.typeDecl (α := EffectRemoved),
    EmitCpp23.typeDecl (α := EffectParameterChanged),
    EmitCpp23.typeDecl (α := ExportStarted),
    EmitCpp23.typeDecl (α := ExportProgress),
    EmitCpp23.typeDecl (α := ExportCompleted),
    EmitCpp23.typeDecl (α := ExportFailed),
    EmitCpp23.typeDecl (α := RenderJobQueued),
    EmitCpp23.typeDecl (α := RenderJobCompleted),
    EmitCpp23.typeDecl (α := CacheCleared),
    EmitCpp23.typeDecl (α := ErrorOccurred),
    -- Layer 2B Metrics
    EmitCpp23.typeDecl (α := AggregationType),
    EmitCpp23.typeDecl (α := TimeGrain),
    EmitCpp23.typeDecl (α := MetricDataType),
    EmitCpp23.typeDecl (α := MetricCategory),
    EmitCpp23.typeDecl (α := MetricDefinition),
    EmitCpp23.typeDecl (α := FrameRenderTime),
    EmitCpp23.typeDecl (α := TotalRenderTime),
    EmitCpp23.typeDecl (α := MemoryUsage),
    EmitCpp23.typeDecl (α := GpuUsage),
    EmitCpp23.typeDecl (α := CacheHitRate),
    EmitCpp23.typeDecl (α := CacheSize),
    EmitCpp23.typeDecl (α := Fps),
    EmitCpp23.typeDecl (α := DroppedFrames),
    EmitCpp23.typeDecl (α := PlaybackLatency),
    EmitCpp23.typeDecl (α := ScrubLatency),
    EmitCpp23.typeDecl (α := CompressionRatio),
    EmitCpp23.typeDecl (α := Bitrate),
    EmitCpp23.typeDecl (α := ColorAccuracy),
    EmitCpp23.typeDecl (α := MotionBlurQuality),
    EmitCpp23.typeDecl (α := VramUsage),
    EmitCpp23.typeDecl (α := CpuUsage),
    EmitCpp23.typeDecl (α := NetworkBandwidth),
    EmitCpp23.typeDecl (α := StorageUsed),
    EmitCpp23.typeDecl (α := ActionsPerSession),
    EmitCpp23.typeDecl (α := ExportCount),
    EmitCpp23.typeDecl (α := ProjectCount),
    EmitCpp23.typeDecl (α := InferenceTime),
    EmitCpp23.typeDecl (α := ModelLoadTime),
    EmitCpp23.typeDecl (α := TokensUsed),
    EmitCpp23.typeDecl (α := CostUSD),
    -- Layer 3 Triggers
    EmitCpp23.typeDecl (α := ComparisonOperator),
    EmitCpp23.typeDecl (α := PropertyCondition),
    EmitCpp23.typeDecl (α := FrameCondition),
    EmitCpp23.typeDecl (α := AudioCondition),
    EmitCpp23.typeDecl (α := TimeCondition),
    EmitCpp23.typeDecl (α := BaseTrigger),
    EmitCpp23.typeDecl (α := FrameTrigger),
    EmitCpp23.typeDecl (α := PropertyTrigger),
    EmitCpp23.typeDecl (α := AudioTrigger),
    EmitCpp23.typeDecl (α := TimeTrigger),
    EmitCpp23.typeDecl (α := ExpressionTrigger),
    EmitCpp23.typeDecl (α := EventTrigger),
    EmitCpp23.typeDecl (α := CompositeOperator),
    EmitCpp23.typeDecl (α := CompositeTrigger),
    -- Layer 4 Actions
    EmitCpp23.typeDecl (α := ActionResult),
    EmitCpp23.typeDecl (α := RetryPolicy),
    EmitCpp23.typeDecl (α := BaseAction),
    EmitCpp23.typeDecl (α := CreateLayer),
    EmitCpp23.typeDecl (α := DeleteLayer),
    EmitCpp23.typeDecl (α := DuplicateLayer),
    EmitCpp23.typeDecl (α := MoveLayer),
    EmitCpp23.typeDecl (α := SetLayerVisibility),
    EmitCpp23.typeDecl (α := SetLayerOpacity),
    EmitCpp23.typeDecl (α := AddKeyframe),
    EmitCpp23.typeDecl (α := RemoveKeyframe),
    EmitCpp23.typeDecl (α := ModifyKeyframe),
    EmitCpp23.typeDecl (α := SetInterpolation),
    EmitCpp23.typeDecl (α := CopyKeyframes),
    EmitCpp23.typeDecl (α := PasteKeyframes),
    EmitCpp23.typeDecl (α := AnimateProperty),
    EmitCpp23.typeDecl (α := SetPropertyValue),
    EmitCpp23.typeDecl (α := AddExpression),
    EmitCpp23.typeDecl (α := RemoveExpression),
    EmitCpp23.typeDecl (α := AddDriver),
    EmitCpp23.typeDecl (α := AddEffect),
    EmitCpp23.typeDecl (α := RemoveEffect),
    EmitCpp23.typeDecl (α := ModifyEffect),
    EmitCpp23.typeDecl (α := EnableEffect),
    EmitCpp23.typeDecl (α := DisableEffect),
    EmitCpp23.typeDecl (α := CreateComposition),
    EmitCpp23.typeDecl (α := DeleteComposition),
    EmitCpp23.typeDecl (α := SetCompositionSettings),
    EmitCpp23.typeDecl (α := RenderComposition),
    EmitCpp23.typeDecl (α := StartExport),
    EmitCpp23.typeDecl (α := CancelExport),
    EmitCpp23.typeDecl (α := PauseExport),
    EmitCpp23.typeDecl (α := ResumeExport),
    EmitCpp23.typeDecl (α := SetExportSettings),
    EmitCpp23.typeDecl (α := LoadAudio),
    EmitCpp23.typeDecl (α := AnalyzeAudio),
    EmitCpp23.typeDecl (α := SetAudioReactivity),
    EmitCpp23.typeDecl (α := SetCameraPosition),
    EmitCpp23.typeDecl (α := SetCameraRotation),
    EmitCpp23.typeDecl (α := SetCameraFOV),
    EmitCpp23.typeDecl (α := AnimateCamera),
    EmitCpp23.typeDecl (α := SegmentImage),
    EmitCpp23.typeDecl (α := VectorizeImage),
    EmitCpp23.typeDecl (α := DecomposeImage),
    EmitCpp23.typeDecl (α := GenerateDepth),
    EmitCpp23.typeDecl (α := EstimateNormals),
    EmitCpp23.typeDecl (α := ClearCache),
    EmitCpp23.typeDecl (α := OptimizeMemory),
    EmitCpp23.typeDecl (α := SaveProject),
    EmitCpp23.typeDecl (α := LoadProject),
    EmitCpp23.typeDecl (α := Undo),
    EmitCpp23.typeDecl (α := Redo),
    -- Layer 5 Entities
    EmitCpp23.typeDecl (α := ControlMode),
    EmitCpp23.typeDecl (α := BezierHandle),
    EmitCpp23.typeDecl (α := Keyframe),
    EmitCpp23.typeDecl (α := PropertyValueType),
    EmitCpp23.typeDecl (α := PropertyExpression),
    EmitCpp23.typeDecl (α := AnimatableProperty),
    EmitCpp23.typeDecl (α := CompositionSettings),
    EmitCpp23.typeDecl (α := RenderSettings),
    EmitCpp23.typeDecl (α := Composition),
    EmitCpp23.typeDecl (α := LayerTransform),
    EmitCpp23.typeDecl (α := LayerMask),
    EmitCpp23.typeDecl (α := Layer),
    EmitCpp23.typeDecl (α := EffectParameter),
    EmitCpp23.typeDecl (α := EffectInstance),
    EmitCpp23.typeDecl (α := EffectPreset),
    -- Project, Asset, Export
    EmitCpp23.typeDecl (α := ProjectMetadata),
    EmitCpp23.typeDecl (α := ProjectSettings),
    EmitCpp23.typeDecl (α := Project),
    EmitCpp23.typeDecl (α := AssetType),
    EmitCpp23.typeDecl (α := AssetSource),
    EmitCpp23.typeDecl (α := AssetMetadata),
    EmitCpp23.typeDecl (α := Asset),
    EmitCpp23.typeDecl (α := AssetReference),
    EmitCpp23.typeDecl (α := ExportJobStatus),
    EmitCpp23.typeDecl (α := ExportConfig),
    EmitCpp23.typeDecl (α := ExportTemplate),
    EmitCpp23.typeDecl (α := ExportJob),
    -- Camera, Text, Audio
    EmitCpp23.typeDecl (α := CameraControlType),
    EmitCpp23.typeDecl (α := AutoOrientMode),
    EmitCpp23.typeDecl (α := DepthOfField),
    EmitCpp23.typeDecl (α := Camera3D),
    EmitCpp23.typeDecl (α := CameraKeyframe),
    EmitCpp23.typeDecl (α := CameraPath),
    EmitCpp23.typeDecl (α := FontConfig),
    EmitCpp23.typeDecl (α := TextAnimatorProperties),
    EmitCpp23.typeDecl (α := TextRangeSelector),
    EmitCpp23.typeDecl (α := TextAnimator),
    EmitCpp23.typeDecl (α := TextLayerData),
    EmitCpp23.typeDecl (α := TextShaper),
    EmitCpp23.typeDecl (α := BeatData),
    EmitCpp23.typeDecl (α := AudioAnalysis),
    EmitCpp23.typeDecl (α := AudioReactivity),
    EmitCpp23.typeDecl (α := AudioTrack),
    -- Particle and Physics
    EmitCpp23.typeDecl (α := ParticleEmitter),
    EmitCpp23.typeDecl (α := ForceType),
    EmitCpp23.typeDecl (α := Force),
    EmitCpp23.typeDecl (α := CollisionConfig),
    EmitCpp23.typeDecl (α := ParticleRenderer),
    EmitCpp23.typeDecl (α := ParticleSystem),
    EmitCpp23.typeDecl (α := BodyType),
    EmitCpp23.typeDecl (α := JointType),
    EmitCpp23.typeDecl (α := PhysicsMaterial),
    EmitCpp23.typeDecl (α := RigidBody),
    EmitCpp23.typeDecl (α := Joint),
    EmitCpp23.typeDecl (α := PhysicsSpace),
    EmitCpp23.typeDecl (α := Ragdoll),
    EmitCpp23.typeDecl (α := Cloth),
    -- Entity Create/Update models
    EmitCpp23.typeDecl (α := Lattice.Entities.CreateComposition),
    EmitCpp23.typeDecl (α := Lattice.Entities.UpdateComposition),
    EmitCpp23.typeDecl (α := Lattice.Entities.CreateLayer),
    EmitCpp23.typeDecl (α := Lattice.Entities.UpdateLayer),
    EmitCpp23.typeDecl (α := Lattice.Entities.CreateEffectInstance),
    EmitCpp23.typeDecl (α := Lattice.Entities.UpdateEffectInstance),
    EmitCpp23.typeDecl (α := Lattice.Entities.CreateProject),
    EmitCpp23.typeDecl (α := Lattice.Entities.UpdateProject),
    EmitCpp23.typeDecl (α := Lattice.Entities.CreateAsset),
    EmitCpp23.typeDecl (α := Lattice.Entities.UpdateAsset),
    EmitCpp23.typeDecl (α := Lattice.Entities.CreateExportJob),
    EmitCpp23.typeDecl (α := Lattice.Entities.UpdateExportJob)
  ]
  header ++ "\n\n".intercalate types ++ "\n" ++ footer

end Lattice.CodegenCpp23
