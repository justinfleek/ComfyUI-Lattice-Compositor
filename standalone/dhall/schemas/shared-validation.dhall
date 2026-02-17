-- |
-- Module      : Lattice.Schema.SharedValidation
-- Description : Shared validation constants and helpers
--
-- Migrated from ui/src/schemas/shared-validation.ts
-- Defines validation constants and validation function types
-- These are used across all schemas for consistency and security

-- ============================================================================
-- Validation Constants (Fixed - Security Critical)
-- ============================================================================

let MAX_NAME_LENGTH = 200 : Natural

let MAX_DESCRIPTION_LENGTH = 2000 : Natural

let MAX_COMMENT_LENGTH = 5000 : Natural

let MAX_TAG_LENGTH = 50 : Natural

let MAX_TAGS_COUNT = 50 : Natural

let MAX_PATH_LENGTH = 500 : Natural

let MAX_ID_LENGTH = 200 : Natural

let MAX_MIME_TYPE_LENGTH = 100 : Natural

let MAX_FONT_FAMILY_LENGTH = 200 : Natural

let MAX_FONT_STYLE_LENGTH = 100 : Natural

let MAX_URL_LENGTH = 2048 : Natural

let MAX_BASE64_LENGTH = 52428800 : Natural  -- 50MB max base64 data (security limit)

let MAX_SHADER_LENGTH = 100000 : Natural  -- Max shader code length

let MAX_FILENAME_LENGTH = 255 : Natural

let MAX_ANIMATION_NAME_LENGTH = 100 : Natural

let MAX_WARNING_LENGTH = 500 : Natural

-- ============================================================================
-- Configurable Limits (Default values - updated from store at runtime)
-- ============================================================================

let DEFAULT_MAX_DIMENSION = 8192 : Natural

let DEFAULT_MAX_FRAME_COUNT = 10000 : Natural

let DEFAULT_MAX_ARRAY_LENGTH = 100000 : Natural

let DEFAULT_MAX_PARTICLES = 1000000 : Natural

let DEFAULT_MAX_LAYERS = 1000 : Natural

let DEFAULT_MAX_KEYFRAMES_PER_PROPERTY = 10000 : Natural

let DEFAULT_MAX_STRING_LENGTH = 100000 : Natural

let DEFAULT_MAX_FPS = 120 : Natural

-- ============================================================================
-- Validation Limits Configuration
-- ============================================================================

let ValidationLimits =
    { Type =
        { maxDimension : Natural
        , maxFrameCount : Natural
        , maxArrayLength : Natural
        , maxParticles : Natural
        , maxLayers : Natural
        , maxKeyframesPerProperty : Natural
        , maxStringLength : Natural
        , maxFPS : Natural
        }
    , default =
        { maxDimension = DEFAULT_MAX_DIMENSION
        , maxFrameCount = DEFAULT_MAX_FRAME_COUNT
        , maxArrayLength = DEFAULT_MAX_ARRAY_LENGTH
        , maxParticles = DEFAULT_MAX_PARTICLES
        , maxLayers = DEFAULT_MAX_LAYERS
        , maxKeyframesPerProperty = DEFAULT_MAX_KEYFRAMES_PER_PROPERTY
        , maxStringLength = DEFAULT_MAX_STRING_LENGTH
        , maxFPS = DEFAULT_MAX_FPS
        }
    }

-- ============================================================================
-- Export
-- ============================================================================

in  { MAX_NAME_LENGTH
    , MAX_DESCRIPTION_LENGTH
    , MAX_COMMENT_LENGTH
    , MAX_TAG_LENGTH
    , MAX_TAGS_COUNT
    , MAX_PATH_LENGTH
    , MAX_ID_LENGTH
    , MAX_MIME_TYPE_LENGTH
    , MAX_FONT_FAMILY_LENGTH
    , MAX_FONT_STYLE_LENGTH
    , MAX_URL_LENGTH
    , MAX_BASE64_LENGTH
    , MAX_SHADER_LENGTH
    , MAX_FILENAME_LENGTH
    , MAX_ANIMATION_NAME_LENGTH
    , MAX_WARNING_LENGTH
    , DEFAULT_MAX_DIMENSION
    , DEFAULT_MAX_FRAME_COUNT
    , DEFAULT_MAX_ARRAY_LENGTH
    , DEFAULT_MAX_PARTICLES
    , DEFAULT_MAX_LAYERS
    , DEFAULT_MAX_KEYFRAMES_PER_PROPERTY
    , DEFAULT_MAX_STRING_LENGTH
    , DEFAULT_MAX_FPS
    , ValidationLimits
    }
