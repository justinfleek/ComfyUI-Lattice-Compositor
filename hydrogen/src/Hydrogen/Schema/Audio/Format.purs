-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // audio // format
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Audio container and codec formats for import/export.
-- |
-- | Defines container formats (WAV, FLAC, MP3, etc.) and their characteristics.
-- | Used for file I/O, streaming, and interoperability with external systems.
-- |
-- | ## Container Formats
-- | - WAV: Uncompressed PCM, Windows standard
-- | - AIFF: Uncompressed PCM, Apple standard  
-- | - FLAC: Lossless compression, open standard
-- | - MP3: Lossy compression, wide compatibility
-- | - AAC: Lossy compression, modern standard
-- | - OGG: Lossy compression, open container
-- | - Opus: Lossy compression, low latency
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Audio.Buffer (SampleRate, BitDepth, ChannelCount)
-- | - Audio.Time (Duration)
-- |
-- | ## Dependents
-- | - Runtime.Audio (loading/saving files)
-- | - Export.* (legacy format conversion)
-- | - Import.* (legacy format parsing)

module Hydrogen.Schema.Audio.Format
  ( -- * Container Format
    ContainerFormat(..)
  , containerLabel
  , isLossless
  , isCompressed
  , supportsMetadata
  , defaultFileExtension
    
    -- * Codec Format  
  , CodecFormat(..)
  , codecLabel
  , isLossy
  , typicalBitrate
  , qualityToBitrate
    
    -- * Audio File
  , AudioFile
  , audioFile
  , fileFormat
  , fileCodec
  , fileSampleRate
  , fileBitDepth
  , fileChannels
  , fileDuration
  , fileBitrate
  , fileDataSize
    
    -- * Format Options
  , FormatOptions
  , defaultOptions
  , withBitrate
  , withQuality
  , withMetadata
  , isStreaming
    
    -- * Quality Presets
  , QualityPreset(..)
  , presetLabel
  , presetToQuality
  
    -- * File Metadata
  , FileMetadata
  , CoverArt
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (<)
  , (>)
  , (<>)
  )

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Hydrogen.Schema.Audio.Buffer (SampleRate, BitDepth, ChannelCount)
import Hydrogen.Schema.Temporal.Duration (Duration)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // container // format
-- ═════════════════════════════════════════════════════════════════════════════

-- | Audio container format - the file wrapper
data ContainerFormat
  = FormatWAV      -- ^ WAV (PCM)
  | FormatAIFF     -- ^ AIFF (PCM)
  | FormatFLAC     -- ^ FLAC (lossless)
  | FormatMP3      -- ^ MP3 (lossy)
  | FormatAAC      -- ^ AAC (lossy)
  | FormatOGG      -- ^ OGG Vorbis (lossy)
  | FormatOpus     -- ^ Opus (lossy)
  | FormatM4A      -- ^ M4A container (AAC)
  | FormatWebM     -- ^ WebM container (Opus)
  | FormatCustom String -- ^ Custom/other format

derive instance eqContainerFormat :: Eq ContainerFormat
derive instance ordContainerFormat :: Ord ContainerFormat
derive instance genericContainerFormat :: Generic ContainerFormat _

instance showContainerFormat :: Show ContainerFormat where
  show format = containerLabel format

-- | Human-readable container label
containerLabel :: ContainerFormat -> String
containerLabel format = case format of
  FormatWAV    -> "WAV"
  FormatAIFF   -> "AIFF"
  FormatFLAC   -> "FLAC"
  FormatMP3    -> "MP3"
  FormatAAC    -> "AAC"
  FormatOGG    -> "OGG Vorbis"
  FormatOpus   -> "Opus"
  FormatM4A    -> "M4A (AAC)"
  FormatWebM   -> "WebM"
  FormatCustom s -> s

-- | Whether format is lossless
isLossless :: ContainerFormat -> Boolean
isLossless format = case format of
  FormatWAV   -> true
  FormatAIFF  -> true
  FormatFLAC -> true
  _          -> false

-- | Whether format uses compression
isCompressed :: ContainerFormat -> Boolean
isCompressed format = case format of
  FormatWAV   -> false
  FormatAIFF  -> false
  _           -> true

-- | Whether format supports metadata/chapters
supportsMetadata :: ContainerFormat -> Boolean
supportsMetadata format = case format of
  FormatMP3  -> true  -- ID3 tags
  FormatFLAC -> true  -- Vorbis comments
  FormatOGG  -> true  -- Vorbis comments
  FormatM4A  -> true  -- iTunes metadata
  FormatWebM -> true  -- Matroska tags
  _          -> false

-- | Default file extension for format
defaultFileExtension :: ContainerFormat -> String
defaultFileExtension format = case format of
  FormatWAV   -> "wav"
  FormatAIFF  -> "aiff"
  FormatFLAC -> "flac"
  FormatMP3  -> "mp3"
  FormatAAC  -> "m4a"
  FormatOGG  -> "ogg"
  FormatOpus -> "opus"
  FormatM4A  -> "m4a"
  FormatWebM -> "webm"
  FormatCustom _ -> "bin"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // codec // format
-- ═════════════════════════════════════════════════════════════════════════════

-- | Audio codec - the actual encoding
data CodecFormat
  = CodecPCM           -- ^ Uncompressed PCM
  | CodecFLAC          -- ^ FLAC lossless
  | CodecMP3           -- ^ MPEG-1 Layer 3
  | CodecAAC           -- ^ Advanced Audio Coding
  | CodecVorbis        -- ^ OGG Vorbis
  | CodecOpus          -- ^ Opus
  | CodecALAC          -- ^ Apple Lossless
  | CodecAPE           -- ^ Monkey's Audio
  | CodecCustom String -- ^ Custom codec

derive instance eqCodecFormat :: Eq CodecFormat
derive instance ordCodecFormat :: Ord CodecFormat
derive instance genericCodecFormat :: Generic CodecFormat _

instance showCodecFormat :: Show CodecFormat where
  show codec = codecLabel codec

-- | Human-readable codec label
codecLabel :: CodecFormat -> String
codecLabel codec = case codec of
  CodecPCM    -> "PCM"
  CodecFLAC   -> "FLAC"
  CodecMP3    -> "MP3"
  CodecAAC    -> "AAC"
  CodecVorbis -> "Vorbis"
  CodecOpus   -> "Opus"
  CodecALAC   -> "Apple Lossless"
  CodecAPE    -> "Monkey's Audio"
  CodecCustom s -> s

-- | Whether codec is lossy
isLossy :: CodecFormat -> Boolean
isLossy codec = case codec of
  CodecPCM   -> false
  CodecFLAC  -> false
  CodecALAC  -> false
  CodecAPE   -> false
  _          -> true

-- | Typical bitrate in kbps for lossy formats
typicalBitrate :: CodecFormat -> QualityPreset -> Int
typicalBitrate codec preset = case codec of
  CodecMP3   -> qualityToBitrate preset 128 192 256 320
  CodecAAC   -> qualityToBitrate preset 96 128 192 256
  CodecVorbis -> qualityToBitrate preset 80 128 192 320
  CodecOpus   -> qualityToBitrate preset 48 64 128 192
  _          -> 0

-- | Map quality preset to bitrate
qualityToBitrate :: QualityPreset -> Int -> Int -> Int -> Int -> Int
qualityToBitrate preset low mid high max = case preset of
  QualityLow    -> low
  QualityMedium -> mid
  QualityHigh   -> high
  QualityMaximum -> max

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // quality // preset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quality preset for lossy encoding
data QualityPreset
  = QualityLow
  | QualityMedium  
  | QualityHigh
  | QualityMaximum

derive instance eqQualityPreset :: Eq QualityPreset
derive instance ordQualityPreset :: Ord QualityPreset
derive instance genericQualityPreset :: Generic QualityPreset _

instance showQualityPreset :: Show QualityPreset where
  show preset = presetLabel preset

-- | Human-readable preset label
presetLabel :: QualityPreset -> String
presetLabel preset = case preset of
  QualityLow     -> "Low"
  QualityMedium  -> "Medium"
  QualityHigh    -> "High"
  QualityMaximum -> "Maximum"

-- | Convert preset to quality value (0-100 scale)
presetToQuality :: QualityPreset -> Int
presetToQuality preset = case preset of
  QualityLow     -> 25
  QualityMedium  -> 50
  QualityHigh    -> 75
  QualityMaximum -> 100

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // audio // file
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete audio file specification
type AudioFile =
  { format     :: ContainerFormat
  , codec      :: CodecFormat
  , sampleRate :: SampleRate
  , bitDepth   :: Maybe BitDepth      -- ^ Nothing for lossy
  , channels   :: ChannelCount
  , duration   :: Duration            -- ^ Length in milliseconds
  , bitrate    :: Int                 -- ^ Bitrate in kbps (0 for lossless)
  , dataSize   :: Int                 -- ^ Size of audio data in bytes
  , metadata   :: Maybe FileMetadata
  }

-- | Create audio file specification
audioFile 
  :: ContainerFormat 
  -> CodecFormat 
  -> SampleRate 
  -> Maybe BitDepth 
  -> ChannelCount 
  -> Duration 
  -> Int 
  -> Int 
  -> Maybe FileMetadata
  -> AudioFile
audioFile fmt cod sr bd ch dur br sz md =
  { format: fmt
  , codec: cod
  , sampleRate: sr
  , bitDepth: bd
  , channels: ch
  , duration: dur
  , bitrate: br
  , dataSize: sz
  , metadata: md
  }

-- | Get container format from file
fileFormat :: AudioFile -> ContainerFormat
fileFormat f = f.format

-- | Get codec from file
fileCodec :: AudioFile -> CodecFormat
fileCodec f = f.codec

-- | Get sample rate from file
fileSampleRate :: AudioFile -> SampleRate
fileSampleRate f = f.sampleRate

-- | Get bit depth from file
fileBitDepth :: AudioFile -> Maybe BitDepth
fileBitDepth f = f.bitDepth

-- | Get channel count from file
fileChannels :: AudioFile -> ChannelCount
fileChannels f = f.channels

-- | Get duration from file
fileDuration :: AudioFile -> Duration
fileDuration f = f.duration

-- | Get bitrate from file
fileBitrate :: AudioFile -> Int
fileBitrate f = f.bitrate

-- | Get data size from file
fileDataSize :: AudioFile -> Int
fileDataSize f = f.dataSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // metadata // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Audio file metadata
type FileMetadata =
  { title     :: Maybe String
  , artist    :: Maybe String
  , album     :: Maybe String
  , albumArtist :: Maybe String
  , track     :: Maybe { current :: Int, total :: Int }
  , disc      :: Maybe { current :: Int, total :: Int }
  , year      :: Maybe Int
  , genre     :: Maybe String
  , comment   :: Maybe String
  , lyrics    :: Maybe String
  , coverArt  :: Maybe CoverArt
  , composer  :: Maybe String
  , publisher  :: Maybe String
  , copyright  :: Maybe String
  , isrc       :: Maybe String
  }

-- | Cover art attachment
type CoverArt =
  { mimeType :: String
  , width    :: Int
  , height   :: Int
  , data     :: Array Int  -- ^ Raw image bytes
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // format // options
-- ═════════════════════════════════════════════════════════════════════════════

-- | Encoding options for audio export
type FormatOptions =
  { quality     :: QualityPreset
  , bitrate     :: Maybe Int          -- ^ Specific bitrate in kbps
  , metadata    :: Maybe FileMetadata
  , normalize    :: Boolean          -- ^ Normalize volume before encoding
  , addReplayGain :: Boolean         -- ^ Add replay gain metadata
  , streaming   :: Boolean           -- ^ Optimize for streaming
  }

-- | Default encoding options
defaultOptions :: FormatOptions
defaultOptions =
  { quality: QualityHigh
  , bitrate: Nothing
  , metadata: Nothing
  , normalize: false
  , addReplayGain: false
  , streaming: false
  }

-- | Set bitrate for encoding
withBitrate :: FormatOptions -> Int -> FormatOptions
withBitrate opts br = opts { bitrate = Just br }

-- | Set quality preset
withQuality :: FormatOptions -> QualityPreset -> FormatOptions
withQuality opts q = opts { quality = q }

-- | Set metadata
withMetadata :: FormatOptions -> FileMetadata -> FormatOptions
withMetadata opts md = opts { metadata = Just md }

-- | Check if options are for streaming
isStreaming :: FormatOptions -> Boolean
isStreaming opts = opts.streaming
