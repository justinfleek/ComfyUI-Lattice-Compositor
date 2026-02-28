-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // audio // buffer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Audio buffer molecules for raw audio data handling.
-- |
-- | ## AudioBuffer
-- | Raw audio data with sample rate, channel count, and duration.
-- | The fundamental container for digital audio.
-- |
-- | ## AudioRegion
-- | A slice of an AudioBuffer with start/end markers and gain.
-- | Used for non-destructive editing.
-- |
-- | ## AudioClip
-- | A playable audio unit with region, fade curves, and playback options.
-- | The basic building block for audio composition.

module Hydrogen.Schema.Audio.Buffer
  ( -- * Sample Rate
    SampleRate(..)
  , sampleRate
  , unwrapSampleRate
  , sampleRateBounds
  , rate44100
  , rate48000
  , rate96000
  , rate192000
  , isHighResSampleRate
  , sampleRateHigherThan
  
  -- * Bit Depth
  , BitDepth(..)
  , bitDepth
  , unwrapBitDepth
  , bitDepthBounds
  , bit16
  , bit24
  , bit32
  , isProfessionalBitDepth
  
  -- * Channel Count
  , ChannelCount(..)
  , channelCount
  , unwrapChannelCount
  , channelCountBounds
  , mono
  , stereo
  , surround51
  , surround71
  , isStereoOrMore
  , isSurround
  
  -- * Audio Buffer
  , AudioBuffer
  , audioBuffer
  , audioBufferSampleRate
  , audioBufferBitDepth
  , audioBufferChannels
  , audioBufferFrameCount
  , audioBufferDurationMs
  , sameBufferFormat
  , isEmptyBuffer
  
  -- * Audio Region
  , AudioRegion
  , audioRegion
  , regionBuffer
  , regionStartFrame
  , regionEndFrame
  , regionGain
  , regionFadeIn
  , regionFadeOut
  , regionLength
  , isValidRegion
  
  -- * Audio Clip
  , AudioClip
  , audioClip
  , clipRegion
  , clipOffset
  , clipLoop
  , clipReverse
  , clipPitch
  , isPitchShifted
  
  -- * Loop Mode
  , LoopMode(..)
  , loopModeLabel
  , isLooping
  
  -- * Audio Format
  , AudioFormat(..)
  , formatExtension
  , formatMimeType
  , formatLossy
  , formatLossless
  , formatQualityTier
  , formatsDiffer
  
  -- * Gain Utilities
  , gainAdjustmentToUnity
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , not
  , (&&)
  , (||)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (/=)
  , (<>)
  , (*)
  , (/)
  , (-)
  , negate
  , max
  , min
  )

import Data.Int (toNumber)
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // sample rate
-- ═════════════════════════════════════════════════════════════════════════════

-- | SampleRate - audio sample rate in Hz.
-- | Bounded to standard rates: 8000 Hz (telephony) to 192000 Hz (high-res).
newtype SampleRate = SampleRate Int

derive instance eqSampleRate :: Eq SampleRate
derive instance ordSampleRate :: Ord SampleRate

instance showSampleRate :: Show SampleRate where
  show (SampleRate r) = "(SampleRate " <> show r <> "Hz)"

-- | Bounds for sample rate.
sampleRateBounds :: Bounded.IntBounds
sampleRateBounds = Bounded.intBounds 8000 192000 "SampleRate" "Audio sample rate (Hz)"

-- | Construct a bounded sample rate.
sampleRate :: Int -> SampleRate
sampleRate r = SampleRate (Bounded.clampInt 8000 192000 r)

-- | Unwrap sample rate.
unwrapSampleRate :: SampleRate -> Int
unwrapSampleRate (SampleRate r) = r

-- | CD quality: 44.1 kHz
rate44100 :: SampleRate
rate44100 = SampleRate 44100

-- | Professional audio: 48 kHz
rate48000 :: SampleRate
rate48000 = SampleRate 48000

-- | High resolution: 96 kHz
rate96000 :: SampleRate
rate96000 = SampleRate 96000

-- | Ultra high resolution: 192 kHz
rate192000 :: SampleRate
rate192000 = SampleRate 192000

-- | Check if sample rate is high resolution (>= 96 kHz).
isHighResSampleRate :: SampleRate -> Boolean
isHighResSampleRate (SampleRate r) = r >= 96000

-- | Check if first sample rate is higher than second.
sampleRateHigherThan :: SampleRate -> SampleRate -> Boolean
sampleRateHigherThan (SampleRate r1) (SampleRate r2) = r1 > r2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // bit depth
-- ═════════════════════════════════════════════════════════════════════════════

-- | BitDepth - bits per sample.
-- | Bounded to standard depths: 8-bit (lo-fi) to 32-bit (float).
newtype BitDepth = BitDepth Int

derive instance eqBitDepth :: Eq BitDepth
derive instance ordBitDepth :: Ord BitDepth

instance showBitDepth :: Show BitDepth where
  show (BitDepth b) = "(BitDepth " <> show b <> "bit)"

-- | Bounds for bit depth.
bitDepthBounds :: Bounded.IntBounds
bitDepthBounds = Bounded.intBounds 8 32 "BitDepth" "Bits per sample"

-- | Construct a bounded bit depth.
bitDepth :: Int -> BitDepth
bitDepth b = BitDepth (Bounded.clampInt 8 32 b)

-- | Unwrap bit depth.
unwrapBitDepth :: BitDepth -> Int
unwrapBitDepth (BitDepth b) = b

-- | CD quality: 16-bit
bit16 :: BitDepth
bit16 = BitDepth 16

-- | Professional: 24-bit
bit24 :: BitDepth
bit24 = BitDepth 24

-- | Float precision: 32-bit
bit32 :: BitDepth
bit32 = BitDepth 32

-- | Check if bit depth is professional quality (>= 24-bit).
isProfessionalBitDepth :: BitDepth -> Boolean
isProfessionalBitDepth (BitDepth b) = b >= 24

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // channel count
-- ═════════════════════════════════════════════════════════════════════════════

-- | ChannelCount - number of audio channels.
-- | Bounded to 1-8 for standard configurations.
newtype ChannelCount = ChannelCount Int

derive instance eqChannelCount :: Eq ChannelCount
derive instance ordChannelCount :: Ord ChannelCount

instance showChannelCount :: Show ChannelCount where
  show (ChannelCount c) = "(ChannelCount " <> show c <> "ch)"

-- | Bounds for channel count.
channelCountBounds :: Bounded.IntBounds
channelCountBounds = Bounded.intBounds 1 8 "ChannelCount" "Audio channels (1-8)"

-- | Construct a bounded channel count.
channelCount :: Int -> ChannelCount
channelCount c = ChannelCount (Bounded.clampInt 1 8 c)

-- | Unwrap channel count.
unwrapChannelCount :: ChannelCount -> Int
unwrapChannelCount (ChannelCount c) = c

-- | Mono: 1 channel
mono :: ChannelCount
mono = ChannelCount 1

-- | Stereo: 2 channels
stereo :: ChannelCount
stereo = ChannelCount 2

-- | 5.1 Surround: 6 channels
surround51 :: ChannelCount
surround51 = ChannelCount 6

-- | 7.1 Surround: 8 channels
surround71 :: ChannelCount
surround71 = ChannelCount 8

-- | Check if stereo or more channels.
isStereoOrMore :: ChannelCount -> Boolean
isStereoOrMore (ChannelCount c) = c >= 2

-- | Check if surround sound (5.1 or more).
isSurround :: ChannelCount -> Boolean
isSurround (ChannelCount c) = c >= 6

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // audio buffer
-- ═════════════════════════════════════════════════════════════════════════════

-- | AudioBuffer - raw audio data container.
-- | Represents PCM audio with sample rate, bit depth, channels, and frame count.
-- | Actual sample data would be stored externally (ArrayBuffer, etc.).
type AudioBuffer =
  { sampleRate :: SampleRate
  , bitDepth :: BitDepth
  , channels :: ChannelCount
  , frameCount :: Int
  }

-- | Construct an audio buffer descriptor.
audioBuffer :: SampleRate -> BitDepth -> ChannelCount -> Int -> AudioBuffer
audioBuffer sr bd ch frames =
  { sampleRate: sr
  , bitDepth: bd
  , channels: ch
  , frameCount: max 0 frames
  }

-- | Get sample rate from buffer.
audioBufferSampleRate :: AudioBuffer -> SampleRate
audioBufferSampleRate buf = buf.sampleRate

-- | Get bit depth from buffer.
audioBufferBitDepth :: AudioBuffer -> BitDepth
audioBufferBitDepth buf = buf.bitDepth

-- | Get channel count from buffer.
audioBufferChannels :: AudioBuffer -> ChannelCount
audioBufferChannels buf = buf.channels

-- | Get frame count from buffer.
audioBufferFrameCount :: AudioBuffer -> Int
audioBufferFrameCount buf = buf.frameCount

-- | Calculate buffer duration in milliseconds.
audioBufferDurationMs :: AudioBuffer -> Number
audioBufferDurationMs buf =
  let rate = unwrapSampleRate buf.sampleRate
      frames = buf.frameCount
  in (toNumber frames * 1000.0) / toNumber rate

-- | Check if two buffers have the same format (rate, depth, channels).
sameBufferFormat :: AudioBuffer -> AudioBuffer -> Boolean
sameBufferFormat b1 b2 =
  b1.sampleRate == b2.sampleRate &&
  b1.bitDepth == b2.bitDepth &&
  b1.channels == b2.channels

-- | Check if buffer is empty (zero frames).
isEmptyBuffer :: AudioBuffer -> Boolean
isEmptyBuffer buf = buf.frameCount <= 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // audio region
-- ═════════════════════════════════════════════════════════════════════════════

-- | AudioRegion - a non-destructive slice of an AudioBuffer.
-- | Defines start/end points, gain, and fade curves.
type AudioRegion =
  { buffer :: AudioBuffer
  , startFrame :: Int
  , endFrame :: Int
  , gain :: Number        -- Linear gain (0.0 to 2.0)
  , fadeInFrames :: Int
  , fadeOutFrames :: Int
  }

-- | Construct an audio region.
audioRegion :: AudioBuffer -> Int -> Int -> Number -> Int -> Int -> AudioRegion
audioRegion buf start end g fadeIn fadeOut =
  let maxFrame = buf.frameCount
      clampedStart = max 0 (min start maxFrame)
      clampedEnd = max clampedStart (min end maxFrame)
      clampedGain = max 0.0 (min 2.0 g)
      regionLen = clampedEnd - clampedStart
      clampedFadeIn = max 0 (min fadeIn regionLen)
      clampedFadeOut = max 0 (min fadeOut (regionLen - clampedFadeIn))
  in { buffer: buf
     , startFrame: clampedStart
     , endFrame: clampedEnd
     , gain: clampedGain
     , fadeInFrames: clampedFadeIn
     , fadeOutFrames: clampedFadeOut
     }

-- | Get source buffer from region.
regionBuffer :: AudioRegion -> AudioBuffer
regionBuffer r = r.buffer

-- | Get start frame.
regionStartFrame :: AudioRegion -> Int
regionStartFrame r = r.startFrame

-- | Get end frame.
regionEndFrame :: AudioRegion -> Int
regionEndFrame r = r.endFrame

-- | Get region gain.
regionGain :: AudioRegion -> Number
regionGain r = r.gain

-- | Get fade in frames.
regionFadeIn :: AudioRegion -> Int
regionFadeIn r = r.fadeInFrames

-- | Get fade out frames.
regionFadeOut :: AudioRegion -> Int
regionFadeOut r = r.fadeOutFrames

-- | Get region length in frames.
regionLength :: AudioRegion -> Int
regionLength r = r.endFrame - r.startFrame

-- | Check if region is valid (has positive length and valid gain).
isValidRegion :: AudioRegion -> Boolean
isValidRegion r =
  r.startFrame >= 0 &&
  r.endFrame > r.startFrame &&
  r.gain >= 0.0 &&
  r.gain <= 2.0 &&
  r.fadeInFrames >= 0 &&
  r.fadeOutFrames >= 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // loop mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | LoopMode - how audio clips loop.
data LoopMode
  = LoopNone        -- ^ Play once, stop
  | LoopForward     -- ^ Loop from end to start
  | LoopPingPong    -- ^ Alternate forward/backward
  | LoopReverse     -- ^ Loop backward continuously

derive instance eqLoopMode :: Eq LoopMode
derive instance ordLoopMode :: Ord LoopMode

instance showLoopMode :: Show LoopMode where
  show = loopModeLabel

-- | Get display label for loop mode.
loopModeLabel :: LoopMode -> String
loopModeLabel LoopNone = "None"
loopModeLabel LoopForward = "Forward"
loopModeLabel LoopPingPong = "Ping-Pong"
loopModeLabel LoopReverse = "Reverse"

-- | Check if loop mode enables looping.
isLooping :: LoopMode -> Boolean
isLooping LoopNone = false
isLooping _ = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // audio clip
-- ═════════════════════════════════════════════════════════════════════════════

-- | AudioClip - a playable audio unit.
-- | Combines a region with playback options.
type AudioClip =
  { region :: AudioRegion
  , offsetMs :: Number      -- Playback offset in milliseconds
  , loopMode :: LoopMode
  , reverse :: Boolean
  , pitchRatio :: Number    -- 1.0 = normal, 2.0 = octave up, 0.5 = octave down
  }

-- | Construct an audio clip.
audioClip :: AudioRegion -> Number -> LoopMode -> Boolean -> Number -> AudioClip
audioClip reg offset loop rev pitch =
  { region: reg
  , offsetMs: max 0.0 offset
  , loopMode: loop
  , reverse: rev
  , pitchRatio: max 0.1 (min 10.0 pitch)  -- Bounded pitch ratio
  }

-- | Get clip region.
clipRegion :: AudioClip -> AudioRegion
clipRegion c = c.region

-- | Get clip offset.
clipOffset :: AudioClip -> Number
clipOffset c = c.offsetMs

-- | Get loop mode.
clipLoop :: AudioClip -> LoopMode
clipLoop c = c.loopMode

-- | Is clip reversed?
clipReverse :: AudioClip -> Boolean
clipReverse c = c.reverse

-- | Get pitch ratio.
clipPitch :: AudioClip -> Number
clipPitch c = c.pitchRatio

-- | Check if clip has pitch shifting (pitch ratio != 1.0).
isPitchShifted :: AudioClip -> Boolean
isPitchShifted c = c.pitchRatio < 0.99 || c.pitchRatio > 1.01

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // audio format
-- ═════════════════════════════════════════════════════════════════════════════

-- | AudioFormat - supported audio file formats.
data AudioFormat
  = FormatWAV       -- ^ Uncompressed PCM
  | FormatAIFF      -- ^ Uncompressed PCM (Apple)
  | FormatFLAC      -- ^ Lossless compressed
  | FormatMP3       -- ^ Lossy compressed
  | FormatAAC       -- ^ Lossy compressed (Apple)
  | FormatOGG       -- ^ Lossy compressed (Vorbis)
  | FormatOpus      -- ^ Lossy compressed (low latency)
  | FormatWebM      -- ^ Web media container

derive instance eqAudioFormat :: Eq AudioFormat
derive instance ordAudioFormat :: Ord AudioFormat

instance showAudioFormat :: Show AudioFormat where
  show fmt = "(AudioFormat " <> formatExtension fmt <> ")"

-- | Get file extension for format.
formatExtension :: AudioFormat -> String
formatExtension FormatWAV = "wav"
formatExtension FormatAIFF = "aiff"
formatExtension FormatFLAC = "flac"
formatExtension FormatMP3 = "mp3"
formatExtension FormatAAC = "m4a"
formatExtension FormatOGG = "ogg"
formatExtension FormatOpus = "opus"
formatExtension FormatWebM = "webm"

-- | Get MIME type for format.
formatMimeType :: AudioFormat -> String
formatMimeType FormatWAV = "audio/wav"
formatMimeType FormatAIFF = "audio/aiff"
formatMimeType FormatFLAC = "audio/flac"
formatMimeType FormatMP3 = "audio/mpeg"
formatMimeType FormatAAC = "audio/aac"
formatMimeType FormatOGG = "audio/ogg"
formatMimeType FormatOpus = "audio/opus"
formatMimeType FormatWebM = "audio/webm"

-- | Is format lossy (vs lossless)?
formatLossy :: AudioFormat -> Boolean
formatLossy FormatWAV = false
formatLossy FormatAIFF = false
formatLossy FormatFLAC = false
formatLossy FormatMP3 = true
formatLossy FormatAAC = true
formatLossy FormatOGG = true
formatLossy FormatOpus = true
formatLossy FormatWebM = true

-- | Is format lossless (vs lossy)?
formatLossless :: AudioFormat -> Boolean
formatLossless fmt = not (formatLossy fmt)

-- | Classify audio format quality tier.
-- | Returns "archival" for lossless, "streaming" for high-bitrate lossy,
-- | "efficient" for low-latency lossy formats.
formatQualityTier :: AudioFormat -> String
formatQualityTier fmt
  | fmt == FormatWAV = "archival"
  | fmt == FormatAIFF = "archival"
  | fmt == FormatFLAC = "archival"
  | fmt == FormatMP3 = "streaming"
  | fmt == FormatAAC = "streaming"
  | fmt == FormatOGG = "streaming"
  | fmt == FormatOpus = "efficient"
  | fmt == FormatWebM = "efficient"
  | otherwise = "unknown"

-- | Check if two formats are different.
formatsDiffer :: AudioFormat -> AudioFormat -> Boolean
formatsDiffer f1 f2 = f1 /= f2

-- | Calculate gain adjustment to invert current gain around unity.
-- | If gain is 0.5, returns -0.5 (to adjust by 0.5 to reach 1.0).
-- | If gain is 1.5, returns 0.5 (to adjust by -0.5 to reach 1.0).
gainAdjustmentToUnity :: AudioRegion -> Number
gainAdjustmentToUnity r = negate (r.gain - 1.0)
