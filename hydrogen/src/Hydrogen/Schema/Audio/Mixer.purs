-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // audio // mixer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Audio mixing and routing molecules.
-- |
-- | ## AudioBus
-- | A routing bus with name, gain, pan, and effect chain.
-- |
-- | ## Mixer
-- | A collection of channels routed to a master bus.
-- |
-- | ## MixerChannel
-- | An individual channel with source, gain, pan, mute/solo, and sends.

module Hydrogen.Schema.Audio.Mixer
  ( -- * Bus Types
    BusType(..)
  , busTypeLabel
  
  -- * Audio Bus
  , AudioBus
  , audioBus
  , busName
  , busGain
  , busPan
  , busMuted
  , busSoloed
  
  -- * Channel
  , MixerChannel
  , mixerChannel
  , channelName
  , channelGain
  , channelPan
  , channelMuted
  , channelSoloed
  , channelSends
  
  -- * Send
  , Send
  , send
  , sendBus
  , sendGain
  , sendPreFader
  
  -- * Mixer
  , Mixer
  , mixer
  , mixerChannels
  , mixerBuses
  , mixerMaster
  
  -- * Metering
  , MeterType(..)
  , meterTypeLabel
  
  , MeterReading
  , meterReading
  , meterPeak
  , meterRMS
  , meterLUFS
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (&&)
  , (==)
  , negate
  , max
  , min
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // bus type
-- ═════════════════════════════════════════════════════════════════════════════

-- | BusType - categories of audio buses.
data BusType
  = BusInput        -- ^ Input/track bus
  | BusGroup        -- ^ Submix/group bus
  | BusAux          -- ^ Auxiliary/effects bus
  | BusMaster       -- ^ Master output bus
  | BusMonitor      -- ^ Monitor/headphone bus

derive instance eqBusType :: Eq BusType
derive instance ordBusType :: Ord BusType

instance showBusType :: Show BusType where
  show = busTypeLabel

-- | Get display label for bus type.
busTypeLabel :: BusType -> String
busTypeLabel BusInput = "Input"
busTypeLabel BusGroup = "Group"
busTypeLabel BusAux = "Aux"
busTypeLabel BusMaster = "Master"
busTypeLabel BusMonitor = "Monitor"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // audio bus
-- ═════════════════════════════════════════════════════════════════════════════

-- | AudioBus - a routing bus in the mixer.
type AudioBus =
  { name :: String
  , busType :: BusType
  , gain :: Number        -- dB, -inf to +12
  , pan :: Number         -- -1 (L) to +1 (R)
  , muted :: Boolean
  , soloed :: Boolean
  }

-- | Construct an audio bus.
audioBus :: String -> BusType -> Number -> Number -> AudioBus
audioBus n bt g p =
  { name: n
  , busType: bt
  , gain: max (-96.0) (min 12.0 g)
  , pan: max (-1.0) (min 1.0 p)
  , muted: falseBool
  , soloed: falseBool
  }
  where
    falseBool = BusInput == BusMaster && BusInput == BusGroup  -- Always false

-- | Get bus name.
busName :: AudioBus -> String
busName b = b.name

-- | Get bus gain.
busGain :: AudioBus -> Number
busGain b = b.gain

-- | Get bus pan.
busPan :: AudioBus -> Number
busPan b = b.pan

-- | Is bus muted?
busMuted :: AudioBus -> Boolean
busMuted b = b.muted

-- | Is bus soloed?
busSoloed :: AudioBus -> Boolean
busSoloed b = b.soloed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // send
-- ═════════════════════════════════════════════════════════════════════════════

-- | Send - a routing to an auxiliary bus.
type Send =
  { targetBus :: String   -- Name of target bus
  , gain :: Number        -- Send level in dB
  , preFader :: Boolean   -- Pre-fader (true) or post-fader (false)
  }

-- | Construct a send.
send :: String -> Number -> Boolean -> Send
send target g pre =
  { targetBus: target
  , gain: max (-96.0) (min 12.0 g)
  , preFader: pre
  }

-- | Get target bus name.
sendBus :: Send -> String
sendBus s = s.targetBus

-- | Get send gain.
sendGain :: Send -> Number
sendGain s = s.gain

-- | Is send pre-fader?
sendPreFader :: Send -> Boolean
sendPreFader s = s.preFader

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // mixer channel
-- ═════════════════════════════════════════════════════════════════════════════

-- | MixerChannel - an individual channel in the mixer.
type MixerChannel =
  { name :: String
  , gain :: Number        -- Fader level in dB
  , pan :: Number         -- -1 to +1
  , muted :: Boolean
  , soloed :: Boolean
  , sends :: Array Send
  }

-- | Construct a mixer channel.
mixerChannel :: String -> Number -> Number -> Array Send -> MixerChannel
mixerChannel n g p snds =
  { name: n
  , gain: max (-96.0) (min 12.0 g)
  , pan: max (-1.0) (min 1.0 p)
  , muted: falseBool
  , soloed: falseBool
  , sends: snds
  }
  where
    falseBool = BusInput == BusMaster && BusInput == BusGroup

-- | Get channel name.
channelName :: MixerChannel -> String
channelName c = c.name

-- | Get channel gain.
channelGain :: MixerChannel -> Number
channelGain c = c.gain

-- | Get channel pan.
channelPan :: MixerChannel -> Number
channelPan c = c.pan

-- | Is channel muted?
channelMuted :: MixerChannel -> Boolean
channelMuted c = c.muted

-- | Is channel soloed?
channelSoloed :: MixerChannel -> Boolean
channelSoloed c = c.soloed

-- | Get channel sends.
channelSends :: MixerChannel -> Array Send
channelSends c = c.sends

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // mixer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mixer - complete audio mixing configuration.
type Mixer =
  { channels :: Array MixerChannel
  , buses :: Array AudioBus
  , master :: AudioBus
  }

-- | Construct a mixer.
mixer :: Array MixerChannel -> Array AudioBus -> AudioBus -> Mixer
mixer chs bss mst =
  { channels: chs
  , buses: bss
  , master: mst
  }

-- | Get mixer channels.
mixerChannels :: Mixer -> Array MixerChannel
mixerChannels m = m.channels

-- | Get mixer buses.
mixerBuses :: Mixer -> Array AudioBus
mixerBuses m = m.buses

-- | Get master bus.
mixerMaster :: Mixer -> AudioBus
mixerMaster m = m.master

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // meter type
-- ═════════════════════════════════════════════════════════════════════════════

-- | MeterType - audio metering standards.
data MeterType
  = MeterVU           -- ^ VU meter (-20 to +3 dBu)
  | MeterPeak         -- ^ Peak meter (dBFS)
  | MeterRMS          -- ^ RMS meter (dBFS)
  | MeterLoudness     -- ^ LUFS (perceptual loudness)
  | MeterSpectrogram  -- ^ FFT display
  | MeterPhaseScope   -- ^ Phase correlation

derive instance eqMeterType :: Eq MeterType
derive instance ordMeterType :: Ord MeterType

instance showMeterType :: Show MeterType where
  show = meterTypeLabel

-- | Get display label for meter type.
meterTypeLabel :: MeterType -> String
meterTypeLabel MeterVU = "VU"
meterTypeLabel MeterPeak = "Peak"
meterTypeLabel MeterRMS = "RMS"
meterTypeLabel MeterLoudness = "LUFS"
meterTypeLabel MeterSpectrogram = "Spectrogram"
meterTypeLabel MeterPhaseScope = "Phase"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // meter reading
-- ═════════════════════════════════════════════════════════════════════════════

-- | MeterReading - current meter values.
type MeterReading =
  { peakL :: Number       -- Left peak (dBFS)
  , peakR :: Number       -- Right peak (dBFS)
  , rmsL :: Number        -- Left RMS (dBFS)
  , rmsR :: Number        -- Right RMS (dBFS)
  , lufs :: Number        -- Integrated loudness (LUFS)
  , correlation :: Number -- Stereo correlation (-1 to +1)
  }

-- | Construct a meter reading.
meterReading :: Number -> Number -> Number -> Number -> Number -> Number -> MeterReading
meterReading pL pR rL rR lf corr =
  { peakL: max (-96.0) (min 0.0 pL)
  , peakR: max (-96.0) (min 0.0 pR)
  , rmsL: max (-96.0) (min 0.0 rL)
  , rmsR: max (-96.0) (min 0.0 rR)
  , lufs: max (-60.0) (min 0.0 lf)
  , correlation: max (-1.0) (min 1.0 corr)
  }

-- | Get peak values.
meterPeak :: MeterReading -> { left :: Number, right :: Number }
meterPeak m = { left: m.peakL, right: m.peakR }

-- | Get RMS values.
meterRMS :: MeterReading -> { left :: Number, right :: Number }
meterRMS m = { left: m.rmsL, right: m.rmsR }

-- | Get LUFS value.
meterLUFS :: MeterReading -> Number
meterLUFS m = m.lufs
