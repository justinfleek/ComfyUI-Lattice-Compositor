# Audio Schema — Complete Specification

**Status:** Council deliberation in progress  
**Goal:** 1:1 Ableton Live UI recreation capability  
**Date:** 2026-02-24

---

## Design Principles

1. **No infinity** — all types have finite bounds
2. **Type carries bounds** — `TrackGain` is not `EQGain` is not `UtilityGain`
3. **Integers where integers** — Velocity is 1-127, not 1.0-127.0
4. **Industry standard** — match what pros expect from Ableton, FL Studio, TouchDesigner
5. **Smart constructors** — clamp at bounds, invalid states unrepresentable

---

## MIDI (Locked)

### Core MIDI 1.0

| Type | Min | Max | Bits | Step | Notes |
|------|-----|-----|------|------|-------|
| `Velocity` | 1 | 127 | 7 | 1 | Note-on velocity. 0 = note-off in MIDI spec. |
| `NoteNumber` | 0 | 127 | 7 | 1 | C-2 (0) to G8 (127). Middle C = 60. |
| `CCValue` | 0 | 127 | 7 | 1 | Control Change value for any CC. |
| `ChannelPressure` | 0 | 127 | 7 | 1 | Monophonic aftertouch. |
| `PolyPressure` | 0 | 127 | 7 | 1 | Per-note aftertouch (rare). |
| `ProgramChange` | 0 | 127 | 7 | 1 | Preset/patch selection. |
| `PitchBend` | -8192 | +8191 | 14 | 1 | Center = 0. Range interpretation varies. |
| `MIDIChannel` | 1 | 16 | 4 | 1 | Stored as 1-16, not 0-15. |

### MPE Extensions

| Type | Min | Max | Notes |
|------|-----|-----|-------|
| `MPESlide` | 0 | 127 | CC74, per-note Y-axis (Seaboard, Linnstrument) |

MPE reuses `PitchBend` and `PolyPressure` per-note.

### Configuration

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `PitchBendRange` | 1 | 48 | 1 | Semitones per full bend (±8192) |
| `TuningHz` | 420.0 | 460.0 | 0.1 | A4 reference frequency |
| `TuningCents` | -50 | +50 | 1 | Fine tune offset from reference |

### Derived Functions (Pure)

```purescript
-- Note to frequency (A4 = 440Hz)
noteToFrequency :: NoteNumber -> TuningHz -> FrequencyHz
noteToFrequency note tuning = tuning * (2 ^ ((note - 69) / 12))

-- Note to name
noteName :: NoteNumber -> { note :: NoteLetter, octave :: Int }

-- Velocity curves (pure transforms)
velocityCurveLinear :: Velocity -> Velocity
velocityCurveExponential :: Number -> Velocity -> Velocity
velocityCurveSCurve :: Velocity -> Velocity
```

### MIDI 2.0 (Future)

Reserved for later — separate types when needed:
- `Velocity16` (1-65535)
- `CC16` (0-65535)  
- `PitchBend32` (32-bit)

---

## Gain Types

### Channel/Bus Gains

| Type | Min | Max | Unity | Step | Notes |
|------|-----|-----|-------|------|-------|
| `TrackGain` | -96.0 dB | +6.0 dB | 0.0 dB | 0.1 | Channel fader |
| `MasterGain` | -96.0 dB | +6.0 dB | 0.0 dB | 0.1 | Master bus fader |
| `ClipGain` | -96.0 dB | +6.0 dB | 0.0 dB | 0.1 | Per-clip gain (Ableton) |
| `SendLevel` | -96.0 dB | 0.0 dB | -96.0 dB | 0.1 | Aux send (attenuation only) |

### Plugin Gains

| Type | Min | Max | Unity | Step | Notes |
|------|-----|-----|-------|------|-------|
| `UtilityGain` | -96.0 dB | +35.0 dB | 0.0 dB | 0.1 | Utility/gain plugin |
| `EQGain` | -15.0 dB | +15.0 dB | 0.0 dB | 0.1 | EQ band boost/cut |
| `CompMakeup` | 0.0 dB | +24.0 dB | 0.0 dB | 0.1 | Compressor makeup |
| `Drive` | 0 | 100 | 0 | 1 | Saturation/distortion amount (%) |
| `DryWet` | 0 | 100 | — | 1 | Effect mix (%) |

### Display Rules

- Values ≤ -96 dB display as "-inf" but store as -96.0
- Unity (0 dB) should have visual indicator
- Clipping (> 0 dB on master) should have visual indicator

### Conversion (Pure)

```purescript
-- dB to linear amplitude
dbToAmplitude :: Number -> Number
dbToAmplitude db = 10.0 ^ (db / 20.0)

-- Linear amplitude to dB
amplitudeToDb :: Number -> Number
amplitudeToDb amp = 20.0 * log10 amp
```

---

## Spatial / Stereo

| Type | Min | Max | Center | Step | Notes |
|------|-----|-----|--------|------|-------|
| `Pan` | -100 | +100 | 0 | 1 | L=-100, C=0, R=+100 |
| `StereoWidth` | 0 | 200 | 100 | 1 | Mono=0, Normal=100, Wide=200 |
| `MidSideBalance` | -100 | +100 | 0 | 1 | Mid=-100, Center=0, Side=+100 |

---

## Dynamics

### Compressor

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `CompThreshold` | -60.0 dB | 0.0 dB | 0.1 | When compression starts |
| `CompRatio` | 1.0 | 20.0 | 0.1 | 1:1 (off) to 20:1 (limiting) |
| `CompAttack` | 0.1 ms | 500.0 ms | 0.1 | Attack time |
| `CompRelease` | 1.0 ms | 5000.0 ms | 1.0 | Release time |
| `CompKnee` | 0.0 dB | 24.0 dB | 0.1 | Soft knee width |
| `CompMakeup` | 0.0 dB | +24.0 dB | 0.1 | Makeup gain |
| `Lookahead` | 0.0 ms | 10.0 ms | 0.1 | Lookahead time |

### Gate

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `GateThreshold` | -96.0 dB | 0.0 dB | 0.1 | When gate opens |
| `GateRange` | -96.0 dB | 0.0 dB | 0.1 | Attenuation when closed |
| `GateAttack` | 0.01 ms | 100.0 ms | 0.01 | Attack time |
| `GateHold` | 0.0 ms | 500.0 ms | 1.0 | Hold time before release |
| `GateRelease` | 1.0 ms | 2000.0 ms | 1.0 | Release time |

### Expander

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `ExpanderThreshold` | -96.0 dB | 0.0 dB | 0.1 | Expansion threshold |
| `ExpanderRatio` | 1.0 | 4.0 | 0.1 | 1:1 to 1:4 (inverted notation) |

### Limiter

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `LimiterCeiling` | -6.0 dB | 0.0 dB | 0.1 | Output ceiling |
| `LimiterRelease` | 1.0 ms | 1000.0 ms | 1.0 | Release time |

---

## EQ

### Band Parameters

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `EQFrequency` | 20.0 Hz | 20000.0 Hz | — | Logarithmic scale |
| `EQGain` | -15.0 dB | +15.0 dB | 0.1 | Band gain |
| `EQBandwidth` | 0.1 oct | 4.0 oct | 0.01 | Width in octaves |
| `EQQ` | 0.1 | 30.0 | 0.01 | Quality factor (alt to bandwidth) |

### Band Types (Enum)

```purescript
data EQBandType
  = LowShelf
  | HighShelf
  | Peak           -- Bell curve
  | LowPass
  | HighPass
  | Notch
  | BandPass
```

### Filter Slopes (Enum)

```purescript
data FilterSlope
  = Slope6dB      -- 6 dB/octave (1-pole)
  | Slope12dB     -- 12 dB/octave (2-pole)
  | Slope18dB     -- 18 dB/octave (3-pole)
  | Slope24dB     -- 24 dB/octave (4-pole)
  | Slope36dB     -- 36 dB/octave (6-pole)
  | Slope48dB     -- 48 dB/octave (8-pole)
```

### Frequency (General)

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `FrequencyHz` | 20.0 | 20000.0 | — | Audible range, log scale |
| `FilterCutoff` | 20.0 | 20000.0 | — | Filter cutoff frequency |
| `FilterResonance` | 0 | 100 | 1 | Resonance/emphasis (%) |

---

## Synthesis

### Oscillator

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `OscCoarse` | -24 | +24 | 1 | Semitone offset |
| `OscFine` | -100 | +100 | 1 | Cents offset |
| `OscShape` | 0 | 100 | 1 | Waveshape/pulse width (%) |
| `OscLevel` | 0 | 100 | 1 | Oscillator mix level (%) |

### Oscillator Types (Enum)

```purescript
data OscWaveform
  = Sine
  | Triangle
  | Saw
  | Square
  | Pulse
  | Noise
  | Wavetable
```

### Envelope (ADSR)

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `EnvAttack` | 0.1 ms | 60000.0 ms | — | Attack time (log scale) |
| `EnvDecay` | 0.1 ms | 60000.0 ms | — | Decay time |
| `EnvSustain` | 0 | 100 | 1 | Sustain level (%) |
| `EnvRelease` | 0.1 ms | 60000.0 ms | — | Release time |

### LFO

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `LFORate` | 0.01 Hz | 50.0 Hz | 0.01 | Free-running rate |
| `LFOAmount` | -100 | +100 | 1 | Modulation depth (%, bipolar) |
| `LFOPhase` | 0 | 359 | 1 | Start phase (degrees) |

### LFO Sync (Enum)

```purescript
data LFOSync
  = Free              -- Hz-based
  | Sync1_64          -- 1/64 note
  | Sync1_32
  | Sync1_16
  | Sync1_8
  | Sync1_4
  | Sync1_2
  | Sync1Bar
  | Sync2Bars
  | Sync4Bars
  | Sync8Bars
```

### LFO Shape (Enum)

```purescript
data LFOShape
  = SineLFO
  | TriangleLFO
  | SawUpLFO
  | SawDownLFO
  | SquareLFO
  | SampleHoldLFO
  | RandomLFO
```

### Unison

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `UnisonVoices` | 1 | 16 | 1 | Number of unison voices |
| `UnisonDetune` | 0 | 100 | 1 | Detune spread (%) |
| `UnisonSpread` | 0 | 100 | 1 | Stereo spread (%) |

### Portamento

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `PortamentoTime` | 0.0 ms | 5000.0 ms | 1.0 | Glide time |

### Portamento Mode (Enum)

```purescript
data PortamentoMode
  = PortaOff
  | PortaAlways
  | PortaLegato    -- Only when notes overlap
```

### Voice

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `VoiceCount` | 1 | 64 | 1 | Polyphony |

---

## Sampler

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `SampleStart` | 0.0 | 100.0 | 0.01 | % of sample length |
| `SampleEnd` | 0.0 | 100.0 | 0.01 | % of sample length |
| `LoopStart` | 0.0 | 100.0 | 0.01 | Loop region start |
| `LoopEnd` | 0.0 | 100.0 | 0.01 | Loop region end |
| `LoopCrossfade` | 0.0 | 100.0 | 0.1 | Crossfade length (%) |
| `RootNote` | 0 | 127 | 1 | Original pitch of sample |

### Loop Mode (Enum)

```purescript
data LoopMode
  = NoLoop
  | LoopForward
  | LoopBackward
  | LoopPingPong
```

---

## Metering

### Level Meters

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `PeakLevel` | -96.0 dB | +6.0 dB | 0.1 | Instantaneous peak |
| `RMSLevel` | -96.0 dB | +6.0 dB | 0.1 | RMS average |
| `ReductionMeter` | -24.0 dB | 0.0 dB | 0.1 | Gain reduction (compressor) |

### Loudness (Broadcast Standard)

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `LUFSIntegrated` | -70.0 | 0.0 | 0.1 | Integrated loudness (full track) |
| `LUFSMomentary` | -70.0 | 0.0 | 0.1 | 400ms window |
| `LUFSShortTerm` | -70.0 | 0.0 | 0.1 | 3s window |
| `TruePeak` | -96.0 dBTP | +6.0 dBTP | 0.1 | Inter-sample peak |
| `LoudnessRange` | 0.0 LU | 30.0 LU | 0.1 | Dynamic range (LRA) |

### Phase/Stereo Analysis

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `Correlation` | -1.0 | +1.0 | 0.01 | Stereo correlation (+1=mono, 0=unrelated, -1=out of phase) |

---

## Clip / Timing

### Tempo

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `BPM` | 20.0 | 999.0 | 0.01 | Beats per minute |
| `TimeSignatureNum` | 1 | 32 | 1 | Beats per bar |
| `TimeSignatureDenom` | 1 | 32 | — | Beat unit (1,2,4,8,16,32) |

### Clip Properties

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `ClipGain` | -96.0 dB | +6.0 dB | 0.1 | Per-clip gain |
| `Transpose` | -48 | +48 | 1 | Semitones |
| `Detune` | -50 | +50 | 1 | Cents |
| `ClipStart` | 0.0 | — | — | Beats (unbounded, but non-negative) |
| `ClipLength` | 0.0 | — | — | Beats |

### Groove / Swing

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `Swing` | 0 | 100 | 1 | Swing amount (%) |
| `GrooveAmount` | 0 | 130 | 1 | Groove intensity (Ableton goes to 130%) |

### Time Nudge

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `SampleOffset` | -10000 | +10000 | 1 | Samples (at current SR) |
| `MsOffset` | -1000.0 | +1000.0 | 0.1 | Milliseconds |

### Delay

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `DelayMs` | 0.0 | 5000.0 | 0.1 | Free delay time |
| `DelayFeedback` | 0 | 100 | 1 | Feedback amount (%) |

### Delay Sync (Enum)

Same as `LFOSync`:

```purescript
data DelaySync
  = DelayFree
  | Delay1_64
  | Delay1_32
  | Delay1_16
  | Delay1_8
  | Delay1_4
  | Delay1_2
  | Delay1Bar
  | Delay2Bars
  -- etc
```

---

## Summary Statistics

- **Total Types:** ~85
- **Enums:** 12
- **Integer Types:** ~35
- **Number Types:** ~50
- **All bounded:** Yes
- **Infinity:** None

---

## Automation

### Automation Values

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `AutomationValue` | 0.0 | 1.0 | — | Normalized, maps to any parameter |
| `BreakpointPosition` | 0.0 | — | — | Position in beats (non-negative) |

### Automation Curves (Enum)

```purescript
data AutomationCurve
  = Linear          -- Straight line between points
  | CurveIn         -- Ease in (slow start)
  | CurveOut        -- Ease out (slow end)
  | SCurve          -- S-curve (slow start and end)
  | Hold            -- Step/hold until next point
```

### Breakpoint (Compound)

```purescript
type AutomationBreakpoint =
  { position :: BreakpointPosition
  , value :: AutomationValue
  , curve :: AutomationCurve
  }
```

---

## Arrangement / Time

### Position

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `PPQ` | 24 | 960 | — | Pulses per quarter (typically 480 or 960) |
| `TickPosition` | 0 | — | 1 | Absolute position in ticks |
| `BarNumber` | 1 | — | 1 | Bar number (1-indexed) |
| `BeatNumber` | 1 | 32 | 1 | Beat within bar (depends on time sig) |
| `TickInBeat` | 0 | PPQ-1 | 1 | Tick within beat |

### Bar.Beat.Tick (Compound)

```purescript
type BarBeatTick =
  { bar :: BarNumber
  , beat :: BeatNumber
  , tick :: TickInBeat
  }

-- Convert to/from absolute ticks
toTicks :: BarBeatTick -> PPQ -> TimeSignature -> TickPosition
fromTicks :: TickPosition -> PPQ -> TimeSignature -> BarBeatTick
```

---

## Warp

### Warp Modes (Enum)

```purescript
data WarpMode
  = WarpBeats       -- For rhythmic material, preserves transients
  | WarpTones       -- For melodic material (vocals, instruments)
  | WarpTexture     -- For atmospheric/textural sounds
  | WarpRepitch     -- Classic sampler behavior (pitch+time linked)
  | WarpComplex     -- High quality, CPU intensive
  | WarpComplexPro  -- Highest quality, most CPU
```

### Warp Parameters

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `TransientSensitivity` | 0 | 100 | 1 | Beat detection sensitivity (%) |
| `GrainSize` | 1 | 500 | 1 | Grain size in ms (for Texture mode) |
| `FluxAmount` | 0 | 100 | 1 | Randomization (for Texture mode) |

### Warp Marker (Compound)

```purescript
type WarpMarker =
  { originalPosition :: Milliseconds  -- Position in original file
  , warpedPosition :: BarBeatTick     -- Position in arrangement
  }
```

---

## Modulation

### Modulation Sources (Enum)

```purescript
data ModSource
  -- Envelopes
  = ModEnv1
  | ModEnv2
  | ModEnv3
  | ModAmpEnv
  | ModFilterEnv
  -- LFOs
  | ModLFO1
  | ModLFO2
  | ModLFO3
  -- MIDI
  | ModVelocity
  | ModReleaseVelocity
  | ModAftertouch
  | ModModWheel       -- CC1
  | ModPitchBend
  | ModKeytrack       -- Note number
  -- MPE
  | ModMPESlide       -- CC74 / Y-axis
  | ModMPEPressure    -- Per-note pressure
  -- Random
  | ModRandom
```

### Modulation Destinations (Enum)

```purescript
data ModDestination
  -- Oscillators
  = DestOsc1Pitch
  | DestOsc1Fine
  | DestOsc1Shape
  | DestOsc1Level
  | DestOsc2Pitch
  | DestOsc2Fine
  | DestOsc2Shape
  | DestOsc2Level
  -- Filter
  | DestFilterCutoff
  | DestFilterResonance
  | DestFilterEnvAmount
  -- Amplifier
  | DestAmpLevel
  | DestAmpPan
  -- LFOs
  | DestLFO1Rate
  | DestLFO1Amount
  | DestLFO2Rate
  | DestLFO2Amount
  -- Effects
  | DestFXMix
  | DestFXParam1
  | DestFXParam2
```

### Modulation Amounts

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `ModAmount` | -100 | +100 | 1 | Bipolar modulation depth (%) |
| `VelocitySensitivity` | 0 | 100 | 1 | How much velocity affects param (%) |
| `KeyTracking` | -100 | +100 | 1 | How much pitch affects param (%) |

### Modulation Slot (Compound)

```purescript
type ModulationSlot =
  { source :: ModSource
  , destination :: ModDestination
  , amount :: ModAmount
  }
```

---

## Routing

### Channel Assignment

| Type | Min | Max | Step | Notes |
|------|-----|-----|------|-------|
| `InputChannel` | 1 | 128 | 1 | Physical/virtual input |
| `OutputChannel` | 1 | 128 | 1 | Physical/virtual output |
| `BusNumber` | 1 | 64 | 1 | Group/bus assignment |
| `InsertSlot` | 1 | 16 | 1 | Position in effect chain |

### Input Type (Enum)

```purescript
data InputType
  = InputExternal     -- Hardware input
  | InputResampling   -- Internal audio
  | InputNoInput      -- MIDI only
```

### Output Type (Enum)

```purescript
data OutputType
  = OutputMaster
  | OutputBus BusNumber
  | OutputExternal OutputChannel
  | OutputSend          -- Pre/post fader send
```

---

## Track State

### Monitor Mode (Enum)

```purescript
data MonitorMode
  = MonitorAuto   -- Monitor when armed and not playing
  | MonitorIn     -- Always monitor input
  | MonitorOff    -- Never monitor input
```

### Track Flags (Booleans)

```purescript
type TrackState =
  { mute :: Boolean
  , solo :: Boolean
  , recordArm :: Boolean
  , monitorMode :: MonitorMode
  }
```

### Solo Mode (Enum)

```purescript
data SoloMode
  = SoloExclusive   -- Only one track at a time
  | SoloAdditive    -- Multiple tracks can solo
  | SoloInPlace     -- AFL/PFL style
```

---

## Summary Statistics (Final)

- **Total Types:** ~110
- **Enums:** 22
- **Integer Types:** ~45
- **Number Types:** ~55
- **Compound Types:** 8
- **All bounded:** Yes
- **Infinity:** None

---

## Implementation Priority

### Phase 1 — Core (Required for basic DAW)
1. MIDI types (Velocity, NoteNumber, CC, PitchBend)
2. Gain types (TrackGain, MasterGain, ClipGain)
3. Pan, DryWet
4. Dynamics (CompThreshold, CompRatio, CompAttack, CompRelease)
5. EQ (EQFrequency, EQGain, EQBandType)
6. Metering (PeakLevel, RMSLevel)
7. Tempo (BPM, TimeSignature)
8. Track State (Mute, Solo, RecordArm)

### Phase 2 — Professional Features
1. Full dynamics (Gate, Limiter, Expander)
2. Full EQ (all band types, slopes)
3. Automation (breakpoints, curves)
4. Loudness metering (LUFS)
5. Modulation routing

### Phase 3 — Advanced
1. Synthesis (Oscillators, Envelopes, LFOs, Unison)
2. Sampler (Start/End, Loop, Warp)
3. MPE / MIDI 2.0
4. Advanced routing

---

## Next Steps

1. Implement as PureScript newtypes with smart constructors
2. Add `BoundedValue` instances for slider compatibility
3. Create Lean4 proofs for critical conversions (dB↔amplitude, note↔frequency)
4. Build compound types (EQBand, Compressor, Oscillator, etc.)
5. Create UI components that compose from these atoms

---

*Document finalized by The Council — Round 3*
*Status: LOCKED for implementation*
