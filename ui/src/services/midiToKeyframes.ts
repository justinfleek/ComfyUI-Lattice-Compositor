/**
 * MIDI File to Keyframes Conversion Service
 *
 * Parses Standard MIDI Files (.mid) and converts note/CC events
 * into animation keyframes for properties.
 *
 * Features:
 * - Note on/off → keyframes
 * - Velocity → value scaling
 * - CC (Control Change) → continuous values
 * - Multiple tracks support
 * - Tempo mapping
 *
 * @module services/midiToKeyframes
 */

import type { AnimatableProperty, Keyframe } from "@/types/project";
import { isFiniteNumber } from "@/utils/typeGuards";

// ============================================================================
// Types
// ============================================================================

export interface MIDINote {
  noteNumber: number; // 0-127 MIDI note
  noteName: string; // e.g., "C4", "F#5"
  velocity: number; // 0-127
  startTime: number; // Seconds
  duration: number; // Seconds
  channel: number; // 0-15
  track: number;
}

export interface MIDIControlChange {
  controller: number; // CC number (0-127)
  controllerName: string; // e.g., "Modulation", "Expression"
  value: number; // 0-127
  time: number; // Seconds
  channel: number;
  track: number;
}

export interface MIDITrack {
  name: string;
  notes: MIDINote[];
  controlChanges: MIDIControlChange[];
}

export interface MIDIParsedFile {
  format: number; // 0, 1, or 2
  ticksPerBeat: number; // Resolution
  tempos: Array<{ time: number; bpm: number }>;
  timeSignatures: Array<{
    time: number;
    numerator: number;
    denominator: number;
  }>;
  tracks: MIDITrack[];
  duration: number; // Total duration in seconds
}

export interface MIDIToKeyframeConfig {
  // Source selection
  trackIndex?: number; // Specific track, or all if undefined
  channel?: number; // Specific channel, or all if undefined
  noteRange?: { min: number; max: number }; // Filter notes

  // Mapping type
  mappingType: "noteOnOff" | "noteVelocity" | "notePitch" | "controlChange";

  // For controlChange type
  ccNumber?: number;

  // Value mapping
  valueMin: number; // Output minimum
  valueMax: number; // Output maximum

  // Timing
  fps: number; // Frame rate for keyframe conversion

  // Options
  sustainPedal?: boolean; // Respect sustain pedal (CC64)
  interpolation?: "linear" | "hold" | "bezier";
}

// ============================================================================
// Note Names
// ============================================================================

const NOTE_NAMES = [
  "C",
  "C#",
  "D",
  "D#",
  "E",
  "F",
  "F#",
  "G",
  "G#",
  "A",
  "A#",
  "B",
];

// Deterministic hash for stable ID generation (djb2 algorithm)
function simpleHash(str: string): string {
  let hash = 5381;
  for (let i = 0; i < str.length; i++) {
    hash = (hash << 5) + hash + str.charCodeAt(i);
    hash = hash & hash; // Convert to 32-bit integer
  }
  return Math.abs(hash).toString(36);
}

function midiNoteToName(noteNumber: number): string {
  const octave = Math.floor(noteNumber / 12) - 1;
  const noteName = NOTE_NAMES[noteNumber % 12];
  return `${noteName}${octave}`;
}

// ============================================================================
// Controller Names
// ============================================================================

const CC_NAMES: Record<number, string> = {
  0: "Bank Select",
  1: "Modulation",
  2: "Breath",
  4: "Foot Controller",
  5: "Portamento Time",
  7: "Volume",
  8: "Balance",
  10: "Pan",
  11: "Expression",
  64: "Sustain Pedal",
  65: "Portamento",
  66: "Sostenuto",
  67: "Soft Pedal",
  68: "Legato",
  69: "Hold 2",
  71: "Resonance",
  72: "Release Time",
  73: "Attack Time",
  74: "Cutoff",
  75: "Decay Time",
  91: "Reverb",
  93: "Chorus",
  94: "Detune",
  95: "Phaser",
};

function ccNumberToName(cc: number): string {
  return CC_NAMES[cc] || `CC${cc}`;
}

// ============================================================================
// MIDI File Parsing
// ============================================================================

/**
 * Parse a Standard MIDI File
 */
export async function parseMIDIFile(
  arrayBuffer: ArrayBuffer,
): Promise<MIDIParsedFile> {
  const view = new DataView(arrayBuffer);
  let offset = 0;

  // Read header chunk
  const headerChunk = readString(view, offset, 4);
  if (headerChunk !== "MThd") {
    throw new Error("Invalid MIDI file: Missing MThd header");
  }
  offset += 4;

  const headerLength = view.getUint32(offset);
  offset += 4;

  const format = view.getUint16(offset);
  offset += 2;

  const numTracks = view.getUint16(offset);
  offset += 2;

  const ticksPerBeat = view.getUint16(offset);
  offset += 2;

  offset = 8 + headerLength + 4; // Skip to track chunks

  // Parse tracks
  const tracks: MIDITrack[] = [];
  const tempos: Array<{ time: number; bpm: number }> = [{ time: 0, bpm: 120 }];
  const timeSignatures: Array<{
    time: number;
    numerator: number;
    denominator: number;
  }> = [{ time: 0, numerator: 4, denominator: 4 }];
  // Track tempo changes by tick position for accurate MIDI-to-seconds conversion.
  // Initialized empty - default tempo added after parsing if no tick 0 tempo exists.
  const tempoChangesByTick: Array<{ tick: number; bpm: number }> = [];

  for (let t = 0; t < numTracks; t++) {
    const trackResult = parseTrack(
      view,
      offset,
      ticksPerBeat,
      tempos,
      tempoChangesByTick,
    );
    tracks.push(trackResult.track);
    offset = trackResult.nextOffset;

    // Extract tempo and time signature events
    for (const tempo of trackResult.tempos) {
      tempos.push(tempo);
    }
    for (const ts of trackResult.timeSignatures) {
      timeSignatures.push(ts);
    }
  }

  // Sort tempo changes by tick for correct interpolation
  tempoChangesByTick.sort((a, b) => a.tick - b.tick);

  // Add default 120 BPM at tick 0 only if no tempo exists there
  if (tempoChangesByTick.length === 0 || tempoChangesByTick[0].tick !== 0) {
    tempoChangesByTick.unshift({ tick: 0, bpm: 120 });
  }

  // Sort tempo and time signature events
  tempos.sort((a, b) => a.time - b.time);
  timeSignatures.sort((a, b) => a.time - b.time);

  // Calculate total duration
  let maxDuration = 0;
  for (const track of tracks) {
    for (const note of track.notes) {
      const endTime = note.startTime + note.duration;
      if (endTime > maxDuration) maxDuration = endTime;
    }
    for (const cc of track.controlChanges) {
      if (cc.time > maxDuration) maxDuration = cc.time;
    }
  }

  return {
    format,
    ticksPerBeat,
    tempos,
    timeSignatures,
    tracks,
    duration: maxDuration,
  };
}

/**
 * Convert ticks to seconds accounting for tempo changes.
 * Tempo changes occur at specific tick positions, so we need to calculate
 * cumulative time by summing durations at each tempo.
 */
function ticksToSecondsWithTempoMap(
  ticks: number,
  ticksPerBeat: number,
  tempoChanges: Array<{ tick: number; bpm: number }>,
): number {
  if (tempoChanges.length === 0) {
    // No tempo changes, use default 120 BPM
    const secondsPerBeat = 60 / 120;
    return (ticks / ticksPerBeat) * secondsPerBeat;
  }

  let totalSeconds = 0;
  let lastTick = 0;
  // Type proof: currentBpm ∈ number | undefined → number
  const currentBpm = tempoChanges.length > 0 &&
    isFiniteNumber(tempoChanges[0].bpm) && tempoChanges[0].bpm > 0
    ? tempoChanges[0].bpm
    : 120;

  // Process each tempo change up to the target tick
  for (const change of tempoChanges) {
    if (change.tick >= ticks) {
      // Target is before this tempo change
      break;
    }

    // Add time from lastTick to this tempo change at the previous tempo
    const ticksDelta = change.tick - lastTick;
    const secondsPerBeat = 60 / currentBpm;
    totalSeconds += (ticksDelta / ticksPerBeat) * secondsPerBeat;

    // Update for next segment
    lastTick = change.tick;
    currentBpm = change.bpm;
  }

  // Add remaining ticks at current tempo
  const remainingTicks = ticks - lastTick;
  const secondsPerBeat = 60 / currentBpm;
  totalSeconds += (remainingTicks / ticksPerBeat) * secondsPerBeat;

  return totalSeconds;
}

/**
 * Parse a single MIDI track
 */
function parseTrack(
  view: DataView,
  startOffset: number,
  ticksPerBeat: number,
  globalTempos: Array<{ time: number; bpm: number }>,
  // Tempo changes indexed by tick for precise timing calculations
  tempoChangesByTick: Array<{ tick: number; bpm: number }>,
): {
  track: MIDITrack;
  nextOffset: number;
  tempos: Array<{ time: number; bpm: number }>;
  timeSignatures: Array<{
    time: number;
    numerator: number;
    denominator: number;
  }>;
  tempoChangesByTick: Array<{ tick: number; bpm: number }>;
} {
  let offset = startOffset;

  // Read track header
  const trackChunk = readString(view, offset, 4);
  if (trackChunk !== "MTrk") {
    throw new Error(`Invalid track header at offset ${offset}`);
  }
  offset += 4;

  const trackLength = view.getUint32(offset);
  offset += 4;

  const trackEnd = offset + trackLength;

  const track: MIDITrack = {
    name: "",
    notes: [],
    controlChanges: [],
  };

  const tempos: Array<{ time: number; bpm: number }> = [];
  const timeSignatures: Array<{
    time: number;
    numerator: number;
    denominator: number;
  }> = [];
  const localTempoChanges: Array<{ tick: number; bpm: number }> = [];

  // Track note-on events for pairing with note-off
  const activeNotes = new Map<
    string,
    { noteNumber: number; velocity: number; startTick: number; channel: number }
  >();

  let currentTick = 0;
  let runningStatus = 0;

  // Convert MIDI ticks to seconds accounting for tempo changes
  const ticksToSeconds = (ticks: number): number => {
    return ticksToSecondsWithTempoMap(ticks, ticksPerBeat, tempoChangesByTick);
  };

  while (offset < trackEnd) {
    // Read delta time
    const deltaResult = readVariableLength(view, offset);
    currentTick += deltaResult.value;
    offset = deltaResult.nextOffset;

    // Read event
    let status = view.getUint8(offset);

    // Handle running status
    if (status < 0x80) {
      status = runningStatus;
    } else {
      runningStatus = status;
      offset++;
    }

    const eventType = status & 0xf0;
    const channel = status & 0x0f;

    // Note Off
    if (eventType === 0x80) {
      const noteNumber = view.getUint8(offset++);
      offset++; // velocity (ignored for note off)

      const key = `${channel}-${noteNumber}`;
      const activeNote = activeNotes.get(key);
      if (activeNote) {
        track.notes.push({
          noteNumber,
          noteName: midiNoteToName(noteNumber),
          velocity: activeNote.velocity,
          startTime: ticksToSeconds(activeNote.startTick),
          duration: ticksToSeconds(currentTick - activeNote.startTick),
          channel,
          track: 0,
        });
        activeNotes.delete(key);
      }
    }
    // Note On
    else if (eventType === 0x90) {
      const noteNumber = view.getUint8(offset++);
      const velocity = view.getUint8(offset++);

      const key = `${channel}-${noteNumber}`;

      if (velocity === 0) {
        // Note On with velocity 0 = Note Off
        const activeNote = activeNotes.get(key);
        if (activeNote) {
          track.notes.push({
            noteNumber,
            noteName: midiNoteToName(noteNumber),
            velocity: activeNote.velocity,
            startTime: ticksToSeconds(activeNote.startTick),
            duration: ticksToSeconds(currentTick - activeNote.startTick),
            channel,
            track: 0,
          });
          activeNotes.delete(key);
        }
      } else {
        activeNotes.set(key, {
          noteNumber,
          velocity,
          startTick: currentTick,
          channel,
        });
      }
    }
    // Polyphonic Aftertouch
    else if (eventType === 0xa0) {
      offset += 2;
    }
    // Control Change
    else if (eventType === 0xb0) {
      const controller = view.getUint8(offset++);
      const value = view.getUint8(offset++);

      track.controlChanges.push({
        controller,
        controllerName: ccNumberToName(controller),
        value,
        time: ticksToSeconds(currentTick),
        channel,
        track: 0,
      });
    }
    // Program Change
    else if (eventType === 0xc0) {
      offset++;
    }
    // Channel Aftertouch
    else if (eventType === 0xd0) {
      offset++;
    }
    // Pitch Bend
    else if (eventType === 0xe0) {
      offset += 2;
    }
    // Meta Event
    else if (status === 0xff) {
      const metaType = view.getUint8(offset++);
      const lengthResult = readVariableLength(view, offset);
      const length = lengthResult.value;
      offset = lengthResult.nextOffset;

      // Track name
      if (metaType === 0x03) {
        track.name = readString(view, offset, length);
      }
      // Tempo
      else if (metaType === 0x51 && length === 3) {
        const microsecondsPerBeat =
          (view.getUint8(offset) << 16) |
          (view.getUint8(offset + 1) << 8) |
          view.getUint8(offset + 2);
        const bpm = 60000000 / microsecondsPerBeat;
        // Record tempo change at this tick position for timing calculations
        localTempoChanges.push({ tick: currentTick, bpm });
        tempoChangesByTick.push({ tick: currentTick, bpm });
        tempos.push({ time: ticksToSeconds(currentTick), bpm });
        globalTempos.push({ time: ticksToSeconds(currentTick), bpm });
      }
      // Time Signature
      else if (metaType === 0x58 && length >= 2) {
        const numerator = view.getUint8(offset);
        const denominator = 2 ** view.getUint8(offset + 1);
        timeSignatures.push({
          time: ticksToSeconds(currentTick),
          numerator,
          denominator,
        });
      }

      offset += length;
    }
    // SysEx
    else if (status === 0xf0 || status === 0xf7) {
      const lengthResult = readVariableLength(view, offset);
      offset = lengthResult.nextOffset + lengthResult.value;
    }
  }

  return {
    track,
    nextOffset: trackEnd,
    tempos,
    timeSignatures,
    tempoChangesByTick: localTempoChanges,
  };
}

/**
 * Read variable-length quantity
 */
function readVariableLength(
  view: DataView,
  offset: number,
): { value: number; nextOffset: number } {
  let value = 0;
  let byte: number;

  do {
    byte = view.getUint8(offset++);
    value = (value << 7) | (byte & 0x7f);
  } while (byte & 0x80);

  return { value, nextOffset: offset };
}

/**
 * Read string from buffer
 */
function readString(view: DataView, offset: number, length: number): string {
  let str = "";
  for (let i = 0; i < length; i++) {
    str += String.fromCharCode(view.getUint8(offset + i));
  }
  return str;
}

// ============================================================================
// Keyframe Conversion
// ============================================================================

/**
 * Convert MIDI notes to keyframes
 * @param midiFile - Parsed MIDI file data
 * @param config - Conversion configuration
 * @param idPrefix - Unique prefix for keyframe IDs (default: hash of config)
 */
export function midiNotesToKeyframes(
  midiFile: MIDIParsedFile,
  config: MIDIToKeyframeConfig,
  idPrefix?: string,
): Keyframe<number>[] {
  const keyframes: Keyframe<number>[] = [];
  const fps = config.fps;

  // Generate deterministic ID prefix from config hash if not provided
  const prefix =
    idPrefix ||
    simpleHash(
      JSON.stringify({
        type: config.mappingType,
        track: config.trackIndex,
        channel: config.channel,
        range: config.noteRange,
        duration: midiFile.duration,
      }),
    );

  // Collect notes from specified tracks/channels
  const notes: MIDINote[] = [];

  for (let t = 0; t < midiFile.tracks.length; t++) {
    if (config.trackIndex !== undefined && t !== config.trackIndex) continue;

    for (const note of midiFile.tracks[t].notes) {
      if (config.channel !== undefined && note.channel !== config.channel)
        continue;

      if (config.noteRange) {
        if (
          note.noteNumber < config.noteRange.min ||
          note.noteNumber > config.noteRange.max
        )
          continue;
      }

      notes.push({ ...note, track: t });
    }
  }

  // Sort by time
  notes.sort((a, b) => a.startTime - b.startTime);

  let keyframeId = 0;

  for (const note of notes) {
    const startFrame = Math.round(note.startTime * fps);
    const endFrame = Math.round((note.startTime + note.duration) * fps);

    let value: number;

    switch (config.mappingType) {
      case "noteOnOff":
        // Create on/off keyframes
        keyframes.push({
          id: `midi_${prefix}_${keyframeId++}`,
          frame: startFrame,
          value: config.valueMax,
          interpolation: config.interpolation || "hold",
          inHandle: { frame: 0, value: 0, enabled: false },
          outHandle: { frame: 0, value: 0, enabled: false },
          controlMode: "smooth" as const,
        });
        keyframes.push({
          id: `midi_${prefix}_${keyframeId++}`,
          frame: endFrame,
          value: config.valueMin,
          interpolation: config.interpolation || "hold",
          inHandle: { frame: 0, value: 0, enabled: false },
          outHandle: { frame: 0, value: 0, enabled: false },
          controlMode: "smooth" as const,
        });
        break;

      case "noteVelocity":
        // Value based on velocity
        value =
          config.valueMin +
          (note.velocity / 127) * (config.valueMax - config.valueMin);
        keyframes.push({
          id: `midi_${prefix}_${keyframeId++}`,
          frame: startFrame,
          value,
          interpolation: config.interpolation || "linear",
          inHandle: { frame: 0, value: 0, enabled: false },
          outHandle: { frame: 0, value: 0, enabled: false },
          controlMode: "smooth" as const,
        });
        keyframes.push({
          id: `midi_${prefix}_${keyframeId++}`,
          frame: endFrame,
          value: config.valueMin,
          interpolation: config.interpolation || "linear",
          inHandle: { frame: 0, value: 0, enabled: false },
          outHandle: { frame: 0, value: 0, enabled: false },
          controlMode: "smooth" as const,
        });
        break;

      case "notePitch": {
        // Value based on note number
        // Type proof: noteRange.max ∈ number | undefined → number
        const maxNote = config.noteRange && isFiniteNumber(config.noteRange.max)
          ? config.noteRange.max
          : 127;
        // Type proof: noteRange.min ∈ number | undefined → number
        const minNote = config.noteRange && isFiniteNumber(config.noteRange.min)
          ? config.noteRange.min
          : 0;
        const pitchRange = maxNote - minNote;
        const normalizedPitch = (note.noteNumber - minNote) / pitchRange;
        value =
          config.valueMin +
          normalizedPitch * (config.valueMax - config.valueMin);
        keyframes.push({
          id: `midi_${prefix}_${keyframeId++}`,
          frame: startFrame,
          value,
          interpolation: config.interpolation || "linear",
          inHandle: { frame: 0, value: 0, enabled: false },
          outHandle: { frame: 0, value: 0, enabled: false },
          controlMode: "smooth" as const,
        });
        break;
      }
    }
  }

  // Sort and deduplicate
  keyframes.sort((a, b) => a.frame - b.frame);

  return keyframes;
}

/**
 * Convert MIDI Control Changes to keyframes
 * @param midiFile - Parsed MIDI file data
 * @param config - Conversion configuration
 * @param idPrefix - Unique prefix for keyframe IDs (default: hash of config)
 */
export function midiCCToKeyframes(
  midiFile: MIDIParsedFile,
  config: MIDIToKeyframeConfig,
  idPrefix?: string,
): Keyframe<number>[] {
  if (config.ccNumber === undefined) {
    throw new Error("ccNumber is required for controlChange mapping");
  }

  const keyframes: Keyframe<number>[] = [];
  const fps = config.fps;

  // Generate deterministic ID prefix from config hash if not provided
  const prefix =
    idPrefix ||
    simpleHash(
      JSON.stringify({
        type: "cc",
        ccNumber: config.ccNumber,
        track: config.trackIndex,
        channel: config.channel,
        duration: midiFile.duration,
      }),
    );

  // Collect CC events from specified tracks/channels
  const ccEvents: MIDIControlChange[] = [];

  for (let t = 0; t < midiFile.tracks.length; t++) {
    if (config.trackIndex !== undefined && t !== config.trackIndex) continue;

    for (const cc of midiFile.tracks[t].controlChanges) {
      if (config.channel !== undefined && cc.channel !== config.channel)
        continue;
      if (cc.controller !== config.ccNumber) continue;

      ccEvents.push({ ...cc, track: t });
    }
  }

  // Sort by time
  ccEvents.sort((a, b) => a.time - b.time);

  let keyframeId = 0;

  for (const cc of ccEvents) {
    const frame = Math.round(cc.time * fps);
    const value =
      config.valueMin + (cc.value / 127) * (config.valueMax - config.valueMin);

    keyframes.push({
      id: `midi_${prefix}_${keyframeId++}`,
      frame,
      value,
      interpolation: config.interpolation || "linear",
      inHandle: { frame: 0, value: 0, enabled: false },
      outHandle: { frame: 0, value: 0, enabled: false },
      controlMode: "smooth" as const,
    });
  }

  return keyframes;
}

/**
 * Create an animatable property from MIDI data
 */
export function createMIDIAnimatableProperty(
  name: string,
  midiFile: MIDIParsedFile,
  config: MIDIToKeyframeConfig,
): AnimatableProperty<number> {
  // Generate deterministic property ID from name and config for reproducibility
  const idHash = simpleHash(
    JSON.stringify({
      name,
      mappingType: config.mappingType,
      trackIndex: config.trackIndex,
      channel: config.channel,
      ccNumber: config.ccNumber,
      duration: midiFile.duration,
      trackCount: midiFile.tracks.length,
    }),
  );
  const id = `midi_prop_${idHash}`;

  // Pass the id as prefix so keyframes are also unique
  const keyframes =
    config.mappingType === "controlChange"
      ? midiCCToKeyframes(midiFile, config, idHash)
      : midiNotesToKeyframes(midiFile, config, idHash);

  return {
    id,
    name,
    type: "number" as const,
    value: config.valueMin,
    animated: keyframes.length > 0,
    keyframes,
  };
}

// ============================================================================
// Exports
// ============================================================================

export default {
  parseMIDIFile,
  midiNotesToKeyframes,
  midiCCToKeyframes,
  createMIDIAnimatableProperty,
  midiNoteToName,
  ccNumberToName,
};
