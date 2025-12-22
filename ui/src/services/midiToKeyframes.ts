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

import type { Keyframe, AnimatableProperty } from '@/types/project';

// ============================================================================
// Types
// ============================================================================

export interface MIDINote {
  noteNumber: number;     // 0-127 MIDI note
  noteName: string;       // e.g., "C4", "F#5"
  velocity: number;       // 0-127
  startTime: number;      // Seconds
  duration: number;       // Seconds
  channel: number;        // 0-15
  track: number;
}

export interface MIDIControlChange {
  controller: number;     // CC number (0-127)
  controllerName: string; // e.g., "Modulation", "Expression"
  value: number;          // 0-127
  time: number;           // Seconds
  channel: number;
  track: number;
}

export interface MIDITrack {
  name: string;
  notes: MIDINote[];
  controlChanges: MIDIControlChange[];
}

export interface MIDIParsedFile {
  format: number;         // 0, 1, or 2
  ticksPerBeat: number;   // Resolution
  tempos: Array<{ time: number; bpm: number }>;
  timeSignatures: Array<{ time: number; numerator: number; denominator: number }>;
  tracks: MIDITrack[];
  duration: number;       // Total duration in seconds
}

export interface MIDIToKeyframeConfig {
  // Source selection
  trackIndex?: number;    // Specific track, or all if undefined
  channel?: number;       // Specific channel, or all if undefined
  noteRange?: { min: number; max: number }; // Filter notes

  // Mapping type
  mappingType: 'noteOnOff' | 'noteVelocity' | 'notePitch' | 'controlChange';

  // For controlChange type
  ccNumber?: number;

  // Value mapping
  valueMin: number;       // Output minimum
  valueMax: number;       // Output maximum

  // Timing
  fps: number;            // Frame rate for keyframe conversion

  // Options
  sustainPedal?: boolean; // Respect sustain pedal (CC64)
  interpolation?: 'linear' | 'hold' | 'bezier';
}

// ============================================================================
// Note Names
// ============================================================================

const NOTE_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];

function midiNoteToName(noteNumber: number): string {
  const octave = Math.floor(noteNumber / 12) - 1;
  const noteName = NOTE_NAMES[noteNumber % 12];
  return `${noteName}${octave}`;
}

// ============================================================================
// Controller Names
// ============================================================================

const CC_NAMES: Record<number, string> = {
  0: 'Bank Select',
  1: 'Modulation',
  2: 'Breath',
  4: 'Foot Controller',
  5: 'Portamento Time',
  7: 'Volume',
  8: 'Balance',
  10: 'Pan',
  11: 'Expression',
  64: 'Sustain Pedal',
  65: 'Portamento',
  66: 'Sostenuto',
  67: 'Soft Pedal',
  68: 'Legato',
  69: 'Hold 2',
  71: 'Resonance',
  72: 'Release Time',
  73: 'Attack Time',
  74: 'Cutoff',
  75: 'Decay Time',
  91: 'Reverb',
  93: 'Chorus',
  94: 'Detune',
  95: 'Phaser'
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
export async function parseMIDIFile(arrayBuffer: ArrayBuffer): Promise<MIDIParsedFile> {
  const view = new DataView(arrayBuffer);
  let offset = 0;

  // Read header chunk
  const headerChunk = readString(view, offset, 4);
  if (headerChunk !== 'MThd') {
    throw new Error('Invalid MIDI file: Missing MThd header');
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
  const timeSignatures: Array<{ time: number; numerator: number; denominator: number }> = [
    { time: 0, numerator: 4, denominator: 4 }
  ];

  for (let t = 0; t < numTracks; t++) {
    const trackResult = parseTrack(view, offset, ticksPerBeat, tempos);
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
    duration: maxDuration
  };
}

/**
 * Parse a single MIDI track
 */
function parseTrack(
  view: DataView,
  startOffset: number,
  ticksPerBeat: number,
  globalTempos: Array<{ time: number; bpm: number }>
): {
  track: MIDITrack;
  nextOffset: number;
  tempos: Array<{ time: number; bpm: number }>;
  timeSignatures: Array<{ time: number; numerator: number; denominator: number }>;
} {
  let offset = startOffset;

  // Read track header
  const trackChunk = readString(view, offset, 4);
  if (trackChunk !== 'MTrk') {
    throw new Error(`Invalid track header at offset ${offset}`);
  }
  offset += 4;

  const trackLength = view.getUint32(offset);
  offset += 4;

  const trackEnd = offset + trackLength;

  const track: MIDITrack = {
    name: '',
    notes: [],
    controlChanges: []
  };

  const tempos: Array<{ time: number; bpm: number }> = [];
  const timeSignatures: Array<{ time: number; numerator: number; denominator: number }> = [];

  // Track note-on events for pairing with note-off
  const activeNotes = new Map<string, { noteNumber: number; velocity: number; startTick: number; channel: number }>();

  let currentTick = 0;
  let runningStatus = 0;

  // Helper to convert ticks to seconds
  const ticksToSeconds = (ticks: number): number => {
    // Simple conversion using current tempo
    const tempo = globalTempos[globalTempos.length - 1]?.bpm ?? 120;
    const secondsPerBeat = 60 / tempo;
    return (ticks / ticksPerBeat) * secondsPerBeat;
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

    const eventType = status & 0xF0;
    const channel = status & 0x0F;

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
          track: 0
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
            track: 0
          });
          activeNotes.delete(key);
        }
      } else {
        activeNotes.set(key, { noteNumber, velocity, startTick: currentTick, channel });
      }
    }
    // Polyphonic Aftertouch
    else if (eventType === 0xA0) {
      offset += 2;
    }
    // Control Change
    else if (eventType === 0xB0) {
      const controller = view.getUint8(offset++);
      const value = view.getUint8(offset++);

      track.controlChanges.push({
        controller,
        controllerName: ccNumberToName(controller),
        value,
        time: ticksToSeconds(currentTick),
        channel,
        track: 0
      });
    }
    // Program Change
    else if (eventType === 0xC0) {
      offset++;
    }
    // Channel Aftertouch
    else if (eventType === 0xD0) {
      offset++;
    }
    // Pitch Bend
    else if (eventType === 0xE0) {
      offset += 2;
    }
    // Meta Event
    else if (status === 0xFF) {
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
        tempos.push({ time: ticksToSeconds(currentTick), bpm });
        globalTempos.push({ time: ticksToSeconds(currentTick), bpm });
      }
      // Time Signature
      else if (metaType === 0x58 && length >= 2) {
        const numerator = view.getUint8(offset);
        const denominator = Math.pow(2, view.getUint8(offset + 1));
        timeSignatures.push({ time: ticksToSeconds(currentTick), numerator, denominator });
      }

      offset += length;
    }
    // SysEx
    else if (status === 0xF0 || status === 0xF7) {
      const lengthResult = readVariableLength(view, offset);
      offset = lengthResult.nextOffset + lengthResult.value;
    }
  }

  return { track, nextOffset: trackEnd, tempos, timeSignatures };
}

/**
 * Read variable-length quantity
 */
function readVariableLength(view: DataView, offset: number): { value: number; nextOffset: number } {
  let value = 0;
  let byte: number;

  do {
    byte = view.getUint8(offset++);
    value = (value << 7) | (byte & 0x7F);
  } while (byte & 0x80);

  return { value, nextOffset: offset };
}

/**
 * Read string from buffer
 */
function readString(view: DataView, offset: number, length: number): string {
  let str = '';
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
 */
export function midiNotesToKeyframes(
  midiFile: MIDIParsedFile,
  config: MIDIToKeyframeConfig
): Keyframe<number>[] {
  const keyframes: Keyframe<number>[] = [];
  const fps = config.fps;

  // Collect notes from specified tracks/channels
  const notes: MIDINote[] = [];

  for (let t = 0; t < midiFile.tracks.length; t++) {
    if (config.trackIndex !== undefined && t !== config.trackIndex) continue;

    for (const note of midiFile.tracks[t].notes) {
      if (config.channel !== undefined && note.channel !== config.channel) continue;

      if (config.noteRange) {
        if (note.noteNumber < config.noteRange.min || note.noteNumber > config.noteRange.max) continue;
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
      case 'noteOnOff':
        // Create on/off keyframes
        keyframes.push({
          id: `midi_kf_${keyframeId++}`,
          frame: startFrame,
          value: config.valueMax,
          interpolation: config.interpolation || 'hold',
          inHandle: { frame: 0, value: 0, enabled: false },
          outHandle: { frame: 0, value: 0, enabled: false },
          controlMode: 'smooth' as const
        });
        keyframes.push({
          id: `midi_kf_${keyframeId++}`,
          frame: endFrame,
          value: config.valueMin,
          interpolation: config.interpolation || 'hold',
          inHandle: { frame: 0, value: 0, enabled: false },
          outHandle: { frame: 0, value: 0, enabled: false },
          controlMode: 'smooth' as const
        });
        break;

      case 'noteVelocity':
        // Value based on velocity
        value = config.valueMin + (note.velocity / 127) * (config.valueMax - config.valueMin);
        keyframes.push({
          id: `midi_kf_${keyframeId++}`,
          frame: startFrame,
          value,
          interpolation: config.interpolation || 'linear',
          inHandle: { frame: 0, value: 0, enabled: false },
          outHandle: { frame: 0, value: 0, enabled: false },
          controlMode: 'smooth' as const
        });
        keyframes.push({
          id: `midi_kf_${keyframeId++}`,
          frame: endFrame,
          value: config.valueMin,
          interpolation: config.interpolation || 'linear',
          inHandle: { frame: 0, value: 0, enabled: false },
          outHandle: { frame: 0, value: 0, enabled: false },
          controlMode: 'smooth' as const
        });
        break;

      case 'notePitch':
        // Value based on note number
        const pitchRange = (config.noteRange?.max ?? 127) - (config.noteRange?.min ?? 0);
        const normalizedPitch = (note.noteNumber - (config.noteRange?.min ?? 0)) / pitchRange;
        value = config.valueMin + normalizedPitch * (config.valueMax - config.valueMin);
        keyframes.push({
          id: `midi_kf_${keyframeId++}`,
          frame: startFrame,
          value,
          interpolation: config.interpolation || 'linear',
          inHandle: { frame: 0, value: 0, enabled: false },
          outHandle: { frame: 0, value: 0, enabled: false },
          controlMode: 'smooth' as const
        });
        break;
    }
  }

  // Sort and deduplicate
  keyframes.sort((a, b) => a.frame - b.frame);

  return keyframes;
}

/**
 * Convert MIDI Control Changes to keyframes
 */
export function midiCCToKeyframes(
  midiFile: MIDIParsedFile,
  config: MIDIToKeyframeConfig
): Keyframe<number>[] {
  if (config.ccNumber === undefined) {
    throw new Error('ccNumber is required for controlChange mapping');
  }

  const keyframes: Keyframe<number>[] = [];
  const fps = config.fps;

  // Collect CC events from specified tracks/channels
  const ccEvents: MIDIControlChange[] = [];

  for (let t = 0; t < midiFile.tracks.length; t++) {
    if (config.trackIndex !== undefined && t !== config.trackIndex) continue;

    for (const cc of midiFile.tracks[t].controlChanges) {
      if (config.channel !== undefined && cc.channel !== config.channel) continue;
      if (cc.controller !== config.ccNumber) continue;

      ccEvents.push({ ...cc, track: t });
    }
  }

  // Sort by time
  ccEvents.sort((a, b) => a.time - b.time);

  let keyframeId = 0;

  for (const cc of ccEvents) {
    const frame = Math.round(cc.time * fps);
    const value = config.valueMin + (cc.value / 127) * (config.valueMax - config.valueMin);

    keyframes.push({
      id: `midi_kf_${keyframeId++}`,
      frame,
      value,
      interpolation: config.interpolation || 'linear',
      inHandle: { frame: 0, value: 0, enabled: false },
      outHandle: { frame: 0, value: 0, enabled: false },
      controlMode: 'smooth' as const
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
  config: MIDIToKeyframeConfig
): AnimatableProperty<number> {
  const keyframes = config.mappingType === 'controlChange'
    ? midiCCToKeyframes(midiFile, config)
    : midiNotesToKeyframes(midiFile, config);

  const id = `midi_prop_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;

  return {
    id,
    name,
    defaultValue: config.valueMin,
    animated: keyframes.length > 0,
    keyframes
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
  ccNumberToName
};
