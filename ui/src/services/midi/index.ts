/**
 * MIDI Module - Index
 *
 * Web MIDI API integration for Lattice Compositor.
 * Enables MIDI controller input for real-time property control.
 */

export {
  ccToNormalized,
  disposeMIDIService,
  getMIDIService,
  type MIDIDeviceInfo,
  type MIDIEventCallback,
  type MIDIFilter,
  type MIDIMapping,
  type MIDIMessage,
  type MIDIMessageType,
  MIDIService,
  midiNoteToName,
  normalizedToCC,
  noteNameToMidi,
} from "./MIDIService";
