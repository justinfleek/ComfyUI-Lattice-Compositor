/**
 * MIDIService.ts - Web MIDI API wrapper for Lattice Compositor
 *
 * Provides real-time MIDI device capture, message filtering, and property mapping.
 * Inspired by Jovi_MIDI with browser-native Web MIDI API.
 */

import { isFiniteNumber, safeCoordinateDefault } from "@/utils/typeGuards";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

export interface MIDIDeviceInfo {
  id: string;
  name: string;
  manufacturer: string;
  type: "input" | "output";
  state: "connected" | "disconnected";
}

export interface MIDIMessage {
  timestamp: number;
  type: MIDIMessageType;
  channel: number; // 1-16
  note?: number; // 0-127 for note events
  velocity?: number; // 0-127 for note events
  controller?: number; // 0-127 for CC events
  value?: number; // 0-127 for CC, 0-16383 for pitch bend
  program?: number; // 0-127 for program change
  raw: Uint8Array;
}

export type MIDIMessageType =
  | "note-on"
  | "note-off"
  | "control-change"
  | "program-change"
  | "pitch-bend"
  | "aftertouch"
  | "channel-pressure"
  | "system";

export interface MIDIFilter {
  channels?: number[]; // 1-16, empty = all
  types?: MIDIMessageType[];
  noteRange?: { min: number; max: number }; // 0-127
  velocityRange?: { min: number; max: number }; // 0-127
  controllers?: number[]; // Specific CC numbers
}

export interface MIDIMapping {
  id: string;
  enabled: boolean;
  deviceId: string;
  filter: MIDIFilter;

  // Target
  targetLayerId: string;
  targetPropertyPath: string;

  // Transform
  inputMin: number; // 0-127
  inputMax: number; // 0-127
  outputMin: number;
  outputMax: number;
  smoothing: number; // 0-1

  // Mode
  mode: "absolute" | "relative" | "toggle" | "trigger";

  // For note events
  useVelocity: boolean;
  useNoteNumber: boolean;
}

export type MIDIEventCallback = (message: MIDIMessage) => void;

// ════════════════════════════════════════════════════════════════════════════
//                                                  // midi // service // class
// ════════════════════════════════════════════════════════════════════════════

export class MIDIService {
  private midiAccess: MIDIAccess | null = null;
  private inputs: Map<string, MIDIInput> = new Map();
  private outputs: Map<string, MIDIOutput> = new Map();
  private listeners: Map<string, Set<MIDIEventCallback>> = new Map();
  private globalListeners: Set<MIDIEventCallback> = new Set();
  private messageHistory: MIDIMessage[] = [];
  private maxHistorySize: number = 1000;
  private isInitialized: boolean = false;
  private initPromise: Promise<boolean> | null = null;

  // Current state for property mapping
  private ccValues: Map<string, number> = new Map(); // "channel:controller" -> value
  private noteStates: Map<string, { velocity: number; timestamp: number }> =
    new Map(); // "channel:note" -> state
  private smoothedValues: Map<string, number> = new Map(); // mapping id -> smoothed value

  // ════════════════════════════════════════════════════════════════════════════
  //                                                            // initialization
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Initialize MIDI access
   */
  async initialize(): Promise<boolean> {
    if (this.isInitialized) return true;
    if (this.initPromise) return this.initPromise;

    this.initPromise = this._doInitialize();
    return this.initPromise;
  }

  private async _doInitialize(): Promise<boolean> {
    // Check for Web MIDI API support
    if (!navigator.requestMIDIAccess) {
      console.warn("Web MIDI API not supported in this browser");
      return false;
    }

    try {
      // Request MIDI access (with sysex for future extensibility)
      this.midiAccess = await navigator.requestMIDIAccess({ sysex: false });

      // Set up device change listeners
      this.midiAccess.onstatechange = this.handleStateChange.bind(this);

      // Register existing inputs
      this.midiAccess.inputs.forEach((input, id) => {
        this.registerInput(id, input);
      });

      // Register existing outputs
      this.midiAccess.outputs.forEach((output, id) => {
        this.outputs.set(id, output);
      });

      this.isInitialized = true;
      console.log(
        `MIDI initialized: ${this.inputs.size} inputs, ${this.outputs.size} outputs`,
      );
      return true;
    } catch (error) {
      console.error("Failed to initialize MIDI:", error);
      return false;
    }
  }

  /**
   * Check if MIDI is available
   */
  isAvailable(): boolean {
    return !!navigator.requestMIDIAccess;
  }

  /**
   * Check if MIDI is initialized
   */
  isReady(): boolean {
    return this.isInitialized;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                      // device // management
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Get all connected MIDI devices
   */
  getDevices(): MIDIDeviceInfo[] {
    const devices: MIDIDeviceInfo[] = [];

    this.inputs.forEach((input, id) => {
      devices.push({
        id,
        name: input.name || "Unknown Input",
        manufacturer: input.manufacturer || "Unknown",
        type: "input",
        state: input.state as "connected" | "disconnected",
      });
    });

    this.outputs.forEach((output, id) => {
      devices.push({
        id,
        name: output.name || "Unknown Output",
        manufacturer: output.manufacturer || "Unknown",
        type: "output",
        state: output.state as "connected" | "disconnected",
      });
    });

    return devices;
  }

  /**
   * Get input devices only
   */
  getInputDevices(): MIDIDeviceInfo[] {
    return this.getDevices().filter((d) => d.type === "input");
  }

  /**
   * Get output devices only
   */
  getOutputDevices(): MIDIDeviceInfo[] {
    return this.getDevices().filter((d) => d.type === "output");
  }

  private registerInput(id: string, input: MIDIInput): void {
    this.inputs.set(id, input);
    input.onmidimessage = (event) => this.handleMIDIMessage(id, event);
  }

  private handleStateChange(event: MIDIConnectionEvent): void {
    const port = event.port;
    if (!port) return;

    if (port.type === "input") {
      if (port.state === "connected") {
        this.registerInput(port.id, port as MIDIInput);
        console.log(`MIDI input connected: ${port.name}`);
      } else {
        this.inputs.delete(port.id);
        console.log(`MIDI input disconnected: ${port.name}`);
      }
    } else if (port.type === "output") {
      if (port.state === "connected") {
        this.outputs.set(port.id, port as MIDIOutput);
        console.log(`MIDI output connected: ${port.name}`);
      } else {
        this.outputs.delete(port.id);
        console.log(`MIDI output disconnected: ${port.name}`);
      }
    }

    // Notify global listeners of device change
    // (Could emit a separate event type for this)
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // message // handling
  // ════════════════════════════════════════════════════════════════════════════

  private handleMIDIMessage(deviceId: string, event: MIDIMessageEvent): void {
    if (!event.data || event.data.length < 1) return;

    let message: MIDIMessage;
    try {
      message = this.parseMIDIMessage(event.data, event.timeStamp);
    } catch (error) {
      // Unknown MIDI message types are logged but not fatal
      console.warn(`[MIDIService] Skipping unknown MIDI message:`, error);
      return;
    }

    // Store in history
    this.messageHistory.push(message);
    if (this.messageHistory.length > this.maxHistorySize) {
      this.messageHistory.shift();
    }

    // Update state maps
    this.updateState(message);

    // Notify device-specific listeners
    const deviceListeners = this.listeners.get(deviceId);
    if (deviceListeners) {
      deviceListeners.forEach((callback) => callback(message));
    }

    // Notify global listeners
    this.globalListeners.forEach((callback) => callback(message));
  }

  private parseMIDIMessage(
    data: Uint8Array,
    timestamp: number,
  ): MIDIMessage {
    const status = data[0];
    const messageType = status & 0xf0;
    const channel = (status & 0x0f) + 1; // MIDI channels are 1-16

    const message: MIDIMessage = {
      timestamp,
      type: "system",
      channel,
      raw: data,
    };

    switch (messageType) {
      case 0x90: // Note On
        message.type = data[2] > 0 ? "note-on" : "note-off"; // Velocity 0 = note off
        message.note = data[1];
        message.velocity = data[2];
        break;

      case 0x80: // Note Off
        message.type = "note-off";
        message.note = data[1];
        message.velocity = data[2];
        break;

      case 0xb0: // Control Change
        message.type = "control-change";
        message.controller = data[1];
        message.value = data[2];
        break;

      case 0xc0: // Program Change
        message.type = "program-change";
        message.program = data[1];
        break;

      case 0xe0: // Pitch Bend
        message.type = "pitch-bend";
        message.value = (data[2] << 7) | data[1]; // 14-bit value
        break;

      case 0xa0: // Polyphonic Aftertouch
        message.type = "aftertouch";
        message.note = data[1];
        message.value = data[2];
        break;

      case 0xd0: // Channel Pressure
        message.type = "channel-pressure";
        message.value = data[1];
        break;

      case 0xf0: // System messages
        message.type = "system";
        message.channel = 0;
        break;

      default:
        throw new Error(`[MIDIService] Cannot parse MIDI message: Unknown status byte 0x${status.toString(16).padStart(2, "0")} (decimal ${status})`);
    }

    return message;
  }

  private updateState(message: MIDIMessage): void {
    if (
      message.type === "control-change" &&
      message.controller !== undefined &&
      message.value !== undefined
    ) {
      const key = `${message.channel}:${message.controller}`;
      this.ccValues.set(key, message.value);
    }

    if (message.type === "note-on" && message.note !== undefined) {
      const key = `${message.channel}:${message.note}`;
      this.noteStates.set(key, {
        velocity: message.velocity || 127,
        timestamp: message.timestamp,
      });
    }

    if (message.type === "note-off" && message.note !== undefined) {
      const key = `${message.channel}:${message.note}`;
      this.noteStates.delete(key);
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                 // listeners
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Add a listener for all MIDI messages
   */
  addGlobalListener(callback: MIDIEventCallback): void {
    this.globalListeners.add(callback);
  }

  /**
   * Remove a global listener
   */
  removeGlobalListener(callback: MIDIEventCallback): void {
    this.globalListeners.delete(callback);
  }

  /**
   * Add a listener for a specific device
   */
  addDeviceListener(deviceId: string, callback: MIDIEventCallback): void {
    if (!this.listeners.has(deviceId)) {
      this.listeners.set(deviceId, new Set());
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const listenerSet = this.listeners.get(deviceId);
    if (listenerSet != null && typeof listenerSet === "object" && typeof listenerSet.add === "function") {
      listenerSet.add(callback);
    }
  }

  /**
   * Remove a device-specific listener
   */
  removeDeviceListener(deviceId: string, callback: MIDIEventCallback): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const listenerSet = this.listeners.get(deviceId);
    if (listenerSet != null && typeof listenerSet === "object" && typeof listenerSet.delete === "function") {
      listenerSet.delete(callback);
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                      // message // filtering
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Check if a message passes a filter
   */
  matchesFilter(message: MIDIMessage, filter: MIDIFilter): boolean {
    // Channel filter
    if (filter.channels && filter.channels.length > 0) {
      if (!filter.channels.includes(message.channel)) return false;
    }

    // Type filter
    if (filter.types && filter.types.length > 0) {
      if (!filter.types.includes(message.type)) return false;
    }

    // Note range filter
    if (filter.noteRange && message.note !== undefined) {
      if (
        message.note < filter.noteRange.min ||
        message.note > filter.noteRange.max
      ) {
        return false;
      }
    }

    // Velocity range filter
    if (filter.velocityRange && message.velocity !== undefined) {
      if (
        message.velocity < filter.velocityRange.min ||
        message.velocity > filter.velocityRange.max
      ) {
        return false;
      }
    }

    // Controller filter
    if (
      filter.controllers &&
      filter.controllers.length > 0 &&
      message.controller !== undefined
    ) {
      if (!filter.controllers.includes(message.controller)) return false;
    }

    return true;
  }

  /**
   * Create a filtered listener
   */
  addFilteredListener(
    filter: MIDIFilter,
    callback: MIDIEventCallback,
  ): () => void {
    const wrappedCallback = (message: MIDIMessage) => {
      if (this.matchesFilter(message, filter)) {
        callback(message);
      }
    };

    this.addGlobalListener(wrappedCallback);
    return () => this.removeGlobalListener(wrappedCallback);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                           // value // access
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Get the current value of a CC controller
   */
  getCCValue(channel: number, controller: number): number | undefined {
    return this.ccValues.get(`${channel}:${controller}`);
  }

  /**
   * Get the current state of a note
   */
  getNoteState(
    channel: number,
    note: number,
  ): { velocity: number; timestamp: number } | undefined {
    return this.noteStates.get(`${channel}:${note}`);
  }

  /**
   * Check if a note is currently held
   */
  isNoteOn(channel: number, note: number): boolean {
    return this.noteStates.has(`${channel}:${note}`);
  }

  /**
   * Get all currently held notes
   */
  getHeldNotes(): { channel: number; note: number; velocity: number }[] {
    const notes: { channel: number; note: number; velocity: number }[] = [];
    this.noteStates.forEach((state, key) => {
      const [channel, note] = key.split(":").map(Number);
      notes.push({ channel, note, velocity: state.velocity });
    });
    return notes;
  }

  /**
   * Get message history
   */
  getMessageHistory(limit?: number): MIDIMessage[] {
    if (limit) {
      return this.messageHistory.slice(-limit);
    }
    return [...this.messageHistory];
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // property // mapping
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Calculate mapped value from MIDI input
   */
  getMappedValue(mapping: MIDIMapping, message?: MIDIMessage): number {
    let inputValue = 0;

    if (message) {
      // Use the message value
      if (mapping.useVelocity && message.velocity !== undefined) {
        inputValue = message.velocity;
      } else if (mapping.useNoteNumber && message.note !== undefined) {
        inputValue = message.note;
      } else if (message.value !== undefined) {
        inputValue =
          message.type === "pitch-bend"
            ? (message.value / 16383) * 127 // Normalize pitch bend to 0-127
            : message.value;
      } else if (message.controller !== undefined) {
        // Type proof: MIDI CC value ∈ number | undefined → number (coordinate-like, can be negative)
        inputValue = safeCoordinateDefault(
          this.getCCValue(message.channel, message.controller),
          0,
          `getCCValue(${message.channel}, ${message.controller})`,
        );
      }
    } else {
      // Use stored CC value (for continuous display)
      // Would need filter info to know which CC to read
      return this.smoothedValues.get(mapping.id) || mapping.outputMin;
    }

    // Map input range to output range
    const normalizedInput =
      (inputValue - mapping.inputMin) / (mapping.inputMax - mapping.inputMin);
    const clampedInput = Math.max(0, Math.min(1, normalizedInput));
    let outputValue =
      mapping.outputMin +
      clampedInput * (mapping.outputMax - mapping.outputMin);

    // Apply smoothing
    // Type proof: smoothedValue ∈ number | undefined → number
    const cachedSmoothed = this.smoothedValues.get(mapping.id);
    const currentSmoothed = isFiniteNumber(cachedSmoothed)
      ? cachedSmoothed
      : outputValue;
    outputValue =
      currentSmoothed +
      (outputValue - currentSmoothed) * (1 - mapping.smoothing);
    this.smoothedValues.set(mapping.id, outputValue);

    return outputValue;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                            // midi // output
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Send a MIDI message to an output device
   */
  sendMessage(deviceId: string, message: number[]): boolean {
    const output = this.outputs.get(deviceId);
    if (!output) {
      console.warn(`MIDI output not found: ${deviceId}`);
      return false;
    }

    try {
      output.send(message);
      return true;
    } catch (error) {
      console.error("Failed to send MIDI message:", error);
      return false;
    }
  }

  /**
   * Send a Note On message
   */
  sendNoteOn(
    deviceId: string,
    channel: number,
    note: number,
    velocity: number = 127,
  ): boolean {
    const status = 0x90 | (channel - 1);
    return this.sendMessage(deviceId, [status, note, velocity]);
  }

  /**
   * Send a Note Off message
   */
  sendNoteOff(
    deviceId: string,
    channel: number,
    note: number,
    velocity: number = 0,
  ): boolean {
    const status = 0x80 | (channel - 1);
    return this.sendMessage(deviceId, [status, note, velocity]);
  }

  /**
   * Send a Control Change message
   */
  sendCC(
    deviceId: string,
    channel: number,
    controller: number,
    value: number,
  ): boolean {
    const status = 0xb0 | (channel - 1);
    return this.sendMessage(deviceId, [status, controller, value]);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                   // midi // file // parsing
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Parse a MIDI file into messages
   * Note: This is a basic implementation. For full MIDI file support,
   * consider using a library like midi-parser-js
   */
  async parseMIDIFile(file: File): Promise<MIDIMessage[]> {
    const buffer = await file.arrayBuffer();
    const data = new Uint8Array(buffer);

    // Verify MIDI file header
    if (
      data[0] !== 0x4d ||
      data[1] !== 0x54 ||
      data[2] !== 0x68 ||
      data[3] !== 0x64
    ) {
      throw new Error("Invalid MIDI file: Missing MThd header");
    }

    // This is a simplified parser - full MIDI files are complex
    // For production use, integrate a proper MIDI parser library
    console.warn(
      "MIDI file parsing is simplified. Consider using midi-parser-js for full support.",
    );

    const messages: MIDIMessage[] = [];
    // ... Full parsing would go here

    return messages;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                   // cleanup
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Dispose of MIDI service
   */
  dispose(): void {
    // Remove all listeners from inputs
    this.inputs.forEach((input) => {
      input.onmidimessage = null;
    });

    // Clear all stored data
    this.inputs.clear();
    this.outputs.clear();
    this.listeners.clear();
    this.globalListeners.clear();
    this.messageHistory = [];
    this.ccValues.clear();
    this.noteStates.clear();
    this.smoothedValues.clear();

    this.midiAccess = null;
    this.isInitialized = false;
    this.initPromise = null;

    console.log("MIDI service disposed");
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                     // singleton // instance
// ════════════════════════════════════════════════════════════════════════════

let midiServiceInstance: MIDIService | null = null;

export function getMIDIService(): MIDIService {
  if (!midiServiceInstance) {
    midiServiceInstance = new MIDIService();
  }
  return midiServiceInstance;
}

export function disposeMIDIService(): void {
  if (midiServiceInstance) {
    midiServiceInstance.dispose();
    midiServiceInstance = null;
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                      // utility // functions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Get note name from MIDI note number
 */
export function midiNoteToName(note: number): string {
  const names = [
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
  const octave = Math.floor(note / 12) - 1;
  const name = names[note % 12];
  return `${name}${octave}`;
}

/**
 * Get MIDI note number from note name
 */
export function noteNameToMidi(name: string): number {
  const match = name.match(/^([A-G]#?)(-?\d+)$/i);
  if (!match) return -1;

  const noteNames: Record<string, number> = {
    C: 0,
    "C#": 1,
    D: 2,
    "D#": 3,
    E: 4,
    F: 5,
    "F#": 6,
    G: 7,
    "G#": 8,
    A: 9,
    "A#": 10,
    B: 11,
  };

  const noteName = match[1].toUpperCase();
  const octave = parseInt(match[2], 10);

  if (!(noteName in noteNames)) return -1;

  return (octave + 1) * 12 + noteNames[noteName];
}

/**
 * Convert CC value (0-127) to normalized (0-1)
 */
export function ccToNormalized(value: number): number {
  return value / 127;
}

/**
 * Convert normalized (0-1) to CC value (0-127)
 */
export function normalizedToCC(value: number): number {
  return Math.round(value * 127);
}
