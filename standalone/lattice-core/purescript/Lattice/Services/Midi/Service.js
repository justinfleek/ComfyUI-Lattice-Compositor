// FFI bindings for Lattice.Services.Midi.Service
// Web MIDI API integration

// Singleton instance
let midiAccess = null;
let isInitialized = false;
const inputs = new Map();
const outputs = new Map();
const globalListeners = new Set();
const deviceListeners = new Map();
const ccValues = new Map();
const noteStates = new Map();
const messageHistory = [];
const MAX_HISTORY = 1000;

// Check if Web MIDI API is available
export const isWebMIDIAvailable = () => () => {
  return !!navigator.requestMIDIAccess;
};

// Initialize MIDI access
export const initializeMIDIImpl = () => async () => {
  if (isInitialized) return true;

  if (!navigator.requestMIDIAccess) {
    console.warn("Web MIDI API not supported");
    return false;
  }

  try {
    midiAccess = await navigator.requestMIDIAccess({ sysex: false });

    // Register state change handler
    midiAccess.onstatechange = handleStateChange;

    // Register existing inputs
    midiAccess.inputs.forEach((input, id) => {
      registerInput(id, input);
    });

    // Register existing outputs
    midiAccess.outputs.forEach((output, id) => {
      outputs.set(id, output);
    });

    isInitialized = true;
    console.log(`MIDI initialized: ${inputs.size} inputs, ${outputs.size} outputs`);
    return true;
  } catch (error) {
    console.error("Failed to initialize MIDI:", error);
    return false;
  }
};

// Register an input device
function registerInput(id, input) {
  inputs.set(id, input);
  input.onmidimessage = (event) => handleMIDIMessage(id, event);
}

// Handle device state changes
function handleStateChange(event) {
  const port = event.port;
  if (!port) return;

  if (port.type === "input") {
    if (port.state === "connected") {
      registerInput(port.id, port);
      console.log(`MIDI input connected: ${port.name}`);
    } else {
      inputs.delete(port.id);
      console.log(`MIDI input disconnected: ${port.name}`);
    }
  } else if (port.type === "output") {
    if (port.state === "connected") {
      outputs.set(port.id, port);
      console.log(`MIDI output connected: ${port.name}`);
    } else {
      outputs.delete(port.id);
      console.log(`MIDI output disconnected: ${port.name}`);
    }
  }
}

// Parse MIDI message
function parseMIDIMessage(data, timestamp) {
  const status = data[0];
  const messageType = status & 0xF0;
  const channel = (status & 0x0F) + 1;

  const message = {
    timestamp,
    msgType: "SystemMessage",
    channel,
    note: null,
    velocity: null,
    controller: null,
    value: null,
    program: null,
    raw: Array.from(data)
  };

  switch (messageType) {
    case 0x90: // Note On
      message.msgType = data[2] > 0 ? "NoteOn" : "NoteOff";
      message.note = data[1];
      message.velocity = data[2];
      break;
    case 0x80: // Note Off
      message.msgType = "NoteOff";
      message.note = data[1];
      message.velocity = data[2];
      break;
    case 0xB0: // Control Change
      message.msgType = "ControlChange";
      message.controller = data[1];
      message.value = data[2];
      break;
    case 0xC0: // Program Change
      message.msgType = "ProgramChange";
      message.program = data[1];
      break;
    case 0xE0: // Pitch Bend
      message.msgType = "PitchBend";
      message.value = (data[2] << 7) | data[1];
      break;
    case 0xA0: // Polyphonic Aftertouch
      message.msgType = "Aftertouch";
      message.note = data[1];
      message.value = data[2];
      break;
    case 0xD0: // Channel Pressure
      message.msgType = "ChannelPressure";
      message.value = data[1];
      break;
  }

  return message;
}

// Handle incoming MIDI message
function handleMIDIMessage(deviceId, event) {
  if (!event.data || event.data.length < 1) return;

  const message = parseMIDIMessage(event.data, event.timeStamp);

  // Store in history
  messageHistory.push(message);
  if (messageHistory.length > MAX_HISTORY) {
    messageHistory.shift();
  }

  // Update state
  if (message.msgType === "ControlChange" && message.controller !== null) {
    ccValues.set(`${message.channel}:${message.controller}`, message.value);
  }
  if (message.msgType === "NoteOn" && message.note !== null) {
    noteStates.set(`${message.channel}:${message.note}`, {
      velocity: message.velocity || 127,
      timestamp: message.timestamp
    });
  }
  if (message.msgType === "NoteOff" && message.note !== null) {
    noteStates.delete(`${message.channel}:${message.note}`);
  }

  // Notify device listeners
  const listeners = deviceListeners.get(deviceId);
  if (listeners) {
    listeners.forEach(cb => cb(message)());
  }

  // Notify global listeners
  globalListeners.forEach(cb => cb(message)());
}

// Get service instance (singleton)
export const getServiceInstanceImpl = () => () => ({});

// Check if initialized
export const isInitializedImpl = (_handle) => () => isInitialized;

// Get devices
export const getDevicesImpl = (_handle) => () => {
  const devices = [];

  inputs.forEach((input, id) => {
    devices.push({
      id,
      name: input.name || "Unknown Input",
      manufacturer: input.manufacturer || "Unknown",
      deviceType: "MIDIInput",
      state: input.state === "connected" ? "MIDIConnected" : "MIDIDisconnected"
    });
  });

  outputs.forEach((output, id) => {
    devices.push({
      id,
      name: output.name || "Unknown Output",
      manufacturer: output.manufacturer || "Unknown",
      deviceType: "MIDIOutput",
      state: output.state === "connected" ? "MIDIConnected" : "MIDIDisconnected"
    });
  });

  return devices;
};

// Add global listener
export const addGlobalListenerImpl = (_handle) => (callback) => () => {
  globalListeners.add(callback);
};

// Remove global listener
export const removeGlobalListenerImpl = (_handle) => (callback) => () => {
  globalListeners.delete(callback);
};

// Add device listener
export const addDeviceListenerImpl = (_handle) => (deviceId) => (callback) => () => {
  if (!deviceListeners.has(deviceId)) {
    deviceListeners.set(deviceId, new Set());
  }
  deviceListeners.get(deviceId).add(callback);
};

// Remove device listener
export const removeDeviceListenerImpl = (_handle) => (deviceId) => (callback) => () => {
  const listeners = deviceListeners.get(deviceId);
  if (listeners) {
    listeners.delete(callback);
  }
};

// Get CC value
export const getCCValueImpl = (_handle) => (channel) => (controller) => () => {
  const value = ccValues.get(`${channel}:${controller}`);
  return value !== undefined ? value : null;
};

// Get note state
export const getNoteStateImpl = (_handle) => (channel) => (note) => () => {
  return noteStates.get(`${channel}:${note}`) || null;
};

// Get held notes
export const getHeldNotesImpl = (_handle) => () => {
  const notes = [];
  noteStates.forEach((state, key) => {
    const [channel, note] = key.split(":").map(Number);
    notes.push({ channel, note, velocity: state.velocity });
  });
  return notes;
};

// Get message history
export const getMessageHistoryImpl = (_handle) => (limit) => () => {
  if (limit !== null) {
    return messageHistory.slice(-limit);
  }
  return [...messageHistory];
};

// Send MIDI message
export const sendMessageImpl = (_handle) => (deviceId) => (message) => () => {
  const output = outputs.get(deviceId);
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
};

// Dispose service
export const disposeImpl = (_handle) => () => {
  inputs.forEach(input => {
    input.onmidimessage = null;
  });

  inputs.clear();
  outputs.clear();
  globalListeners.clear();
  deviceListeners.clear();
  messageHistory.length = 0;
  ccValues.clear();
  noteStates.clear();

  midiAccess = null;
  isInitialized = false;

  console.log("MIDI service disposed");
};
