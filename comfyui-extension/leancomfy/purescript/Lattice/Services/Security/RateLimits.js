// FFI bindings for RateLimits.purs

// Date utilities
export const getCurrentDateUTC = () => () => {
  return new Date().toISOString().split("T")[0];
};

export const getTomorrowMidnightUTC = () => () => {
  const tomorrow = new Date();
  tomorrow.setUTCDate(tomorrow.getUTCDate() + 1);
  tomorrow.setUTCHours(0, 0, 0, 0);
  return tomorrow.toISOString();
};

export const getTimeUntilReset = () => () => {
  const now = new Date();
  const tomorrow = new Date();
  tomorrow.setUTCDate(tomorrow.getUTCDate() + 1);
  tomorrow.setUTCHours(0, 0, 0, 0);

  const diffMs = tomorrow.getTime() - now.getTime();
  const hours = Math.floor(diffMs / (1000 * 60 * 60));
  const minutes = Math.floor((diffMs % (1000 * 60 * 60)) / (1000 * 60));

  if (hours > 0) {
    return `${hours}h ${minutes}m`;
  }
  return `${minutes}m`;
};

export const getCurrentISOTimestamp = () => () => {
  return new Date().toISOString();
};

// localStorage
export const localStorageGetItem = (key) => () => {
  try {
    const value = localStorage.getItem(key);
    if (value === null) {
      return null; // PureScript Nothing
    }
    return value; // PureScript Just value
  } catch {
    return null;
  }
};

export const localStorageSetItem = (key) => (value) => () => {
  try {
    localStorage.setItem(key, value);
  } catch (e) {
    console.warn("[SECURITY] Failed to save to localStorage:", e);
  }
};

// sessionStorage
export const sessionStorageGetItem = (key) => () => {
  try {
    const value = sessionStorage.getItem(key);
    if (value === null) {
      return null;
    }
    return value;
  } catch {
    return null;
  }
};

export const sessionStorageSetItem = (key) => (value) => () => {
  try {
    sessionStorage.setItem(key, value);
  } catch (e) {
    console.warn("[SECURITY] Failed to save to sessionStorage:", e);
  }
};

// JSON parsing for counts (Map String Int)
export const parseCountsJson = (json) => {
  try {
    const parsed = JSON.parse(json);
    if (parsed && typeof parsed.counts === "object") {
      // Return as array of tuples for PureScript Map.fromFoldable
      return Object.entries(parsed.counts).map(([k, v]) => [k, v]);
    }
    return null;
  } catch {
    return null;
  }
};

export const stringifyCountsJson = (counts) => {
  // counts is an array of tuples from PureScript Map.toUnfoldable
  const obj = {};
  for (const [k, v] of counts) {
    obj[k] = v;
  }
  return JSON.stringify(obj);
};

// JSON field extraction helpers
export const extractDateFromJson = (json) => {
  try {
    const parsed = JSON.parse(json);
    return parsed.date || "";
  } catch {
    return "";
  }
};

export const extractLastResetFromJson = (json) => {
  try {
    const parsed = JSON.parse(json);
    return parsed.lastReset || "";
  } catch {
    return "";
  }
};

// State refs (initialized on module load)
let _customLimits = new Map();
let _sessionCounts = new Map();

export const customLimitsRef = {
  read: () => () => Array.from(_customLimits.entries()),
  write: (entries) => () => {
    _customLimits = new Map(entries);
  },
  modify: (f) => () => {
    const current = Array.from(_customLimits.entries());
    const newVal = f(current);
    _customLimits = new Map(newVal);
    return newVal;
  }
};

export const sessionCountsRef = {
  read: () => () => Array.from(_sessionCounts.entries()),
  write: (entries) => () => {
    _sessionCounts = new Map(entries);
  },
  modify: (f) => () => {
    const current = Array.from(_sessionCounts.entries());
    const newVal = f(current);
    _sessionCounts = new Map(newVal);
    return newVal;
  }
};
