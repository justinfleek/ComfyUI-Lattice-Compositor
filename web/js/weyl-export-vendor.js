var __accessCheck$1 = (obj, member, msg) => {
  if (!member.has(obj))
    throw TypeError("Cannot " + msg);
};
var __privateGet$1 = (obj, member, getter) => {
  __accessCheck$1(obj, member, "read from private field");
  return getter ? getter.call(obj) : member.get(obj);
};
var __privateAdd$1 = (obj, member, value) => {
  if (member.has(obj))
    throw TypeError("Cannot add the same private member more than once");
  member instanceof WeakSet ? member.add(obj) : member.set(obj, value);
};
var __privateSet$1 = (obj, member, value, setter) => {
  __accessCheck$1(obj, member, "write to private field");
  member.set(obj, value);
  return value;
};
var __privateMethod$1 = (obj, member, method) => {
  __accessCheck$1(obj, member, "access private method");
  return method;
};

// src/ebml.ts
var EBMLFloat32 = class {
  constructor(value) {
    this.value = value;
  }
};
var EBMLFloat64 = class {
  constructor(value) {
    this.value = value;
  }
};
var measureUnsignedInt = (value) => {
  if (value < 1 << 8) {
    return 1;
  } else if (value < 1 << 16) {
    return 2;
  } else if (value < 1 << 24) {
    return 3;
  } else if (value < 2 ** 32) {
    return 4;
  } else if (value < 2 ** 40) {
    return 5;
  } else {
    return 6;
  }
};
var measureEBMLVarInt = (value) => {
  if (value < (1 << 7) - 1) {
    return 1;
  } else if (value < (1 << 14) - 1) {
    return 2;
  } else if (value < (1 << 21) - 1) {
    return 3;
  } else if (value < (1 << 28) - 1) {
    return 4;
  } else if (value < 2 ** 35 - 1) {
    return 5;
  } else if (value < 2 ** 42 - 1) {
    return 6;
  } else {
    throw new Error("EBML VINT size not supported " + value);
  }
};

// src/misc.ts
var readBits = (bytes, start, end) => {
  let result = 0;
  for (let i = start; i < end; i++) {
    let byteIndex = Math.floor(i / 8);
    let byte = bytes[byteIndex];
    let bitIndex = 7 - (i & 7);
    let bit = (byte & 1 << bitIndex) >> bitIndex;
    result <<= 1;
    result |= bit;
  }
  return result;
};
var writeBits = (bytes, start, end, value) => {
  for (let i = start; i < end; i++) {
    let byteIndex = Math.floor(i / 8);
    let byte = bytes[byteIndex];
    let bitIndex = 7 - (i & 7);
    byte &= ~(1 << bitIndex);
    byte |= (value & 1 << end - i - 1) >> end - i - 1 << bitIndex;
    bytes[byteIndex] = byte;
  }
};
var Target$1 = class Target {
};
var ArrayBufferTarget$1 = class ArrayBufferTarget extends Target$1 {
  constructor() {
    super(...arguments);
    this.buffer = null;
  }
};
var StreamTarget$1 = class StreamTarget extends Target$1 {
  constructor(options) {
    super();
    this.options = options;
    if (typeof options !== "object") {
      throw new TypeError("StreamTarget requires an options object to be passed to its constructor.");
    }
    if (options.onData) {
      if (typeof options.onData !== "function") {
        throw new TypeError("options.onData, when provided, must be a function.");
      }
      if (options.onData.length < 2) {
        throw new TypeError(
          "options.onData, when provided, must be a function that takes in at least two arguments (data and position). Ignoring the position argument, which specifies the byte offset at which the data is to be written, can lead to broken outputs."
        );
      }
    }
    if (options.onHeader && typeof options.onHeader !== "function") {
      throw new TypeError("options.onHeader, when provided, must be a function.");
    }
    if (options.onCluster && typeof options.onCluster !== "function") {
      throw new TypeError("options.onCluster, when provided, must be a function.");
    }
    if (options.chunked !== void 0 && typeof options.chunked !== "boolean") {
      throw new TypeError("options.chunked, when provided, must be a boolean.");
    }
    if (options.chunkSize !== void 0 && (!Number.isInteger(options.chunkSize) || options.chunkSize < 1024)) {
      throw new TypeError("options.chunkSize, when provided, must be an integer and not smaller than 1024.");
    }
  }
};
var FileSystemWritableFileStreamTarget$1 = class FileSystemWritableFileStreamTarget extends Target$1 {
  constructor(stream, options) {
    super();
    this.stream = stream;
    this.options = options;
    if (!(stream instanceof FileSystemWritableFileStream)) {
      throw new TypeError("FileSystemWritableFileStreamTarget requires a FileSystemWritableFileStream instance.");
    }
    if (options !== void 0 && typeof options !== "object") {
      throw new TypeError("FileSystemWritableFileStreamTarget's options, when provided, must be an object.");
    }
    if (options) {
      if (options.chunkSize !== void 0 && (!Number.isInteger(options.chunkSize) || options.chunkSize <= 0)) {
        throw new TypeError("options.chunkSize, when provided, must be a positive integer");
      }
    }
  }
};

// src/writer.ts
var _helper$1, _helperView$1, _writeByte, writeByte_fn, _writeFloat32, writeFloat32_fn, _writeFloat64, writeFloat64_fn, _writeUnsignedInt, writeUnsignedInt_fn, _writeString, writeString_fn;
var Writer$1 = class Writer {
  constructor() {
    __privateAdd$1(this, _writeByte);
    __privateAdd$1(this, _writeFloat32);
    __privateAdd$1(this, _writeFloat64);
    __privateAdd$1(this, _writeUnsignedInt);
    __privateAdd$1(this, _writeString);
    this.pos = 0;
    __privateAdd$1(this, _helper$1, new Uint8Array(8));
    __privateAdd$1(this, _helperView$1, new DataView(__privateGet$1(this, _helper$1).buffer));
    this.offsets = /* @__PURE__ */ new WeakMap();
    this.dataOffsets = /* @__PURE__ */ new WeakMap();
  }
  seek(newPos) {
    this.pos = newPos;
  }
  writeEBMLVarInt(value, width = measureEBMLVarInt(value)) {
    let pos = 0;
    switch (width) {
      case 1:
        __privateGet$1(this, _helperView$1).setUint8(pos++, 1 << 7 | value);
        break;
      case 2:
        __privateGet$1(this, _helperView$1).setUint8(pos++, 1 << 6 | value >> 8);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value);
        break;
      case 3:
        __privateGet$1(this, _helperView$1).setUint8(pos++, 1 << 5 | value >> 16);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value >> 8);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value);
        break;
      case 4:
        __privateGet$1(this, _helperView$1).setUint8(pos++, 1 << 4 | value >> 24);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value >> 16);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value >> 8);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value);
        break;
      case 5:
        __privateGet$1(this, _helperView$1).setUint8(pos++, 1 << 3 | value / 2 ** 32 & 7);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value >> 24);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value >> 16);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value >> 8);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value);
        break;
      case 6:
        __privateGet$1(this, _helperView$1).setUint8(pos++, 1 << 2 | value / 2 ** 40 & 3);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value / 2 ** 32 | 0);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value >> 24);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value >> 16);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value >> 8);
        __privateGet$1(this, _helperView$1).setUint8(pos++, value);
        break;
      default:
        throw new Error("Bad EBML VINT size " + width);
    }
    this.write(__privateGet$1(this, _helper$1).subarray(0, pos));
  }
  writeEBML(data) {
    if (data === null)
      return;
    if (data instanceof Uint8Array) {
      this.write(data);
    } else if (Array.isArray(data)) {
      for (let elem of data) {
        this.writeEBML(elem);
      }
    } else {
      this.offsets.set(data, this.pos);
      __privateMethod$1(this, _writeUnsignedInt, writeUnsignedInt_fn).call(this, data.id);
      if (Array.isArray(data.data)) {
        let sizePos = this.pos;
        let sizeSize = data.size === -1 ? 1 : data.size ?? 4;
        if (data.size === -1) {
          __privateMethod$1(this, _writeByte, writeByte_fn).call(this, 255);
        } else {
          this.seek(this.pos + sizeSize);
        }
        let startPos = this.pos;
        this.dataOffsets.set(data, startPos);
        this.writeEBML(data.data);
        if (data.size !== -1) {
          let size = this.pos - startPos;
          let endPos = this.pos;
          this.seek(sizePos);
          this.writeEBMLVarInt(size, sizeSize);
          this.seek(endPos);
        }
      } else if (typeof data.data === "number") {
        let size = data.size ?? measureUnsignedInt(data.data);
        this.writeEBMLVarInt(size);
        __privateMethod$1(this, _writeUnsignedInt, writeUnsignedInt_fn).call(this, data.data, size);
      } else if (typeof data.data === "string") {
        this.writeEBMLVarInt(data.data.length);
        __privateMethod$1(this, _writeString, writeString_fn).call(this, data.data);
      } else if (data.data instanceof Uint8Array) {
        this.writeEBMLVarInt(data.data.byteLength, data.size);
        this.write(data.data);
      } else if (data.data instanceof EBMLFloat32) {
        this.writeEBMLVarInt(4);
        __privateMethod$1(this, _writeFloat32, writeFloat32_fn).call(this, data.data.value);
      } else if (data.data instanceof EBMLFloat64) {
        this.writeEBMLVarInt(8);
        __privateMethod$1(this, _writeFloat64, writeFloat64_fn).call(this, data.data.value);
      }
    }
  }
};
_helper$1 = new WeakMap();
_helperView$1 = new WeakMap();
_writeByte = new WeakSet();
writeByte_fn = function(value) {
  __privateGet$1(this, _helperView$1).setUint8(0, value);
  this.write(__privateGet$1(this, _helper$1).subarray(0, 1));
};
_writeFloat32 = new WeakSet();
writeFloat32_fn = function(value) {
  __privateGet$1(this, _helperView$1).setFloat32(0, value, false);
  this.write(__privateGet$1(this, _helper$1).subarray(0, 4));
};
_writeFloat64 = new WeakSet();
writeFloat64_fn = function(value) {
  __privateGet$1(this, _helperView$1).setFloat64(0, value, false);
  this.write(__privateGet$1(this, _helper$1));
};
_writeUnsignedInt = new WeakSet();
writeUnsignedInt_fn = function(value, width = measureUnsignedInt(value)) {
  let pos = 0;
  switch (width) {
    case 6:
      __privateGet$1(this, _helperView$1).setUint8(pos++, value / 2 ** 40 | 0);
    case 5:
      __privateGet$1(this, _helperView$1).setUint8(pos++, value / 2 ** 32 | 0);
    case 4:
      __privateGet$1(this, _helperView$1).setUint8(pos++, value >> 24);
    case 3:
      __privateGet$1(this, _helperView$1).setUint8(pos++, value >> 16);
    case 2:
      __privateGet$1(this, _helperView$1).setUint8(pos++, value >> 8);
    case 1:
      __privateGet$1(this, _helperView$1).setUint8(pos++, value);
      break;
    default:
      throw new Error("Bad UINT size " + width);
  }
  this.write(__privateGet$1(this, _helper$1).subarray(0, pos));
};
_writeString = new WeakSet();
writeString_fn = function(str) {
  this.write(new Uint8Array(str.split("").map((x) => x.charCodeAt(0))));
};
var _target$1, _buffer$1, _bytes$1, _ensureSize$1, ensureSize_fn$1;
var ArrayBufferTargetWriter$1 = class ArrayBufferTargetWriter extends Writer$1 {
  constructor(target) {
    super();
    __privateAdd$1(this, _ensureSize$1);
    __privateAdd$1(this, _target$1, void 0);
    __privateAdd$1(this, _buffer$1, new ArrayBuffer(2 ** 16));
    __privateAdd$1(this, _bytes$1, new Uint8Array(__privateGet$1(this, _buffer$1)));
    __privateSet$1(this, _target$1, target);
  }
  write(data) {
    __privateMethod$1(this, _ensureSize$1, ensureSize_fn$1).call(this, this.pos + data.byteLength);
    __privateGet$1(this, _bytes$1).set(data, this.pos);
    this.pos += data.byteLength;
  }
  finalize() {
    __privateMethod$1(this, _ensureSize$1, ensureSize_fn$1).call(this, this.pos);
    __privateGet$1(this, _target$1).buffer = __privateGet$1(this, _buffer$1).slice(0, this.pos);
  }
};
_target$1 = new WeakMap();
_buffer$1 = new WeakMap();
_bytes$1 = new WeakMap();
_ensureSize$1 = new WeakSet();
ensureSize_fn$1 = function(size) {
  let newLength = __privateGet$1(this, _buffer$1).byteLength;
  while (newLength < size)
    newLength *= 2;
  if (newLength === __privateGet$1(this, _buffer$1).byteLength)
    return;
  let newBuffer = new ArrayBuffer(newLength);
  let newBytes = new Uint8Array(newBuffer);
  newBytes.set(__privateGet$1(this, _bytes$1), 0);
  __privateSet$1(this, _buffer$1, newBuffer);
  __privateSet$1(this, _bytes$1, newBytes);
};
var _trackingWrites, _trackedWrites, _trackedStart, _trackedEnd;
var BaseStreamTargetWriter = class extends Writer$1 {
  constructor(target) {
    super();
    this.target = target;
    __privateAdd$1(this, _trackingWrites, false);
    __privateAdd$1(this, _trackedWrites, void 0);
    __privateAdd$1(this, _trackedStart, void 0);
    __privateAdd$1(this, _trackedEnd, void 0);
  }
  write(data) {
    if (!__privateGet$1(this, _trackingWrites))
      return;
    let pos = this.pos;
    if (pos < __privateGet$1(this, _trackedStart)) {
      if (pos + data.byteLength <= __privateGet$1(this, _trackedStart))
        return;
      data = data.subarray(__privateGet$1(this, _trackedStart) - pos);
      pos = 0;
    }
    let neededSize = pos + data.byteLength - __privateGet$1(this, _trackedStart);
    let newLength = __privateGet$1(this, _trackedWrites).byteLength;
    while (newLength < neededSize)
      newLength *= 2;
    if (newLength !== __privateGet$1(this, _trackedWrites).byteLength) {
      let copy = new Uint8Array(newLength);
      copy.set(__privateGet$1(this, _trackedWrites), 0);
      __privateSet$1(this, _trackedWrites, copy);
    }
    __privateGet$1(this, _trackedWrites).set(data, pos - __privateGet$1(this, _trackedStart));
    __privateSet$1(this, _trackedEnd, Math.max(__privateGet$1(this, _trackedEnd), pos + data.byteLength));
  }
  startTrackingWrites() {
    __privateSet$1(this, _trackingWrites, true);
    __privateSet$1(this, _trackedWrites, new Uint8Array(2 ** 10));
    __privateSet$1(this, _trackedStart, this.pos);
    __privateSet$1(this, _trackedEnd, this.pos);
  }
  getTrackedWrites() {
    if (!__privateGet$1(this, _trackingWrites)) {
      throw new Error("Can't get tracked writes since nothing was tracked.");
    }
    let slice = __privateGet$1(this, _trackedWrites).subarray(0, __privateGet$1(this, _trackedEnd) - __privateGet$1(this, _trackedStart));
    let result = {
      data: slice,
      start: __privateGet$1(this, _trackedStart),
      end: __privateGet$1(this, _trackedEnd)
    };
    __privateSet$1(this, _trackedWrites, void 0);
    __privateSet$1(this, _trackingWrites, false);
    return result;
  }
};
_trackingWrites = new WeakMap();
_trackedWrites = new WeakMap();
_trackedStart = new WeakMap();
_trackedEnd = new WeakMap();
var DEFAULT_CHUNK_SIZE$1 = 2 ** 24;
var MAX_CHUNKS_AT_ONCE$1 = 2;
var _sections$1, _lastFlushEnd, _ensureMonotonicity, _chunked$1, _chunkSize$1, _chunks$1, _writeDataIntoChunks$1, writeDataIntoChunks_fn$1, _insertSectionIntoChunk$1, insertSectionIntoChunk_fn$1, _createChunk$1, createChunk_fn$1, _flushChunks$1, flushChunks_fn$1;
var StreamTargetWriter$1 = class StreamTargetWriter extends BaseStreamTargetWriter {
  constructor(target, ensureMonotonicity) {
    super(target);
    __privateAdd$1(this, _writeDataIntoChunks$1);
    __privateAdd$1(this, _insertSectionIntoChunk$1);
    __privateAdd$1(this, _createChunk$1);
    __privateAdd$1(this, _flushChunks$1);
    __privateAdd$1(this, _sections$1, []);
    __privateAdd$1(this, _lastFlushEnd, 0);
    __privateAdd$1(this, _ensureMonotonicity, void 0);
    __privateAdd$1(this, _chunked$1, void 0);
    __privateAdd$1(this, _chunkSize$1, void 0);
    __privateAdd$1(this, _chunks$1, []);
    __privateSet$1(this, _ensureMonotonicity, ensureMonotonicity);
    __privateSet$1(this, _chunked$1, target.options?.chunked ?? false);
    __privateSet$1(this, _chunkSize$1, target.options?.chunkSize ?? DEFAULT_CHUNK_SIZE$1);
  }
  write(data) {
    super.write(data);
    __privateGet$1(this, _sections$1).push({
      data: data.slice(),
      start: this.pos
    });
    this.pos += data.byteLength;
  }
  flush() {
    if (__privateGet$1(this, _sections$1).length === 0)
      return;
    let chunks = [];
    let sorted = [...__privateGet$1(this, _sections$1)].sort((a, b) => a.start - b.start);
    chunks.push({
      start: sorted[0].start,
      size: sorted[0].data.byteLength
    });
    for (let i = 1; i < sorted.length; i++) {
      let lastChunk = chunks[chunks.length - 1];
      let section = sorted[i];
      if (section.start <= lastChunk.start + lastChunk.size) {
        lastChunk.size = Math.max(lastChunk.size, section.start + section.data.byteLength - lastChunk.start);
      } else {
        chunks.push({
          start: section.start,
          size: section.data.byteLength
        });
      }
    }
    for (let chunk of chunks) {
      chunk.data = new Uint8Array(chunk.size);
      for (let section of __privateGet$1(this, _sections$1)) {
        if (chunk.start <= section.start && section.start < chunk.start + chunk.size) {
          chunk.data.set(section.data, section.start - chunk.start);
        }
      }
      if (__privateGet$1(this, _chunked$1)) {
        __privateMethod$1(this, _writeDataIntoChunks$1, writeDataIntoChunks_fn$1).call(this, chunk.data, chunk.start);
        __privateMethod$1(this, _flushChunks$1, flushChunks_fn$1).call(this);
      } else {
        if (__privateGet$1(this, _ensureMonotonicity) && chunk.start < __privateGet$1(this, _lastFlushEnd)) {
          throw new Error("Internal error: Monotonicity violation.");
        }
        this.target.options.onData?.(chunk.data, chunk.start);
        __privateSet$1(this, _lastFlushEnd, chunk.start + chunk.data.byteLength);
      }
    }
    __privateGet$1(this, _sections$1).length = 0;
  }
  finalize() {
    if (__privateGet$1(this, _chunked$1)) {
      __privateMethod$1(this, _flushChunks$1, flushChunks_fn$1).call(this, true);
    }
  }
};
_sections$1 = new WeakMap();
_lastFlushEnd = new WeakMap();
_ensureMonotonicity = new WeakMap();
_chunked$1 = new WeakMap();
_chunkSize$1 = new WeakMap();
_chunks$1 = new WeakMap();
_writeDataIntoChunks$1 = new WeakSet();
writeDataIntoChunks_fn$1 = function(data, position) {
  let chunkIndex = __privateGet$1(this, _chunks$1).findIndex((x) => x.start <= position && position < x.start + __privateGet$1(this, _chunkSize$1));
  if (chunkIndex === -1)
    chunkIndex = __privateMethod$1(this, _createChunk$1, createChunk_fn$1).call(this, position);
  let chunk = __privateGet$1(this, _chunks$1)[chunkIndex];
  let relativePosition = position - chunk.start;
  let toWrite = data.subarray(0, Math.min(__privateGet$1(this, _chunkSize$1) - relativePosition, data.byteLength));
  chunk.data.set(toWrite, relativePosition);
  let section = {
    start: relativePosition,
    end: relativePosition + toWrite.byteLength
  };
  __privateMethod$1(this, _insertSectionIntoChunk$1, insertSectionIntoChunk_fn$1).call(this, chunk, section);
  if (chunk.written[0].start === 0 && chunk.written[0].end === __privateGet$1(this, _chunkSize$1)) {
    chunk.shouldFlush = true;
  }
  if (__privateGet$1(this, _chunks$1).length > MAX_CHUNKS_AT_ONCE$1) {
    for (let i = 0; i < __privateGet$1(this, _chunks$1).length - 1; i++) {
      __privateGet$1(this, _chunks$1)[i].shouldFlush = true;
    }
    __privateMethod$1(this, _flushChunks$1, flushChunks_fn$1).call(this);
  }
  if (toWrite.byteLength < data.byteLength) {
    __privateMethod$1(this, _writeDataIntoChunks$1, writeDataIntoChunks_fn$1).call(this, data.subarray(toWrite.byteLength), position + toWrite.byteLength);
  }
};
_insertSectionIntoChunk$1 = new WeakSet();
insertSectionIntoChunk_fn$1 = function(chunk, section) {
  let low = 0;
  let high = chunk.written.length - 1;
  let index = -1;
  while (low <= high) {
    let mid = Math.floor(low + (high - low + 1) / 2);
    if (chunk.written[mid].start <= section.start) {
      low = mid + 1;
      index = mid;
    } else {
      high = mid - 1;
    }
  }
  chunk.written.splice(index + 1, 0, section);
  if (index === -1 || chunk.written[index].end < section.start)
    index++;
  while (index < chunk.written.length - 1 && chunk.written[index].end >= chunk.written[index + 1].start) {
    chunk.written[index].end = Math.max(chunk.written[index].end, chunk.written[index + 1].end);
    chunk.written.splice(index + 1, 1);
  }
};
_createChunk$1 = new WeakSet();
createChunk_fn$1 = function(includesPosition) {
  let start = Math.floor(includesPosition / __privateGet$1(this, _chunkSize$1)) * __privateGet$1(this, _chunkSize$1);
  let chunk = {
    start,
    data: new Uint8Array(__privateGet$1(this, _chunkSize$1)),
    written: [],
    shouldFlush: false
  };
  __privateGet$1(this, _chunks$1).push(chunk);
  __privateGet$1(this, _chunks$1).sort((a, b) => a.start - b.start);
  return __privateGet$1(this, _chunks$1).indexOf(chunk);
};
_flushChunks$1 = new WeakSet();
flushChunks_fn$1 = function(force = false) {
  for (let i = 0; i < __privateGet$1(this, _chunks$1).length; i++) {
    let chunk = __privateGet$1(this, _chunks$1)[i];
    if (!chunk.shouldFlush && !force)
      continue;
    for (let section of chunk.written) {
      if (__privateGet$1(this, _ensureMonotonicity) && chunk.start + section.start < __privateGet$1(this, _lastFlushEnd)) {
        throw new Error("Internal error: Monotonicity violation.");
      }
      this.target.options.onData?.(
        chunk.data.subarray(section.start, section.end),
        chunk.start + section.start
      );
      __privateSet$1(this, _lastFlushEnd, chunk.start + section.end);
    }
    __privateGet$1(this, _chunks$1).splice(i--, 1);
  }
};
var FileSystemWritableFileStreamTargetWriter$1 = class FileSystemWritableFileStreamTargetWriter extends StreamTargetWriter$1 {
  constructor(target, ensureMonotonicity) {
    super(new StreamTarget$1({
      onData: (data, position) => target.stream.write({
        type: "write",
        data,
        position
      }),
      chunked: true,
      chunkSize: target.options?.chunkSize
    }), ensureMonotonicity);
  }
};

// src/muxer.ts
var VIDEO_TRACK_NUMBER = 1;
var AUDIO_TRACK_NUMBER = 2;
var SUBTITLE_TRACK_NUMBER = 3;
var VIDEO_TRACK_TYPE = 1;
var AUDIO_TRACK_TYPE = 2;
var SUBTITLE_TRACK_TYPE = 17;
var MAX_CHUNK_LENGTH_MS = 2 ** 15;
var CODEC_PRIVATE_MAX_SIZE = 2 ** 13;
var APP_NAME = "https://github.com/Vanilagy/webm-muxer";
var SEGMENT_SIZE_BYTES = 6;
var CLUSTER_SIZE_BYTES = 5;
var FIRST_TIMESTAMP_BEHAVIORS$1 = ["strict", "offset", "permissive"];
var _options$1, _writer$1, _segment, _segmentInfo, _seekHead, _tracksElement, _segmentDuration, _colourElement, _videoCodecPrivate, _audioCodecPrivate, _subtitleCodecPrivate, _cues, _currentCluster, _currentClusterTimestamp, _duration, _videoChunkQueue, _audioChunkQueue, _subtitleChunkQueue, _firstVideoTimestamp, _firstAudioTimestamp, _lastVideoTimestamp, _lastAudioTimestamp, _lastSubtitleTimestamp, _colorSpace, _finalized$1, _validateOptions$1, validateOptions_fn$1, _createFileHeader, createFileHeader_fn, _writeEBMLHeader, writeEBMLHeader_fn, _createCodecPrivatePlaceholders, createCodecPrivatePlaceholders_fn, _createColourElement, createColourElement_fn, _createSeekHead, createSeekHead_fn, _createSegmentInfo, createSegmentInfo_fn, _createTracks, createTracks_fn, _createSegment, createSegment_fn, _createCues, createCues_fn, _maybeFlushStreamingTargetWriter$1, maybeFlushStreamingTargetWriter_fn$1, _segmentDataOffset, segmentDataOffset_get, _writeVideoDecoderConfig, writeVideoDecoderConfig_fn, _fixVP9ColorSpace, fixVP9ColorSpace_fn, _writeSubtitleChunks, writeSubtitleChunks_fn, _createInternalChunk, createInternalChunk_fn, _validateTimestamp$1, validateTimestamp_fn$1, _writeBlock, writeBlock_fn, _createCodecPrivateElement, createCodecPrivateElement_fn, _writeCodecPrivate, writeCodecPrivate_fn, _createNewCluster, createNewCluster_fn, _finalizeCurrentCluster, finalizeCurrentCluster_fn, _ensureNotFinalized$1, ensureNotFinalized_fn$1;
var Muxer$1 = class Muxer {
  constructor(options) {
    __privateAdd$1(this, _validateOptions$1);
    __privateAdd$1(this, _createFileHeader);
    __privateAdd$1(this, _writeEBMLHeader);
    __privateAdd$1(this, _createCodecPrivatePlaceholders);
    __privateAdd$1(this, _createColourElement);
    __privateAdd$1(this, _createSeekHead);
    __privateAdd$1(this, _createSegmentInfo);
    __privateAdd$1(this, _createTracks);
    __privateAdd$1(this, _createSegment);
    __privateAdd$1(this, _createCues);
    __privateAdd$1(this, _maybeFlushStreamingTargetWriter$1);
    __privateAdd$1(this, _segmentDataOffset);
    __privateAdd$1(this, _writeVideoDecoderConfig);
    __privateAdd$1(this, _fixVP9ColorSpace);
    __privateAdd$1(this, _writeSubtitleChunks);
    __privateAdd$1(this, _createInternalChunk);
    __privateAdd$1(this, _validateTimestamp$1);
    __privateAdd$1(this, _writeBlock);
    __privateAdd$1(this, _createCodecPrivateElement);
    __privateAdd$1(this, _writeCodecPrivate);
    __privateAdd$1(this, _createNewCluster);
    __privateAdd$1(this, _finalizeCurrentCluster);
    __privateAdd$1(this, _ensureNotFinalized$1);
    __privateAdd$1(this, _options$1, void 0);
    __privateAdd$1(this, _writer$1, void 0);
    __privateAdd$1(this, _segment, void 0);
    __privateAdd$1(this, _segmentInfo, void 0);
    __privateAdd$1(this, _seekHead, void 0);
    __privateAdd$1(this, _tracksElement, void 0);
    __privateAdd$1(this, _segmentDuration, void 0);
    __privateAdd$1(this, _colourElement, void 0);
    __privateAdd$1(this, _videoCodecPrivate, void 0);
    __privateAdd$1(this, _audioCodecPrivate, void 0);
    __privateAdd$1(this, _subtitleCodecPrivate, void 0);
    __privateAdd$1(this, _cues, void 0);
    __privateAdd$1(this, _currentCluster, void 0);
    __privateAdd$1(this, _currentClusterTimestamp, void 0);
    __privateAdd$1(this, _duration, 0);
    __privateAdd$1(this, _videoChunkQueue, []);
    __privateAdd$1(this, _audioChunkQueue, []);
    __privateAdd$1(this, _subtitleChunkQueue, []);
    __privateAdd$1(this, _firstVideoTimestamp, void 0);
    __privateAdd$1(this, _firstAudioTimestamp, void 0);
    __privateAdd$1(this, _lastVideoTimestamp, -1);
    __privateAdd$1(this, _lastAudioTimestamp, -1);
    __privateAdd$1(this, _lastSubtitleTimestamp, -1);
    __privateAdd$1(this, _colorSpace, void 0);
    __privateAdd$1(this, _finalized$1, false);
    __privateMethod$1(this, _validateOptions$1, validateOptions_fn$1).call(this, options);
    __privateSet$1(this, _options$1, {
      type: "webm",
      firstTimestampBehavior: "strict",
      ...options
    });
    this.target = options.target;
    let ensureMonotonicity = !!__privateGet$1(this, _options$1).streaming;
    if (options.target instanceof ArrayBufferTarget$1) {
      __privateSet$1(this, _writer$1, new ArrayBufferTargetWriter$1(options.target));
    } else if (options.target instanceof StreamTarget$1) {
      __privateSet$1(this, _writer$1, new StreamTargetWriter$1(options.target, ensureMonotonicity));
    } else if (options.target instanceof FileSystemWritableFileStreamTarget$1) {
      __privateSet$1(this, _writer$1, new FileSystemWritableFileStreamTargetWriter$1(options.target, ensureMonotonicity));
    } else {
      throw new Error(`Invalid target: ${options.target}`);
    }
    __privateMethod$1(this, _createFileHeader, createFileHeader_fn).call(this);
  }
  addVideoChunk(chunk, meta, timestamp) {
    if (!(chunk instanceof EncodedVideoChunk)) {
      throw new TypeError("addVideoChunk's first argument (chunk) must be of type EncodedVideoChunk.");
    }
    if (meta && typeof meta !== "object") {
      throw new TypeError("addVideoChunk's second argument (meta), when provided, must be an object.");
    }
    if (timestamp !== void 0 && (!Number.isFinite(timestamp) || timestamp < 0)) {
      throw new TypeError(
        "addVideoChunk's third argument (timestamp), when provided, must be a non-negative real number."
      );
    }
    let data = new Uint8Array(chunk.byteLength);
    chunk.copyTo(data);
    this.addVideoChunkRaw(data, chunk.type, timestamp ?? chunk.timestamp, meta);
  }
  addVideoChunkRaw(data, type, timestamp, meta) {
    if (!(data instanceof Uint8Array)) {
      throw new TypeError("addVideoChunkRaw's first argument (data) must be an instance of Uint8Array.");
    }
    if (type !== "key" && type !== "delta") {
      throw new TypeError("addVideoChunkRaw's second argument (type) must be either 'key' or 'delta'.");
    }
    if (!Number.isFinite(timestamp) || timestamp < 0) {
      throw new TypeError("addVideoChunkRaw's third argument (timestamp) must be a non-negative real number.");
    }
    if (meta && typeof meta !== "object") {
      throw new TypeError("addVideoChunkRaw's fourth argument (meta), when provided, must be an object.");
    }
    __privateMethod$1(this, _ensureNotFinalized$1, ensureNotFinalized_fn$1).call(this);
    if (!__privateGet$1(this, _options$1).video)
      throw new Error("No video track declared.");
    if (__privateGet$1(this, _firstVideoTimestamp) === void 0)
      __privateSet$1(this, _firstVideoTimestamp, timestamp);
    if (meta)
      __privateMethod$1(this, _writeVideoDecoderConfig, writeVideoDecoderConfig_fn).call(this, meta);
    let videoChunk = __privateMethod$1(this, _createInternalChunk, createInternalChunk_fn).call(this, data, type, timestamp, VIDEO_TRACK_NUMBER);
    if (__privateGet$1(this, _options$1).video.codec === "V_VP9")
      __privateMethod$1(this, _fixVP9ColorSpace, fixVP9ColorSpace_fn).call(this, videoChunk);
    __privateSet$1(this, _lastVideoTimestamp, videoChunk.timestamp);
    while (__privateGet$1(this, _audioChunkQueue).length > 0 && __privateGet$1(this, _audioChunkQueue)[0].timestamp <= videoChunk.timestamp) {
      let audioChunk = __privateGet$1(this, _audioChunkQueue).shift();
      __privateMethod$1(this, _writeBlock, writeBlock_fn).call(this, audioChunk, false);
    }
    if (!__privateGet$1(this, _options$1).audio || videoChunk.timestamp <= __privateGet$1(this, _lastAudioTimestamp)) {
      __privateMethod$1(this, _writeBlock, writeBlock_fn).call(this, videoChunk, true);
    } else {
      __privateGet$1(this, _videoChunkQueue).push(videoChunk);
    }
    __privateMethod$1(this, _writeSubtitleChunks, writeSubtitleChunks_fn).call(this);
    __privateMethod$1(this, _maybeFlushStreamingTargetWriter$1, maybeFlushStreamingTargetWriter_fn$1).call(this);
  }
  addAudioChunk(chunk, meta, timestamp) {
    if (!(chunk instanceof EncodedAudioChunk)) {
      throw new TypeError("addAudioChunk's first argument (chunk) must be of type EncodedAudioChunk.");
    }
    if (meta && typeof meta !== "object") {
      throw new TypeError("addAudioChunk's second argument (meta), when provided, must be an object.");
    }
    if (timestamp !== void 0 && (!Number.isFinite(timestamp) || timestamp < 0)) {
      throw new TypeError(
        "addAudioChunk's third argument (timestamp), when provided, must be a non-negative real number."
      );
    }
    let data = new Uint8Array(chunk.byteLength);
    chunk.copyTo(data);
    this.addAudioChunkRaw(data, chunk.type, timestamp ?? chunk.timestamp, meta);
  }
  addAudioChunkRaw(data, type, timestamp, meta) {
    if (!(data instanceof Uint8Array)) {
      throw new TypeError("addAudioChunkRaw's first argument (data) must be an instance of Uint8Array.");
    }
    if (type !== "key" && type !== "delta") {
      throw new TypeError("addAudioChunkRaw's second argument (type) must be either 'key' or 'delta'.");
    }
    if (!Number.isFinite(timestamp) || timestamp < 0) {
      throw new TypeError("addAudioChunkRaw's third argument (timestamp) must be a non-negative real number.");
    }
    if (meta && typeof meta !== "object") {
      throw new TypeError("addAudioChunkRaw's fourth argument (meta), when provided, must be an object.");
    }
    __privateMethod$1(this, _ensureNotFinalized$1, ensureNotFinalized_fn$1).call(this);
    if (!__privateGet$1(this, _options$1).audio)
      throw new Error("No audio track declared.");
    if (__privateGet$1(this, _firstAudioTimestamp) === void 0)
      __privateSet$1(this, _firstAudioTimestamp, timestamp);
    if (meta?.decoderConfig) {
      if (__privateGet$1(this, _options$1).streaming) {
        __privateSet$1(this, _audioCodecPrivate, __privateMethod$1(this, _createCodecPrivateElement, createCodecPrivateElement_fn).call(this, meta.decoderConfig.description));
      } else {
        __privateMethod$1(this, _writeCodecPrivate, writeCodecPrivate_fn).call(this, __privateGet$1(this, _audioCodecPrivate), meta.decoderConfig.description);
      }
    }
    let audioChunk = __privateMethod$1(this, _createInternalChunk, createInternalChunk_fn).call(this, data, type, timestamp, AUDIO_TRACK_NUMBER);
    __privateSet$1(this, _lastAudioTimestamp, audioChunk.timestamp);
    while (__privateGet$1(this, _videoChunkQueue).length > 0 && __privateGet$1(this, _videoChunkQueue)[0].timestamp <= audioChunk.timestamp) {
      let videoChunk = __privateGet$1(this, _videoChunkQueue).shift();
      __privateMethod$1(this, _writeBlock, writeBlock_fn).call(this, videoChunk, true);
    }
    if (!__privateGet$1(this, _options$1).video || audioChunk.timestamp <= __privateGet$1(this, _lastVideoTimestamp)) {
      __privateMethod$1(this, _writeBlock, writeBlock_fn).call(this, audioChunk, !__privateGet$1(this, _options$1).video);
    } else {
      __privateGet$1(this, _audioChunkQueue).push(audioChunk);
    }
    __privateMethod$1(this, _writeSubtitleChunks, writeSubtitleChunks_fn).call(this);
    __privateMethod$1(this, _maybeFlushStreamingTargetWriter$1, maybeFlushStreamingTargetWriter_fn$1).call(this);
  }
  addSubtitleChunk(chunk, meta, timestamp) {
    if (typeof chunk !== "object" || !chunk) {
      throw new TypeError("addSubtitleChunk's first argument (chunk) must be an object.");
    } else {
      if (!(chunk.body instanceof Uint8Array)) {
        throw new TypeError("body must be an instance of Uint8Array.");
      }
      if (!Number.isFinite(chunk.timestamp) || chunk.timestamp < 0) {
        throw new TypeError("timestamp must be a non-negative real number.");
      }
      if (!Number.isFinite(chunk.duration) || chunk.duration < 0) {
        throw new TypeError("duration must be a non-negative real number.");
      }
      if (chunk.additions && !(chunk.additions instanceof Uint8Array)) {
        throw new TypeError("additions, when present, must be an instance of Uint8Array.");
      }
    }
    if (typeof meta !== "object") {
      throw new TypeError("addSubtitleChunk's second argument (meta) must be an object.");
    }
    __privateMethod$1(this, _ensureNotFinalized$1, ensureNotFinalized_fn$1).call(this);
    if (!__privateGet$1(this, _options$1).subtitles)
      throw new Error("No subtitle track declared.");
    if (meta?.decoderConfig) {
      if (__privateGet$1(this, _options$1).streaming) {
        __privateSet$1(this, _subtitleCodecPrivate, __privateMethod$1(this, _createCodecPrivateElement, createCodecPrivateElement_fn).call(this, meta.decoderConfig.description));
      } else {
        __privateMethod$1(this, _writeCodecPrivate, writeCodecPrivate_fn).call(this, __privateGet$1(this, _subtitleCodecPrivate), meta.decoderConfig.description);
      }
    }
    let subtitleChunk = __privateMethod$1(this, _createInternalChunk, createInternalChunk_fn).call(this, chunk.body, "key", timestamp ?? chunk.timestamp, SUBTITLE_TRACK_NUMBER, chunk.duration, chunk.additions);
    __privateSet$1(this, _lastSubtitleTimestamp, subtitleChunk.timestamp);
    __privateGet$1(this, _subtitleChunkQueue).push(subtitleChunk);
    __privateMethod$1(this, _writeSubtitleChunks, writeSubtitleChunks_fn).call(this);
    __privateMethod$1(this, _maybeFlushStreamingTargetWriter$1, maybeFlushStreamingTargetWriter_fn$1).call(this);
  }
  finalize() {
    if (__privateGet$1(this, _finalized$1)) {
      throw new Error("Cannot finalize a muxer more than once.");
    }
    while (__privateGet$1(this, _videoChunkQueue).length > 0)
      __privateMethod$1(this, _writeBlock, writeBlock_fn).call(this, __privateGet$1(this, _videoChunkQueue).shift(), true);
    while (__privateGet$1(this, _audioChunkQueue).length > 0)
      __privateMethod$1(this, _writeBlock, writeBlock_fn).call(this, __privateGet$1(this, _audioChunkQueue).shift(), true);
    while (__privateGet$1(this, _subtitleChunkQueue).length > 0 && __privateGet$1(this, _subtitleChunkQueue)[0].timestamp <= __privateGet$1(this, _duration)) {
      __privateMethod$1(this, _writeBlock, writeBlock_fn).call(this, __privateGet$1(this, _subtitleChunkQueue).shift(), false);
    }
    if (__privateGet$1(this, _currentCluster)) {
      __privateMethod$1(this, _finalizeCurrentCluster, finalizeCurrentCluster_fn).call(this);
    }
    __privateGet$1(this, _writer$1).writeEBML(__privateGet$1(this, _cues));
    if (!__privateGet$1(this, _options$1).streaming) {
      let endPos = __privateGet$1(this, _writer$1).pos;
      let segmentSize = __privateGet$1(this, _writer$1).pos - __privateGet$1(this, _segmentDataOffset, segmentDataOffset_get);
      __privateGet$1(this, _writer$1).seek(__privateGet$1(this, _writer$1).offsets.get(__privateGet$1(this, _segment)) + 4);
      __privateGet$1(this, _writer$1).writeEBMLVarInt(segmentSize, SEGMENT_SIZE_BYTES);
      __privateGet$1(this, _segmentDuration).data = new EBMLFloat64(__privateGet$1(this, _duration));
      __privateGet$1(this, _writer$1).seek(__privateGet$1(this, _writer$1).offsets.get(__privateGet$1(this, _segmentDuration)));
      __privateGet$1(this, _writer$1).writeEBML(__privateGet$1(this, _segmentDuration));
      __privateGet$1(this, _seekHead).data[0].data[1].data = __privateGet$1(this, _writer$1).offsets.get(__privateGet$1(this, _cues)) - __privateGet$1(this, _segmentDataOffset, segmentDataOffset_get);
      __privateGet$1(this, _seekHead).data[1].data[1].data = __privateGet$1(this, _writer$1).offsets.get(__privateGet$1(this, _segmentInfo)) - __privateGet$1(this, _segmentDataOffset, segmentDataOffset_get);
      __privateGet$1(this, _seekHead).data[2].data[1].data = __privateGet$1(this, _writer$1).offsets.get(__privateGet$1(this, _tracksElement)) - __privateGet$1(this, _segmentDataOffset, segmentDataOffset_get);
      __privateGet$1(this, _writer$1).seek(__privateGet$1(this, _writer$1).offsets.get(__privateGet$1(this, _seekHead)));
      __privateGet$1(this, _writer$1).writeEBML(__privateGet$1(this, _seekHead));
      __privateGet$1(this, _writer$1).seek(endPos);
    }
    __privateMethod$1(this, _maybeFlushStreamingTargetWriter$1, maybeFlushStreamingTargetWriter_fn$1).call(this);
    __privateGet$1(this, _writer$1).finalize();
    __privateSet$1(this, _finalized$1, true);
  }
};
_options$1 = new WeakMap();
_writer$1 = new WeakMap();
_segment = new WeakMap();
_segmentInfo = new WeakMap();
_seekHead = new WeakMap();
_tracksElement = new WeakMap();
_segmentDuration = new WeakMap();
_colourElement = new WeakMap();
_videoCodecPrivate = new WeakMap();
_audioCodecPrivate = new WeakMap();
_subtitleCodecPrivate = new WeakMap();
_cues = new WeakMap();
_currentCluster = new WeakMap();
_currentClusterTimestamp = new WeakMap();
_duration = new WeakMap();
_videoChunkQueue = new WeakMap();
_audioChunkQueue = new WeakMap();
_subtitleChunkQueue = new WeakMap();
_firstVideoTimestamp = new WeakMap();
_firstAudioTimestamp = new WeakMap();
_lastVideoTimestamp = new WeakMap();
_lastAudioTimestamp = new WeakMap();
_lastSubtitleTimestamp = new WeakMap();
_colorSpace = new WeakMap();
_finalized$1 = new WeakMap();
_validateOptions$1 = new WeakSet();
validateOptions_fn$1 = function(options) {
  if (typeof options !== "object") {
    throw new TypeError("The muxer requires an options object to be passed to its constructor.");
  }
  if (!(options.target instanceof Target$1)) {
    throw new TypeError("The target must be provided and an instance of Target.");
  }
  if (options.video) {
    if (typeof options.video.codec !== "string") {
      throw new TypeError(`Invalid video codec: ${options.video.codec}. Must be a string.`);
    }
    if (!Number.isInteger(options.video.width) || options.video.width <= 0) {
      throw new TypeError(`Invalid video width: ${options.video.width}. Must be a positive integer.`);
    }
    if (!Number.isInteger(options.video.height) || options.video.height <= 0) {
      throw new TypeError(`Invalid video height: ${options.video.height}. Must be a positive integer.`);
    }
    if (options.video.frameRate !== void 0) {
      if (!Number.isFinite(options.video.frameRate) || options.video.frameRate <= 0) {
        throw new TypeError(
          `Invalid video frame rate: ${options.video.frameRate}. Must be a positive number.`
        );
      }
    }
    if (options.video.alpha !== void 0 && typeof options.video.alpha !== "boolean") {
      throw new TypeError(`Invalid video alpha: ${options.video.alpha}. Must be a boolean.`);
    }
  }
  if (options.audio) {
    if (typeof options.audio.codec !== "string") {
      throw new TypeError(`Invalid audio codec: ${options.audio.codec}. Must be a string.`);
    }
    if (!Number.isInteger(options.audio.numberOfChannels) || options.audio.numberOfChannels <= 0) {
      throw new TypeError(
        `Invalid number of audio channels: ${options.audio.numberOfChannels}. Must be a positive integer.`
      );
    }
    if (!Number.isInteger(options.audio.sampleRate) || options.audio.sampleRate <= 0) {
      throw new TypeError(
        `Invalid audio sample rate: ${options.audio.sampleRate}. Must be a positive integer.`
      );
    }
    if (options.audio.bitDepth !== void 0) {
      if (!Number.isInteger(options.audio.bitDepth) || options.audio.bitDepth <= 0) {
        throw new TypeError(
          `Invalid audio bit depth: ${options.audio.bitDepth}. Must be a positive integer.`
        );
      }
    }
  }
  if (options.subtitles) {
    if (typeof options.subtitles.codec !== "string") {
      throw new TypeError(`Invalid subtitles codec: ${options.subtitles.codec}. Must be a string.`);
    }
  }
  if (options.type !== void 0 && !["webm", "matroska"].includes(options.type)) {
    throw new TypeError(`Invalid type: ${options.type}. Must be 'webm' or 'matroska'.`);
  }
  if (options.firstTimestampBehavior && !FIRST_TIMESTAMP_BEHAVIORS$1.includes(options.firstTimestampBehavior)) {
    throw new TypeError(`Invalid first timestamp behavior: ${options.firstTimestampBehavior}`);
  }
  if (options.streaming !== void 0 && typeof options.streaming !== "boolean") {
    throw new TypeError(`Invalid streaming option: ${options.streaming}. Must be a boolean.`);
  }
};
_createFileHeader = new WeakSet();
createFileHeader_fn = function() {
  if (__privateGet$1(this, _writer$1) instanceof BaseStreamTargetWriter && __privateGet$1(this, _writer$1).target.options.onHeader) {
    __privateGet$1(this, _writer$1).startTrackingWrites();
  }
  __privateMethod$1(this, _writeEBMLHeader, writeEBMLHeader_fn).call(this);
  if (!__privateGet$1(this, _options$1).streaming) {
    __privateMethod$1(this, _createSeekHead, createSeekHead_fn).call(this);
  }
  __privateMethod$1(this, _createSegmentInfo, createSegmentInfo_fn).call(this);
  __privateMethod$1(this, _createCodecPrivatePlaceholders, createCodecPrivatePlaceholders_fn).call(this);
  __privateMethod$1(this, _createColourElement, createColourElement_fn).call(this);
  if (!__privateGet$1(this, _options$1).streaming) {
    __privateMethod$1(this, _createTracks, createTracks_fn).call(this);
    __privateMethod$1(this, _createSegment, createSegment_fn).call(this);
  }
  __privateMethod$1(this, _createCues, createCues_fn).call(this);
  __privateMethod$1(this, _maybeFlushStreamingTargetWriter$1, maybeFlushStreamingTargetWriter_fn$1).call(this);
};
_writeEBMLHeader = new WeakSet();
writeEBMLHeader_fn = function() {
  let ebmlHeader = { id: 440786851 /* EBML */, data: [
    { id: 17030 /* EBMLVersion */, data: 1 },
    { id: 17143 /* EBMLReadVersion */, data: 1 },
    { id: 17138 /* EBMLMaxIDLength */, data: 4 },
    { id: 17139 /* EBMLMaxSizeLength */, data: 8 },
    { id: 17026 /* DocType */, data: __privateGet$1(this, _options$1).type ?? "webm" },
    { id: 17031 /* DocTypeVersion */, data: 2 },
    { id: 17029 /* DocTypeReadVersion */, data: 2 }
  ] };
  __privateGet$1(this, _writer$1).writeEBML(ebmlHeader);
};
_createCodecPrivatePlaceholders = new WeakSet();
createCodecPrivatePlaceholders_fn = function() {
  __privateSet$1(this, _videoCodecPrivate, { id: 236 /* Void */, size: 4, data: new Uint8Array(CODEC_PRIVATE_MAX_SIZE) });
  __privateSet$1(this, _audioCodecPrivate, { id: 236 /* Void */, size: 4, data: new Uint8Array(CODEC_PRIVATE_MAX_SIZE) });
  __privateSet$1(this, _subtitleCodecPrivate, { id: 236 /* Void */, size: 4, data: new Uint8Array(CODEC_PRIVATE_MAX_SIZE) });
};
_createColourElement = new WeakSet();
createColourElement_fn = function() {
  __privateSet$1(this, _colourElement, { id: 21936 /* Colour */, data: [
    { id: 21937 /* MatrixCoefficients */, data: 2 },
    { id: 21946 /* TransferCharacteristics */, data: 2 },
    { id: 21947 /* Primaries */, data: 2 },
    { id: 21945 /* Range */, data: 0 }
  ] });
};
_createSeekHead = new WeakSet();
createSeekHead_fn = function() {
  const kaxCues = new Uint8Array([28, 83, 187, 107]);
  const kaxInfo = new Uint8Array([21, 73, 169, 102]);
  const kaxTracks = new Uint8Array([22, 84, 174, 107]);
  let seekHead = { id: 290298740 /* SeekHead */, data: [
    { id: 19899 /* Seek */, data: [
      { id: 21419 /* SeekID */, data: kaxCues },
      { id: 21420 /* SeekPosition */, size: 5, data: 0 }
    ] },
    { id: 19899 /* Seek */, data: [
      { id: 21419 /* SeekID */, data: kaxInfo },
      { id: 21420 /* SeekPosition */, size: 5, data: 0 }
    ] },
    { id: 19899 /* Seek */, data: [
      { id: 21419 /* SeekID */, data: kaxTracks },
      { id: 21420 /* SeekPosition */, size: 5, data: 0 }
    ] }
  ] };
  __privateSet$1(this, _seekHead, seekHead);
};
_createSegmentInfo = new WeakSet();
createSegmentInfo_fn = function() {
  let segmentDuration = { id: 17545 /* Duration */, data: new EBMLFloat64(0) };
  __privateSet$1(this, _segmentDuration, segmentDuration);
  let segmentInfo = { id: 357149030 /* Info */, data: [
    { id: 2807729 /* TimestampScale */, data: 1e6 },
    { id: 19840 /* MuxingApp */, data: APP_NAME },
    { id: 22337 /* WritingApp */, data: APP_NAME },
    !__privateGet$1(this, _options$1).streaming ? segmentDuration : null
  ] };
  __privateSet$1(this, _segmentInfo, segmentInfo);
};
_createTracks = new WeakSet();
createTracks_fn = function() {
  let tracksElement = { id: 374648427 /* Tracks */, data: [] };
  __privateSet$1(this, _tracksElement, tracksElement);
  if (__privateGet$1(this, _options$1).video) {
    tracksElement.data.push({ id: 174 /* TrackEntry */, data: [
      { id: 215 /* TrackNumber */, data: VIDEO_TRACK_NUMBER },
      { id: 29637 /* TrackUID */, data: VIDEO_TRACK_NUMBER },
      { id: 131 /* TrackType */, data: VIDEO_TRACK_TYPE },
      { id: 134 /* CodecID */, data: __privateGet$1(this, _options$1).video.codec },
      __privateGet$1(this, _videoCodecPrivate),
      __privateGet$1(this, _options$1).video.frameRate ? { id: 2352003 /* DefaultDuration */, data: 1e9 / __privateGet$1(this, _options$1).video.frameRate } : null,
      { id: 224 /* Video */, data: [
        { id: 176 /* PixelWidth */, data: __privateGet$1(this, _options$1).video.width },
        { id: 186 /* PixelHeight */, data: __privateGet$1(this, _options$1).video.height },
        __privateGet$1(this, _options$1).video.alpha ? { id: 21440 /* AlphaMode */, data: 1 } : null,
        __privateGet$1(this, _colourElement)
      ] }
    ] });
  }
  if (__privateGet$1(this, _options$1).audio) {
    __privateSet$1(this, _audioCodecPrivate, __privateGet$1(this, _options$1).streaming ? __privateGet$1(this, _audioCodecPrivate) || null : { id: 236 /* Void */, size: 4, data: new Uint8Array(CODEC_PRIVATE_MAX_SIZE) });
    tracksElement.data.push({ id: 174 /* TrackEntry */, data: [
      { id: 215 /* TrackNumber */, data: AUDIO_TRACK_NUMBER },
      { id: 29637 /* TrackUID */, data: AUDIO_TRACK_NUMBER },
      { id: 131 /* TrackType */, data: AUDIO_TRACK_TYPE },
      { id: 134 /* CodecID */, data: __privateGet$1(this, _options$1).audio.codec },
      __privateGet$1(this, _audioCodecPrivate),
      { id: 225 /* Audio */, data: [
        { id: 181 /* SamplingFrequency */, data: new EBMLFloat32(__privateGet$1(this, _options$1).audio.sampleRate) },
        { id: 159 /* Channels */, data: __privateGet$1(this, _options$1).audio.numberOfChannels },
        __privateGet$1(this, _options$1).audio.bitDepth ? { id: 25188 /* BitDepth */, data: __privateGet$1(this, _options$1).audio.bitDepth } : null
      ] }
    ] });
  }
  if (__privateGet$1(this, _options$1).subtitles) {
    tracksElement.data.push({ id: 174 /* TrackEntry */, data: [
      { id: 215 /* TrackNumber */, data: SUBTITLE_TRACK_NUMBER },
      { id: 29637 /* TrackUID */, data: SUBTITLE_TRACK_NUMBER },
      { id: 131 /* TrackType */, data: SUBTITLE_TRACK_TYPE },
      { id: 134 /* CodecID */, data: __privateGet$1(this, _options$1).subtitles.codec },
      __privateGet$1(this, _subtitleCodecPrivate)
    ] });
  }
};
_createSegment = new WeakSet();
createSegment_fn = function() {
  let segment = {
    id: 408125543 /* Segment */,
    size: __privateGet$1(this, _options$1).streaming ? -1 : SEGMENT_SIZE_BYTES,
    data: [
      !__privateGet$1(this, _options$1).streaming ? __privateGet$1(this, _seekHead) : null,
      __privateGet$1(this, _segmentInfo),
      __privateGet$1(this, _tracksElement)
    ]
  };
  __privateSet$1(this, _segment, segment);
  __privateGet$1(this, _writer$1).writeEBML(segment);
  if (__privateGet$1(this, _writer$1) instanceof BaseStreamTargetWriter && __privateGet$1(this, _writer$1).target.options.onHeader) {
    let { data, start } = __privateGet$1(this, _writer$1).getTrackedWrites();
    __privateGet$1(this, _writer$1).target.options.onHeader(data, start);
  }
};
_createCues = new WeakSet();
createCues_fn = function() {
  __privateSet$1(this, _cues, { id: 475249515 /* Cues */, data: [] });
};
_maybeFlushStreamingTargetWriter$1 = new WeakSet();
maybeFlushStreamingTargetWriter_fn$1 = function() {
  if (__privateGet$1(this, _writer$1) instanceof StreamTargetWriter$1) {
    __privateGet$1(this, _writer$1).flush();
  }
};
_segmentDataOffset = new WeakSet();
segmentDataOffset_get = function() {
  return __privateGet$1(this, _writer$1).dataOffsets.get(__privateGet$1(this, _segment));
};
_writeVideoDecoderConfig = new WeakSet();
writeVideoDecoderConfig_fn = function(meta) {
  if (!meta.decoderConfig)
    return;
  if (meta.decoderConfig.colorSpace) {
    let colorSpace = meta.decoderConfig.colorSpace;
    __privateSet$1(this, _colorSpace, colorSpace);
    __privateGet$1(this, _colourElement).data = [
      { id: 21937 /* MatrixCoefficients */, data: {
        "rgb": 1,
        "bt709": 1,
        "bt470bg": 5,
        "smpte170m": 6
      }[colorSpace.matrix] },
      { id: 21946 /* TransferCharacteristics */, data: {
        "bt709": 1,
        "smpte170m": 6,
        "iec61966-2-1": 13
      }[colorSpace.transfer] },
      { id: 21947 /* Primaries */, data: {
        "bt709": 1,
        "bt470bg": 5,
        "smpte170m": 6
      }[colorSpace.primaries] },
      { id: 21945 /* Range */, data: [1, 2][Number(colorSpace.fullRange)] }
    ];
    if (!__privateGet$1(this, _options$1).streaming) {
      let endPos = __privateGet$1(this, _writer$1).pos;
      __privateGet$1(this, _writer$1).seek(__privateGet$1(this, _writer$1).offsets.get(__privateGet$1(this, _colourElement)));
      __privateGet$1(this, _writer$1).writeEBML(__privateGet$1(this, _colourElement));
      __privateGet$1(this, _writer$1).seek(endPos);
    }
  }
  if (meta.decoderConfig.description) {
    if (__privateGet$1(this, _options$1).streaming) {
      __privateSet$1(this, _videoCodecPrivate, __privateMethod$1(this, _createCodecPrivateElement, createCodecPrivateElement_fn).call(this, meta.decoderConfig.description));
    } else {
      __privateMethod$1(this, _writeCodecPrivate, writeCodecPrivate_fn).call(this, __privateGet$1(this, _videoCodecPrivate), meta.decoderConfig.description);
    }
  }
};
_fixVP9ColorSpace = new WeakSet();
fixVP9ColorSpace_fn = function(chunk) {
  if (chunk.type !== "key")
    return;
  if (!__privateGet$1(this, _colorSpace))
    return;
  let i = 0;
  if (readBits(chunk.data, 0, 2) !== 2)
    return;
  i += 2;
  let profile = (readBits(chunk.data, i + 1, i + 2) << 1) + readBits(chunk.data, i + 0, i + 1);
  i += 2;
  if (profile === 3)
    i++;
  let showExistingFrame = readBits(chunk.data, i + 0, i + 1);
  i++;
  if (showExistingFrame)
    return;
  let frameType = readBits(chunk.data, i + 0, i + 1);
  i++;
  if (frameType !== 0)
    return;
  i += 2;
  let syncCode = readBits(chunk.data, i + 0, i + 24);
  i += 24;
  if (syncCode !== 4817730)
    return;
  if (profile >= 2)
    i++;
  let colorSpaceID = {
    "rgb": 7,
    "bt709": 2,
    "bt470bg": 1,
    "smpte170m": 3
  }[__privateGet$1(this, _colorSpace).matrix];
  writeBits(chunk.data, i + 0, i + 3, colorSpaceID);
};
_writeSubtitleChunks = new WeakSet();
writeSubtitleChunks_fn = function() {
  let lastWrittenMediaTimestamp = Math.min(
    __privateGet$1(this, _options$1).video ? __privateGet$1(this, _lastVideoTimestamp) : Infinity,
    __privateGet$1(this, _options$1).audio ? __privateGet$1(this, _lastAudioTimestamp) : Infinity
  );
  let queue = __privateGet$1(this, _subtitleChunkQueue);
  while (queue.length > 0 && queue[0].timestamp <= lastWrittenMediaTimestamp) {
    __privateMethod$1(this, _writeBlock, writeBlock_fn).call(this, queue.shift(), !__privateGet$1(this, _options$1).video && !__privateGet$1(this, _options$1).audio);
  }
};
_createInternalChunk = new WeakSet();
createInternalChunk_fn = function(data, type, timestamp, trackNumber, duration, additions) {
  let adjustedTimestamp = __privateMethod$1(this, _validateTimestamp$1, validateTimestamp_fn$1).call(this, timestamp, trackNumber);
  let internalChunk = {
    data,
    additions,
    type,
    timestamp: adjustedTimestamp,
    duration,
    trackNumber
  };
  return internalChunk;
};
_validateTimestamp$1 = new WeakSet();
validateTimestamp_fn$1 = function(timestamp, trackNumber) {
  let lastTimestamp = trackNumber === VIDEO_TRACK_NUMBER ? __privateGet$1(this, _lastVideoTimestamp) : trackNumber === AUDIO_TRACK_NUMBER ? __privateGet$1(this, _lastAudioTimestamp) : __privateGet$1(this, _lastSubtitleTimestamp);
  if (trackNumber !== SUBTITLE_TRACK_NUMBER) {
    let firstTimestamp = trackNumber === VIDEO_TRACK_NUMBER ? __privateGet$1(this, _firstVideoTimestamp) : __privateGet$1(this, _firstAudioTimestamp);
    if (__privateGet$1(this, _options$1).firstTimestampBehavior === "strict" && lastTimestamp === -1 && timestamp !== 0) {
      throw new Error(
        `The first chunk for your media track must have a timestamp of 0 (received ${timestamp}). Non-zero first timestamps are often caused by directly piping frames or audio data from a MediaStreamTrack into the encoder. Their timestamps are typically relative to the age of the document, which is probably what you want.

If you want to offset all timestamps of a track such that the first one is zero, set firstTimestampBehavior: 'offset' in the options.
If you want to allow non-zero first timestamps, set firstTimestampBehavior: 'permissive'.
`
      );
    } else if (__privateGet$1(this, _options$1).firstTimestampBehavior === "offset") {
      timestamp -= firstTimestamp;
    }
  }
  if (timestamp < lastTimestamp) {
    throw new Error(
      `Timestamps must be monotonically increasing (went from ${lastTimestamp} to ${timestamp}).`
    );
  }
  if (timestamp < 0) {
    throw new Error(`Timestamps must be non-negative (received ${timestamp}).`);
  }
  return timestamp;
};
_writeBlock = new WeakSet();
writeBlock_fn = function(chunk, canCreateNewCluster) {
  if (__privateGet$1(this, _options$1).streaming && !__privateGet$1(this, _tracksElement)) {
    __privateMethod$1(this, _createTracks, createTracks_fn).call(this);
    __privateMethod$1(this, _createSegment, createSegment_fn).call(this);
  }
  let msTimestamp = Math.floor(chunk.timestamp / 1e3);
  let relativeTimestamp = msTimestamp - __privateGet$1(this, _currentClusterTimestamp);
  let shouldCreateNewClusterFromKeyFrame = canCreateNewCluster && chunk.type === "key" && relativeTimestamp >= 1e3;
  let clusterWouldBeTooLong = relativeTimestamp >= MAX_CHUNK_LENGTH_MS;
  if (!__privateGet$1(this, _currentCluster) || shouldCreateNewClusterFromKeyFrame || clusterWouldBeTooLong) {
    __privateMethod$1(this, _createNewCluster, createNewCluster_fn).call(this, msTimestamp);
    relativeTimestamp = 0;
  }
  if (relativeTimestamp < 0) {
    return;
  }
  let prelude = new Uint8Array(4);
  let view = new DataView(prelude.buffer);
  view.setUint8(0, 128 | chunk.trackNumber);
  view.setInt16(1, relativeTimestamp, false);
  if (chunk.duration === void 0 && !chunk.additions) {
    view.setUint8(3, Number(chunk.type === "key") << 7);
    let simpleBlock = { id: 163 /* SimpleBlock */, data: [
      prelude,
      chunk.data
    ] };
    __privateGet$1(this, _writer$1).writeEBML(simpleBlock);
  } else {
    let msDuration = Math.floor(chunk.duration / 1e3);
    let blockGroup = { id: 160 /* BlockGroup */, data: [
      { id: 161 /* Block */, data: [
        prelude,
        chunk.data
      ] },
      chunk.duration !== void 0 ? { id: 155 /* BlockDuration */, data: msDuration } : null,
      chunk.additions ? { id: 30113 /* BlockAdditions */, data: chunk.additions } : null
    ] };
    __privateGet$1(this, _writer$1).writeEBML(blockGroup);
  }
  __privateSet$1(this, _duration, Math.max(__privateGet$1(this, _duration), msTimestamp));
};
_createCodecPrivateElement = new WeakSet();
createCodecPrivateElement_fn = function(data) {
  return { id: 25506 /* CodecPrivate */, size: 4, data: new Uint8Array(data) };
};
_writeCodecPrivate = new WeakSet();
writeCodecPrivate_fn = function(element, data) {
  let endPos = __privateGet$1(this, _writer$1).pos;
  __privateGet$1(this, _writer$1).seek(__privateGet$1(this, _writer$1).offsets.get(element));
  let codecPrivateElementSize = 2 + 4 + data.byteLength;
  let voidDataSize = CODEC_PRIVATE_MAX_SIZE - codecPrivateElementSize;
  if (voidDataSize < 0) {
    let newByteLength = data.byteLength + voidDataSize;
    if (data instanceof ArrayBuffer) {
      data = data.slice(0, newByteLength);
    } else {
      data = data.buffer.slice(0, newByteLength);
    }
    voidDataSize = 0;
  }
  element = [
    __privateMethod$1(this, _createCodecPrivateElement, createCodecPrivateElement_fn).call(this, data),
    { id: 236 /* Void */, size: 4, data: new Uint8Array(voidDataSize) }
  ];
  __privateGet$1(this, _writer$1).writeEBML(element);
  __privateGet$1(this, _writer$1).seek(endPos);
};
_createNewCluster = new WeakSet();
createNewCluster_fn = function(timestamp) {
  if (__privateGet$1(this, _currentCluster)) {
    __privateMethod$1(this, _finalizeCurrentCluster, finalizeCurrentCluster_fn).call(this);
  }
  if (__privateGet$1(this, _writer$1) instanceof BaseStreamTargetWriter && __privateGet$1(this, _writer$1).target.options.onCluster) {
    __privateGet$1(this, _writer$1).startTrackingWrites();
  }
  __privateSet$1(this, _currentCluster, {
    id: 524531317 /* Cluster */,
    size: __privateGet$1(this, _options$1).streaming ? -1 : CLUSTER_SIZE_BYTES,
    data: [
      { id: 231 /* Timestamp */, data: timestamp }
    ]
  });
  __privateGet$1(this, _writer$1).writeEBML(__privateGet$1(this, _currentCluster));
  __privateSet$1(this, _currentClusterTimestamp, timestamp);
  let clusterOffsetFromSegment = __privateGet$1(this, _writer$1).offsets.get(__privateGet$1(this, _currentCluster)) - __privateGet$1(this, _segmentDataOffset, segmentDataOffset_get);
  __privateGet$1(this, _cues).data.push({ id: 187 /* CuePoint */, data: [
    { id: 179 /* CueTime */, data: timestamp },
    __privateGet$1(this, _options$1).video ? { id: 183 /* CueTrackPositions */, data: [
      { id: 247 /* CueTrack */, data: VIDEO_TRACK_NUMBER },
      { id: 241 /* CueClusterPosition */, data: clusterOffsetFromSegment }
    ] } : null,
    __privateGet$1(this, _options$1).audio ? { id: 183 /* CueTrackPositions */, data: [
      { id: 247 /* CueTrack */, data: AUDIO_TRACK_NUMBER },
      { id: 241 /* CueClusterPosition */, data: clusterOffsetFromSegment }
    ] } : null
  ] });
};
_finalizeCurrentCluster = new WeakSet();
finalizeCurrentCluster_fn = function() {
  if (!__privateGet$1(this, _options$1).streaming) {
    let clusterSize = __privateGet$1(this, _writer$1).pos - __privateGet$1(this, _writer$1).dataOffsets.get(__privateGet$1(this, _currentCluster));
    let endPos = __privateGet$1(this, _writer$1).pos;
    __privateGet$1(this, _writer$1).seek(__privateGet$1(this, _writer$1).offsets.get(__privateGet$1(this, _currentCluster)) + 4);
    __privateGet$1(this, _writer$1).writeEBMLVarInt(clusterSize, CLUSTER_SIZE_BYTES);
    __privateGet$1(this, _writer$1).seek(endPos);
  }
  if (__privateGet$1(this, _writer$1) instanceof BaseStreamTargetWriter && __privateGet$1(this, _writer$1).target.options.onCluster) {
    let { data, start } = __privateGet$1(this, _writer$1).getTrackedWrites();
    __privateGet$1(this, _writer$1).target.options.onCluster(data, start, __privateGet$1(this, _currentClusterTimestamp));
  }
};
_ensureNotFinalized$1 = new WeakSet();
ensureNotFinalized_fn$1 = function() {
  if (__privateGet$1(this, _finalized$1)) {
    throw new Error("Cannot add new video or audio chunks after the file has been finalized.");
  }
};
new TextEncoder();

var __accessCheck = (obj, member, msg) => {
  if (!member.has(obj))
    throw TypeError("Cannot " + msg);
};
var __privateGet = (obj, member, getter) => {
  __accessCheck(obj, member, "read from private field");
  return member.get(obj);
};
var __privateAdd = (obj, member, value) => {
  if (member.has(obj))
    throw TypeError("Cannot add the same private member more than once");
  member instanceof WeakSet ? member.add(obj) : member.set(obj, value);
};
var __privateSet = (obj, member, value, setter) => {
  __accessCheck(obj, member, "write to private field");
  member.set(obj, value);
  return value;
};
var __privateWrapper = (obj, member, setter, getter) => ({
  set _(value) {
    __privateSet(obj, member, value);
  },
  get _() {
    return __privateGet(obj, member);
  }
});
var __privateMethod = (obj, member, method) => {
  __accessCheck(obj, member, "access private method");
  return method;
};

// src/misc.ts
var bytes = new Uint8Array(8);
var view = new DataView(bytes.buffer);
var u8 = (value) => {
  return [(value % 256 + 256) % 256];
};
var u16 = (value) => {
  view.setUint16(0, value, false);
  return [bytes[0], bytes[1]];
};
var i16 = (value) => {
  view.setInt16(0, value, false);
  return [bytes[0], bytes[1]];
};
var u24 = (value) => {
  view.setUint32(0, value, false);
  return [bytes[1], bytes[2], bytes[3]];
};
var u32 = (value) => {
  view.setUint32(0, value, false);
  return [bytes[0], bytes[1], bytes[2], bytes[3]];
};
var i32 = (value) => {
  view.setInt32(0, value, false);
  return [bytes[0], bytes[1], bytes[2], bytes[3]];
};
var u64 = (value) => {
  view.setUint32(0, Math.floor(value / 2 ** 32), false);
  view.setUint32(4, value, false);
  return [bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7]];
};
var fixed_8_8 = (value) => {
  view.setInt16(0, 2 ** 8 * value, false);
  return [bytes[0], bytes[1]];
};
var fixed_16_16 = (value) => {
  view.setInt32(0, 2 ** 16 * value, false);
  return [bytes[0], bytes[1], bytes[2], bytes[3]];
};
var fixed_2_30 = (value) => {
  view.setInt32(0, 2 ** 30 * value, false);
  return [bytes[0], bytes[1], bytes[2], bytes[3]];
};
var ascii = (text, nullTerminated = false) => {
  let bytes2 = Array(text.length).fill(null).map((_, i) => text.charCodeAt(i));
  if (nullTerminated)
    bytes2.push(0);
  return bytes2;
};
var last = (arr) => {
  return arr && arr[arr.length - 1];
};
var lastPresentedSample = (samples) => {
  let result = void 0;
  for (let sample of samples) {
    if (!result || sample.presentationTimestamp > result.presentationTimestamp) {
      result = sample;
    }
  }
  return result;
};
var intoTimescale = (timeInSeconds, timescale, round = true) => {
  let value = timeInSeconds * timescale;
  return round ? Math.round(value) : value;
};
var rotationMatrix = (rotationInDegrees) => {
  let theta = rotationInDegrees * (Math.PI / 180);
  let cosTheta = Math.cos(theta);
  let sinTheta = Math.sin(theta);
  return [
    cosTheta,
    sinTheta,
    0,
    -sinTheta,
    cosTheta,
    0,
    0,
    0,
    1
  ];
};
var IDENTITY_MATRIX = rotationMatrix(0);
var matrixToBytes = (matrix) => {
  return [
    fixed_16_16(matrix[0]),
    fixed_16_16(matrix[1]),
    fixed_2_30(matrix[2]),
    fixed_16_16(matrix[3]),
    fixed_16_16(matrix[4]),
    fixed_2_30(matrix[5]),
    fixed_16_16(matrix[6]),
    fixed_16_16(matrix[7]),
    fixed_2_30(matrix[8])
  ];
};
var deepClone = (x) => {
  if (!x)
    return x;
  if (typeof x !== "object")
    return x;
  if (Array.isArray(x))
    return x.map(deepClone);
  return Object.fromEntries(Object.entries(x).map(([key, value]) => [key, deepClone(value)]));
};
var isU32 = (value) => {
  return value >= 0 && value < 2 ** 32;
};

// src/box.ts
var box = (type, contents, children) => ({
  type,
  contents: contents && new Uint8Array(contents.flat(10)),
  children
});
var fullBox = (type, version, flags, contents, children) => box(
  type,
  [u8(version), u24(flags), contents ?? []],
  children
);
var ftyp = (details) => {
  let minorVersion = 512;
  if (details.fragmented)
    return box("ftyp", [
      ascii("iso5"),
      // Major brand
      u32(minorVersion),
      // Minor version
      // Compatible brands
      ascii("iso5"),
      ascii("iso6"),
      ascii("mp41")
    ]);
  return box("ftyp", [
    ascii("isom"),
    // Major brand
    u32(minorVersion),
    // Minor version
    // Compatible brands
    ascii("isom"),
    details.holdsAvc ? ascii("avc1") : [],
    ascii("mp41")
  ]);
};
var mdat = (reserveLargeSize) => ({ type: "mdat", largeSize: reserveLargeSize });
var free = (size) => ({ type: "free", size });
var moov = (tracks, creationTime, fragmented = false) => box("moov", null, [
  mvhd(creationTime, tracks),
  ...tracks.map((x) => trak(x, creationTime)),
  fragmented ? mvex(tracks) : null
]);
var mvhd = (creationTime, tracks) => {
  let duration = intoTimescale(Math.max(
    0,
    ...tracks.filter((x) => x.samples.length > 0).map((x) => {
      const lastSample = lastPresentedSample(x.samples);
      return lastSample.presentationTimestamp + lastSample.duration;
    })
  ), GLOBAL_TIMESCALE);
  let nextTrackId = Math.max(...tracks.map((x) => x.id)) + 1;
  let needsU64 = !isU32(creationTime) || !isU32(duration);
  let u32OrU64 = needsU64 ? u64 : u32;
  return fullBox("mvhd", +needsU64, 0, [
    u32OrU64(creationTime),
    // Creation time
    u32OrU64(creationTime),
    // Modification time
    u32(GLOBAL_TIMESCALE),
    // Timescale
    u32OrU64(duration),
    // Duration
    fixed_16_16(1),
    // Preferred rate
    fixed_8_8(1),
    // Preferred volume
    Array(10).fill(0),
    // Reserved
    matrixToBytes(IDENTITY_MATRIX),
    // Matrix
    Array(24).fill(0),
    // Pre-defined
    u32(nextTrackId)
    // Next track ID
  ]);
};
var trak = (track, creationTime) => box("trak", null, [
  tkhd(track, creationTime),
  mdia(track, creationTime)
]);
var tkhd = (track, creationTime) => {
  let lastSample = lastPresentedSample(track.samples);
  let durationInGlobalTimescale = intoTimescale(
    lastSample ? lastSample.presentationTimestamp + lastSample.duration : 0,
    GLOBAL_TIMESCALE
  );
  let needsU64 = !isU32(creationTime) || !isU32(durationInGlobalTimescale);
  let u32OrU64 = needsU64 ? u64 : u32;
  let matrix;
  if (track.info.type === "video") {
    matrix = typeof track.info.rotation === "number" ? rotationMatrix(track.info.rotation) : track.info.rotation;
  } else {
    matrix = IDENTITY_MATRIX;
  }
  return fullBox("tkhd", +needsU64, 3, [
    u32OrU64(creationTime),
    // Creation time
    u32OrU64(creationTime),
    // Modification time
    u32(track.id),
    // Track ID
    u32(0),
    // Reserved
    u32OrU64(durationInGlobalTimescale),
    // Duration
    Array(8).fill(0),
    // Reserved
    u16(0),
    // Layer
    u16(0),
    // Alternate group
    fixed_8_8(track.info.type === "audio" ? 1 : 0),
    // Volume
    u16(0),
    // Reserved
    matrixToBytes(matrix),
    // Matrix
    fixed_16_16(track.info.type === "video" ? track.info.width : 0),
    // Track width
    fixed_16_16(track.info.type === "video" ? track.info.height : 0)
    // Track height
  ]);
};
var mdia = (track, creationTime) => box("mdia", null, [
  mdhd(track, creationTime),
  hdlr(track.info.type === "video" ? "vide" : "soun"),
  minf(track)
]);
var mdhd = (track, creationTime) => {
  let lastSample = lastPresentedSample(track.samples);
  let localDuration = intoTimescale(
    lastSample ? lastSample.presentationTimestamp + lastSample.duration : 0,
    track.timescale
  );
  let needsU64 = !isU32(creationTime) || !isU32(localDuration);
  let u32OrU64 = needsU64 ? u64 : u32;
  return fullBox("mdhd", +needsU64, 0, [
    u32OrU64(creationTime),
    // Creation time
    u32OrU64(creationTime),
    // Modification time
    u32(track.timescale),
    // Timescale
    u32OrU64(localDuration),
    // Duration
    u16(21956),
    // Language ("und", undetermined)
    u16(0)
    // Quality
  ]);
};
var hdlr = (componentSubtype) => fullBox("hdlr", 0, 0, [
  ascii("mhlr"),
  // Component type
  ascii(componentSubtype),
  // Component subtype
  u32(0),
  // Component manufacturer
  u32(0),
  // Component flags
  u32(0),
  // Component flags mask
  ascii("mp4-muxer-hdlr", true)
  // Component name
]);
var minf = (track) => box("minf", null, [
  track.info.type === "video" ? vmhd() : smhd(),
  dinf(),
  stbl(track)
]);
var vmhd = () => fullBox("vmhd", 0, 1, [
  u16(0),
  // Graphics mode
  u16(0),
  // Opcolor R
  u16(0),
  // Opcolor G
  u16(0)
  // Opcolor B
]);
var smhd = () => fullBox("smhd", 0, 0, [
  u16(0),
  // Balance
  u16(0)
  // Reserved
]);
var dinf = () => box("dinf", null, [
  dref()
]);
var dref = () => fullBox("dref", 0, 0, [
  u32(1)
  // Entry count
], [
  url()
]);
var url = () => fullBox("url ", 0, 1);
var stbl = (track) => {
  const needsCtts = track.compositionTimeOffsetTable.length > 1 || track.compositionTimeOffsetTable.some((x) => x.sampleCompositionTimeOffset !== 0);
  return box("stbl", null, [
    stsd(track),
    stts(track),
    stss(track),
    stsc(track),
    stsz(track),
    stco(track),
    needsCtts ? ctts(track) : null
  ]);
};
var stsd = (track) => fullBox("stsd", 0, 0, [
  u32(1)
  // Entry count
], [
  track.info.type === "video" ? videoSampleDescription(
    VIDEO_CODEC_TO_BOX_NAME[track.info.codec],
    track
  ) : soundSampleDescription(
    AUDIO_CODEC_TO_BOX_NAME[track.info.codec],
    track
  )
]);
var videoSampleDescription = (compressionType, track) => box(compressionType, [
  Array(6).fill(0),
  // Reserved
  u16(1),
  // Data reference index
  u16(0),
  // Pre-defined
  u16(0),
  // Reserved
  Array(12).fill(0),
  // Pre-defined
  u16(track.info.width),
  // Width
  u16(track.info.height),
  // Height
  u32(4718592),
  // Horizontal resolution
  u32(4718592),
  // Vertical resolution
  u32(0),
  // Reserved
  u16(1),
  // Frame count
  Array(32).fill(0),
  // Compressor name
  u16(24),
  // Depth
  i16(65535)
  // Pre-defined
], [
  VIDEO_CODEC_TO_CONFIGURATION_BOX[track.info.codec](track),
  track.info.decoderConfig.colorSpace ? colr(track) : null
]);
var COLOR_PRIMARIES_MAP = {
  "bt709": 1,
  // ITU-R BT.709
  "bt470bg": 5,
  // ITU-R BT.470BG
  "smpte170m": 6
  // ITU-R BT.601 525 - SMPTE 170M
};
var TRANSFER_CHARACTERISTICS_MAP = {
  "bt709": 1,
  // ITU-R BT.709
  "smpte170m": 6,
  // SMPTE 170M
  "iec61966-2-1": 13
  // IEC 61966-2-1
};
var MATRIX_COEFFICIENTS_MAP = {
  "rgb": 0,
  // Identity
  "bt709": 1,
  // ITU-R BT.709
  "bt470bg": 5,
  // ITU-R BT.470BG
  "smpte170m": 6
  // SMPTE 170M
};
var colr = (track) => box("colr", [
  ascii("nclx"),
  // Colour type
  u16(COLOR_PRIMARIES_MAP[track.info.decoderConfig.colorSpace.primaries]),
  // Colour primaries
  u16(TRANSFER_CHARACTERISTICS_MAP[track.info.decoderConfig.colorSpace.transfer]),
  // Transfer characteristics
  u16(MATRIX_COEFFICIENTS_MAP[track.info.decoderConfig.colorSpace.matrix]),
  // Matrix coefficients
  u8((track.info.decoderConfig.colorSpace.fullRange ? 1 : 0) << 7)
  // Full range flag
]);
var avcC = (track) => track.info.decoderConfig && box("avcC", [
  // For AVC, description is an AVCDecoderConfigurationRecord, so nothing else to do here
  ...new Uint8Array(track.info.decoderConfig.description)
]);
var hvcC = (track) => track.info.decoderConfig && box("hvcC", [
  // For HEVC, description is a HEVCDecoderConfigurationRecord, so nothing else to do here
  ...new Uint8Array(track.info.decoderConfig.description)
]);
var vpcC = (track) => {
  if (!track.info.decoderConfig) {
    return null;
  }
  let decoderConfig = track.info.decoderConfig;
  if (!decoderConfig.colorSpace) {
    throw new Error(`'colorSpace' is required in the decoder config for VP9.`);
  }
  let parts = decoderConfig.codec.split(".");
  let profile = Number(parts[1]);
  let level = Number(parts[2]);
  let bitDepth = Number(parts[3]);
  let chromaSubsampling = 0;
  let thirdByte = (bitDepth << 4) + (chromaSubsampling << 1) + Number(decoderConfig.colorSpace.fullRange);
  let colourPrimaries = 2;
  let transferCharacteristics = 2;
  let matrixCoefficients = 2;
  return fullBox("vpcC", 1, 0, [
    u8(profile),
    // Profile
    u8(level),
    // Level
    u8(thirdByte),
    // Bit depth, chroma subsampling, full range
    u8(colourPrimaries),
    // Colour primaries
    u8(transferCharacteristics),
    // Transfer characteristics
    u8(matrixCoefficients),
    // Matrix coefficients
    u16(0)
    // Codec initialization data size
  ]);
};
var av1C = () => {
  let marker = 1;
  let version = 1;
  let firstByte = (marker << 7) + version;
  return box("av1C", [
    firstByte,
    0,
    0,
    0
  ]);
};
var soundSampleDescription = (compressionType, track) => box(compressionType, [
  Array(6).fill(0),
  // Reserved
  u16(1),
  // Data reference index
  u16(0),
  // Version
  u16(0),
  // Revision level
  u32(0),
  // Vendor
  u16(track.info.numberOfChannels),
  // Number of channels
  u16(16),
  // Sample size (bits)
  u16(0),
  // Compression ID
  u16(0),
  // Packet size
  fixed_16_16(track.info.sampleRate)
  // Sample rate
], [
  AUDIO_CODEC_TO_CONFIGURATION_BOX[track.info.codec](track)
]);
var esds = (track) => {
  let description = new Uint8Array(track.info.decoderConfig.description);
  return fullBox("esds", 0, 0, [
    // https://stackoverflow.com/a/54803118
    u32(58753152),
    // TAG(3) = Object Descriptor ([2])
    u8(32 + description.byteLength),
    // length of this OD (which includes the next 2 tags)
    u16(1),
    // ES_ID = 1
    u8(0),
    // flags etc = 0
    u32(75530368),
    // TAG(4) = ES Descriptor ([2]) embedded in above OD
    u8(18 + description.byteLength),
    // length of this ESD
    u8(64),
    // MPEG-4 Audio
    u8(21),
    // stream type(6bits)=5 audio, flags(2bits)=1
    u24(0),
    // 24bit buffer size
    u32(130071),
    // max bitrate
    u32(130071),
    // avg bitrate
    u32(92307584),
    // TAG(5) = ASC ([2],[3]) embedded in above OD
    u8(description.byteLength),
    // length
    ...description,
    u32(109084800),
    // TAG(6)
    u8(1),
    // length
    u8(2)
    // data
  ]);
};
var dOps = (track) => {
  let preskip = 3840;
  let gain = 0;
  const description = track.info.decoderConfig?.description;
  if (description) {
    if (description.byteLength < 18) {
      throw new TypeError("Invalid decoder description provided for Opus; must be at least 18 bytes long.");
    }
    const view2 = ArrayBuffer.isView(description) ? new DataView(description.buffer, description.byteOffset, description.byteLength) : new DataView(description);
    preskip = view2.getUint16(10, true);
    gain = view2.getInt16(14, true);
  }
  return box("dOps", [
    u8(0),
    // Version
    u8(track.info.numberOfChannels),
    // OutputChannelCount
    u16(preskip),
    u32(track.info.sampleRate),
    // InputSampleRate
    fixed_8_8(gain),
    // OutputGain
    u8(0)
    // ChannelMappingFamily
  ]);
};
var stts = (track) => {
  return fullBox("stts", 0, 0, [
    u32(track.timeToSampleTable.length),
    // Number of entries
    track.timeToSampleTable.map((x) => [
      // Time-to-sample table
      u32(x.sampleCount),
      // Sample count
      u32(x.sampleDelta)
      // Sample duration
    ])
  ]);
};
var stss = (track) => {
  if (track.samples.every((x) => x.type === "key"))
    return null;
  let keySamples = [...track.samples.entries()].filter(([, sample]) => sample.type === "key");
  return fullBox("stss", 0, 0, [
    u32(keySamples.length),
    // Number of entries
    keySamples.map(([index]) => u32(index + 1))
    // Sync sample table
  ]);
};
var stsc = (track) => {
  return fullBox("stsc", 0, 0, [
    u32(track.compactlyCodedChunkTable.length),
    // Number of entries
    track.compactlyCodedChunkTable.map((x) => [
      // Sample-to-chunk table
      u32(x.firstChunk),
      // First chunk
      u32(x.samplesPerChunk),
      // Samples per chunk
      u32(1)
      // Sample description index
    ])
  ]);
};
var stsz = (track) => fullBox("stsz", 0, 0, [
  u32(0),
  // Sample size (0 means non-constant size)
  u32(track.samples.length),
  // Number of entries
  track.samples.map((x) => u32(x.size))
  // Sample size table
]);
var stco = (track) => {
  if (track.finalizedChunks.length > 0 && last(track.finalizedChunks).offset >= 2 ** 32) {
    return fullBox("co64", 0, 0, [
      u32(track.finalizedChunks.length),
      // Number of entries
      track.finalizedChunks.map((x) => u64(x.offset))
      // Chunk offset table
    ]);
  }
  return fullBox("stco", 0, 0, [
    u32(track.finalizedChunks.length),
    // Number of entries
    track.finalizedChunks.map((x) => u32(x.offset))
    // Chunk offset table
  ]);
};
var ctts = (track) => {
  return fullBox("ctts", 0, 0, [
    u32(track.compositionTimeOffsetTable.length),
    // Number of entries
    track.compositionTimeOffsetTable.map((x) => [
      // Time-to-sample table
      u32(x.sampleCount),
      // Sample count
      u32(x.sampleCompositionTimeOffset)
      // Sample offset
    ])
  ]);
};
var mvex = (tracks) => {
  return box("mvex", null, tracks.map(trex));
};
var trex = (track) => {
  return fullBox("trex", 0, 0, [
    u32(track.id),
    // Track ID
    u32(1),
    // Default sample description index
    u32(0),
    // Default sample duration
    u32(0),
    // Default sample size
    u32(0)
    // Default sample flags
  ]);
};
var moof = (sequenceNumber, tracks) => {
  return box("moof", null, [
    mfhd(sequenceNumber),
    ...tracks.map(traf)
  ]);
};
var mfhd = (sequenceNumber) => {
  return fullBox("mfhd", 0, 0, [
    u32(sequenceNumber)
    // Sequence number
  ]);
};
var fragmentSampleFlags = (sample) => {
  let byte1 = 0;
  let byte2 = 0;
  let byte3 = 0;
  let byte4 = 0;
  let sampleIsDifferenceSample = sample.type === "delta";
  byte2 |= +sampleIsDifferenceSample;
  if (sampleIsDifferenceSample) {
    byte1 |= 1;
  } else {
    byte1 |= 2;
  }
  return byte1 << 24 | byte2 << 16 | byte3 << 8 | byte4;
};
var traf = (track) => {
  return box("traf", null, [
    tfhd(track),
    tfdt(track),
    trun(track)
  ]);
};
var tfhd = (track) => {
  let tfFlags = 0;
  tfFlags |= 8;
  tfFlags |= 16;
  tfFlags |= 32;
  tfFlags |= 131072;
  let referenceSample = track.currentChunk.samples[1] ?? track.currentChunk.samples[0];
  let referenceSampleInfo = {
    duration: referenceSample.timescaleUnitsToNextSample,
    size: referenceSample.size,
    flags: fragmentSampleFlags(referenceSample)
  };
  return fullBox("tfhd", 0, tfFlags, [
    u32(track.id),
    // Track ID
    u32(referenceSampleInfo.duration),
    // Default sample duration
    u32(referenceSampleInfo.size),
    // Default sample size
    u32(referenceSampleInfo.flags)
    // Default sample flags
  ]);
};
var tfdt = (track) => {
  return fullBox("tfdt", 1, 0, [
    u64(intoTimescale(track.currentChunk.startTimestamp, track.timescale))
    // Base Media Decode Time
  ]);
};
var trun = (track) => {
  let allSampleDurations = track.currentChunk.samples.map((x) => x.timescaleUnitsToNextSample);
  let allSampleSizes = track.currentChunk.samples.map((x) => x.size);
  let allSampleFlags = track.currentChunk.samples.map(fragmentSampleFlags);
  let allSampleCompositionTimeOffsets = track.currentChunk.samples.map((x) => intoTimescale(x.presentationTimestamp - x.decodeTimestamp, track.timescale));
  let uniqueSampleDurations = new Set(allSampleDurations);
  let uniqueSampleSizes = new Set(allSampleSizes);
  let uniqueSampleFlags = new Set(allSampleFlags);
  let uniqueSampleCompositionTimeOffsets = new Set(allSampleCompositionTimeOffsets);
  let firstSampleFlagsPresent = uniqueSampleFlags.size === 2 && allSampleFlags[0] !== allSampleFlags[1];
  let sampleDurationPresent = uniqueSampleDurations.size > 1;
  let sampleSizePresent = uniqueSampleSizes.size > 1;
  let sampleFlagsPresent = !firstSampleFlagsPresent && uniqueSampleFlags.size > 1;
  let sampleCompositionTimeOffsetsPresent = uniqueSampleCompositionTimeOffsets.size > 1 || [...uniqueSampleCompositionTimeOffsets].some((x) => x !== 0);
  let flags = 0;
  flags |= 1;
  flags |= 4 * +firstSampleFlagsPresent;
  flags |= 256 * +sampleDurationPresent;
  flags |= 512 * +sampleSizePresent;
  flags |= 1024 * +sampleFlagsPresent;
  flags |= 2048 * +sampleCompositionTimeOffsetsPresent;
  return fullBox("trun", 1, flags, [
    u32(track.currentChunk.samples.length),
    // Sample count
    u32(track.currentChunk.offset - track.currentChunk.moofOffset || 0),
    // Data offset
    firstSampleFlagsPresent ? u32(allSampleFlags[0]) : [],
    track.currentChunk.samples.map((_, i) => [
      sampleDurationPresent ? u32(allSampleDurations[i]) : [],
      // Sample duration
      sampleSizePresent ? u32(allSampleSizes[i]) : [],
      // Sample size
      sampleFlagsPresent ? u32(allSampleFlags[i]) : [],
      // Sample flags
      // Sample composition time offsets
      sampleCompositionTimeOffsetsPresent ? i32(allSampleCompositionTimeOffsets[i]) : []
    ])
  ]);
};
var mfra = (tracks) => {
  return box("mfra", null, [
    ...tracks.map(tfra),
    mfro()
  ]);
};
var tfra = (track, trackIndex) => {
  let version = 1;
  return fullBox("tfra", version, 0, [
    u32(track.id),
    // Track ID
    u32(63),
    // This specifies that traf number, trun number and sample number are 32-bit ints
    u32(track.finalizedChunks.length),
    // Number of entries
    track.finalizedChunks.map((chunk) => [
      u64(intoTimescale(chunk.startTimestamp, track.timescale)),
      // Time
      u64(chunk.moofOffset),
      // moof offset
      u32(trackIndex + 1),
      // traf number
      u32(1),
      // trun number
      u32(1)
      // Sample number
    ])
  ]);
};
var mfro = () => {
  return fullBox("mfro", 0, 0, [
    // This value needs to be overwritten manually from the outside, where the actual size of the enclosing mfra box
    // is known
    u32(0)
    // Size
  ]);
};
var VIDEO_CODEC_TO_BOX_NAME = {
  "avc": "avc1",
  "hevc": "hvc1",
  "vp9": "vp09",
  "av1": "av01"
};
var VIDEO_CODEC_TO_CONFIGURATION_BOX = {
  "avc": avcC,
  "hevc": hvcC,
  "vp9": vpcC,
  "av1": av1C
};
var AUDIO_CODEC_TO_BOX_NAME = {
  "aac": "mp4a",
  "opus": "Opus"
};
var AUDIO_CODEC_TO_CONFIGURATION_BOX = {
  "aac": esds,
  "opus": dOps
};
var Target = class {
};
var ArrayBufferTarget = class extends Target {
  constructor() {
    super(...arguments);
    this.buffer = null;
  }
};
var StreamTarget = class extends Target {
  constructor(options) {
    super();
    this.options = options;
    if (typeof options !== "object") {
      throw new TypeError("StreamTarget requires an options object to be passed to its constructor.");
    }
    if (options.onData) {
      if (typeof options.onData !== "function") {
        throw new TypeError("options.onData, when provided, must be a function.");
      }
      if (options.onData.length < 2) {
        throw new TypeError(
          "options.onData, when provided, must be a function that takes in at least two arguments (data and position). Ignoring the position argument, which specifies the byte offset at which the data is to be written, can lead to broken outputs."
        );
      }
    }
    if (options.chunked !== void 0 && typeof options.chunked !== "boolean") {
      throw new TypeError("options.chunked, when provided, must be a boolean.");
    }
    if (options.chunkSize !== void 0 && (!Number.isInteger(options.chunkSize) || options.chunkSize < 1024)) {
      throw new TypeError("options.chunkSize, when provided, must be an integer and not smaller than 1024.");
    }
  }
};
var FileSystemWritableFileStreamTarget = class extends Target {
  constructor(stream, options) {
    super();
    this.stream = stream;
    this.options = options;
    if (!(stream instanceof FileSystemWritableFileStream)) {
      throw new TypeError("FileSystemWritableFileStreamTarget requires a FileSystemWritableFileStream instance.");
    }
    if (options !== void 0 && typeof options !== "object") {
      throw new TypeError("FileSystemWritableFileStreamTarget's options, when provided, must be an object.");
    }
    if (options) {
      if (options.chunkSize !== void 0 && (!Number.isInteger(options.chunkSize) || options.chunkSize <= 0)) {
        throw new TypeError("options.chunkSize, when provided, must be a positive integer");
      }
    }
  }
};

// src/writer.ts
var _helper, _helperView;
var Writer = class {
  constructor() {
    this.pos = 0;
    __privateAdd(this, _helper, new Uint8Array(8));
    __privateAdd(this, _helperView, new DataView(__privateGet(this, _helper).buffer));
    /**
     * Stores the position from the start of the file to where boxes elements have been written. This is used to
     * rewrite/edit elements that were already added before, and to measure sizes of things.
     */
    this.offsets = /* @__PURE__ */ new WeakMap();
  }
  /** Sets the current position for future writes to a new one. */
  seek(newPos) {
    this.pos = newPos;
  }
  writeU32(value) {
    __privateGet(this, _helperView).setUint32(0, value, false);
    this.write(__privateGet(this, _helper).subarray(0, 4));
  }
  writeU64(value) {
    __privateGet(this, _helperView).setUint32(0, Math.floor(value / 2 ** 32), false);
    __privateGet(this, _helperView).setUint32(4, value, false);
    this.write(__privateGet(this, _helper).subarray(0, 8));
  }
  writeAscii(text) {
    for (let i = 0; i < text.length; i++) {
      __privateGet(this, _helperView).setUint8(i % 8, text.charCodeAt(i));
      if (i % 8 === 7)
        this.write(__privateGet(this, _helper));
    }
    if (text.length % 8 !== 0) {
      this.write(__privateGet(this, _helper).subarray(0, text.length % 8));
    }
  }
  writeBox(box2) {
    this.offsets.set(box2, this.pos);
    if (box2.contents && !box2.children) {
      this.writeBoxHeader(box2, box2.size ?? box2.contents.byteLength + 8);
      this.write(box2.contents);
    } else {
      let startPos = this.pos;
      this.writeBoxHeader(box2, 0);
      if (box2.contents)
        this.write(box2.contents);
      if (box2.children) {
        for (let child of box2.children)
          if (child)
            this.writeBox(child);
      }
      let endPos = this.pos;
      let size = box2.size ?? endPos - startPos;
      this.seek(startPos);
      this.writeBoxHeader(box2, size);
      this.seek(endPos);
    }
  }
  writeBoxHeader(box2, size) {
    this.writeU32(box2.largeSize ? 1 : size);
    this.writeAscii(box2.type);
    if (box2.largeSize)
      this.writeU64(size);
  }
  measureBoxHeader(box2) {
    return 8 + (box2.largeSize ? 8 : 0);
  }
  patchBox(box2) {
    let endPos = this.pos;
    this.seek(this.offsets.get(box2));
    this.writeBox(box2);
    this.seek(endPos);
  }
  measureBox(box2) {
    if (box2.contents && !box2.children) {
      let headerSize = this.measureBoxHeader(box2);
      return headerSize + box2.contents.byteLength;
    } else {
      let result = this.measureBoxHeader(box2);
      if (box2.contents)
        result += box2.contents.byteLength;
      if (box2.children) {
        for (let child of box2.children)
          if (child)
            result += this.measureBox(child);
      }
      return result;
    }
  }
};
_helper = new WeakMap();
_helperView = new WeakMap();
var _target, _buffer, _bytes, _maxPos, _ensureSize, ensureSize_fn;
var ArrayBufferTargetWriter = class extends Writer {
  constructor(target) {
    super();
    __privateAdd(this, _ensureSize);
    __privateAdd(this, _target, void 0);
    __privateAdd(this, _buffer, new ArrayBuffer(2 ** 16));
    __privateAdd(this, _bytes, new Uint8Array(__privateGet(this, _buffer)));
    __privateAdd(this, _maxPos, 0);
    __privateSet(this, _target, target);
  }
  write(data) {
    __privateMethod(this, _ensureSize, ensureSize_fn).call(this, this.pos + data.byteLength);
    __privateGet(this, _bytes).set(data, this.pos);
    this.pos += data.byteLength;
    __privateSet(this, _maxPos, Math.max(__privateGet(this, _maxPos), this.pos));
  }
  finalize() {
    __privateMethod(this, _ensureSize, ensureSize_fn).call(this, this.pos);
    __privateGet(this, _target).buffer = __privateGet(this, _buffer).slice(0, Math.max(__privateGet(this, _maxPos), this.pos));
  }
};
_target = new WeakMap();
_buffer = new WeakMap();
_bytes = new WeakMap();
_maxPos = new WeakMap();
_ensureSize = new WeakSet();
ensureSize_fn = function(size) {
  let newLength = __privateGet(this, _buffer).byteLength;
  while (newLength < size)
    newLength *= 2;
  if (newLength === __privateGet(this, _buffer).byteLength)
    return;
  let newBuffer = new ArrayBuffer(newLength);
  let newBytes = new Uint8Array(newBuffer);
  newBytes.set(__privateGet(this, _bytes), 0);
  __privateSet(this, _buffer, newBuffer);
  __privateSet(this, _bytes, newBytes);
};
var DEFAULT_CHUNK_SIZE = 2 ** 24;
var MAX_CHUNKS_AT_ONCE = 2;
var _target2, _sections, _chunked, _chunkSize, _chunks, _writeDataIntoChunks, writeDataIntoChunks_fn, _insertSectionIntoChunk, insertSectionIntoChunk_fn, _createChunk, createChunk_fn, _flushChunks, flushChunks_fn;
var StreamTargetWriter = class extends Writer {
  constructor(target) {
    super();
    __privateAdd(this, _writeDataIntoChunks);
    __privateAdd(this, _insertSectionIntoChunk);
    __privateAdd(this, _createChunk);
    __privateAdd(this, _flushChunks);
    __privateAdd(this, _target2, void 0);
    __privateAdd(this, _sections, []);
    __privateAdd(this, _chunked, void 0);
    __privateAdd(this, _chunkSize, void 0);
    /**
     * The data is divided up into fixed-size chunks, whose contents are first filled in RAM and then flushed out.
     * A chunk is flushed if all of its contents have been written.
     */
    __privateAdd(this, _chunks, []);
    __privateSet(this, _target2, target);
    __privateSet(this, _chunked, target.options?.chunked ?? false);
    __privateSet(this, _chunkSize, target.options?.chunkSize ?? DEFAULT_CHUNK_SIZE);
  }
  write(data) {
    __privateGet(this, _sections).push({
      data: data.slice(),
      start: this.pos
    });
    this.pos += data.byteLength;
  }
  flush() {
    if (__privateGet(this, _sections).length === 0)
      return;
    let chunks = [];
    let sorted = [...__privateGet(this, _sections)].sort((a, b) => a.start - b.start);
    chunks.push({
      start: sorted[0].start,
      size: sorted[0].data.byteLength
    });
    for (let i = 1; i < sorted.length; i++) {
      let lastChunk = chunks[chunks.length - 1];
      let section = sorted[i];
      if (section.start <= lastChunk.start + lastChunk.size) {
        lastChunk.size = Math.max(lastChunk.size, section.start + section.data.byteLength - lastChunk.start);
      } else {
        chunks.push({
          start: section.start,
          size: section.data.byteLength
        });
      }
    }
    for (let chunk of chunks) {
      chunk.data = new Uint8Array(chunk.size);
      for (let section of __privateGet(this, _sections)) {
        if (chunk.start <= section.start && section.start < chunk.start + chunk.size) {
          chunk.data.set(section.data, section.start - chunk.start);
        }
      }
      if (__privateGet(this, _chunked)) {
        __privateMethod(this, _writeDataIntoChunks, writeDataIntoChunks_fn).call(this, chunk.data, chunk.start);
        __privateMethod(this, _flushChunks, flushChunks_fn).call(this);
      } else {
        __privateGet(this, _target2).options.onData?.(chunk.data, chunk.start);
      }
    }
    __privateGet(this, _sections).length = 0;
  }
  finalize() {
    if (__privateGet(this, _chunked)) {
      __privateMethod(this, _flushChunks, flushChunks_fn).call(this, true);
    }
  }
};
_target2 = new WeakMap();
_sections = new WeakMap();
_chunked = new WeakMap();
_chunkSize = new WeakMap();
_chunks = new WeakMap();
_writeDataIntoChunks = new WeakSet();
writeDataIntoChunks_fn = function(data, position) {
  let chunkIndex = __privateGet(this, _chunks).findIndex((x) => x.start <= position && position < x.start + __privateGet(this, _chunkSize));
  if (chunkIndex === -1)
    chunkIndex = __privateMethod(this, _createChunk, createChunk_fn).call(this, position);
  let chunk = __privateGet(this, _chunks)[chunkIndex];
  let relativePosition = position - chunk.start;
  let toWrite = data.subarray(0, Math.min(__privateGet(this, _chunkSize) - relativePosition, data.byteLength));
  chunk.data.set(toWrite, relativePosition);
  let section = {
    start: relativePosition,
    end: relativePosition + toWrite.byteLength
  };
  __privateMethod(this, _insertSectionIntoChunk, insertSectionIntoChunk_fn).call(this, chunk, section);
  if (chunk.written[0].start === 0 && chunk.written[0].end === __privateGet(this, _chunkSize)) {
    chunk.shouldFlush = true;
  }
  if (__privateGet(this, _chunks).length > MAX_CHUNKS_AT_ONCE) {
    for (let i = 0; i < __privateGet(this, _chunks).length - 1; i++) {
      __privateGet(this, _chunks)[i].shouldFlush = true;
    }
    __privateMethod(this, _flushChunks, flushChunks_fn).call(this);
  }
  if (toWrite.byteLength < data.byteLength) {
    __privateMethod(this, _writeDataIntoChunks, writeDataIntoChunks_fn).call(this, data.subarray(toWrite.byteLength), position + toWrite.byteLength);
  }
};
_insertSectionIntoChunk = new WeakSet();
insertSectionIntoChunk_fn = function(chunk, section) {
  let low = 0;
  let high = chunk.written.length - 1;
  let index = -1;
  while (low <= high) {
    let mid = Math.floor(low + (high - low + 1) / 2);
    if (chunk.written[mid].start <= section.start) {
      low = mid + 1;
      index = mid;
    } else {
      high = mid - 1;
    }
  }
  chunk.written.splice(index + 1, 0, section);
  if (index === -1 || chunk.written[index].end < section.start)
    index++;
  while (index < chunk.written.length - 1 && chunk.written[index].end >= chunk.written[index + 1].start) {
    chunk.written[index].end = Math.max(chunk.written[index].end, chunk.written[index + 1].end);
    chunk.written.splice(index + 1, 1);
  }
};
_createChunk = new WeakSet();
createChunk_fn = function(includesPosition) {
  let start = Math.floor(includesPosition / __privateGet(this, _chunkSize)) * __privateGet(this, _chunkSize);
  let chunk = {
    start,
    data: new Uint8Array(__privateGet(this, _chunkSize)),
    written: [],
    shouldFlush: false
  };
  __privateGet(this, _chunks).push(chunk);
  __privateGet(this, _chunks).sort((a, b) => a.start - b.start);
  return __privateGet(this, _chunks).indexOf(chunk);
};
_flushChunks = new WeakSet();
flushChunks_fn = function(force = false) {
  for (let i = 0; i < __privateGet(this, _chunks).length; i++) {
    let chunk = __privateGet(this, _chunks)[i];
    if (!chunk.shouldFlush && !force)
      continue;
    for (let section of chunk.written) {
      __privateGet(this, _target2).options.onData?.(
        chunk.data.subarray(section.start, section.end),
        chunk.start + section.start
      );
    }
    __privateGet(this, _chunks).splice(i--, 1);
  }
};
var FileSystemWritableFileStreamTargetWriter = class extends StreamTargetWriter {
  constructor(target) {
    super(new StreamTarget({
      onData: (data, position) => target.stream.write({
        type: "write",
        data,
        position
      }),
      chunked: true,
      chunkSize: target.options?.chunkSize
    }));
  }
};

// src/muxer.ts
var GLOBAL_TIMESCALE = 1e3;
var SUPPORTED_VIDEO_CODECS = ["avc", "hevc", "vp9", "av1"];
var SUPPORTED_AUDIO_CODECS = ["aac", "opus"];
var TIMESTAMP_OFFSET = 2082844800;
var FIRST_TIMESTAMP_BEHAVIORS = ["strict", "offset", "cross-track-offset"];
var _options, _writer, _ftypSize, _mdat, _videoTrack, _audioTrack, _creationTime, _finalizedChunks, _nextFragmentNumber, _videoSampleQueue, _audioSampleQueue, _finalized, _validateOptions, validateOptions_fn, _writeHeader, writeHeader_fn, _computeMoovSizeUpperBound, computeMoovSizeUpperBound_fn, _prepareTracks, prepareTracks_fn, _generateMpeg4AudioSpecificConfig, generateMpeg4AudioSpecificConfig_fn, _createSampleForTrack, createSampleForTrack_fn, _addSampleToTrack, addSampleToTrack_fn, _validateTimestamp, validateTimestamp_fn, _finalizeCurrentChunk, finalizeCurrentChunk_fn, _finalizeFragment, finalizeFragment_fn, _maybeFlushStreamingTargetWriter, maybeFlushStreamingTargetWriter_fn, _ensureNotFinalized, ensureNotFinalized_fn;
var Muxer = class {
  constructor(options) {
    __privateAdd(this, _validateOptions);
    __privateAdd(this, _writeHeader);
    __privateAdd(this, _computeMoovSizeUpperBound);
    __privateAdd(this, _prepareTracks);
    // https://wiki.multimedia.cx/index.php/MPEG-4_Audio
    __privateAdd(this, _generateMpeg4AudioSpecificConfig);
    __privateAdd(this, _createSampleForTrack);
    __privateAdd(this, _addSampleToTrack);
    __privateAdd(this, _validateTimestamp);
    __privateAdd(this, _finalizeCurrentChunk);
    __privateAdd(this, _finalizeFragment);
    __privateAdd(this, _maybeFlushStreamingTargetWriter);
    __privateAdd(this, _ensureNotFinalized);
    __privateAdd(this, _options, void 0);
    __privateAdd(this, _writer, void 0);
    __privateAdd(this, _ftypSize, void 0);
    __privateAdd(this, _mdat, void 0);
    __privateAdd(this, _videoTrack, null);
    __privateAdd(this, _audioTrack, null);
    __privateAdd(this, _creationTime, Math.floor(Date.now() / 1e3) + TIMESTAMP_OFFSET);
    __privateAdd(this, _finalizedChunks, []);
    // Fields for fragmented MP4:
    __privateAdd(this, _nextFragmentNumber, 1);
    __privateAdd(this, _videoSampleQueue, []);
    __privateAdd(this, _audioSampleQueue, []);
    __privateAdd(this, _finalized, false);
    __privateMethod(this, _validateOptions, validateOptions_fn).call(this, options);
    options.video = deepClone(options.video);
    options.audio = deepClone(options.audio);
    options.fastStart = deepClone(options.fastStart);
    this.target = options.target;
    __privateSet(this, _options, {
      firstTimestampBehavior: "strict",
      ...options
    });
    if (options.target instanceof ArrayBufferTarget) {
      __privateSet(this, _writer, new ArrayBufferTargetWriter(options.target));
    } else if (options.target instanceof StreamTarget) {
      __privateSet(this, _writer, new StreamTargetWriter(options.target));
    } else if (options.target instanceof FileSystemWritableFileStreamTarget) {
      __privateSet(this, _writer, new FileSystemWritableFileStreamTargetWriter(options.target));
    } else {
      throw new Error(`Invalid target: ${options.target}`);
    }
    __privateMethod(this, _prepareTracks, prepareTracks_fn).call(this);
    __privateMethod(this, _writeHeader, writeHeader_fn).call(this);
  }
  addVideoChunk(sample, meta, timestamp, compositionTimeOffset) {
    if (!(sample instanceof EncodedVideoChunk)) {
      throw new TypeError("addVideoChunk's first argument (sample) must be of type EncodedVideoChunk.");
    }
    if (meta && typeof meta !== "object") {
      throw new TypeError("addVideoChunk's second argument (meta), when provided, must be an object.");
    }
    if (timestamp !== void 0 && (!Number.isFinite(timestamp) || timestamp < 0)) {
      throw new TypeError(
        "addVideoChunk's third argument (timestamp), when provided, must be a non-negative real number."
      );
    }
    if (compositionTimeOffset !== void 0 && !Number.isFinite(compositionTimeOffset)) {
      throw new TypeError(
        "addVideoChunk's fourth argument (compositionTimeOffset), when provided, must be a real number."
      );
    }
    let data = new Uint8Array(sample.byteLength);
    sample.copyTo(data);
    this.addVideoChunkRaw(
      data,
      sample.type,
      timestamp ?? sample.timestamp,
      sample.duration,
      meta,
      compositionTimeOffset
    );
  }
  addVideoChunkRaw(data, type, timestamp, duration, meta, compositionTimeOffset) {
    if (!(data instanceof Uint8Array)) {
      throw new TypeError("addVideoChunkRaw's first argument (data) must be an instance of Uint8Array.");
    }
    if (type !== "key" && type !== "delta") {
      throw new TypeError("addVideoChunkRaw's second argument (type) must be either 'key' or 'delta'.");
    }
    if (!Number.isFinite(timestamp) || timestamp < 0) {
      throw new TypeError("addVideoChunkRaw's third argument (timestamp) must be a non-negative real number.");
    }
    if (!Number.isFinite(duration) || duration < 0) {
      throw new TypeError("addVideoChunkRaw's fourth argument (duration) must be a non-negative real number.");
    }
    if (meta && typeof meta !== "object") {
      throw new TypeError("addVideoChunkRaw's fifth argument (meta), when provided, must be an object.");
    }
    if (compositionTimeOffset !== void 0 && !Number.isFinite(compositionTimeOffset)) {
      throw new TypeError(
        "addVideoChunkRaw's sixth argument (compositionTimeOffset), when provided, must be a real number."
      );
    }
    __privateMethod(this, _ensureNotFinalized, ensureNotFinalized_fn).call(this);
    if (!__privateGet(this, _options).video)
      throw new Error("No video track declared.");
    if (typeof __privateGet(this, _options).fastStart === "object" && __privateGet(this, _videoTrack).samples.length === __privateGet(this, _options).fastStart.expectedVideoChunks) {
      throw new Error(`Cannot add more video chunks than specified in 'fastStart' (${__privateGet(this, _options).fastStart.expectedVideoChunks}).`);
    }
    let videoSample = __privateMethod(this, _createSampleForTrack, createSampleForTrack_fn).call(this, __privateGet(this, _videoTrack), data, type, timestamp, duration, meta, compositionTimeOffset);
    if (__privateGet(this, _options).fastStart === "fragmented" && __privateGet(this, _audioTrack)) {
      while (__privateGet(this, _audioSampleQueue).length > 0 && __privateGet(this, _audioSampleQueue)[0].decodeTimestamp <= videoSample.decodeTimestamp) {
        let audioSample = __privateGet(this, _audioSampleQueue).shift();
        __privateMethod(this, _addSampleToTrack, addSampleToTrack_fn).call(this, __privateGet(this, _audioTrack), audioSample);
      }
      if (videoSample.decodeTimestamp <= __privateGet(this, _audioTrack).lastDecodeTimestamp) {
        __privateMethod(this, _addSampleToTrack, addSampleToTrack_fn).call(this, __privateGet(this, _videoTrack), videoSample);
      } else {
        __privateGet(this, _videoSampleQueue).push(videoSample);
      }
    } else {
      __privateMethod(this, _addSampleToTrack, addSampleToTrack_fn).call(this, __privateGet(this, _videoTrack), videoSample);
    }
  }
  addAudioChunk(sample, meta, timestamp) {
    if (!(sample instanceof EncodedAudioChunk)) {
      throw new TypeError("addAudioChunk's first argument (sample) must be of type EncodedAudioChunk.");
    }
    if (meta && typeof meta !== "object") {
      throw new TypeError("addAudioChunk's second argument (meta), when provided, must be an object.");
    }
    if (timestamp !== void 0 && (!Number.isFinite(timestamp) || timestamp < 0)) {
      throw new TypeError(
        "addAudioChunk's third argument (timestamp), when provided, must be a non-negative real number."
      );
    }
    let data = new Uint8Array(sample.byteLength);
    sample.copyTo(data);
    this.addAudioChunkRaw(data, sample.type, timestamp ?? sample.timestamp, sample.duration, meta);
  }
  addAudioChunkRaw(data, type, timestamp, duration, meta) {
    if (!(data instanceof Uint8Array)) {
      throw new TypeError("addAudioChunkRaw's first argument (data) must be an instance of Uint8Array.");
    }
    if (type !== "key" && type !== "delta") {
      throw new TypeError("addAudioChunkRaw's second argument (type) must be either 'key' or 'delta'.");
    }
    if (!Number.isFinite(timestamp) || timestamp < 0) {
      throw new TypeError("addAudioChunkRaw's third argument (timestamp) must be a non-negative real number.");
    }
    if (!Number.isFinite(duration) || duration < 0) {
      throw new TypeError("addAudioChunkRaw's fourth argument (duration) must be a non-negative real number.");
    }
    if (meta && typeof meta !== "object") {
      throw new TypeError("addAudioChunkRaw's fifth argument (meta), when provided, must be an object.");
    }
    __privateMethod(this, _ensureNotFinalized, ensureNotFinalized_fn).call(this);
    if (!__privateGet(this, _options).audio)
      throw new Error("No audio track declared.");
    if (typeof __privateGet(this, _options).fastStart === "object" && __privateGet(this, _audioTrack).samples.length === __privateGet(this, _options).fastStart.expectedAudioChunks) {
      throw new Error(`Cannot add more audio chunks than specified in 'fastStart' (${__privateGet(this, _options).fastStart.expectedAudioChunks}).`);
    }
    let audioSample = __privateMethod(this, _createSampleForTrack, createSampleForTrack_fn).call(this, __privateGet(this, _audioTrack), data, type, timestamp, duration, meta);
    if (__privateGet(this, _options).fastStart === "fragmented" && __privateGet(this, _videoTrack)) {
      while (__privateGet(this, _videoSampleQueue).length > 0 && __privateGet(this, _videoSampleQueue)[0].decodeTimestamp <= audioSample.decodeTimestamp) {
        let videoSample = __privateGet(this, _videoSampleQueue).shift();
        __privateMethod(this, _addSampleToTrack, addSampleToTrack_fn).call(this, __privateGet(this, _videoTrack), videoSample);
      }
      if (audioSample.decodeTimestamp <= __privateGet(this, _videoTrack).lastDecodeTimestamp) {
        __privateMethod(this, _addSampleToTrack, addSampleToTrack_fn).call(this, __privateGet(this, _audioTrack), audioSample);
      } else {
        __privateGet(this, _audioSampleQueue).push(audioSample);
      }
    } else {
      __privateMethod(this, _addSampleToTrack, addSampleToTrack_fn).call(this, __privateGet(this, _audioTrack), audioSample);
    }
  }
  /** Finalizes the file, making it ready for use. Must be called after all video and audio chunks have been added. */
  finalize() {
    if (__privateGet(this, _finalized)) {
      throw new Error("Cannot finalize a muxer more than once.");
    }
    if (__privateGet(this, _options).fastStart === "fragmented") {
      for (let videoSample of __privateGet(this, _videoSampleQueue))
        __privateMethod(this, _addSampleToTrack, addSampleToTrack_fn).call(this, __privateGet(this, _videoTrack), videoSample);
      for (let audioSample of __privateGet(this, _audioSampleQueue))
        __privateMethod(this, _addSampleToTrack, addSampleToTrack_fn).call(this, __privateGet(this, _audioTrack), audioSample);
      __privateMethod(this, _finalizeFragment, finalizeFragment_fn).call(this, false);
    } else {
      if (__privateGet(this, _videoTrack))
        __privateMethod(this, _finalizeCurrentChunk, finalizeCurrentChunk_fn).call(this, __privateGet(this, _videoTrack));
      if (__privateGet(this, _audioTrack))
        __privateMethod(this, _finalizeCurrentChunk, finalizeCurrentChunk_fn).call(this, __privateGet(this, _audioTrack));
    }
    let tracks = [__privateGet(this, _videoTrack), __privateGet(this, _audioTrack)].filter(Boolean);
    if (__privateGet(this, _options).fastStart === "in-memory") {
      let mdatSize;
      for (let i = 0; i < 2; i++) {
        let movieBox2 = moov(tracks, __privateGet(this, _creationTime));
        let movieBoxSize = __privateGet(this, _writer).measureBox(movieBox2);
        mdatSize = __privateGet(this, _writer).measureBox(__privateGet(this, _mdat));
        let currentChunkPos = __privateGet(this, _writer).pos + movieBoxSize + mdatSize;
        for (let chunk of __privateGet(this, _finalizedChunks)) {
          chunk.offset = currentChunkPos;
          for (let { data } of chunk.samples) {
            currentChunkPos += data.byteLength;
            mdatSize += data.byteLength;
          }
        }
        if (currentChunkPos < 2 ** 32)
          break;
        if (mdatSize >= 2 ** 32)
          __privateGet(this, _mdat).largeSize = true;
      }
      let movieBox = moov(tracks, __privateGet(this, _creationTime));
      __privateGet(this, _writer).writeBox(movieBox);
      __privateGet(this, _mdat).size = mdatSize;
      __privateGet(this, _writer).writeBox(__privateGet(this, _mdat));
      for (let chunk of __privateGet(this, _finalizedChunks)) {
        for (let sample of chunk.samples) {
          __privateGet(this, _writer).write(sample.data);
          sample.data = null;
        }
      }
    } else if (__privateGet(this, _options).fastStart === "fragmented") {
      let startPos = __privateGet(this, _writer).pos;
      let mfraBox = mfra(tracks);
      __privateGet(this, _writer).writeBox(mfraBox);
      let mfraBoxSize = __privateGet(this, _writer).pos - startPos;
      __privateGet(this, _writer).seek(__privateGet(this, _writer).pos - 4);
      __privateGet(this, _writer).writeU32(mfraBoxSize);
    } else {
      let mdatPos = __privateGet(this, _writer).offsets.get(__privateGet(this, _mdat));
      let mdatSize = __privateGet(this, _writer).pos - mdatPos;
      __privateGet(this, _mdat).size = mdatSize;
      __privateGet(this, _mdat).largeSize = mdatSize >= 2 ** 32;
      __privateGet(this, _writer).patchBox(__privateGet(this, _mdat));
      let movieBox = moov(tracks, __privateGet(this, _creationTime));
      if (typeof __privateGet(this, _options).fastStart === "object") {
        __privateGet(this, _writer).seek(__privateGet(this, _ftypSize));
        __privateGet(this, _writer).writeBox(movieBox);
        let remainingBytes = mdatPos - __privateGet(this, _writer).pos;
        __privateGet(this, _writer).writeBox(free(remainingBytes));
      } else {
        __privateGet(this, _writer).writeBox(movieBox);
      }
    }
    __privateMethod(this, _maybeFlushStreamingTargetWriter, maybeFlushStreamingTargetWriter_fn).call(this);
    __privateGet(this, _writer).finalize();
    __privateSet(this, _finalized, true);
  }
};
_options = new WeakMap();
_writer = new WeakMap();
_ftypSize = new WeakMap();
_mdat = new WeakMap();
_videoTrack = new WeakMap();
_audioTrack = new WeakMap();
_creationTime = new WeakMap();
_finalizedChunks = new WeakMap();
_nextFragmentNumber = new WeakMap();
_videoSampleQueue = new WeakMap();
_audioSampleQueue = new WeakMap();
_finalized = new WeakMap();
_validateOptions = new WeakSet();
validateOptions_fn = function(options) {
  if (typeof options !== "object") {
    throw new TypeError("The muxer requires an options object to be passed to its constructor.");
  }
  if (!(options.target instanceof Target)) {
    throw new TypeError("The target must be provided and an instance of Target.");
  }
  if (options.video) {
    if (!SUPPORTED_VIDEO_CODECS.includes(options.video.codec)) {
      throw new TypeError(`Unsupported video codec: ${options.video.codec}`);
    }
    if (!Number.isInteger(options.video.width) || options.video.width <= 0) {
      throw new TypeError(`Invalid video width: ${options.video.width}. Must be a positive integer.`);
    }
    if (!Number.isInteger(options.video.height) || options.video.height <= 0) {
      throw new TypeError(`Invalid video height: ${options.video.height}. Must be a positive integer.`);
    }
    const videoRotation = options.video.rotation;
    if (typeof videoRotation === "number" && ![0, 90, 180, 270].includes(videoRotation)) {
      throw new TypeError(`Invalid video rotation: ${videoRotation}. Has to be 0, 90, 180 or 270.`);
    } else if (Array.isArray(videoRotation) && (videoRotation.length !== 9 || videoRotation.some((value) => typeof value !== "number"))) {
      throw new TypeError(`Invalid video transformation matrix: ${videoRotation.join()}`);
    }
    if (options.video.frameRate !== void 0 && (!Number.isInteger(options.video.frameRate) || options.video.frameRate <= 0)) {
      throw new TypeError(
        `Invalid video frame rate: ${options.video.frameRate}. Must be a positive integer.`
      );
    }
  }
  if (options.audio) {
    if (!SUPPORTED_AUDIO_CODECS.includes(options.audio.codec)) {
      throw new TypeError(`Unsupported audio codec: ${options.audio.codec}`);
    }
    if (!Number.isInteger(options.audio.numberOfChannels) || options.audio.numberOfChannels <= 0) {
      throw new TypeError(
        `Invalid number of audio channels: ${options.audio.numberOfChannels}. Must be a positive integer.`
      );
    }
    if (!Number.isInteger(options.audio.sampleRate) || options.audio.sampleRate <= 0) {
      throw new TypeError(
        `Invalid audio sample rate: ${options.audio.sampleRate}. Must be a positive integer.`
      );
    }
  }
  if (options.firstTimestampBehavior && !FIRST_TIMESTAMP_BEHAVIORS.includes(options.firstTimestampBehavior)) {
    throw new TypeError(`Invalid first timestamp behavior: ${options.firstTimestampBehavior}`);
  }
  if (typeof options.fastStart === "object") {
    if (options.video) {
      if (options.fastStart.expectedVideoChunks === void 0) {
        throw new TypeError(`'fastStart' is an object but is missing property 'expectedVideoChunks'.`);
      } else if (!Number.isInteger(options.fastStart.expectedVideoChunks) || options.fastStart.expectedVideoChunks < 0) {
        throw new TypeError(`'expectedVideoChunks' must be a non-negative integer.`);
      }
    }
    if (options.audio) {
      if (options.fastStart.expectedAudioChunks === void 0) {
        throw new TypeError(`'fastStart' is an object but is missing property 'expectedAudioChunks'.`);
      } else if (!Number.isInteger(options.fastStart.expectedAudioChunks) || options.fastStart.expectedAudioChunks < 0) {
        throw new TypeError(`'expectedAudioChunks' must be a non-negative integer.`);
      }
    }
  } else if (![false, "in-memory", "fragmented"].includes(options.fastStart)) {
    throw new TypeError(`'fastStart' option must be false, 'in-memory', 'fragmented' or an object.`);
  }
  if (options.minFragmentDuration !== void 0 && (!Number.isFinite(options.minFragmentDuration) || options.minFragmentDuration < 0)) {
    throw new TypeError(`'minFragmentDuration' must be a non-negative number.`);
  }
};
_writeHeader = new WeakSet();
writeHeader_fn = function() {
  __privateGet(this, _writer).writeBox(ftyp({
    holdsAvc: __privateGet(this, _options).video?.codec === "avc",
    fragmented: __privateGet(this, _options).fastStart === "fragmented"
  }));
  __privateSet(this, _ftypSize, __privateGet(this, _writer).pos);
  if (__privateGet(this, _options).fastStart === "in-memory") {
    __privateSet(this, _mdat, mdat(false));
  } else if (__privateGet(this, _options).fastStart === "fragmented") ; else {
    if (typeof __privateGet(this, _options).fastStart === "object") {
      let moovSizeUpperBound = __privateMethod(this, _computeMoovSizeUpperBound, computeMoovSizeUpperBound_fn).call(this);
      __privateGet(this, _writer).seek(__privateGet(this, _writer).pos + moovSizeUpperBound);
    }
    __privateSet(this, _mdat, mdat(true));
    __privateGet(this, _writer).writeBox(__privateGet(this, _mdat));
  }
  __privateMethod(this, _maybeFlushStreamingTargetWriter, maybeFlushStreamingTargetWriter_fn).call(this);
};
_computeMoovSizeUpperBound = new WeakSet();
computeMoovSizeUpperBound_fn = function() {
  if (typeof __privateGet(this, _options).fastStart !== "object")
    return;
  let upperBound = 0;
  let sampleCounts = [
    __privateGet(this, _options).fastStart.expectedVideoChunks,
    __privateGet(this, _options).fastStart.expectedAudioChunks
  ];
  for (let n of sampleCounts) {
    if (!n)
      continue;
    upperBound += (4 + 4) * Math.ceil(2 / 3 * n);
    upperBound += 4 * n;
    upperBound += (4 + 4 + 4) * Math.ceil(2 / 3 * n);
    upperBound += 4 * n;
    upperBound += 8 * n;
  }
  upperBound += 4096;
  return upperBound;
};
_prepareTracks = new WeakSet();
prepareTracks_fn = function() {
  if (__privateGet(this, _options).video) {
    __privateSet(this, _videoTrack, {
      id: 1,
      info: {
        type: "video",
        codec: __privateGet(this, _options).video.codec,
        width: __privateGet(this, _options).video.width,
        height: __privateGet(this, _options).video.height,
        rotation: __privateGet(this, _options).video.rotation ?? 0,
        decoderConfig: null
      },
      // The fallback contains many common frame rates as factors
      timescale: __privateGet(this, _options).video.frameRate ?? 57600,
      samples: [],
      finalizedChunks: [],
      currentChunk: null,
      firstDecodeTimestamp: void 0,
      lastDecodeTimestamp: -1,
      timeToSampleTable: [],
      compositionTimeOffsetTable: [],
      lastTimescaleUnits: null,
      lastSample: null,
      compactlyCodedChunkTable: []
    });
  }
  if (__privateGet(this, _options).audio) {
    __privateSet(this, _audioTrack, {
      id: __privateGet(this, _options).video ? 2 : 1,
      info: {
        type: "audio",
        codec: __privateGet(this, _options).audio.codec,
        numberOfChannels: __privateGet(this, _options).audio.numberOfChannels,
        sampleRate: __privateGet(this, _options).audio.sampleRate,
        decoderConfig: null
      },
      timescale: __privateGet(this, _options).audio.sampleRate,
      samples: [],
      finalizedChunks: [],
      currentChunk: null,
      firstDecodeTimestamp: void 0,
      lastDecodeTimestamp: -1,
      timeToSampleTable: [],
      compositionTimeOffsetTable: [],
      lastTimescaleUnits: null,
      lastSample: null,
      compactlyCodedChunkTable: []
    });
    if (__privateGet(this, _options).audio.codec === "aac") {
      let guessedCodecPrivate = __privateMethod(this, _generateMpeg4AudioSpecificConfig, generateMpeg4AudioSpecificConfig_fn).call(
        this,
        2,
        // Object type for AAC-LC, since it's the most common
        __privateGet(this, _options).audio.sampleRate,
        __privateGet(this, _options).audio.numberOfChannels
      );
      __privateGet(this, _audioTrack).info.decoderConfig = {
        codec: __privateGet(this, _options).audio.codec,
        description: guessedCodecPrivate,
        numberOfChannels: __privateGet(this, _options).audio.numberOfChannels,
        sampleRate: __privateGet(this, _options).audio.sampleRate
      };
    }
  }
};
_generateMpeg4AudioSpecificConfig = new WeakSet();
generateMpeg4AudioSpecificConfig_fn = function(objectType, sampleRate, numberOfChannels) {
  let frequencyIndices = [96e3, 88200, 64e3, 48e3, 44100, 32e3, 24e3, 22050, 16e3, 12e3, 11025, 8e3, 7350];
  let frequencyIndex = frequencyIndices.indexOf(sampleRate);
  let channelConfig = numberOfChannels;
  let configBits = "";
  configBits += objectType.toString(2).padStart(5, "0");
  configBits += frequencyIndex.toString(2).padStart(4, "0");
  if (frequencyIndex === 15)
    configBits += sampleRate.toString(2).padStart(24, "0");
  configBits += channelConfig.toString(2).padStart(4, "0");
  let paddingLength = Math.ceil(configBits.length / 8) * 8;
  configBits = configBits.padEnd(paddingLength, "0");
  let configBytes = new Uint8Array(configBits.length / 8);
  for (let i = 0; i < configBits.length; i += 8) {
    configBytes[i / 8] = parseInt(configBits.slice(i, i + 8), 2);
  }
  return configBytes;
};
_createSampleForTrack = new WeakSet();
createSampleForTrack_fn = function(track, data, type, timestamp, duration, meta, compositionTimeOffset) {
  let presentationTimestampInSeconds = timestamp / 1e6;
  let decodeTimestampInSeconds = (timestamp - (compositionTimeOffset ?? 0)) / 1e6;
  let durationInSeconds = duration / 1e6;
  let adjusted = __privateMethod(this, _validateTimestamp, validateTimestamp_fn).call(this, presentationTimestampInSeconds, decodeTimestampInSeconds, track);
  presentationTimestampInSeconds = adjusted.presentationTimestamp;
  decodeTimestampInSeconds = adjusted.decodeTimestamp;
  if (meta?.decoderConfig) {
    if (track.info.decoderConfig === null) {
      track.info.decoderConfig = meta.decoderConfig;
    } else {
      Object.assign(track.info.decoderConfig, meta.decoderConfig);
    }
  }
  let sample = {
    presentationTimestamp: presentationTimestampInSeconds,
    decodeTimestamp: decodeTimestampInSeconds,
    duration: durationInSeconds,
    data,
    size: data.byteLength,
    type,
    // Will be refined once the next sample comes in
    timescaleUnitsToNextSample: intoTimescale(durationInSeconds, track.timescale)
  };
  return sample;
};
_addSampleToTrack = new WeakSet();
addSampleToTrack_fn = function(track, sample) {
  if (__privateGet(this, _options).fastStart !== "fragmented") {
    track.samples.push(sample);
  }
  const sampleCompositionTimeOffset = intoTimescale(sample.presentationTimestamp - sample.decodeTimestamp, track.timescale);
  if (track.lastTimescaleUnits !== null) {
    let timescaleUnits = intoTimescale(sample.decodeTimestamp, track.timescale, false);
    let delta = Math.round(timescaleUnits - track.lastTimescaleUnits);
    track.lastTimescaleUnits += delta;
    track.lastSample.timescaleUnitsToNextSample = delta;
    if (__privateGet(this, _options).fastStart !== "fragmented") {
      let lastTableEntry = last(track.timeToSampleTable);
      if (lastTableEntry.sampleCount === 1) {
        lastTableEntry.sampleDelta = delta;
        lastTableEntry.sampleCount++;
      } else if (lastTableEntry.sampleDelta === delta) {
        lastTableEntry.sampleCount++;
      } else {
        lastTableEntry.sampleCount--;
        track.timeToSampleTable.push({
          sampleCount: 2,
          sampleDelta: delta
        });
      }
      const lastCompositionTimeOffsetTableEntry = last(track.compositionTimeOffsetTable);
      if (lastCompositionTimeOffsetTableEntry.sampleCompositionTimeOffset === sampleCompositionTimeOffset) {
        lastCompositionTimeOffsetTableEntry.sampleCount++;
      } else {
        track.compositionTimeOffsetTable.push({
          sampleCount: 1,
          sampleCompositionTimeOffset
        });
      }
    }
  } else {
    track.lastTimescaleUnits = 0;
    if (__privateGet(this, _options).fastStart !== "fragmented") {
      track.timeToSampleTable.push({
        sampleCount: 1,
        sampleDelta: intoTimescale(sample.duration, track.timescale)
      });
      track.compositionTimeOffsetTable.push({
        sampleCount: 1,
        sampleCompositionTimeOffset
      });
    }
  }
  track.lastSample = sample;
  let beginNewChunk = false;
  if (!track.currentChunk) {
    beginNewChunk = true;
  } else {
    let currentChunkDuration = sample.presentationTimestamp - track.currentChunk.startTimestamp;
    if (__privateGet(this, _options).fastStart === "fragmented") {
      let mostImportantTrack = __privateGet(this, _videoTrack) ?? __privateGet(this, _audioTrack);
      const chunkDuration = __privateGet(this, _options).minFragmentDuration ?? 1;
      if (track === mostImportantTrack && sample.type === "key" && currentChunkDuration >= chunkDuration) {
        beginNewChunk = true;
        __privateMethod(this, _finalizeFragment, finalizeFragment_fn).call(this);
      }
    } else {
      beginNewChunk = currentChunkDuration >= 0.5;
    }
  }
  if (beginNewChunk) {
    if (track.currentChunk) {
      __privateMethod(this, _finalizeCurrentChunk, finalizeCurrentChunk_fn).call(this, track);
    }
    track.currentChunk = {
      startTimestamp: sample.presentationTimestamp,
      samples: []
    };
  }
  track.currentChunk.samples.push(sample);
};
_validateTimestamp = new WeakSet();
validateTimestamp_fn = function(presentationTimestamp, decodeTimestamp, track) {
  const strictTimestampBehavior = __privateGet(this, _options).firstTimestampBehavior === "strict";
  const noLastDecodeTimestamp = track.lastDecodeTimestamp === -1;
  const timestampNonZero = decodeTimestamp !== 0;
  if (strictTimestampBehavior && noLastDecodeTimestamp && timestampNonZero) {
    throw new Error(
      `The first chunk for your media track must have a timestamp of 0 (received DTS=${decodeTimestamp}).Non-zero first timestamps are often caused by directly piping frames or audio data from a MediaStreamTrack into the encoder. Their timestamps are typically relative to the age of thedocument, which is probably what you want.

If you want to offset all timestamps of a track such that the first one is zero, set firstTimestampBehavior: 'offset' in the options.
`
    );
  } else if (__privateGet(this, _options).firstTimestampBehavior === "offset" || __privateGet(this, _options).firstTimestampBehavior === "cross-track-offset") {
    if (track.firstDecodeTimestamp === void 0) {
      track.firstDecodeTimestamp = decodeTimestamp;
    }
    let baseDecodeTimestamp;
    if (__privateGet(this, _options).firstTimestampBehavior === "offset") {
      baseDecodeTimestamp = track.firstDecodeTimestamp;
    } else {
      baseDecodeTimestamp = Math.min(
        __privateGet(this, _videoTrack)?.firstDecodeTimestamp ?? Infinity,
        __privateGet(this, _audioTrack)?.firstDecodeTimestamp ?? Infinity
      );
    }
    decodeTimestamp -= baseDecodeTimestamp;
    presentationTimestamp -= baseDecodeTimestamp;
  }
  if (decodeTimestamp < track.lastDecodeTimestamp) {
    throw new Error(
      `Timestamps must be monotonically increasing (DTS went from ${track.lastDecodeTimestamp * 1e6} to ${decodeTimestamp * 1e6}).`
    );
  }
  track.lastDecodeTimestamp = decodeTimestamp;
  return { presentationTimestamp, decodeTimestamp };
};
_finalizeCurrentChunk = new WeakSet();
finalizeCurrentChunk_fn = function(track) {
  if (__privateGet(this, _options).fastStart === "fragmented") {
    throw new Error("Can't finalize individual chunks if 'fastStart' is set to 'fragmented'.");
  }
  if (!track.currentChunk)
    return;
  track.finalizedChunks.push(track.currentChunk);
  __privateGet(this, _finalizedChunks).push(track.currentChunk);
  if (track.compactlyCodedChunkTable.length === 0 || last(track.compactlyCodedChunkTable).samplesPerChunk !== track.currentChunk.samples.length) {
    track.compactlyCodedChunkTable.push({
      firstChunk: track.finalizedChunks.length,
      // 1-indexed
      samplesPerChunk: track.currentChunk.samples.length
    });
  }
  if (__privateGet(this, _options).fastStart === "in-memory") {
    track.currentChunk.offset = 0;
    return;
  }
  track.currentChunk.offset = __privateGet(this, _writer).pos;
  for (let sample of track.currentChunk.samples) {
    __privateGet(this, _writer).write(sample.data);
    sample.data = null;
  }
  __privateMethod(this, _maybeFlushStreamingTargetWriter, maybeFlushStreamingTargetWriter_fn).call(this);
};
_finalizeFragment = new WeakSet();
finalizeFragment_fn = function(flushStreamingWriter = true) {
  if (__privateGet(this, _options).fastStart !== "fragmented") {
    throw new Error("Can't finalize a fragment unless 'fastStart' is set to 'fragmented'.");
  }
  let tracks = [__privateGet(this, _videoTrack), __privateGet(this, _audioTrack)].filter((track) => track && track.currentChunk);
  if (tracks.length === 0)
    return;
  let fragmentNumber = __privateWrapper(this, _nextFragmentNumber)._++;
  if (fragmentNumber === 1) {
    let movieBox = moov(tracks, __privateGet(this, _creationTime), true);
    __privateGet(this, _writer).writeBox(movieBox);
  }
  let moofOffset = __privateGet(this, _writer).pos;
  let moofBox = moof(fragmentNumber, tracks);
  __privateGet(this, _writer).writeBox(moofBox);
  {
    let mdatBox = mdat(false);
    let totalTrackSampleSize = 0;
    for (let track of tracks) {
      for (let sample of track.currentChunk.samples) {
        totalTrackSampleSize += sample.size;
      }
    }
    let mdatSize = __privateGet(this, _writer).measureBox(mdatBox) + totalTrackSampleSize;
    if (mdatSize >= 2 ** 32) {
      mdatBox.largeSize = true;
      mdatSize = __privateGet(this, _writer).measureBox(mdatBox) + totalTrackSampleSize;
    }
    mdatBox.size = mdatSize;
    __privateGet(this, _writer).writeBox(mdatBox);
  }
  for (let track of tracks) {
    track.currentChunk.offset = __privateGet(this, _writer).pos;
    track.currentChunk.moofOffset = moofOffset;
    for (let sample of track.currentChunk.samples) {
      __privateGet(this, _writer).write(sample.data);
      sample.data = null;
    }
  }
  let endPos = __privateGet(this, _writer).pos;
  __privateGet(this, _writer).seek(__privateGet(this, _writer).offsets.get(moofBox));
  let newMoofBox = moof(fragmentNumber, tracks);
  __privateGet(this, _writer).writeBox(newMoofBox);
  __privateGet(this, _writer).seek(endPos);
  for (let track of tracks) {
    track.finalizedChunks.push(track.currentChunk);
    __privateGet(this, _finalizedChunks).push(track.currentChunk);
    track.currentChunk = null;
  }
  if (flushStreamingWriter) {
    __privateMethod(this, _maybeFlushStreamingTargetWriter, maybeFlushStreamingTargetWriter_fn).call(this);
  }
};
_maybeFlushStreamingTargetWriter = new WeakSet();
maybeFlushStreamingTargetWriter_fn = function() {
  if (__privateGet(this, _writer) instanceof StreamTargetWriter) {
    __privateGet(this, _writer).flush();
  }
};
_ensureNotFinalized = new WeakSet();
ensureNotFinalized_fn = function() {
  if (__privateGet(this, _finalized)) {
    throw new Error("Cannot add new video or audio chunks after the file has been finalized.");
  }
};

var commonjsGlobal = typeof globalThis !== 'undefined' ? globalThis : typeof window !== 'undefined' ? window : typeof global !== 'undefined' ? global : typeof self !== 'undefined' ? self : {};

function getDefaultExportFromCjs (x) {
	return x && x.__esModule && Object.prototype.hasOwnProperty.call(x, 'default') ? x['default'] : x;
}

function commonjsRequire(path) {
	throw new Error('Could not dynamically require "' + path + '". Please configure the dynamicRequireTargets or/and ignoreDynamicRequires option of @rollup/plugin-commonjs appropriately for this require call to work.');
}

var jszip_min$1 = {exports: {}};

(function (module, exports$1) {
	var define_process_default = { env: {} };
	/*!

	JSZip v3.10.1 - A JavaScript class for generating and reading zip files
	<http://stuartk.com/jszip>

	(c) 2009-2016 Stuart Knightley <stuart [at] stuartk.com>
	Dual licenced under the MIT license or GPLv3. See https://raw.github.com/Stuk/jszip/main/LICENSE.markdown.

	JSZip uses the library pako released under the MIT license :
	https://github.com/nodeca/pako/blob/main/LICENSE
	*/
	!function(e) {
	  module.exports = e();
	}(function() {
	  return function s(a, o, h) {
	    function u(r, e2) {
	      if (!o[r]) {
	        if (!a[r]) {
	          var t = "function" == typeof commonjsRequire && commonjsRequire;
	          if (!e2 && t) return t(r, true);
	          if (l) return l(r, true);
	          var n = new Error("Cannot find module '" + r + "'");
	          throw n.code = "MODULE_NOT_FOUND", n;
	        }
	        var i = o[r] = { exports: {} };
	        a[r][0].call(i.exports, function(e3) {
	          var t2 = a[r][1][e3];
	          return u(t2 || e3);
	        }, i, i.exports, s, a, o, h);
	      }
	      return o[r].exports;
	    }
	    for (var l = "function" == typeof commonjsRequire && commonjsRequire, e = 0; e < h.length; e++) u(h[e]);
	    return u;
	  }({ 1: [function(e, t, r) {
	    var d = e("./utils"), c = e("./support"), p = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=";
	    r.encode = function(e2) {
	      for (var t2, r2, n, i, s, a, o, h = [], u = 0, l = e2.length, f = l, c2 = "string" !== d.getTypeOf(e2); u < e2.length; ) f = l - u, n = c2 ? (t2 = e2[u++], r2 = u < l ? e2[u++] : 0, u < l ? e2[u++] : 0) : (t2 = e2.charCodeAt(u++), r2 = u < l ? e2.charCodeAt(u++) : 0, u < l ? e2.charCodeAt(u++) : 0), i = t2 >> 2, s = (3 & t2) << 4 | r2 >> 4, a = 1 < f ? (15 & r2) << 2 | n >> 6 : 64, o = 2 < f ? 63 & n : 64, h.push(p.charAt(i) + p.charAt(s) + p.charAt(a) + p.charAt(o));
	      return h.join("");
	    }, r.decode = function(e2) {
	      var t2, r2, n, i, s, a, o = 0, h = 0, u = "data:";
	      if (e2.substr(0, u.length) === u) throw new Error("Invalid base64 input, it looks like a data url.");
	      var l, f = 3 * (e2 = e2.replace(/[^A-Za-z0-9+/=]/g, "")).length / 4;
	      if (e2.charAt(e2.length - 1) === p.charAt(64) && f--, e2.charAt(e2.length - 2) === p.charAt(64) && f--, f % 1 != 0) throw new Error("Invalid base64 input, bad content length.");
	      for (l = c.uint8array ? new Uint8Array(0 | f) : new Array(0 | f); o < e2.length; ) t2 = p.indexOf(e2.charAt(o++)) << 2 | (i = p.indexOf(e2.charAt(o++))) >> 4, r2 = (15 & i) << 4 | (s = p.indexOf(e2.charAt(o++))) >> 2, n = (3 & s) << 6 | (a = p.indexOf(e2.charAt(o++))), l[h++] = t2, 64 !== s && (l[h++] = r2), 64 !== a && (l[h++] = n);
	      return l;
	    };
	  }, { "./support": 30, "./utils": 32 }], 2: [function(e, t, r) {
	    var n = e("./external"), i = e("./stream/DataWorker"), s = e("./stream/Crc32Probe"), a = e("./stream/DataLengthProbe");
	    function o(e2, t2, r2, n2, i2) {
	      this.compressedSize = e2, this.uncompressedSize = t2, this.crc32 = r2, this.compression = n2, this.compressedContent = i2;
	    }
	    o.prototype = { getContentWorker: function() {
	      var e2 = new i(n.Promise.resolve(this.compressedContent)).pipe(this.compression.uncompressWorker()).pipe(new a("data_length")), t2 = this;
	      return e2.on("end", function() {
	        if (this.streamInfo.data_length !== t2.uncompressedSize) throw new Error("Bug : uncompressed data size mismatch");
	      }), e2;
	    }, getCompressedWorker: function() {
	      return new i(n.Promise.resolve(this.compressedContent)).withStreamInfo("compressedSize", this.compressedSize).withStreamInfo("uncompressedSize", this.uncompressedSize).withStreamInfo("crc32", this.crc32).withStreamInfo("compression", this.compression);
	    } }, o.createWorkerFrom = function(e2, t2, r2) {
	      return e2.pipe(new s()).pipe(new a("uncompressedSize")).pipe(t2.compressWorker(r2)).pipe(new a("compressedSize")).withStreamInfo("compression", t2);
	    }, t.exports = o;
	  }, { "./external": 6, "./stream/Crc32Probe": 25, "./stream/DataLengthProbe": 26, "./stream/DataWorker": 27 }], 3: [function(e, t, r) {
	    var n = e("./stream/GenericWorker");
	    r.STORE = { magic: "\0\0", compressWorker: function() {
	      return new n("STORE compression");
	    }, uncompressWorker: function() {
	      return new n("STORE decompression");
	    } }, r.DEFLATE = e("./flate");
	  }, { "./flate": 7, "./stream/GenericWorker": 28 }], 4: [function(e, t, r) {
	    var n = e("./utils");
	    var o = function() {
	      for (var e2, t2 = [], r2 = 0; r2 < 256; r2++) {
	        e2 = r2;
	        for (var n2 = 0; n2 < 8; n2++) e2 = 1 & e2 ? 3988292384 ^ e2 >>> 1 : e2 >>> 1;
	        t2[r2] = e2;
	      }
	      return t2;
	    }();
	    t.exports = function(e2, t2) {
	      return void 0 !== e2 && e2.length ? "string" !== n.getTypeOf(e2) ? function(e3, t3, r2, n2) {
	        var i = o, s = n2 + r2;
	        e3 ^= -1;
	        for (var a = n2; a < s; a++) e3 = e3 >>> 8 ^ i[255 & (e3 ^ t3[a])];
	        return -1 ^ e3;
	      }(0 | t2, e2, e2.length, 0) : function(e3, t3, r2, n2) {
	        var i = o, s = n2 + r2;
	        e3 ^= -1;
	        for (var a = n2; a < s; a++) e3 = e3 >>> 8 ^ i[255 & (e3 ^ t3.charCodeAt(a))];
	        return -1 ^ e3;
	      }(0 | t2, e2, e2.length, 0) : 0;
	    };
	  }, { "./utils": 32 }], 5: [function(e, t, r) {
	    r.base64 = false, r.binary = false, r.dir = false, r.createFolders = true, r.date = null, r.compression = null, r.compressionOptions = null, r.comment = null, r.unixPermissions = null, r.dosPermissions = null;
	  }, {}], 6: [function(e, t, r) {
	    var n = null;
	    n = "undefined" != typeof Promise ? Promise : e("lie"), t.exports = { Promise: n };
	  }, { lie: 37 }], 7: [function(e, t, r) {
	    var n = "undefined" != typeof Uint8Array && "undefined" != typeof Uint16Array && "undefined" != typeof Uint32Array, i = e("pako"), s = e("./utils"), a = e("./stream/GenericWorker"), o = n ? "uint8array" : "array";
	    function h(e2, t2) {
	      a.call(this, "FlateWorker/" + e2), this._pako = null, this._pakoAction = e2, this._pakoOptions = t2, this.meta = {};
	    }
	    r.magic = "\b\0", s.inherits(h, a), h.prototype.processChunk = function(e2) {
	      this.meta = e2.meta, null === this._pako && this._createPako(), this._pako.push(s.transformTo(o, e2.data), false);
	    }, h.prototype.flush = function() {
	      a.prototype.flush.call(this), null === this._pako && this._createPako(), this._pako.push([], true);
	    }, h.prototype.cleanUp = function() {
	      a.prototype.cleanUp.call(this), this._pako = null;
	    }, h.prototype._createPako = function() {
	      this._pako = new i[this._pakoAction]({ raw: true, level: this._pakoOptions.level || -1 });
	      var t2 = this;
	      this._pako.onData = function(e2) {
	        t2.push({ data: e2, meta: t2.meta });
	      };
	    }, r.compressWorker = function(e2) {
	      return new h("Deflate", e2);
	    }, r.uncompressWorker = function() {
	      return new h("Inflate", {});
	    };
	  }, { "./stream/GenericWorker": 28, "./utils": 32, pako: 38 }], 8: [function(e, t, r) {
	    function A(e2, t2) {
	      var r2, n2 = "";
	      for (r2 = 0; r2 < t2; r2++) n2 += String.fromCharCode(255 & e2), e2 >>>= 8;
	      return n2;
	    }
	    function n(e2, t2, r2, n2, i2, s2) {
	      var a, o, h = e2.file, u = e2.compression, l = s2 !== O.utf8encode, f = I.transformTo("string", s2(h.name)), c = I.transformTo("string", O.utf8encode(h.name)), d = h.comment, p = I.transformTo("string", s2(d)), m = I.transformTo("string", O.utf8encode(d)), _ = c.length !== h.name.length, g = m.length !== d.length, b = "", v = "", y = "", w = h.dir, k = h.date, x = { crc32: 0, compressedSize: 0, uncompressedSize: 0 };
	      t2 && !r2 || (x.crc32 = e2.crc32, x.compressedSize = e2.compressedSize, x.uncompressedSize = e2.uncompressedSize);
	      var S = 0;
	      t2 && (S |= 8), l || !_ && !g || (S |= 2048);
	      var z = 0, C = 0;
	      w && (z |= 16), "UNIX" === i2 ? (C = 798, z |= function(e3, t3) {
	        var r3 = e3;
	        return e3 || (r3 = t3 ? 16893 : 33204), (65535 & r3) << 16;
	      }(h.unixPermissions, w)) : (C = 20, z |= function(e3) {
	        return 63 & (e3 || 0);
	      }(h.dosPermissions)), a = k.getUTCHours(), a <<= 6, a |= k.getUTCMinutes(), a <<= 5, a |= k.getUTCSeconds() / 2, o = k.getUTCFullYear() - 1980, o <<= 4, o |= k.getUTCMonth() + 1, o <<= 5, o |= k.getUTCDate(), _ && (v = A(1, 1) + A(B(f), 4) + c, b += "up" + A(v.length, 2) + v), g && (y = A(1, 1) + A(B(p), 4) + m, b += "uc" + A(y.length, 2) + y);
	      var E = "";
	      return E += "\n\0", E += A(S, 2), E += u.magic, E += A(a, 2), E += A(o, 2), E += A(x.crc32, 4), E += A(x.compressedSize, 4), E += A(x.uncompressedSize, 4), E += A(f.length, 2), E += A(b.length, 2), { fileRecord: R.LOCAL_FILE_HEADER + E + f + b, dirRecord: R.CENTRAL_FILE_HEADER + A(C, 2) + E + A(p.length, 2) + "\0\0\0\0" + A(z, 4) + A(n2, 4) + f + b + p };
	    }
	    var I = e("../utils"), i = e("../stream/GenericWorker"), O = e("../utf8"), B = e("../crc32"), R = e("../signature");
	    function s(e2, t2, r2, n2) {
	      i.call(this, "ZipFileWorker"), this.bytesWritten = 0, this.zipComment = t2, this.zipPlatform = r2, this.encodeFileName = n2, this.streamFiles = e2, this.accumulate = false, this.contentBuffer = [], this.dirRecords = [], this.currentSourceOffset = 0, this.entriesCount = 0, this.currentFile = null, this._sources = [];
	    }
	    I.inherits(s, i), s.prototype.push = function(e2) {
	      var t2 = e2.meta.percent || 0, r2 = this.entriesCount, n2 = this._sources.length;
	      this.accumulate ? this.contentBuffer.push(e2) : (this.bytesWritten += e2.data.length, i.prototype.push.call(this, { data: e2.data, meta: { currentFile: this.currentFile, percent: r2 ? (t2 + 100 * (r2 - n2 - 1)) / r2 : 100 } }));
	    }, s.prototype.openedSource = function(e2) {
	      this.currentSourceOffset = this.bytesWritten, this.currentFile = e2.file.name;
	      var t2 = this.streamFiles && !e2.file.dir;
	      if (t2) {
	        var r2 = n(e2, t2, false, this.currentSourceOffset, this.zipPlatform, this.encodeFileName);
	        this.push({ data: r2.fileRecord, meta: { percent: 0 } });
	      } else this.accumulate = true;
	    }, s.prototype.closedSource = function(e2) {
	      this.accumulate = false;
	      var t2 = this.streamFiles && !e2.file.dir, r2 = n(e2, t2, true, this.currentSourceOffset, this.zipPlatform, this.encodeFileName);
	      if (this.dirRecords.push(r2.dirRecord), t2) this.push({ data: function(e3) {
	        return R.DATA_DESCRIPTOR + A(e3.crc32, 4) + A(e3.compressedSize, 4) + A(e3.uncompressedSize, 4);
	      }(e2), meta: { percent: 100 } });
	      else for (this.push({ data: r2.fileRecord, meta: { percent: 0 } }); this.contentBuffer.length; ) this.push(this.contentBuffer.shift());
	      this.currentFile = null;
	    }, s.prototype.flush = function() {
	      for (var e2 = this.bytesWritten, t2 = 0; t2 < this.dirRecords.length; t2++) this.push({ data: this.dirRecords[t2], meta: { percent: 100 } });
	      var r2 = this.bytesWritten - e2, n2 = function(e3, t3, r3, n3, i2) {
	        var s2 = I.transformTo("string", i2(n3));
	        return R.CENTRAL_DIRECTORY_END + "\0\0\0\0" + A(e3, 2) + A(e3, 2) + A(t3, 4) + A(r3, 4) + A(s2.length, 2) + s2;
	      }(this.dirRecords.length, r2, e2, this.zipComment, this.encodeFileName);
	      this.push({ data: n2, meta: { percent: 100 } });
	    }, s.prototype.prepareNextSource = function() {
	      this.previous = this._sources.shift(), this.openedSource(this.previous.streamInfo), this.isPaused ? this.previous.pause() : this.previous.resume();
	    }, s.prototype.registerPrevious = function(e2) {
	      this._sources.push(e2);
	      var t2 = this;
	      return e2.on("data", function(e3) {
	        t2.processChunk(e3);
	      }), e2.on("end", function() {
	        t2.closedSource(t2.previous.streamInfo), t2._sources.length ? t2.prepareNextSource() : t2.end();
	      }), e2.on("error", function(e3) {
	        t2.error(e3);
	      }), this;
	    }, s.prototype.resume = function() {
	      return !!i.prototype.resume.call(this) && (!this.previous && this._sources.length ? (this.prepareNextSource(), true) : this.previous || this._sources.length || this.generatedError ? void 0 : (this.end(), true));
	    }, s.prototype.error = function(e2) {
	      var t2 = this._sources;
	      if (!i.prototype.error.call(this, e2)) return false;
	      for (var r2 = 0; r2 < t2.length; r2++) try {
	        t2[r2].error(e2);
	      } catch (e3) {
	      }
	      return true;
	    }, s.prototype.lock = function() {
	      i.prototype.lock.call(this);
	      for (var e2 = this._sources, t2 = 0; t2 < e2.length; t2++) e2[t2].lock();
	    }, t.exports = s;
	  }, { "../crc32": 4, "../signature": 23, "../stream/GenericWorker": 28, "../utf8": 31, "../utils": 32 }], 9: [function(e, t, r) {
	    var u = e("../compressions"), n = e("./ZipFileWorker");
	    r.generateWorker = function(e2, a, t2) {
	      var o = new n(a.streamFiles, t2, a.platform, a.encodeFileName), h = 0;
	      try {
	        e2.forEach(function(e3, t3) {
	          h++;
	          var r2 = function(e4, t4) {
	            var r3 = e4 || t4, n3 = u[r3];
	            if (!n3) throw new Error(r3 + " is not a valid compression method !");
	            return n3;
	          }(t3.options.compression, a.compression), n2 = t3.options.compressionOptions || a.compressionOptions || {}, i = t3.dir, s = t3.date;
	          t3._compressWorker(r2, n2).withStreamInfo("file", { name: e3, dir: i, date: s, comment: t3.comment || "", unixPermissions: t3.unixPermissions, dosPermissions: t3.dosPermissions }).pipe(o);
	        }), o.entriesCount = h;
	      } catch (e3) {
	        o.error(e3);
	      }
	      return o;
	    };
	  }, { "../compressions": 3, "./ZipFileWorker": 8 }], 10: [function(e, t, r) {
	    function n() {
	      if (!(this instanceof n)) return new n();
	      if (arguments.length) throw new Error("The constructor with parameters has been removed in JSZip 3.0, please check the upgrade guide.");
	      this.files = /* @__PURE__ */ Object.create(null), this.comment = null, this.root = "", this.clone = function() {
	        var e2 = new n();
	        for (var t2 in this) "function" != typeof this[t2] && (e2[t2] = this[t2]);
	        return e2;
	      };
	    }
	    (n.prototype = e("./object")).loadAsync = e("./load"), n.support = e("./support"), n.defaults = e("./defaults"), n.version = "3.10.1", n.loadAsync = function(e2, t2) {
	      return new n().loadAsync(e2, t2);
	    }, n.external = e("./external"), t.exports = n;
	  }, { "./defaults": 5, "./external": 6, "./load": 11, "./object": 15, "./support": 30 }], 11: [function(e, t, r) {
	    var u = e("./utils"), i = e("./external"), n = e("./utf8"), s = e("./zipEntries"), a = e("./stream/Crc32Probe"), l = e("./nodejsUtils");
	    function f(n2) {
	      return new i.Promise(function(e2, t2) {
	        var r2 = n2.decompressed.getContentWorker().pipe(new a());
	        r2.on("error", function(e3) {
	          t2(e3);
	        }).on("end", function() {
	          r2.streamInfo.crc32 !== n2.decompressed.crc32 ? t2(new Error("Corrupted zip : CRC32 mismatch")) : e2();
	        }).resume();
	      });
	    }
	    t.exports = function(e2, o) {
	      var h = this;
	      return o = u.extend(o || {}, { base64: false, checkCRC32: false, optimizedBinaryString: false, createFolders: false, decodeFileName: n.utf8decode }), l.isNode && l.isStream(e2) ? i.Promise.reject(new Error("JSZip can't accept a stream when loading a zip file.")) : u.prepareContent("the loaded zip file", e2, true, o.optimizedBinaryString, o.base64).then(function(e3) {
	        var t2 = new s(o);
	        return t2.load(e3), t2;
	      }).then(function(e3) {
	        var t2 = [i.Promise.resolve(e3)], r2 = e3.files;
	        if (o.checkCRC32) for (var n2 = 0; n2 < r2.length; n2++) t2.push(f(r2[n2]));
	        return i.Promise.all(t2);
	      }).then(function(e3) {
	        for (var t2 = e3.shift(), r2 = t2.files, n2 = 0; n2 < r2.length; n2++) {
	          var i2 = r2[n2], s2 = i2.fileNameStr, a2 = u.resolve(i2.fileNameStr);
	          h.file(a2, i2.decompressed, { binary: true, optimizedBinaryString: true, date: i2.date, dir: i2.dir, comment: i2.fileCommentStr.length ? i2.fileCommentStr : null, unixPermissions: i2.unixPermissions, dosPermissions: i2.dosPermissions, createFolders: o.createFolders }), i2.dir || (h.file(a2).unsafeOriginalName = s2);
	        }
	        return t2.zipComment.length && (h.comment = t2.zipComment), h;
	      });
	    };
	  }, { "./external": 6, "./nodejsUtils": 14, "./stream/Crc32Probe": 25, "./utf8": 31, "./utils": 32, "./zipEntries": 33 }], 12: [function(e, t, r) {
	    var n = e("../utils"), i = e("../stream/GenericWorker");
	    function s(e2, t2) {
	      i.call(this, "Nodejs stream input adapter for " + e2), this._upstreamEnded = false, this._bindStream(t2);
	    }
	    n.inherits(s, i), s.prototype._bindStream = function(e2) {
	      var t2 = this;
	      (this._stream = e2).pause(), e2.on("data", function(e3) {
	        t2.push({ data: e3, meta: { percent: 0 } });
	      }).on("error", function(e3) {
	        t2.isPaused ? this.generatedError = e3 : t2.error(e3);
	      }).on("end", function() {
	        t2.isPaused ? t2._upstreamEnded = true : t2.end();
	      });
	    }, s.prototype.pause = function() {
	      return !!i.prototype.pause.call(this) && (this._stream.pause(), true);
	    }, s.prototype.resume = function() {
	      return !!i.prototype.resume.call(this) && (this._upstreamEnded ? this.end() : this._stream.resume(), true);
	    }, t.exports = s;
	  }, { "../stream/GenericWorker": 28, "../utils": 32 }], 13: [function(e, t, r) {
	    var i = e("readable-stream").Readable;
	    function n(e2, t2, r2) {
	      i.call(this, t2), this._helper = e2;
	      var n2 = this;
	      e2.on("data", function(e3, t3) {
	        n2.push(e3) || n2._helper.pause(), r2 && r2(t3);
	      }).on("error", function(e3) {
	        n2.emit("error", e3);
	      }).on("end", function() {
	        n2.push(null);
	      });
	    }
	    e("../utils").inherits(n, i), n.prototype._read = function() {
	      this._helper.resume();
	    }, t.exports = n;
	  }, { "../utils": 32, "readable-stream": 16 }], 14: [function(e, t, r) {
	    t.exports = { isNode: "undefined" != typeof Buffer, newBufferFrom: function(e2, t2) {
	      if (Buffer.from && Buffer.from !== Uint8Array.from) return Buffer.from(e2, t2);
	      if ("number" == typeof e2) throw new Error('The "data" argument must not be a number');
	      return new Buffer(e2, t2);
	    }, allocBuffer: function(e2) {
	      if (Buffer.alloc) return Buffer.alloc(e2);
	      var t2 = new Buffer(e2);
	      return t2.fill(0), t2;
	    }, isBuffer: function(e2) {
	      return Buffer.isBuffer(e2);
	    }, isStream: function(e2) {
	      return e2 && "function" == typeof e2.on && "function" == typeof e2.pause && "function" == typeof e2.resume;
	    } };
	  }, {}], 15: [function(e, t, r) {
	    function s(e2, t2, r2) {
	      var n2, i2 = u.getTypeOf(t2), s2 = u.extend(r2 || {}, f);
	      s2.date = s2.date || /* @__PURE__ */ new Date(), null !== s2.compression && (s2.compression = s2.compression.toUpperCase()), "string" == typeof s2.unixPermissions && (s2.unixPermissions = parseInt(s2.unixPermissions, 8)), s2.unixPermissions && 16384 & s2.unixPermissions && (s2.dir = true), s2.dosPermissions && 16 & s2.dosPermissions && (s2.dir = true), s2.dir && (e2 = g(e2)), s2.createFolders && (n2 = _(e2)) && b.call(this, n2, true);
	      var a2 = "string" === i2 && false === s2.binary && false === s2.base64;
	      r2 && void 0 !== r2.binary || (s2.binary = !a2), (t2 instanceof c && 0 === t2.uncompressedSize || s2.dir || !t2 || 0 === t2.length) && (s2.base64 = false, s2.binary = true, t2 = "", s2.compression = "STORE", i2 = "string");
	      var o2 = null;
	      o2 = t2 instanceof c || t2 instanceof l ? t2 : p.isNode && p.isStream(t2) ? new m(e2, t2) : u.prepareContent(e2, t2, s2.binary, s2.optimizedBinaryString, s2.base64);
	      var h2 = new d(e2, o2, s2);
	      this.files[e2] = h2;
	    }
	    var i = e("./utf8"), u = e("./utils"), l = e("./stream/GenericWorker"), a = e("./stream/StreamHelper"), f = e("./defaults"), c = e("./compressedObject"), d = e("./zipObject"), o = e("./generate"), p = e("./nodejsUtils"), m = e("./nodejs/NodejsStreamInputAdapter"), _ = function(e2) {
	      "/" === e2.slice(-1) && (e2 = e2.substring(0, e2.length - 1));
	      var t2 = e2.lastIndexOf("/");
	      return 0 < t2 ? e2.substring(0, t2) : "";
	    }, g = function(e2) {
	      return "/" !== e2.slice(-1) && (e2 += "/"), e2;
	    }, b = function(e2, t2) {
	      return t2 = void 0 !== t2 ? t2 : f.createFolders, e2 = g(e2), this.files[e2] || s.call(this, e2, null, { dir: true, createFolders: t2 }), this.files[e2];
	    };
	    function h(e2) {
	      return "[object RegExp]" === Object.prototype.toString.call(e2);
	    }
	    var n = { load: function() {
	      throw new Error("This method has been removed in JSZip 3.0, please check the upgrade guide.");
	    }, forEach: function(e2) {
	      var t2, r2, n2;
	      for (t2 in this.files) n2 = this.files[t2], (r2 = t2.slice(this.root.length, t2.length)) && t2.slice(0, this.root.length) === this.root && e2(r2, n2);
	    }, filter: function(r2) {
	      var n2 = [];
	      return this.forEach(function(e2, t2) {
	        r2(e2, t2) && n2.push(t2);
	      }), n2;
	    }, file: function(e2, t2, r2) {
	      if (1 !== arguments.length) return e2 = this.root + e2, s.call(this, e2, t2, r2), this;
	      if (h(e2)) {
	        var n2 = e2;
	        return this.filter(function(e3, t3) {
	          return !t3.dir && n2.test(e3);
	        });
	      }
	      var i2 = this.files[this.root + e2];
	      return i2 && !i2.dir ? i2 : null;
	    }, folder: function(r2) {
	      if (!r2) return this;
	      if (h(r2)) return this.filter(function(e3, t3) {
	        return t3.dir && r2.test(e3);
	      });
	      var e2 = this.root + r2, t2 = b.call(this, e2), n2 = this.clone();
	      return n2.root = t2.name, n2;
	    }, remove: function(r2) {
	      r2 = this.root + r2;
	      var e2 = this.files[r2];
	      if (e2 || ("/" !== r2.slice(-1) && (r2 += "/"), e2 = this.files[r2]), e2 && !e2.dir) delete this.files[r2];
	      else for (var t2 = this.filter(function(e3, t3) {
	        return t3.name.slice(0, r2.length) === r2;
	      }), n2 = 0; n2 < t2.length; n2++) delete this.files[t2[n2].name];
	      return this;
	    }, generate: function() {
	      throw new Error("This method has been removed in JSZip 3.0, please check the upgrade guide.");
	    }, generateInternalStream: function(e2) {
	      var t2, r2 = {};
	      try {
	        if ((r2 = u.extend(e2 || {}, { streamFiles: false, compression: "STORE", compressionOptions: null, type: "", platform: "DOS", comment: null, mimeType: "application/zip", encodeFileName: i.utf8encode })).type = r2.type.toLowerCase(), r2.compression = r2.compression.toUpperCase(), "binarystring" === r2.type && (r2.type = "string"), !r2.type) throw new Error("No output type specified.");
	        u.checkSupport(r2.type), "darwin" !== r2.platform && "freebsd" !== r2.platform && "linux" !== r2.platform && "sunos" !== r2.platform || (r2.platform = "UNIX"), "win32" === r2.platform && (r2.platform = "DOS");
	        var n2 = r2.comment || this.comment || "";
	        t2 = o.generateWorker(this, r2, n2);
	      } catch (e3) {
	        (t2 = new l("error")).error(e3);
	      }
	      return new a(t2, r2.type || "string", r2.mimeType);
	    }, generateAsync: function(e2, t2) {
	      return this.generateInternalStream(e2).accumulate(t2);
	    }, generateNodeStream: function(e2, t2) {
	      return (e2 = e2 || {}).type || (e2.type = "nodebuffer"), this.generateInternalStream(e2).toNodejsStream(t2);
	    } };
	    t.exports = n;
	  }, { "./compressedObject": 2, "./defaults": 5, "./generate": 9, "./nodejs/NodejsStreamInputAdapter": 12, "./nodejsUtils": 14, "./stream/GenericWorker": 28, "./stream/StreamHelper": 29, "./utf8": 31, "./utils": 32, "./zipObject": 35 }], 16: [function(e, t, r) {
	    t.exports = e("stream");
	  }, { stream: void 0 }], 17: [function(e, t, r) {
	    var n = e("./DataReader");
	    function i(e2) {
	      n.call(this, e2);
	      for (var t2 = 0; t2 < this.data.length; t2++) e2[t2] = 255 & e2[t2];
	    }
	    e("../utils").inherits(i, n), i.prototype.byteAt = function(e2) {
	      return this.data[this.zero + e2];
	    }, i.prototype.lastIndexOfSignature = function(e2) {
	      for (var t2 = e2.charCodeAt(0), r2 = e2.charCodeAt(1), n2 = e2.charCodeAt(2), i2 = e2.charCodeAt(3), s = this.length - 4; 0 <= s; --s) if (this.data[s] === t2 && this.data[s + 1] === r2 && this.data[s + 2] === n2 && this.data[s + 3] === i2) return s - this.zero;
	      return -1;
	    }, i.prototype.readAndCheckSignature = function(e2) {
	      var t2 = e2.charCodeAt(0), r2 = e2.charCodeAt(1), n2 = e2.charCodeAt(2), i2 = e2.charCodeAt(3), s = this.readData(4);
	      return t2 === s[0] && r2 === s[1] && n2 === s[2] && i2 === s[3];
	    }, i.prototype.readData = function(e2) {
	      if (this.checkOffset(e2), 0 === e2) return [];
	      var t2 = this.data.slice(this.zero + this.index, this.zero + this.index + e2);
	      return this.index += e2, t2;
	    }, t.exports = i;
	  }, { "../utils": 32, "./DataReader": 18 }], 18: [function(e, t, r) {
	    var n = e("../utils");
	    function i(e2) {
	      this.data = e2, this.length = e2.length, this.index = 0, this.zero = 0;
	    }
	    i.prototype = { checkOffset: function(e2) {
	      this.checkIndex(this.index + e2);
	    }, checkIndex: function(e2) {
	      if (this.length < this.zero + e2 || e2 < 0) throw new Error("End of data reached (data length = " + this.length + ", asked index = " + e2 + "). Corrupted zip ?");
	    }, setIndex: function(e2) {
	      this.checkIndex(e2), this.index = e2;
	    }, skip: function(e2) {
	      this.setIndex(this.index + e2);
	    }, byteAt: function() {
	    }, readInt: function(e2) {
	      var t2, r2 = 0;
	      for (this.checkOffset(e2), t2 = this.index + e2 - 1; t2 >= this.index; t2--) r2 = (r2 << 8) + this.byteAt(t2);
	      return this.index += e2, r2;
	    }, readString: function(e2) {
	      return n.transformTo("string", this.readData(e2));
	    }, readData: function() {
	    }, lastIndexOfSignature: function() {
	    }, readAndCheckSignature: function() {
	    }, readDate: function() {
	      var e2 = this.readInt(4);
	      return new Date(Date.UTC(1980 + (e2 >> 25 & 127), (e2 >> 21 & 15) - 1, e2 >> 16 & 31, e2 >> 11 & 31, e2 >> 5 & 63, (31 & e2) << 1));
	    } }, t.exports = i;
	  }, { "../utils": 32 }], 19: [function(e, t, r) {
	    var n = e("./Uint8ArrayReader");
	    function i(e2) {
	      n.call(this, e2);
	    }
	    e("../utils").inherits(i, n), i.prototype.readData = function(e2) {
	      this.checkOffset(e2);
	      var t2 = this.data.slice(this.zero + this.index, this.zero + this.index + e2);
	      return this.index += e2, t2;
	    }, t.exports = i;
	  }, { "../utils": 32, "./Uint8ArrayReader": 21 }], 20: [function(e, t, r) {
	    var n = e("./DataReader");
	    function i(e2) {
	      n.call(this, e2);
	    }
	    e("../utils").inherits(i, n), i.prototype.byteAt = function(e2) {
	      return this.data.charCodeAt(this.zero + e2);
	    }, i.prototype.lastIndexOfSignature = function(e2) {
	      return this.data.lastIndexOf(e2) - this.zero;
	    }, i.prototype.readAndCheckSignature = function(e2) {
	      return e2 === this.readData(4);
	    }, i.prototype.readData = function(e2) {
	      this.checkOffset(e2);
	      var t2 = this.data.slice(this.zero + this.index, this.zero + this.index + e2);
	      return this.index += e2, t2;
	    }, t.exports = i;
	  }, { "../utils": 32, "./DataReader": 18 }], 21: [function(e, t, r) {
	    var n = e("./ArrayReader");
	    function i(e2) {
	      n.call(this, e2);
	    }
	    e("../utils").inherits(i, n), i.prototype.readData = function(e2) {
	      if (this.checkOffset(e2), 0 === e2) return new Uint8Array(0);
	      var t2 = this.data.subarray(this.zero + this.index, this.zero + this.index + e2);
	      return this.index += e2, t2;
	    }, t.exports = i;
	  }, { "../utils": 32, "./ArrayReader": 17 }], 22: [function(e, t, r) {
	    var n = e("../utils"), i = e("../support"), s = e("./ArrayReader"), a = e("./StringReader"), o = e("./NodeBufferReader"), h = e("./Uint8ArrayReader");
	    t.exports = function(e2) {
	      var t2 = n.getTypeOf(e2);
	      return n.checkSupport(t2), "string" !== t2 || i.uint8array ? "nodebuffer" === t2 ? new o(e2) : i.uint8array ? new h(n.transformTo("uint8array", e2)) : new s(n.transformTo("array", e2)) : new a(e2);
	    };
	  }, { "../support": 30, "../utils": 32, "./ArrayReader": 17, "./NodeBufferReader": 19, "./StringReader": 20, "./Uint8ArrayReader": 21 }], 23: [function(e, t, r) {
	    r.LOCAL_FILE_HEADER = "PK", r.CENTRAL_FILE_HEADER = "PK", r.CENTRAL_DIRECTORY_END = "PK", r.ZIP64_CENTRAL_DIRECTORY_LOCATOR = "PK\x07", r.ZIP64_CENTRAL_DIRECTORY_END = "PK", r.DATA_DESCRIPTOR = "PK\x07\b";
	  }, {}], 24: [function(e, t, r) {
	    var n = e("./GenericWorker"), i = e("../utils");
	    function s(e2) {
	      n.call(this, "ConvertWorker to " + e2), this.destType = e2;
	    }
	    i.inherits(s, n), s.prototype.processChunk = function(e2) {
	      this.push({ data: i.transformTo(this.destType, e2.data), meta: e2.meta });
	    }, t.exports = s;
	  }, { "../utils": 32, "./GenericWorker": 28 }], 25: [function(e, t, r) {
	    var n = e("./GenericWorker"), i = e("../crc32");
	    function s() {
	      n.call(this, "Crc32Probe"), this.withStreamInfo("crc32", 0);
	    }
	    e("../utils").inherits(s, n), s.prototype.processChunk = function(e2) {
	      this.streamInfo.crc32 = i(e2.data, this.streamInfo.crc32 || 0), this.push(e2);
	    }, t.exports = s;
	  }, { "../crc32": 4, "../utils": 32, "./GenericWorker": 28 }], 26: [function(e, t, r) {
	    var n = e("../utils"), i = e("./GenericWorker");
	    function s(e2) {
	      i.call(this, "DataLengthProbe for " + e2), this.propName = e2, this.withStreamInfo(e2, 0);
	    }
	    n.inherits(s, i), s.prototype.processChunk = function(e2) {
	      if (e2) {
	        var t2 = this.streamInfo[this.propName] || 0;
	        this.streamInfo[this.propName] = t2 + e2.data.length;
	      }
	      i.prototype.processChunk.call(this, e2);
	    }, t.exports = s;
	  }, { "../utils": 32, "./GenericWorker": 28 }], 27: [function(e, t, r) {
	    var n = e("../utils"), i = e("./GenericWorker");
	    function s(e2) {
	      i.call(this, "DataWorker");
	      var t2 = this;
	      this.dataIsReady = false, this.index = 0, this.max = 0, this.data = null, this.type = "", this._tickScheduled = false, e2.then(function(e3) {
	        t2.dataIsReady = true, t2.data = e3, t2.max = e3 && e3.length || 0, t2.type = n.getTypeOf(e3), t2.isPaused || t2._tickAndRepeat();
	      }, function(e3) {
	        t2.error(e3);
	      });
	    }
	    n.inherits(s, i), s.prototype.cleanUp = function() {
	      i.prototype.cleanUp.call(this), this.data = null;
	    }, s.prototype.resume = function() {
	      return !!i.prototype.resume.call(this) && (!this._tickScheduled && this.dataIsReady && (this._tickScheduled = true, n.delay(this._tickAndRepeat, [], this)), true);
	    }, s.prototype._tickAndRepeat = function() {
	      this._tickScheduled = false, this.isPaused || this.isFinished || (this._tick(), this.isFinished || (n.delay(this._tickAndRepeat, [], this), this._tickScheduled = true));
	    }, s.prototype._tick = function() {
	      if (this.isPaused || this.isFinished) return false;
	      var e2 = null, t2 = Math.min(this.max, this.index + 16384);
	      if (this.index >= this.max) return this.end();
	      switch (this.type) {
	        case "string":
	          e2 = this.data.substring(this.index, t2);
	          break;
	        case "uint8array":
	          e2 = this.data.subarray(this.index, t2);
	          break;
	        case "array":
	        case "nodebuffer":
	          e2 = this.data.slice(this.index, t2);
	      }
	      return this.index = t2, this.push({ data: e2, meta: { percent: this.max ? this.index / this.max * 100 : 0 } });
	    }, t.exports = s;
	  }, { "../utils": 32, "./GenericWorker": 28 }], 28: [function(e, t, r) {
	    function n(e2) {
	      this.name = e2 || "default", this.streamInfo = {}, this.generatedError = null, this.extraStreamInfo = {}, this.isPaused = true, this.isFinished = false, this.isLocked = false, this._listeners = { data: [], end: [], error: [] }, this.previous = null;
	    }
	    n.prototype = { push: function(e2) {
	      this.emit("data", e2);
	    }, end: function() {
	      if (this.isFinished) return false;
	      this.flush();
	      try {
	        this.emit("end"), this.cleanUp(), this.isFinished = true;
	      } catch (e2) {
	        this.emit("error", e2);
	      }
	      return true;
	    }, error: function(e2) {
	      return !this.isFinished && (this.isPaused ? this.generatedError = e2 : (this.isFinished = true, this.emit("error", e2), this.previous && this.previous.error(e2), this.cleanUp()), true);
	    }, on: function(e2, t2) {
	      return this._listeners[e2].push(t2), this;
	    }, cleanUp: function() {
	      this.streamInfo = this.generatedError = this.extraStreamInfo = null, this._listeners = [];
	    }, emit: function(e2, t2) {
	      if (this._listeners[e2]) for (var r2 = 0; r2 < this._listeners[e2].length; r2++) this._listeners[e2][r2].call(this, t2);
	    }, pipe: function(e2) {
	      return e2.registerPrevious(this);
	    }, registerPrevious: function(e2) {
	      if (this.isLocked) throw new Error("The stream '" + this + "' has already been used.");
	      this.streamInfo = e2.streamInfo, this.mergeStreamInfo(), this.previous = e2;
	      var t2 = this;
	      return e2.on("data", function(e3) {
	        t2.processChunk(e3);
	      }), e2.on("end", function() {
	        t2.end();
	      }), e2.on("error", function(e3) {
	        t2.error(e3);
	      }), this;
	    }, pause: function() {
	      return !this.isPaused && !this.isFinished && (this.isPaused = true, this.previous && this.previous.pause(), true);
	    }, resume: function() {
	      if (!this.isPaused || this.isFinished) return false;
	      var e2 = this.isPaused = false;
	      return this.generatedError && (this.error(this.generatedError), e2 = true), this.previous && this.previous.resume(), !e2;
	    }, flush: function() {
	    }, processChunk: function(e2) {
	      this.push(e2);
	    }, withStreamInfo: function(e2, t2) {
	      return this.extraStreamInfo[e2] = t2, this.mergeStreamInfo(), this;
	    }, mergeStreamInfo: function() {
	      for (var e2 in this.extraStreamInfo) Object.prototype.hasOwnProperty.call(this.extraStreamInfo, e2) && (this.streamInfo[e2] = this.extraStreamInfo[e2]);
	    }, lock: function() {
	      if (this.isLocked) throw new Error("The stream '" + this + "' has already been used.");
	      this.isLocked = true, this.previous && this.previous.lock();
	    }, toString: function() {
	      var e2 = "Worker " + this.name;
	      return this.previous ? this.previous + " -> " + e2 : e2;
	    } }, t.exports = n;
	  }, {}], 29: [function(e, t, r) {
	    var h = e("../utils"), i = e("./ConvertWorker"), s = e("./GenericWorker"), u = e("../base64"), n = e("../support"), a = e("../external"), o = null;
	    if (n.nodestream) try {
	      o = e("../nodejs/NodejsStreamOutputAdapter");
	    } catch (e2) {
	    }
	    function l(e2, o2) {
	      return new a.Promise(function(t2, r2) {
	        var n2 = [], i2 = e2._internalType, s2 = e2._outputType, a2 = e2._mimeType;
	        e2.on("data", function(e3, t3) {
	          n2.push(e3), o2 && o2(t3);
	        }).on("error", function(e3) {
	          n2 = [], r2(e3);
	        }).on("end", function() {
	          try {
	            var e3 = function(e4, t3, r3) {
	              switch (e4) {
	                case "blob":
	                  return h.newBlob(h.transformTo("arraybuffer", t3), r3);
	                case "base64":
	                  return u.encode(t3);
	                default:
	                  return h.transformTo(e4, t3);
	              }
	            }(s2, function(e4, t3) {
	              var r3, n3 = 0, i3 = null, s3 = 0;
	              for (r3 = 0; r3 < t3.length; r3++) s3 += t3[r3].length;
	              switch (e4) {
	                case "string":
	                  return t3.join("");
	                case "array":
	                  return Array.prototype.concat.apply([], t3);
	                case "uint8array":
	                  for (i3 = new Uint8Array(s3), r3 = 0; r3 < t3.length; r3++) i3.set(t3[r3], n3), n3 += t3[r3].length;
	                  return i3;
	                case "nodebuffer":
	                  return Buffer.concat(t3);
	                default:
	                  throw new Error("concat : unsupported type '" + e4 + "'");
	              }
	            }(i2, n2), a2);
	            t2(e3);
	          } catch (e4) {
	            r2(e4);
	          }
	          n2 = [];
	        }).resume();
	      });
	    }
	    function f(e2, t2, r2) {
	      var n2 = t2;
	      switch (t2) {
	        case "blob":
	        case "arraybuffer":
	          n2 = "uint8array";
	          break;
	        case "base64":
	          n2 = "string";
	      }
	      try {
	        this._internalType = n2, this._outputType = t2, this._mimeType = r2, h.checkSupport(n2), this._worker = e2.pipe(new i(n2)), e2.lock();
	      } catch (e3) {
	        this._worker = new s("error"), this._worker.error(e3);
	      }
	    }
	    f.prototype = { accumulate: function(e2) {
	      return l(this, e2);
	    }, on: function(e2, t2) {
	      var r2 = this;
	      return "data" === e2 ? this._worker.on(e2, function(e3) {
	        t2.call(r2, e3.data, e3.meta);
	      }) : this._worker.on(e2, function() {
	        h.delay(t2, arguments, r2);
	      }), this;
	    }, resume: function() {
	      return h.delay(this._worker.resume, [], this._worker), this;
	    }, pause: function() {
	      return this._worker.pause(), this;
	    }, toNodejsStream: function(e2) {
	      if (h.checkSupport("nodestream"), "nodebuffer" !== this._outputType) throw new Error(this._outputType + " is not supported by this method");
	      return new o(this, { objectMode: "nodebuffer" !== this._outputType }, e2);
	    } }, t.exports = f;
	  }, { "../base64": 1, "../external": 6, "../nodejs/NodejsStreamOutputAdapter": 13, "../support": 30, "../utils": 32, "./ConvertWorker": 24, "./GenericWorker": 28 }], 30: [function(e, t, r) {
	    if (r.base64 = true, r.array = true, r.string = true, r.arraybuffer = "undefined" != typeof ArrayBuffer && "undefined" != typeof Uint8Array, r.nodebuffer = "undefined" != typeof Buffer, r.uint8array = "undefined" != typeof Uint8Array, "undefined" == typeof ArrayBuffer) r.blob = false;
	    else {
	      var n = new ArrayBuffer(0);
	      try {
	        r.blob = 0 === new Blob([n], { type: "application/zip" }).size;
	      } catch (e2) {
	        try {
	          var i = new (self.BlobBuilder || self.WebKitBlobBuilder || self.MozBlobBuilder || self.MSBlobBuilder)();
	          i.append(n), r.blob = 0 === i.getBlob("application/zip").size;
	        } catch (e3) {
	          r.blob = false;
	        }
	      }
	    }
	    try {
	      r.nodestream = !!e("readable-stream").Readable;
	    } catch (e2) {
	      r.nodestream = false;
	    }
	  }, { "readable-stream": 16 }], 31: [function(e, t, s) {
	    for (var o = e("./utils"), h = e("./support"), r = e("./nodejsUtils"), n = e("./stream/GenericWorker"), u = new Array(256), i = 0; i < 256; i++) u[i] = 252 <= i ? 6 : 248 <= i ? 5 : 240 <= i ? 4 : 224 <= i ? 3 : 192 <= i ? 2 : 1;
	    u[254] = u[254] = 1;
	    function a() {
	      n.call(this, "utf-8 decode"), this.leftOver = null;
	    }
	    function l() {
	      n.call(this, "utf-8 encode");
	    }
	    s.utf8encode = function(e2) {
	      return h.nodebuffer ? r.newBufferFrom(e2, "utf-8") : function(e3) {
	        var t2, r2, n2, i2, s2, a2 = e3.length, o2 = 0;
	        for (i2 = 0; i2 < a2; i2++) 55296 == (64512 & (r2 = e3.charCodeAt(i2))) && i2 + 1 < a2 && 56320 == (64512 & (n2 = e3.charCodeAt(i2 + 1))) && (r2 = 65536 + (r2 - 55296 << 10) + (n2 - 56320), i2++), o2 += r2 < 128 ? 1 : r2 < 2048 ? 2 : r2 < 65536 ? 3 : 4;
	        for (t2 = h.uint8array ? new Uint8Array(o2) : new Array(o2), i2 = s2 = 0; s2 < o2; i2++) 55296 == (64512 & (r2 = e3.charCodeAt(i2))) && i2 + 1 < a2 && 56320 == (64512 & (n2 = e3.charCodeAt(i2 + 1))) && (r2 = 65536 + (r2 - 55296 << 10) + (n2 - 56320), i2++), r2 < 128 ? t2[s2++] = r2 : (r2 < 2048 ? t2[s2++] = 192 | r2 >>> 6 : (r2 < 65536 ? t2[s2++] = 224 | r2 >>> 12 : (t2[s2++] = 240 | r2 >>> 18, t2[s2++] = 128 | r2 >>> 12 & 63), t2[s2++] = 128 | r2 >>> 6 & 63), t2[s2++] = 128 | 63 & r2);
	        return t2;
	      }(e2);
	    }, s.utf8decode = function(e2) {
	      return h.nodebuffer ? o.transformTo("nodebuffer", e2).toString("utf-8") : function(e3) {
	        var t2, r2, n2, i2, s2 = e3.length, a2 = new Array(2 * s2);
	        for (t2 = r2 = 0; t2 < s2; ) if ((n2 = e3[t2++]) < 128) a2[r2++] = n2;
	        else if (4 < (i2 = u[n2])) a2[r2++] = 65533, t2 += i2 - 1;
	        else {
	          for (n2 &= 2 === i2 ? 31 : 3 === i2 ? 15 : 7; 1 < i2 && t2 < s2; ) n2 = n2 << 6 | 63 & e3[t2++], i2--;
	          1 < i2 ? a2[r2++] = 65533 : n2 < 65536 ? a2[r2++] = n2 : (n2 -= 65536, a2[r2++] = 55296 | n2 >> 10 & 1023, a2[r2++] = 56320 | 1023 & n2);
	        }
	        return a2.length !== r2 && (a2.subarray ? a2 = a2.subarray(0, r2) : a2.length = r2), o.applyFromCharCode(a2);
	      }(e2 = o.transformTo(h.uint8array ? "uint8array" : "array", e2));
	    }, o.inherits(a, n), a.prototype.processChunk = function(e2) {
	      var t2 = o.transformTo(h.uint8array ? "uint8array" : "array", e2.data);
	      if (this.leftOver && this.leftOver.length) {
	        if (h.uint8array) {
	          var r2 = t2;
	          (t2 = new Uint8Array(r2.length + this.leftOver.length)).set(this.leftOver, 0), t2.set(r2, this.leftOver.length);
	        } else t2 = this.leftOver.concat(t2);
	        this.leftOver = null;
	      }
	      var n2 = function(e3, t3) {
	        var r3;
	        for ((t3 = t3 || e3.length) > e3.length && (t3 = e3.length), r3 = t3 - 1; 0 <= r3 && 128 == (192 & e3[r3]); ) r3--;
	        return r3 < 0 ? t3 : 0 === r3 ? t3 : r3 + u[e3[r3]] > t3 ? r3 : t3;
	      }(t2), i2 = t2;
	      n2 !== t2.length && (h.uint8array ? (i2 = t2.subarray(0, n2), this.leftOver = t2.subarray(n2, t2.length)) : (i2 = t2.slice(0, n2), this.leftOver = t2.slice(n2, t2.length))), this.push({ data: s.utf8decode(i2), meta: e2.meta });
	    }, a.prototype.flush = function() {
	      this.leftOver && this.leftOver.length && (this.push({ data: s.utf8decode(this.leftOver), meta: {} }), this.leftOver = null);
	    }, s.Utf8DecodeWorker = a, o.inherits(l, n), l.prototype.processChunk = function(e2) {
	      this.push({ data: s.utf8encode(e2.data), meta: e2.meta });
	    }, s.Utf8EncodeWorker = l;
	  }, { "./nodejsUtils": 14, "./stream/GenericWorker": 28, "./support": 30, "./utils": 32 }], 32: [function(e, t, a) {
	    var o = e("./support"), h = e("./base64"), r = e("./nodejsUtils"), u = e("./external");
	    function n(e2) {
	      return e2;
	    }
	    function l(e2, t2) {
	      for (var r2 = 0; r2 < e2.length; ++r2) t2[r2] = 255 & e2.charCodeAt(r2);
	      return t2;
	    }
	    e("setimmediate"), a.newBlob = function(t2, r2) {
	      a.checkSupport("blob");
	      try {
	        return new Blob([t2], { type: r2 });
	      } catch (e2) {
	        try {
	          var n2 = new (self.BlobBuilder || self.WebKitBlobBuilder || self.MozBlobBuilder || self.MSBlobBuilder)();
	          return n2.append(t2), n2.getBlob(r2);
	        } catch (e3) {
	          throw new Error("Bug : can't construct the Blob.");
	        }
	      }
	    };
	    var i = { stringifyByChunk: function(e2, t2, r2) {
	      var n2 = [], i2 = 0, s2 = e2.length;
	      if (s2 <= r2) return String.fromCharCode.apply(null, e2);
	      for (; i2 < s2; ) "array" === t2 || "nodebuffer" === t2 ? n2.push(String.fromCharCode.apply(null, e2.slice(i2, Math.min(i2 + r2, s2)))) : n2.push(String.fromCharCode.apply(null, e2.subarray(i2, Math.min(i2 + r2, s2)))), i2 += r2;
	      return n2.join("");
	    }, stringifyByChar: function(e2) {
	      for (var t2 = "", r2 = 0; r2 < e2.length; r2++) t2 += String.fromCharCode(e2[r2]);
	      return t2;
	    }, applyCanBeUsed: { uint8array: function() {
	      try {
	        return o.uint8array && 1 === String.fromCharCode.apply(null, new Uint8Array(1)).length;
	      } catch (e2) {
	        return false;
	      }
	    }(), nodebuffer: function() {
	      try {
	        return o.nodebuffer && 1 === String.fromCharCode.apply(null, r.allocBuffer(1)).length;
	      } catch (e2) {
	        return false;
	      }
	    }() } };
	    function s(e2) {
	      var t2 = 65536, r2 = a.getTypeOf(e2), n2 = true;
	      if ("uint8array" === r2 ? n2 = i.applyCanBeUsed.uint8array : "nodebuffer" === r2 && (n2 = i.applyCanBeUsed.nodebuffer), n2) for (; 1 < t2; ) try {
	        return i.stringifyByChunk(e2, r2, t2);
	      } catch (e3) {
	        t2 = Math.floor(t2 / 2);
	      }
	      return i.stringifyByChar(e2);
	    }
	    function f(e2, t2) {
	      for (var r2 = 0; r2 < e2.length; r2++) t2[r2] = e2[r2];
	      return t2;
	    }
	    a.applyFromCharCode = s;
	    var c = {};
	    c.string = { string: n, array: function(e2) {
	      return l(e2, new Array(e2.length));
	    }, arraybuffer: function(e2) {
	      return c.string.uint8array(e2).buffer;
	    }, uint8array: function(e2) {
	      return l(e2, new Uint8Array(e2.length));
	    }, nodebuffer: function(e2) {
	      return l(e2, r.allocBuffer(e2.length));
	    } }, c.array = { string: s, array: n, arraybuffer: function(e2) {
	      return new Uint8Array(e2).buffer;
	    }, uint8array: function(e2) {
	      return new Uint8Array(e2);
	    }, nodebuffer: function(e2) {
	      return r.newBufferFrom(e2);
	    } }, c.arraybuffer = { string: function(e2) {
	      return s(new Uint8Array(e2));
	    }, array: function(e2) {
	      return f(new Uint8Array(e2), new Array(e2.byteLength));
	    }, arraybuffer: n, uint8array: function(e2) {
	      return new Uint8Array(e2);
	    }, nodebuffer: function(e2) {
	      return r.newBufferFrom(new Uint8Array(e2));
	    } }, c.uint8array = { string: s, array: function(e2) {
	      return f(e2, new Array(e2.length));
	    }, arraybuffer: function(e2) {
	      return e2.buffer;
	    }, uint8array: n, nodebuffer: function(e2) {
	      return r.newBufferFrom(e2);
	    } }, c.nodebuffer = { string: s, array: function(e2) {
	      return f(e2, new Array(e2.length));
	    }, arraybuffer: function(e2) {
	      return c.nodebuffer.uint8array(e2).buffer;
	    }, uint8array: function(e2) {
	      return f(e2, new Uint8Array(e2.length));
	    }, nodebuffer: n }, a.transformTo = function(e2, t2) {
	      if (t2 = t2 || "", !e2) return t2;
	      a.checkSupport(e2);
	      var r2 = a.getTypeOf(t2);
	      return c[r2][e2](t2);
	    }, a.resolve = function(e2) {
	      for (var t2 = e2.split("/"), r2 = [], n2 = 0; n2 < t2.length; n2++) {
	        var i2 = t2[n2];
	        "." === i2 || "" === i2 && 0 !== n2 && n2 !== t2.length - 1 || (".." === i2 ? r2.pop() : r2.push(i2));
	      }
	      return r2.join("/");
	    }, a.getTypeOf = function(e2) {
	      return "string" == typeof e2 ? "string" : "[object Array]" === Object.prototype.toString.call(e2) ? "array" : o.nodebuffer && r.isBuffer(e2) ? "nodebuffer" : o.uint8array && e2 instanceof Uint8Array ? "uint8array" : o.arraybuffer && e2 instanceof ArrayBuffer ? "arraybuffer" : void 0;
	    }, a.checkSupport = function(e2) {
	      if (!o[e2.toLowerCase()]) throw new Error(e2 + " is not supported by this platform");
	    }, a.MAX_VALUE_16BITS = 65535, a.MAX_VALUE_32BITS = -1, a.pretty = function(e2) {
	      var t2, r2, n2 = "";
	      for (r2 = 0; r2 < (e2 || "").length; r2++) n2 += "\\x" + ((t2 = e2.charCodeAt(r2)) < 16 ? "0" : "") + t2.toString(16).toUpperCase();
	      return n2;
	    }, a.delay = function(e2, t2, r2) {
	      setImmediate(function() {
	        e2.apply(r2 || null, t2 || []);
	      });
	    }, a.inherits = function(e2, t2) {
	      function r2() {
	      }
	      r2.prototype = t2.prototype, e2.prototype = new r2();
	    }, a.extend = function() {
	      var e2, t2, r2 = {};
	      for (e2 = 0; e2 < arguments.length; e2++) for (t2 in arguments[e2]) Object.prototype.hasOwnProperty.call(arguments[e2], t2) && void 0 === r2[t2] && (r2[t2] = arguments[e2][t2]);
	      return r2;
	    }, a.prepareContent = function(r2, e2, n2, i2, s2) {
	      return u.Promise.resolve(e2).then(function(n3) {
	        return o.blob && (n3 instanceof Blob || -1 !== ["[object File]", "[object Blob]"].indexOf(Object.prototype.toString.call(n3))) && "undefined" != typeof FileReader ? new u.Promise(function(t2, r3) {
	          var e3 = new FileReader();
	          e3.onload = function(e4) {
	            t2(e4.target.result);
	          }, e3.onerror = function(e4) {
	            r3(e4.target.error);
	          }, e3.readAsArrayBuffer(n3);
	        }) : n3;
	      }).then(function(e3) {
	        var t2 = a.getTypeOf(e3);
	        return t2 ? ("arraybuffer" === t2 ? e3 = a.transformTo("uint8array", e3) : "string" === t2 && (s2 ? e3 = h.decode(e3) : n2 && true !== i2 && (e3 = function(e4) {
	          return l(e4, o.uint8array ? new Uint8Array(e4.length) : new Array(e4.length));
	        }(e3))), e3) : u.Promise.reject(new Error("Can't read the data of '" + r2 + "'. Is it in a supported JavaScript type (String, Blob, ArrayBuffer, etc) ?"));
	      });
	    };
	  }, { "./base64": 1, "./external": 6, "./nodejsUtils": 14, "./support": 30, setimmediate: 54 }], 33: [function(e, t, r) {
	    var n = e("./reader/readerFor"), i = e("./utils"), s = e("./signature"), a = e("./zipEntry"), o = e("./support");
	    function h(e2) {
	      this.files = [], this.loadOptions = e2;
	    }
	    h.prototype = { checkSignature: function(e2) {
	      if (!this.reader.readAndCheckSignature(e2)) {
	        this.reader.index -= 4;
	        var t2 = this.reader.readString(4);
	        throw new Error("Corrupted zip or bug: unexpected signature (" + i.pretty(t2) + ", expected " + i.pretty(e2) + ")");
	      }
	    }, isSignature: function(e2, t2) {
	      var r2 = this.reader.index;
	      this.reader.setIndex(e2);
	      var n2 = this.reader.readString(4) === t2;
	      return this.reader.setIndex(r2), n2;
	    }, readBlockEndOfCentral: function() {
	      this.diskNumber = this.reader.readInt(2), this.diskWithCentralDirStart = this.reader.readInt(2), this.centralDirRecordsOnThisDisk = this.reader.readInt(2), this.centralDirRecords = this.reader.readInt(2), this.centralDirSize = this.reader.readInt(4), this.centralDirOffset = this.reader.readInt(4), this.zipCommentLength = this.reader.readInt(2);
	      var e2 = this.reader.readData(this.zipCommentLength), t2 = o.uint8array ? "uint8array" : "array", r2 = i.transformTo(t2, e2);
	      this.zipComment = this.loadOptions.decodeFileName(r2);
	    }, readBlockZip64EndOfCentral: function() {
	      this.zip64EndOfCentralSize = this.reader.readInt(8), this.reader.skip(4), this.diskNumber = this.reader.readInt(4), this.diskWithCentralDirStart = this.reader.readInt(4), this.centralDirRecordsOnThisDisk = this.reader.readInt(8), this.centralDirRecords = this.reader.readInt(8), this.centralDirSize = this.reader.readInt(8), this.centralDirOffset = this.reader.readInt(8), this.zip64ExtensibleData = {};
	      for (var e2, t2, r2, n2 = this.zip64EndOfCentralSize - 44; 0 < n2; ) e2 = this.reader.readInt(2), t2 = this.reader.readInt(4), r2 = this.reader.readData(t2), this.zip64ExtensibleData[e2] = { id: e2, length: t2, value: r2 };
	    }, readBlockZip64EndOfCentralLocator: function() {
	      if (this.diskWithZip64CentralDirStart = this.reader.readInt(4), this.relativeOffsetEndOfZip64CentralDir = this.reader.readInt(8), this.disksCount = this.reader.readInt(4), 1 < this.disksCount) throw new Error("Multi-volumes zip are not supported");
	    }, readLocalFiles: function() {
	      var e2, t2;
	      for (e2 = 0; e2 < this.files.length; e2++) t2 = this.files[e2], this.reader.setIndex(t2.localHeaderOffset), this.checkSignature(s.LOCAL_FILE_HEADER), t2.readLocalPart(this.reader), t2.handleUTF8(), t2.processAttributes();
	    }, readCentralDir: function() {
	      var e2;
	      for (this.reader.setIndex(this.centralDirOffset); this.reader.readAndCheckSignature(s.CENTRAL_FILE_HEADER); ) (e2 = new a({ zip64: this.zip64 }, this.loadOptions)).readCentralPart(this.reader), this.files.push(e2);
	      if (this.centralDirRecords !== this.files.length && 0 !== this.centralDirRecords && 0 === this.files.length) throw new Error("Corrupted zip or bug: expected " + this.centralDirRecords + " records in central dir, got " + this.files.length);
	    }, readEndOfCentral: function() {
	      var e2 = this.reader.lastIndexOfSignature(s.CENTRAL_DIRECTORY_END);
	      if (e2 < 0) throw !this.isSignature(0, s.LOCAL_FILE_HEADER) ? new Error("Can't find end of central directory : is this a zip file ? If it is, see https://stuk.github.io/jszip/documentation/howto/read_zip.html") : new Error("Corrupted zip: can't find end of central directory");
	      this.reader.setIndex(e2);
	      var t2 = e2;
	      if (this.checkSignature(s.CENTRAL_DIRECTORY_END), this.readBlockEndOfCentral(), this.diskNumber === i.MAX_VALUE_16BITS || this.diskWithCentralDirStart === i.MAX_VALUE_16BITS || this.centralDirRecordsOnThisDisk === i.MAX_VALUE_16BITS || this.centralDirRecords === i.MAX_VALUE_16BITS || this.centralDirSize === i.MAX_VALUE_32BITS || this.centralDirOffset === i.MAX_VALUE_32BITS) {
	        if (this.zip64 = true, (e2 = this.reader.lastIndexOfSignature(s.ZIP64_CENTRAL_DIRECTORY_LOCATOR)) < 0) throw new Error("Corrupted zip: can't find the ZIP64 end of central directory locator");
	        if (this.reader.setIndex(e2), this.checkSignature(s.ZIP64_CENTRAL_DIRECTORY_LOCATOR), this.readBlockZip64EndOfCentralLocator(), !this.isSignature(this.relativeOffsetEndOfZip64CentralDir, s.ZIP64_CENTRAL_DIRECTORY_END) && (this.relativeOffsetEndOfZip64CentralDir = this.reader.lastIndexOfSignature(s.ZIP64_CENTRAL_DIRECTORY_END), this.relativeOffsetEndOfZip64CentralDir < 0)) throw new Error("Corrupted zip: can't find the ZIP64 end of central directory");
	        this.reader.setIndex(this.relativeOffsetEndOfZip64CentralDir), this.checkSignature(s.ZIP64_CENTRAL_DIRECTORY_END), this.readBlockZip64EndOfCentral();
	      }
	      var r2 = this.centralDirOffset + this.centralDirSize;
	      this.zip64 && (r2 += 20, r2 += 12 + this.zip64EndOfCentralSize);
	      var n2 = t2 - r2;
	      if (0 < n2) this.isSignature(t2, s.CENTRAL_FILE_HEADER) || (this.reader.zero = n2);
	      else if (n2 < 0) throw new Error("Corrupted zip: missing " + Math.abs(n2) + " bytes.");
	    }, prepareReader: function(e2) {
	      this.reader = n(e2);
	    }, load: function(e2) {
	      this.prepareReader(e2), this.readEndOfCentral(), this.readCentralDir(), this.readLocalFiles();
	    } }, t.exports = h;
	  }, { "./reader/readerFor": 22, "./signature": 23, "./support": 30, "./utils": 32, "./zipEntry": 34 }], 34: [function(e, t, r) {
	    var n = e("./reader/readerFor"), s = e("./utils"), i = e("./compressedObject"), a = e("./crc32"), o = e("./utf8"), h = e("./compressions"), u = e("./support");
	    function l(e2, t2) {
	      this.options = e2, this.loadOptions = t2;
	    }
	    l.prototype = { isEncrypted: function() {
	      return 1 == (1 & this.bitFlag);
	    }, useUTF8: function() {
	      return 2048 == (2048 & this.bitFlag);
	    }, readLocalPart: function(e2) {
	      var t2, r2;
	      if (e2.skip(22), this.fileNameLength = e2.readInt(2), r2 = e2.readInt(2), this.fileName = e2.readData(this.fileNameLength), e2.skip(r2), -1 === this.compressedSize || -1 === this.uncompressedSize) throw new Error("Bug or corrupted zip : didn't get enough information from the central directory (compressedSize === -1 || uncompressedSize === -1)");
	      if (null === (t2 = function(e3) {
	        for (var t3 in h) if (Object.prototype.hasOwnProperty.call(h, t3) && h[t3].magic === e3) return h[t3];
	        return null;
	      }(this.compressionMethod))) throw new Error("Corrupted zip : compression " + s.pretty(this.compressionMethod) + " unknown (inner file : " + s.transformTo("string", this.fileName) + ")");
	      this.decompressed = new i(this.compressedSize, this.uncompressedSize, this.crc32, t2, e2.readData(this.compressedSize));
	    }, readCentralPart: function(e2) {
	      this.versionMadeBy = e2.readInt(2), e2.skip(2), this.bitFlag = e2.readInt(2), this.compressionMethod = e2.readString(2), this.date = e2.readDate(), this.crc32 = e2.readInt(4), this.compressedSize = e2.readInt(4), this.uncompressedSize = e2.readInt(4);
	      var t2 = e2.readInt(2);
	      if (this.extraFieldsLength = e2.readInt(2), this.fileCommentLength = e2.readInt(2), this.diskNumberStart = e2.readInt(2), this.internalFileAttributes = e2.readInt(2), this.externalFileAttributes = e2.readInt(4), this.localHeaderOffset = e2.readInt(4), this.isEncrypted()) throw new Error("Encrypted zip are not supported");
	      e2.skip(t2), this.readExtraFields(e2), this.parseZIP64ExtraField(e2), this.fileComment = e2.readData(this.fileCommentLength);
	    }, processAttributes: function() {
	      this.unixPermissions = null, this.dosPermissions = null;
	      var e2 = this.versionMadeBy >> 8;
	      this.dir = !!(16 & this.externalFileAttributes), 0 == e2 && (this.dosPermissions = 63 & this.externalFileAttributes), 3 == e2 && (this.unixPermissions = this.externalFileAttributes >> 16 & 65535), this.dir || "/" !== this.fileNameStr.slice(-1) || (this.dir = true);
	    }, parseZIP64ExtraField: function() {
	      if (this.extraFields[1]) {
	        var e2 = n(this.extraFields[1].value);
	        this.uncompressedSize === s.MAX_VALUE_32BITS && (this.uncompressedSize = e2.readInt(8)), this.compressedSize === s.MAX_VALUE_32BITS && (this.compressedSize = e2.readInt(8)), this.localHeaderOffset === s.MAX_VALUE_32BITS && (this.localHeaderOffset = e2.readInt(8)), this.diskNumberStart === s.MAX_VALUE_32BITS && (this.diskNumberStart = e2.readInt(4));
	      }
	    }, readExtraFields: function(e2) {
	      var t2, r2, n2, i2 = e2.index + this.extraFieldsLength;
	      for (this.extraFields || (this.extraFields = {}); e2.index + 4 < i2; ) t2 = e2.readInt(2), r2 = e2.readInt(2), n2 = e2.readData(r2), this.extraFields[t2] = { id: t2, length: r2, value: n2 };
	      e2.setIndex(i2);
	    }, handleUTF8: function() {
	      var e2 = u.uint8array ? "uint8array" : "array";
	      if (this.useUTF8()) this.fileNameStr = o.utf8decode(this.fileName), this.fileCommentStr = o.utf8decode(this.fileComment);
	      else {
	        var t2 = this.findExtraFieldUnicodePath();
	        if (null !== t2) this.fileNameStr = t2;
	        else {
	          var r2 = s.transformTo(e2, this.fileName);
	          this.fileNameStr = this.loadOptions.decodeFileName(r2);
	        }
	        var n2 = this.findExtraFieldUnicodeComment();
	        if (null !== n2) this.fileCommentStr = n2;
	        else {
	          var i2 = s.transformTo(e2, this.fileComment);
	          this.fileCommentStr = this.loadOptions.decodeFileName(i2);
	        }
	      }
	    }, findExtraFieldUnicodePath: function() {
	      var e2 = this.extraFields[28789];
	      if (e2) {
	        var t2 = n(e2.value);
	        return 1 !== t2.readInt(1) ? null : a(this.fileName) !== t2.readInt(4) ? null : o.utf8decode(t2.readData(e2.length - 5));
	      }
	      return null;
	    }, findExtraFieldUnicodeComment: function() {
	      var e2 = this.extraFields[25461];
	      if (e2) {
	        var t2 = n(e2.value);
	        return 1 !== t2.readInt(1) ? null : a(this.fileComment) !== t2.readInt(4) ? null : o.utf8decode(t2.readData(e2.length - 5));
	      }
	      return null;
	    } }, t.exports = l;
	  }, { "./compressedObject": 2, "./compressions": 3, "./crc32": 4, "./reader/readerFor": 22, "./support": 30, "./utf8": 31, "./utils": 32 }], 35: [function(e, t, r) {
	    function n(e2, t2, r2) {
	      this.name = e2, this.dir = r2.dir, this.date = r2.date, this.comment = r2.comment, this.unixPermissions = r2.unixPermissions, this.dosPermissions = r2.dosPermissions, this._data = t2, this._dataBinary = r2.binary, this.options = { compression: r2.compression, compressionOptions: r2.compressionOptions };
	    }
	    var s = e("./stream/StreamHelper"), i = e("./stream/DataWorker"), a = e("./utf8"), o = e("./compressedObject"), h = e("./stream/GenericWorker");
	    n.prototype = { internalStream: function(e2) {
	      var t2 = null, r2 = "string";
	      try {
	        if (!e2) throw new Error("No output type specified.");
	        var n2 = "string" === (r2 = e2.toLowerCase()) || "text" === r2;
	        "binarystring" !== r2 && "text" !== r2 || (r2 = "string"), t2 = this._decompressWorker();
	        var i2 = !this._dataBinary;
	        i2 && !n2 && (t2 = t2.pipe(new a.Utf8EncodeWorker())), !i2 && n2 && (t2 = t2.pipe(new a.Utf8DecodeWorker()));
	      } catch (e3) {
	        (t2 = new h("error")).error(e3);
	      }
	      return new s(t2, r2, "");
	    }, async: function(e2, t2) {
	      return this.internalStream(e2).accumulate(t2);
	    }, nodeStream: function(e2, t2) {
	      return this.internalStream(e2 || "nodebuffer").toNodejsStream(t2);
	    }, _compressWorker: function(e2, t2) {
	      if (this._data instanceof o && this._data.compression.magic === e2.magic) return this._data.getCompressedWorker();
	      var r2 = this._decompressWorker();
	      return this._dataBinary || (r2 = r2.pipe(new a.Utf8EncodeWorker())), o.createWorkerFrom(r2, e2, t2);
	    }, _decompressWorker: function() {
	      return this._data instanceof o ? this._data.getContentWorker() : this._data instanceof h ? this._data : new i(this._data);
	    } };
	    for (var u = ["asText", "asBinary", "asNodeBuffer", "asUint8Array", "asArrayBuffer"], l = function() {
	      throw new Error("This method has been removed in JSZip 3.0, please check the upgrade guide.");
	    }, f = 0; f < u.length; f++) n.prototype[u[f]] = l;
	    t.exports = n;
	  }, { "./compressedObject": 2, "./stream/DataWorker": 27, "./stream/GenericWorker": 28, "./stream/StreamHelper": 29, "./utf8": 31 }], 36: [function(e, l, t) {
	    (function(t2) {
	      var r, n, e2 = t2.MutationObserver || t2.WebKitMutationObserver;
	      if (e2) {
	        var i = 0, s = new e2(u), a = t2.document.createTextNode("");
	        s.observe(a, { characterData: true }), r = function() {
	          a.data = i = ++i % 2;
	        };
	      } else if (t2.setImmediate || void 0 === t2.MessageChannel) r = "document" in t2 && "onreadystatechange" in t2.document.createElement("script") ? function() {
	        var e3 = t2.document.createElement("script");
	        e3.onreadystatechange = function() {
	          u(), e3.onreadystatechange = null, e3.parentNode.removeChild(e3), e3 = null;
	        }, t2.document.documentElement.appendChild(e3);
	      } : function() {
	        setTimeout(u, 0);
	      };
	      else {
	        var o = new t2.MessageChannel();
	        o.port1.onmessage = u, r = function() {
	          o.port2.postMessage(0);
	        };
	      }
	      var h = [];
	      function u() {
	        var e3, t3;
	        n = true;
	        for (var r2 = h.length; r2; ) {
	          for (t3 = h, h = [], e3 = -1; ++e3 < r2; ) t3[e3]();
	          r2 = h.length;
	        }
	        n = false;
	      }
	      l.exports = function(e3) {
	        1 !== h.push(e3) || n || r();
	      };
	    }).call(this, "undefined" != typeof commonjsGlobal ? commonjsGlobal : "undefined" != typeof self ? self : "undefined" != typeof window ? window : {});
	  }, {}], 37: [function(e, t, r) {
	    var i = e("immediate");
	    function u() {
	    }
	    var l = {}, s = ["REJECTED"], a = ["FULFILLED"], n = ["PENDING"];
	    function o(e2) {
	      if ("function" != typeof e2) throw new TypeError("resolver must be a function");
	      this.state = n, this.queue = [], this.outcome = void 0, e2 !== u && d(this, e2);
	    }
	    function h(e2, t2, r2) {
	      this.promise = e2, "function" == typeof t2 && (this.onFulfilled = t2, this.callFulfilled = this.otherCallFulfilled), "function" == typeof r2 && (this.onRejected = r2, this.callRejected = this.otherCallRejected);
	    }
	    function f(t2, r2, n2) {
	      i(function() {
	        var e2;
	        try {
	          e2 = r2(n2);
	        } catch (e3) {
	          return l.reject(t2, e3);
	        }
	        e2 === t2 ? l.reject(t2, new TypeError("Cannot resolve promise with itself")) : l.resolve(t2, e2);
	      });
	    }
	    function c(e2) {
	      var t2 = e2 && e2.then;
	      if (e2 && ("object" == typeof e2 || "function" == typeof e2) && "function" == typeof t2) return function() {
	        t2.apply(e2, arguments);
	      };
	    }
	    function d(t2, e2) {
	      var r2 = false;
	      function n2(e3) {
	        r2 || (r2 = true, l.reject(t2, e3));
	      }
	      function i2(e3) {
	        r2 || (r2 = true, l.resolve(t2, e3));
	      }
	      var s2 = p(function() {
	        e2(i2, n2);
	      });
	      "error" === s2.status && n2(s2.value);
	    }
	    function p(e2, t2) {
	      var r2 = {};
	      try {
	        r2.value = e2(t2), r2.status = "success";
	      } catch (e3) {
	        r2.status = "error", r2.value = e3;
	      }
	      return r2;
	    }
	    (t.exports = o).prototype.finally = function(t2) {
	      if ("function" != typeof t2) return this;
	      var r2 = this.constructor;
	      return this.then(function(e2) {
	        return r2.resolve(t2()).then(function() {
	          return e2;
	        });
	      }, function(e2) {
	        return r2.resolve(t2()).then(function() {
	          throw e2;
	        });
	      });
	    }, o.prototype.catch = function(e2) {
	      return this.then(null, e2);
	    }, o.prototype.then = function(e2, t2) {
	      if ("function" != typeof e2 && this.state === a || "function" != typeof t2 && this.state === s) return this;
	      var r2 = new this.constructor(u);
	      this.state !== n ? f(r2, this.state === a ? e2 : t2, this.outcome) : this.queue.push(new h(r2, e2, t2));
	      return r2;
	    }, h.prototype.callFulfilled = function(e2) {
	      l.resolve(this.promise, e2);
	    }, h.prototype.otherCallFulfilled = function(e2) {
	      f(this.promise, this.onFulfilled, e2);
	    }, h.prototype.callRejected = function(e2) {
	      l.reject(this.promise, e2);
	    }, h.prototype.otherCallRejected = function(e2) {
	      f(this.promise, this.onRejected, e2);
	    }, l.resolve = function(e2, t2) {
	      var r2 = p(c, t2);
	      if ("error" === r2.status) return l.reject(e2, r2.value);
	      var n2 = r2.value;
	      if (n2) d(e2, n2);
	      else {
	        e2.state = a, e2.outcome = t2;
	        for (var i2 = -1, s2 = e2.queue.length; ++i2 < s2; ) e2.queue[i2].callFulfilled(t2);
	      }
	      return e2;
	    }, l.reject = function(e2, t2) {
	      e2.state = s, e2.outcome = t2;
	      for (var r2 = -1, n2 = e2.queue.length; ++r2 < n2; ) e2.queue[r2].callRejected(t2);
	      return e2;
	    }, o.resolve = function(e2) {
	      if (e2 instanceof this) return e2;
	      return l.resolve(new this(u), e2);
	    }, o.reject = function(e2) {
	      var t2 = new this(u);
	      return l.reject(t2, e2);
	    }, o.all = function(e2) {
	      var r2 = this;
	      if ("[object Array]" !== Object.prototype.toString.call(e2)) return this.reject(new TypeError("must be an array"));
	      var n2 = e2.length, i2 = false;
	      if (!n2) return this.resolve([]);
	      var s2 = new Array(n2), a2 = 0, t2 = -1, o2 = new this(u);
	      for (; ++t2 < n2; ) h2(e2[t2], t2);
	      return o2;
	      function h2(e3, t3) {
	        r2.resolve(e3).then(function(e4) {
	          s2[t3] = e4, ++a2 !== n2 || i2 || (i2 = true, l.resolve(o2, s2));
	        }, function(e4) {
	          i2 || (i2 = true, l.reject(o2, e4));
	        });
	      }
	    }, o.race = function(e2) {
	      var t2 = this;
	      if ("[object Array]" !== Object.prototype.toString.call(e2)) return this.reject(new TypeError("must be an array"));
	      var r2 = e2.length, n2 = false;
	      if (!r2) return this.resolve([]);
	      var i2 = -1, s2 = new this(u);
	      for (; ++i2 < r2; ) a2 = e2[i2], t2.resolve(a2).then(function(e3) {
	        n2 || (n2 = true, l.resolve(s2, e3));
	      }, function(e3) {
	        n2 || (n2 = true, l.reject(s2, e3));
	      });
	      var a2;
	      return s2;
	    };
	  }, { immediate: 36 }], 38: [function(e, t, r) {
	    var n = {};
	    (0, e("./lib/utils/common").assign)(n, e("./lib/deflate"), e("./lib/inflate"), e("./lib/zlib/constants")), t.exports = n;
	  }, { "./lib/deflate": 39, "./lib/inflate": 40, "./lib/utils/common": 41, "./lib/zlib/constants": 44 }], 39: [function(e, t, r) {
	    var a = e("./zlib/deflate"), o = e("./utils/common"), h = e("./utils/strings"), i = e("./zlib/messages"), s = e("./zlib/zstream"), u = Object.prototype.toString, l = 0, f = -1, c = 0, d = 8;
	    function p(e2) {
	      if (!(this instanceof p)) return new p(e2);
	      this.options = o.assign({ level: f, method: d, chunkSize: 16384, windowBits: 15, memLevel: 8, strategy: c, to: "" }, e2 || {});
	      var t2 = this.options;
	      t2.raw && 0 < t2.windowBits ? t2.windowBits = -t2.windowBits : t2.gzip && 0 < t2.windowBits && t2.windowBits < 16 && (t2.windowBits += 16), this.err = 0, this.msg = "", this.ended = false, this.chunks = [], this.strm = new s(), this.strm.avail_out = 0;
	      var r2 = a.deflateInit2(this.strm, t2.level, t2.method, t2.windowBits, t2.memLevel, t2.strategy);
	      if (r2 !== l) throw new Error(i[r2]);
	      if (t2.header && a.deflateSetHeader(this.strm, t2.header), t2.dictionary) {
	        var n2;
	        if (n2 = "string" == typeof t2.dictionary ? h.string2buf(t2.dictionary) : "[object ArrayBuffer]" === u.call(t2.dictionary) ? new Uint8Array(t2.dictionary) : t2.dictionary, (r2 = a.deflateSetDictionary(this.strm, n2)) !== l) throw new Error(i[r2]);
	        this._dict_set = true;
	      }
	    }
	    function n(e2, t2) {
	      var r2 = new p(t2);
	      if (r2.push(e2, true), r2.err) throw r2.msg || i[r2.err];
	      return r2.result;
	    }
	    p.prototype.push = function(e2, t2) {
	      var r2, n2, i2 = this.strm, s2 = this.options.chunkSize;
	      if (this.ended) return false;
	      n2 = t2 === ~~t2 ? t2 : true === t2 ? 4 : 0, "string" == typeof e2 ? i2.input = h.string2buf(e2) : "[object ArrayBuffer]" === u.call(e2) ? i2.input = new Uint8Array(e2) : i2.input = e2, i2.next_in = 0, i2.avail_in = i2.input.length;
	      do {
	        if (0 === i2.avail_out && (i2.output = new o.Buf8(s2), i2.next_out = 0, i2.avail_out = s2), 1 !== (r2 = a.deflate(i2, n2)) && r2 !== l) return this.onEnd(r2), !(this.ended = true);
	        0 !== i2.avail_out && (0 !== i2.avail_in || 4 !== n2 && 2 !== n2) || ("string" === this.options.to ? this.onData(h.buf2binstring(o.shrinkBuf(i2.output, i2.next_out))) : this.onData(o.shrinkBuf(i2.output, i2.next_out)));
	      } while ((0 < i2.avail_in || 0 === i2.avail_out) && 1 !== r2);
	      return 4 === n2 ? (r2 = a.deflateEnd(this.strm), this.onEnd(r2), this.ended = true, r2 === l) : 2 !== n2 || (this.onEnd(l), !(i2.avail_out = 0));
	    }, p.prototype.onData = function(e2) {
	      this.chunks.push(e2);
	    }, p.prototype.onEnd = function(e2) {
	      e2 === l && ("string" === this.options.to ? this.result = this.chunks.join("") : this.result = o.flattenChunks(this.chunks)), this.chunks = [], this.err = e2, this.msg = this.strm.msg;
	    }, r.Deflate = p, r.deflate = n, r.deflateRaw = function(e2, t2) {
	      return (t2 = t2 || {}).raw = true, n(e2, t2);
	    }, r.gzip = function(e2, t2) {
	      return (t2 = t2 || {}).gzip = true, n(e2, t2);
	    };
	  }, { "./utils/common": 41, "./utils/strings": 42, "./zlib/deflate": 46, "./zlib/messages": 51, "./zlib/zstream": 53 }], 40: [function(e, t, r) {
	    var c = e("./zlib/inflate"), d = e("./utils/common"), p = e("./utils/strings"), m = e("./zlib/constants"), n = e("./zlib/messages"), i = e("./zlib/zstream"), s = e("./zlib/gzheader"), _ = Object.prototype.toString;
	    function a(e2) {
	      if (!(this instanceof a)) return new a(e2);
	      this.options = d.assign({ chunkSize: 16384, windowBits: 0, to: "" }, e2 || {});
	      var t2 = this.options;
	      t2.raw && 0 <= t2.windowBits && t2.windowBits < 16 && (t2.windowBits = -t2.windowBits, 0 === t2.windowBits && (t2.windowBits = -15)), !(0 <= t2.windowBits && t2.windowBits < 16) || e2 && e2.windowBits || (t2.windowBits += 32), 15 < t2.windowBits && t2.windowBits < 48 && 0 == (15 & t2.windowBits) && (t2.windowBits |= 15), this.err = 0, this.msg = "", this.ended = false, this.chunks = [], this.strm = new i(), this.strm.avail_out = 0;
	      var r2 = c.inflateInit2(this.strm, t2.windowBits);
	      if (r2 !== m.Z_OK) throw new Error(n[r2]);
	      this.header = new s(), c.inflateGetHeader(this.strm, this.header);
	    }
	    function o(e2, t2) {
	      var r2 = new a(t2);
	      if (r2.push(e2, true), r2.err) throw r2.msg || n[r2.err];
	      return r2.result;
	    }
	    a.prototype.push = function(e2, t2) {
	      var r2, n2, i2, s2, a2, o2, h = this.strm, u = this.options.chunkSize, l = this.options.dictionary, f = false;
	      if (this.ended) return false;
	      n2 = t2 === ~~t2 ? t2 : true === t2 ? m.Z_FINISH : m.Z_NO_FLUSH, "string" == typeof e2 ? h.input = p.binstring2buf(e2) : "[object ArrayBuffer]" === _.call(e2) ? h.input = new Uint8Array(e2) : h.input = e2, h.next_in = 0, h.avail_in = h.input.length;
	      do {
	        if (0 === h.avail_out && (h.output = new d.Buf8(u), h.next_out = 0, h.avail_out = u), (r2 = c.inflate(h, m.Z_NO_FLUSH)) === m.Z_NEED_DICT && l && (o2 = "string" == typeof l ? p.string2buf(l) : "[object ArrayBuffer]" === _.call(l) ? new Uint8Array(l) : l, r2 = c.inflateSetDictionary(this.strm, o2)), r2 === m.Z_BUF_ERROR && true === f && (r2 = m.Z_OK, f = false), r2 !== m.Z_STREAM_END && r2 !== m.Z_OK) return this.onEnd(r2), !(this.ended = true);
	        h.next_out && (0 !== h.avail_out && r2 !== m.Z_STREAM_END && (0 !== h.avail_in || n2 !== m.Z_FINISH && n2 !== m.Z_SYNC_FLUSH) || ("string" === this.options.to ? (i2 = p.utf8border(h.output, h.next_out), s2 = h.next_out - i2, a2 = p.buf2string(h.output, i2), h.next_out = s2, h.avail_out = u - s2, s2 && d.arraySet(h.output, h.output, i2, s2, 0), this.onData(a2)) : this.onData(d.shrinkBuf(h.output, h.next_out)))), 0 === h.avail_in && 0 === h.avail_out && (f = true);
	      } while ((0 < h.avail_in || 0 === h.avail_out) && r2 !== m.Z_STREAM_END);
	      return r2 === m.Z_STREAM_END && (n2 = m.Z_FINISH), n2 === m.Z_FINISH ? (r2 = c.inflateEnd(this.strm), this.onEnd(r2), this.ended = true, r2 === m.Z_OK) : n2 !== m.Z_SYNC_FLUSH || (this.onEnd(m.Z_OK), !(h.avail_out = 0));
	    }, a.prototype.onData = function(e2) {
	      this.chunks.push(e2);
	    }, a.prototype.onEnd = function(e2) {
	      e2 === m.Z_OK && ("string" === this.options.to ? this.result = this.chunks.join("") : this.result = d.flattenChunks(this.chunks)), this.chunks = [], this.err = e2, this.msg = this.strm.msg;
	    }, r.Inflate = a, r.inflate = o, r.inflateRaw = function(e2, t2) {
	      return (t2 = t2 || {}).raw = true, o(e2, t2);
	    }, r.ungzip = o;
	  }, { "./utils/common": 41, "./utils/strings": 42, "./zlib/constants": 44, "./zlib/gzheader": 47, "./zlib/inflate": 49, "./zlib/messages": 51, "./zlib/zstream": 53 }], 41: [function(e, t, r) {
	    var n = "undefined" != typeof Uint8Array && "undefined" != typeof Uint16Array && "undefined" != typeof Int32Array;
	    r.assign = function(e2) {
	      for (var t2 = Array.prototype.slice.call(arguments, 1); t2.length; ) {
	        var r2 = t2.shift();
	        if (r2) {
	          if ("object" != typeof r2) throw new TypeError(r2 + "must be non-object");
	          for (var n2 in r2) r2.hasOwnProperty(n2) && (e2[n2] = r2[n2]);
	        }
	      }
	      return e2;
	    }, r.shrinkBuf = function(e2, t2) {
	      return e2.length === t2 ? e2 : e2.subarray ? e2.subarray(0, t2) : (e2.length = t2, e2);
	    };
	    var i = { arraySet: function(e2, t2, r2, n2, i2) {
	      if (t2.subarray && e2.subarray) e2.set(t2.subarray(r2, r2 + n2), i2);
	      else for (var s2 = 0; s2 < n2; s2++) e2[i2 + s2] = t2[r2 + s2];
	    }, flattenChunks: function(e2) {
	      var t2, r2, n2, i2, s2, a;
	      for (t2 = n2 = 0, r2 = e2.length; t2 < r2; t2++) n2 += e2[t2].length;
	      for (a = new Uint8Array(n2), t2 = i2 = 0, r2 = e2.length; t2 < r2; t2++) s2 = e2[t2], a.set(s2, i2), i2 += s2.length;
	      return a;
	    } }, s = { arraySet: function(e2, t2, r2, n2, i2) {
	      for (var s2 = 0; s2 < n2; s2++) e2[i2 + s2] = t2[r2 + s2];
	    }, flattenChunks: function(e2) {
	      return [].concat.apply([], e2);
	    } };
	    r.setTyped = function(e2) {
	      e2 ? (r.Buf8 = Uint8Array, r.Buf16 = Uint16Array, r.Buf32 = Int32Array, r.assign(r, i)) : (r.Buf8 = Array, r.Buf16 = Array, r.Buf32 = Array, r.assign(r, s));
	    }, r.setTyped(n);
	  }, {}], 42: [function(e, t, r) {
	    var h = e("./common"), i = true, s = true;
	    try {
	      String.fromCharCode.apply(null, [0]);
	    } catch (e2) {
	      i = false;
	    }
	    try {
	      String.fromCharCode.apply(null, new Uint8Array(1));
	    } catch (e2) {
	      s = false;
	    }
	    for (var u = new h.Buf8(256), n = 0; n < 256; n++) u[n] = 252 <= n ? 6 : 248 <= n ? 5 : 240 <= n ? 4 : 224 <= n ? 3 : 192 <= n ? 2 : 1;
	    function l(e2, t2) {
	      if (t2 < 65537 && (e2.subarray && s || !e2.subarray && i)) return String.fromCharCode.apply(null, h.shrinkBuf(e2, t2));
	      for (var r2 = "", n2 = 0; n2 < t2; n2++) r2 += String.fromCharCode(e2[n2]);
	      return r2;
	    }
	    u[254] = u[254] = 1, r.string2buf = function(e2) {
	      var t2, r2, n2, i2, s2, a = e2.length, o = 0;
	      for (i2 = 0; i2 < a; i2++) 55296 == (64512 & (r2 = e2.charCodeAt(i2))) && i2 + 1 < a && 56320 == (64512 & (n2 = e2.charCodeAt(i2 + 1))) && (r2 = 65536 + (r2 - 55296 << 10) + (n2 - 56320), i2++), o += r2 < 128 ? 1 : r2 < 2048 ? 2 : r2 < 65536 ? 3 : 4;
	      for (t2 = new h.Buf8(o), i2 = s2 = 0; s2 < o; i2++) 55296 == (64512 & (r2 = e2.charCodeAt(i2))) && i2 + 1 < a && 56320 == (64512 & (n2 = e2.charCodeAt(i2 + 1))) && (r2 = 65536 + (r2 - 55296 << 10) + (n2 - 56320), i2++), r2 < 128 ? t2[s2++] = r2 : (r2 < 2048 ? t2[s2++] = 192 | r2 >>> 6 : (r2 < 65536 ? t2[s2++] = 224 | r2 >>> 12 : (t2[s2++] = 240 | r2 >>> 18, t2[s2++] = 128 | r2 >>> 12 & 63), t2[s2++] = 128 | r2 >>> 6 & 63), t2[s2++] = 128 | 63 & r2);
	      return t2;
	    }, r.buf2binstring = function(e2) {
	      return l(e2, e2.length);
	    }, r.binstring2buf = function(e2) {
	      for (var t2 = new h.Buf8(e2.length), r2 = 0, n2 = t2.length; r2 < n2; r2++) t2[r2] = e2.charCodeAt(r2);
	      return t2;
	    }, r.buf2string = function(e2, t2) {
	      var r2, n2, i2, s2, a = t2 || e2.length, o = new Array(2 * a);
	      for (r2 = n2 = 0; r2 < a; ) if ((i2 = e2[r2++]) < 128) o[n2++] = i2;
	      else if (4 < (s2 = u[i2])) o[n2++] = 65533, r2 += s2 - 1;
	      else {
	        for (i2 &= 2 === s2 ? 31 : 3 === s2 ? 15 : 7; 1 < s2 && r2 < a; ) i2 = i2 << 6 | 63 & e2[r2++], s2--;
	        1 < s2 ? o[n2++] = 65533 : i2 < 65536 ? o[n2++] = i2 : (i2 -= 65536, o[n2++] = 55296 | i2 >> 10 & 1023, o[n2++] = 56320 | 1023 & i2);
	      }
	      return l(o, n2);
	    }, r.utf8border = function(e2, t2) {
	      var r2;
	      for ((t2 = t2 || e2.length) > e2.length && (t2 = e2.length), r2 = t2 - 1; 0 <= r2 && 128 == (192 & e2[r2]); ) r2--;
	      return r2 < 0 ? t2 : 0 === r2 ? t2 : r2 + u[e2[r2]] > t2 ? r2 : t2;
	    };
	  }, { "./common": 41 }], 43: [function(e, t, r) {
	    t.exports = function(e2, t2, r2, n) {
	      for (var i = 65535 & e2 | 0, s = e2 >>> 16 & 65535 | 0, a = 0; 0 !== r2; ) {
	        for (r2 -= a = 2e3 < r2 ? 2e3 : r2; s = s + (i = i + t2[n++] | 0) | 0, --a; ) ;
	        i %= 65521, s %= 65521;
	      }
	      return i | s << 16 | 0;
	    };
	  }, {}], 44: [function(e, t, r) {
	    t.exports = { Z_NO_FLUSH: 0, Z_PARTIAL_FLUSH: 1, Z_SYNC_FLUSH: 2, Z_FULL_FLUSH: 3, Z_FINISH: 4, Z_BLOCK: 5, Z_TREES: 6, Z_OK: 0, Z_STREAM_END: 1, Z_NEED_DICT: 2, Z_ERRNO: -1, Z_STREAM_ERROR: -2, Z_DATA_ERROR: -3, Z_BUF_ERROR: -5, Z_NO_COMPRESSION: 0, Z_BEST_SPEED: 1, Z_BEST_COMPRESSION: 9, Z_DEFAULT_COMPRESSION: -1, Z_FILTERED: 1, Z_HUFFMAN_ONLY: 2, Z_RLE: 3, Z_FIXED: 4, Z_DEFAULT_STRATEGY: 0, Z_BINARY: 0, Z_TEXT: 1, Z_UNKNOWN: 2, Z_DEFLATED: 8 };
	  }, {}], 45: [function(e, t, r) {
	    var o = function() {
	      for (var e2, t2 = [], r2 = 0; r2 < 256; r2++) {
	        e2 = r2;
	        for (var n = 0; n < 8; n++) e2 = 1 & e2 ? 3988292384 ^ e2 >>> 1 : e2 >>> 1;
	        t2[r2] = e2;
	      }
	      return t2;
	    }();
	    t.exports = function(e2, t2, r2, n) {
	      var i = o, s = n + r2;
	      e2 ^= -1;
	      for (var a = n; a < s; a++) e2 = e2 >>> 8 ^ i[255 & (e2 ^ t2[a])];
	      return -1 ^ e2;
	    };
	  }, {}], 46: [function(e, t, r) {
	    var h, c = e("../utils/common"), u = e("./trees"), d = e("./adler32"), p = e("./crc32"), n = e("./messages"), l = 0, f = 4, m = 0, _ = -2, g = -1, b = 4, i = 2, v = 8, y = 9, s = 286, a = 30, o = 19, w = 2 * s + 1, k = 15, x = 3, S = 258, z = S + x + 1, C = 42, E = 113, A = 1, I = 2, O = 3, B = 4;
	    function R(e2, t2) {
	      return e2.msg = n[t2], t2;
	    }
	    function T(e2) {
	      return (e2 << 1) - (4 < e2 ? 9 : 0);
	    }
	    function D(e2) {
	      for (var t2 = e2.length; 0 <= --t2; ) e2[t2] = 0;
	    }
	    function F(e2) {
	      var t2 = e2.state, r2 = t2.pending;
	      r2 > e2.avail_out && (r2 = e2.avail_out), 0 !== r2 && (c.arraySet(e2.output, t2.pending_buf, t2.pending_out, r2, e2.next_out), e2.next_out += r2, t2.pending_out += r2, e2.total_out += r2, e2.avail_out -= r2, t2.pending -= r2, 0 === t2.pending && (t2.pending_out = 0));
	    }
	    function N(e2, t2) {
	      u._tr_flush_block(e2, 0 <= e2.block_start ? e2.block_start : -1, e2.strstart - e2.block_start, t2), e2.block_start = e2.strstart, F(e2.strm);
	    }
	    function U(e2, t2) {
	      e2.pending_buf[e2.pending++] = t2;
	    }
	    function P(e2, t2) {
	      e2.pending_buf[e2.pending++] = t2 >>> 8 & 255, e2.pending_buf[e2.pending++] = 255 & t2;
	    }
	    function L(e2, t2) {
	      var r2, n2, i2 = e2.max_chain_length, s2 = e2.strstart, a2 = e2.prev_length, o2 = e2.nice_match, h2 = e2.strstart > e2.w_size - z ? e2.strstart - (e2.w_size - z) : 0, u2 = e2.window, l2 = e2.w_mask, f2 = e2.prev, c2 = e2.strstart + S, d2 = u2[s2 + a2 - 1], p2 = u2[s2 + a2];
	      e2.prev_length >= e2.good_match && (i2 >>= 2), o2 > e2.lookahead && (o2 = e2.lookahead);
	      do {
	        if (u2[(r2 = t2) + a2] === p2 && u2[r2 + a2 - 1] === d2 && u2[r2] === u2[s2] && u2[++r2] === u2[s2 + 1]) {
	          s2 += 2, r2++;
	          do {
	          } while (u2[++s2] === u2[++r2] && u2[++s2] === u2[++r2] && u2[++s2] === u2[++r2] && u2[++s2] === u2[++r2] && u2[++s2] === u2[++r2] && u2[++s2] === u2[++r2] && u2[++s2] === u2[++r2] && u2[++s2] === u2[++r2] && s2 < c2);
	          if (n2 = S - (c2 - s2), s2 = c2 - S, a2 < n2) {
	            if (e2.match_start = t2, o2 <= (a2 = n2)) break;
	            d2 = u2[s2 + a2 - 1], p2 = u2[s2 + a2];
	          }
	        }
	      } while ((t2 = f2[t2 & l2]) > h2 && 0 != --i2);
	      return a2 <= e2.lookahead ? a2 : e2.lookahead;
	    }
	    function j(e2) {
	      var t2, r2, n2, i2, s2, a2, o2, h2, u2, l2, f2 = e2.w_size;
	      do {
	        if (i2 = e2.window_size - e2.lookahead - e2.strstart, e2.strstart >= f2 + (f2 - z)) {
	          for (c.arraySet(e2.window, e2.window, f2, f2, 0), e2.match_start -= f2, e2.strstart -= f2, e2.block_start -= f2, t2 = r2 = e2.hash_size; n2 = e2.head[--t2], e2.head[t2] = f2 <= n2 ? n2 - f2 : 0, --r2; ) ;
	          for (t2 = r2 = f2; n2 = e2.prev[--t2], e2.prev[t2] = f2 <= n2 ? n2 - f2 : 0, --r2; ) ;
	          i2 += f2;
	        }
	        if (0 === e2.strm.avail_in) break;
	        if (a2 = e2.strm, o2 = e2.window, h2 = e2.strstart + e2.lookahead, u2 = i2, l2 = void 0, l2 = a2.avail_in, u2 < l2 && (l2 = u2), r2 = 0 === l2 ? 0 : (a2.avail_in -= l2, c.arraySet(o2, a2.input, a2.next_in, l2, h2), 1 === a2.state.wrap ? a2.adler = d(a2.adler, o2, l2, h2) : 2 === a2.state.wrap && (a2.adler = p(a2.adler, o2, l2, h2)), a2.next_in += l2, a2.total_in += l2, l2), e2.lookahead += r2, e2.lookahead + e2.insert >= x) for (s2 = e2.strstart - e2.insert, e2.ins_h = e2.window[s2], e2.ins_h = (e2.ins_h << e2.hash_shift ^ e2.window[s2 + 1]) & e2.hash_mask; e2.insert && (e2.ins_h = (e2.ins_h << e2.hash_shift ^ e2.window[s2 + x - 1]) & e2.hash_mask, e2.prev[s2 & e2.w_mask] = e2.head[e2.ins_h], e2.head[e2.ins_h] = s2, s2++, e2.insert--, !(e2.lookahead + e2.insert < x)); ) ;
	      } while (e2.lookahead < z && 0 !== e2.strm.avail_in);
	    }
	    function Z(e2, t2) {
	      for (var r2, n2; ; ) {
	        if (e2.lookahead < z) {
	          if (j(e2), e2.lookahead < z && t2 === l) return A;
	          if (0 === e2.lookahead) break;
	        }
	        if (r2 = 0, e2.lookahead >= x && (e2.ins_h = (e2.ins_h << e2.hash_shift ^ e2.window[e2.strstart + x - 1]) & e2.hash_mask, r2 = e2.prev[e2.strstart & e2.w_mask] = e2.head[e2.ins_h], e2.head[e2.ins_h] = e2.strstart), 0 !== r2 && e2.strstart - r2 <= e2.w_size - z && (e2.match_length = L(e2, r2)), e2.match_length >= x) if (n2 = u._tr_tally(e2, e2.strstart - e2.match_start, e2.match_length - x), e2.lookahead -= e2.match_length, e2.match_length <= e2.max_lazy_match && e2.lookahead >= x) {
	          for (e2.match_length--; e2.strstart++, e2.ins_h = (e2.ins_h << e2.hash_shift ^ e2.window[e2.strstart + x - 1]) & e2.hash_mask, r2 = e2.prev[e2.strstart & e2.w_mask] = e2.head[e2.ins_h], e2.head[e2.ins_h] = e2.strstart, 0 != --e2.match_length; ) ;
	          e2.strstart++;
	        } else e2.strstart += e2.match_length, e2.match_length = 0, e2.ins_h = e2.window[e2.strstart], e2.ins_h = (e2.ins_h << e2.hash_shift ^ e2.window[e2.strstart + 1]) & e2.hash_mask;
	        else n2 = u._tr_tally(e2, 0, e2.window[e2.strstart]), e2.lookahead--, e2.strstart++;
	        if (n2 && (N(e2, false), 0 === e2.strm.avail_out)) return A;
	      }
	      return e2.insert = e2.strstart < x - 1 ? e2.strstart : x - 1, t2 === f ? (N(e2, true), 0 === e2.strm.avail_out ? O : B) : e2.last_lit && (N(e2, false), 0 === e2.strm.avail_out) ? A : I;
	    }
	    function W(e2, t2) {
	      for (var r2, n2, i2; ; ) {
	        if (e2.lookahead < z) {
	          if (j(e2), e2.lookahead < z && t2 === l) return A;
	          if (0 === e2.lookahead) break;
	        }
	        if (r2 = 0, e2.lookahead >= x && (e2.ins_h = (e2.ins_h << e2.hash_shift ^ e2.window[e2.strstart + x - 1]) & e2.hash_mask, r2 = e2.prev[e2.strstart & e2.w_mask] = e2.head[e2.ins_h], e2.head[e2.ins_h] = e2.strstart), e2.prev_length = e2.match_length, e2.prev_match = e2.match_start, e2.match_length = x - 1, 0 !== r2 && e2.prev_length < e2.max_lazy_match && e2.strstart - r2 <= e2.w_size - z && (e2.match_length = L(e2, r2), e2.match_length <= 5 && (1 === e2.strategy || e2.match_length === x && 4096 < e2.strstart - e2.match_start) && (e2.match_length = x - 1)), e2.prev_length >= x && e2.match_length <= e2.prev_length) {
	          for (i2 = e2.strstart + e2.lookahead - x, n2 = u._tr_tally(e2, e2.strstart - 1 - e2.prev_match, e2.prev_length - x), e2.lookahead -= e2.prev_length - 1, e2.prev_length -= 2; ++e2.strstart <= i2 && (e2.ins_h = (e2.ins_h << e2.hash_shift ^ e2.window[e2.strstart + x - 1]) & e2.hash_mask, r2 = e2.prev[e2.strstart & e2.w_mask] = e2.head[e2.ins_h], e2.head[e2.ins_h] = e2.strstart), 0 != --e2.prev_length; ) ;
	          if (e2.match_available = 0, e2.match_length = x - 1, e2.strstart++, n2 && (N(e2, false), 0 === e2.strm.avail_out)) return A;
	        } else if (e2.match_available) {
	          if ((n2 = u._tr_tally(e2, 0, e2.window[e2.strstart - 1])) && N(e2, false), e2.strstart++, e2.lookahead--, 0 === e2.strm.avail_out) return A;
	        } else e2.match_available = 1, e2.strstart++, e2.lookahead--;
	      }
	      return e2.match_available && (n2 = u._tr_tally(e2, 0, e2.window[e2.strstart - 1]), e2.match_available = 0), e2.insert = e2.strstart < x - 1 ? e2.strstart : x - 1, t2 === f ? (N(e2, true), 0 === e2.strm.avail_out ? O : B) : e2.last_lit && (N(e2, false), 0 === e2.strm.avail_out) ? A : I;
	    }
	    function M(e2, t2, r2, n2, i2) {
	      this.good_length = e2, this.max_lazy = t2, this.nice_length = r2, this.max_chain = n2, this.func = i2;
	    }
	    function H() {
	      this.strm = null, this.status = 0, this.pending_buf = null, this.pending_buf_size = 0, this.pending_out = 0, this.pending = 0, this.wrap = 0, this.gzhead = null, this.gzindex = 0, this.method = v, this.last_flush = -1, this.w_size = 0, this.w_bits = 0, this.w_mask = 0, this.window = null, this.window_size = 0, this.prev = null, this.head = null, this.ins_h = 0, this.hash_size = 0, this.hash_bits = 0, this.hash_mask = 0, this.hash_shift = 0, this.block_start = 0, this.match_length = 0, this.prev_match = 0, this.match_available = 0, this.strstart = 0, this.match_start = 0, this.lookahead = 0, this.prev_length = 0, this.max_chain_length = 0, this.max_lazy_match = 0, this.level = 0, this.strategy = 0, this.good_match = 0, this.nice_match = 0, this.dyn_ltree = new c.Buf16(2 * w), this.dyn_dtree = new c.Buf16(2 * (2 * a + 1)), this.bl_tree = new c.Buf16(2 * (2 * o + 1)), D(this.dyn_ltree), D(this.dyn_dtree), D(this.bl_tree), this.l_desc = null, this.d_desc = null, this.bl_desc = null, this.bl_count = new c.Buf16(k + 1), this.heap = new c.Buf16(2 * s + 1), D(this.heap), this.heap_len = 0, this.heap_max = 0, this.depth = new c.Buf16(2 * s + 1), D(this.depth), this.l_buf = 0, this.lit_bufsize = 0, this.last_lit = 0, this.d_buf = 0, this.opt_len = 0, this.static_len = 0, this.matches = 0, this.insert = 0, this.bi_buf = 0, this.bi_valid = 0;
	    }
	    function G(e2) {
	      var t2;
	      return e2 && e2.state ? (e2.total_in = e2.total_out = 0, e2.data_type = i, (t2 = e2.state).pending = 0, t2.pending_out = 0, t2.wrap < 0 && (t2.wrap = -t2.wrap), t2.status = t2.wrap ? C : E, e2.adler = 2 === t2.wrap ? 0 : 1, t2.last_flush = l, u._tr_init(t2), m) : R(e2, _);
	    }
	    function K(e2) {
	      var t2 = G(e2);
	      return t2 === m && function(e3) {
	        e3.window_size = 2 * e3.w_size, D(e3.head), e3.max_lazy_match = h[e3.level].max_lazy, e3.good_match = h[e3.level].good_length, e3.nice_match = h[e3.level].nice_length, e3.max_chain_length = h[e3.level].max_chain, e3.strstart = 0, e3.block_start = 0, e3.lookahead = 0, e3.insert = 0, e3.match_length = e3.prev_length = x - 1, e3.match_available = 0, e3.ins_h = 0;
	      }(e2.state), t2;
	    }
	    function Y(e2, t2, r2, n2, i2, s2) {
	      if (!e2) return _;
	      var a2 = 1;
	      if (t2 === g && (t2 = 6), n2 < 0 ? (a2 = 0, n2 = -n2) : 15 < n2 && (a2 = 2, n2 -= 16), i2 < 1 || y < i2 || r2 !== v || n2 < 8 || 15 < n2 || t2 < 0 || 9 < t2 || s2 < 0 || b < s2) return R(e2, _);
	      8 === n2 && (n2 = 9);
	      var o2 = new H();
	      return (e2.state = o2).strm = e2, o2.wrap = a2, o2.gzhead = null, o2.w_bits = n2, o2.w_size = 1 << o2.w_bits, o2.w_mask = o2.w_size - 1, o2.hash_bits = i2 + 7, o2.hash_size = 1 << o2.hash_bits, o2.hash_mask = o2.hash_size - 1, o2.hash_shift = ~~((o2.hash_bits + x - 1) / x), o2.window = new c.Buf8(2 * o2.w_size), o2.head = new c.Buf16(o2.hash_size), o2.prev = new c.Buf16(o2.w_size), o2.lit_bufsize = 1 << i2 + 6, o2.pending_buf_size = 4 * o2.lit_bufsize, o2.pending_buf = new c.Buf8(o2.pending_buf_size), o2.d_buf = 1 * o2.lit_bufsize, o2.l_buf = 3 * o2.lit_bufsize, o2.level = t2, o2.strategy = s2, o2.method = r2, K(e2);
	    }
	    h = [new M(0, 0, 0, 0, function(e2, t2) {
	      var r2 = 65535;
	      for (r2 > e2.pending_buf_size - 5 && (r2 = e2.pending_buf_size - 5); ; ) {
	        if (e2.lookahead <= 1) {
	          if (j(e2), 0 === e2.lookahead && t2 === l) return A;
	          if (0 === e2.lookahead) break;
	        }
	        e2.strstart += e2.lookahead, e2.lookahead = 0;
	        var n2 = e2.block_start + r2;
	        if ((0 === e2.strstart || e2.strstart >= n2) && (e2.lookahead = e2.strstart - n2, e2.strstart = n2, N(e2, false), 0 === e2.strm.avail_out)) return A;
	        if (e2.strstart - e2.block_start >= e2.w_size - z && (N(e2, false), 0 === e2.strm.avail_out)) return A;
	      }
	      return e2.insert = 0, t2 === f ? (N(e2, true), 0 === e2.strm.avail_out ? O : B) : (e2.strstart > e2.block_start && (N(e2, false), e2.strm.avail_out), A);
	    }), new M(4, 4, 8, 4, Z), new M(4, 5, 16, 8, Z), new M(4, 6, 32, 32, Z), new M(4, 4, 16, 16, W), new M(8, 16, 32, 32, W), new M(8, 16, 128, 128, W), new M(8, 32, 128, 256, W), new M(32, 128, 258, 1024, W), new M(32, 258, 258, 4096, W)], r.deflateInit = function(e2, t2) {
	      return Y(e2, t2, v, 15, 8, 0);
	    }, r.deflateInit2 = Y, r.deflateReset = K, r.deflateResetKeep = G, r.deflateSetHeader = function(e2, t2) {
	      return e2 && e2.state ? 2 !== e2.state.wrap ? _ : (e2.state.gzhead = t2, m) : _;
	    }, r.deflate = function(e2, t2) {
	      var r2, n2, i2, s2;
	      if (!e2 || !e2.state || 5 < t2 || t2 < 0) return e2 ? R(e2, _) : _;
	      if (n2 = e2.state, !e2.output || !e2.input && 0 !== e2.avail_in || 666 === n2.status && t2 !== f) return R(e2, 0 === e2.avail_out ? -5 : _);
	      if (n2.strm = e2, r2 = n2.last_flush, n2.last_flush = t2, n2.status === C) if (2 === n2.wrap) e2.adler = 0, U(n2, 31), U(n2, 139), U(n2, 8), n2.gzhead ? (U(n2, (n2.gzhead.text ? 1 : 0) + (n2.gzhead.hcrc ? 2 : 0) + (n2.gzhead.extra ? 4 : 0) + (n2.gzhead.name ? 8 : 0) + (n2.gzhead.comment ? 16 : 0)), U(n2, 255 & n2.gzhead.time), U(n2, n2.gzhead.time >> 8 & 255), U(n2, n2.gzhead.time >> 16 & 255), U(n2, n2.gzhead.time >> 24 & 255), U(n2, 9 === n2.level ? 2 : 2 <= n2.strategy || n2.level < 2 ? 4 : 0), U(n2, 255 & n2.gzhead.os), n2.gzhead.extra && n2.gzhead.extra.length && (U(n2, 255 & n2.gzhead.extra.length), U(n2, n2.gzhead.extra.length >> 8 & 255)), n2.gzhead.hcrc && (e2.adler = p(e2.adler, n2.pending_buf, n2.pending, 0)), n2.gzindex = 0, n2.status = 69) : (U(n2, 0), U(n2, 0), U(n2, 0), U(n2, 0), U(n2, 0), U(n2, 9 === n2.level ? 2 : 2 <= n2.strategy || n2.level < 2 ? 4 : 0), U(n2, 3), n2.status = E);
	      else {
	        var a2 = v + (n2.w_bits - 8 << 4) << 8;
	        a2 |= (2 <= n2.strategy || n2.level < 2 ? 0 : n2.level < 6 ? 1 : 6 === n2.level ? 2 : 3) << 6, 0 !== n2.strstart && (a2 |= 32), a2 += 31 - a2 % 31, n2.status = E, P(n2, a2), 0 !== n2.strstart && (P(n2, e2.adler >>> 16), P(n2, 65535 & e2.adler)), e2.adler = 1;
	      }
	      if (69 === n2.status) if (n2.gzhead.extra) {
	        for (i2 = n2.pending; n2.gzindex < (65535 & n2.gzhead.extra.length) && (n2.pending !== n2.pending_buf_size || (n2.gzhead.hcrc && n2.pending > i2 && (e2.adler = p(e2.adler, n2.pending_buf, n2.pending - i2, i2)), F(e2), i2 = n2.pending, n2.pending !== n2.pending_buf_size)); ) U(n2, 255 & n2.gzhead.extra[n2.gzindex]), n2.gzindex++;
	        n2.gzhead.hcrc && n2.pending > i2 && (e2.adler = p(e2.adler, n2.pending_buf, n2.pending - i2, i2)), n2.gzindex === n2.gzhead.extra.length && (n2.gzindex = 0, n2.status = 73);
	      } else n2.status = 73;
	      if (73 === n2.status) if (n2.gzhead.name) {
	        i2 = n2.pending;
	        do {
	          if (n2.pending === n2.pending_buf_size && (n2.gzhead.hcrc && n2.pending > i2 && (e2.adler = p(e2.adler, n2.pending_buf, n2.pending - i2, i2)), F(e2), i2 = n2.pending, n2.pending === n2.pending_buf_size)) {
	            s2 = 1;
	            break;
	          }
	          s2 = n2.gzindex < n2.gzhead.name.length ? 255 & n2.gzhead.name.charCodeAt(n2.gzindex++) : 0, U(n2, s2);
	        } while (0 !== s2);
	        n2.gzhead.hcrc && n2.pending > i2 && (e2.adler = p(e2.adler, n2.pending_buf, n2.pending - i2, i2)), 0 === s2 && (n2.gzindex = 0, n2.status = 91);
	      } else n2.status = 91;
	      if (91 === n2.status) if (n2.gzhead.comment) {
	        i2 = n2.pending;
	        do {
	          if (n2.pending === n2.pending_buf_size && (n2.gzhead.hcrc && n2.pending > i2 && (e2.adler = p(e2.adler, n2.pending_buf, n2.pending - i2, i2)), F(e2), i2 = n2.pending, n2.pending === n2.pending_buf_size)) {
	            s2 = 1;
	            break;
	          }
	          s2 = n2.gzindex < n2.gzhead.comment.length ? 255 & n2.gzhead.comment.charCodeAt(n2.gzindex++) : 0, U(n2, s2);
	        } while (0 !== s2);
	        n2.gzhead.hcrc && n2.pending > i2 && (e2.adler = p(e2.adler, n2.pending_buf, n2.pending - i2, i2)), 0 === s2 && (n2.status = 103);
	      } else n2.status = 103;
	      if (103 === n2.status && (n2.gzhead.hcrc ? (n2.pending + 2 > n2.pending_buf_size && F(e2), n2.pending + 2 <= n2.pending_buf_size && (U(n2, 255 & e2.adler), U(n2, e2.adler >> 8 & 255), e2.adler = 0, n2.status = E)) : n2.status = E), 0 !== n2.pending) {
	        if (F(e2), 0 === e2.avail_out) return n2.last_flush = -1, m;
	      } else if (0 === e2.avail_in && T(t2) <= T(r2) && t2 !== f) return R(e2, -5);
	      if (666 === n2.status && 0 !== e2.avail_in) return R(e2, -5);
	      if (0 !== e2.avail_in || 0 !== n2.lookahead || t2 !== l && 666 !== n2.status) {
	        var o2 = 2 === n2.strategy ? function(e3, t3) {
	          for (var r3; ; ) {
	            if (0 === e3.lookahead && (j(e3), 0 === e3.lookahead)) {
	              if (t3 === l) return A;
	              break;
	            }
	            if (e3.match_length = 0, r3 = u._tr_tally(e3, 0, e3.window[e3.strstart]), e3.lookahead--, e3.strstart++, r3 && (N(e3, false), 0 === e3.strm.avail_out)) return A;
	          }
	          return e3.insert = 0, t3 === f ? (N(e3, true), 0 === e3.strm.avail_out ? O : B) : e3.last_lit && (N(e3, false), 0 === e3.strm.avail_out) ? A : I;
	        }(n2, t2) : 3 === n2.strategy ? function(e3, t3) {
	          for (var r3, n3, i3, s3, a3 = e3.window; ; ) {
	            if (e3.lookahead <= S) {
	              if (j(e3), e3.lookahead <= S && t3 === l) return A;
	              if (0 === e3.lookahead) break;
	            }
	            if (e3.match_length = 0, e3.lookahead >= x && 0 < e3.strstart && (n3 = a3[i3 = e3.strstart - 1]) === a3[++i3] && n3 === a3[++i3] && n3 === a3[++i3]) {
	              s3 = e3.strstart + S;
	              do {
	              } while (n3 === a3[++i3] && n3 === a3[++i3] && n3 === a3[++i3] && n3 === a3[++i3] && n3 === a3[++i3] && n3 === a3[++i3] && n3 === a3[++i3] && n3 === a3[++i3] && i3 < s3);
	              e3.match_length = S - (s3 - i3), e3.match_length > e3.lookahead && (e3.match_length = e3.lookahead);
	            }
	            if (e3.match_length >= x ? (r3 = u._tr_tally(e3, 1, e3.match_length - x), e3.lookahead -= e3.match_length, e3.strstart += e3.match_length, e3.match_length = 0) : (r3 = u._tr_tally(e3, 0, e3.window[e3.strstart]), e3.lookahead--, e3.strstart++), r3 && (N(e3, false), 0 === e3.strm.avail_out)) return A;
	          }
	          return e3.insert = 0, t3 === f ? (N(e3, true), 0 === e3.strm.avail_out ? O : B) : e3.last_lit && (N(e3, false), 0 === e3.strm.avail_out) ? A : I;
	        }(n2, t2) : h[n2.level].func(n2, t2);
	        if (o2 !== O && o2 !== B || (n2.status = 666), o2 === A || o2 === O) return 0 === e2.avail_out && (n2.last_flush = -1), m;
	        if (o2 === I && (1 === t2 ? u._tr_align(n2) : 5 !== t2 && (u._tr_stored_block(n2, 0, 0, false), 3 === t2 && (D(n2.head), 0 === n2.lookahead && (n2.strstart = 0, n2.block_start = 0, n2.insert = 0))), F(e2), 0 === e2.avail_out)) return n2.last_flush = -1, m;
	      }
	      return t2 !== f ? m : n2.wrap <= 0 ? 1 : (2 === n2.wrap ? (U(n2, 255 & e2.adler), U(n2, e2.adler >> 8 & 255), U(n2, e2.adler >> 16 & 255), U(n2, e2.adler >> 24 & 255), U(n2, 255 & e2.total_in), U(n2, e2.total_in >> 8 & 255), U(n2, e2.total_in >> 16 & 255), U(n2, e2.total_in >> 24 & 255)) : (P(n2, e2.adler >>> 16), P(n2, 65535 & e2.adler)), F(e2), 0 < n2.wrap && (n2.wrap = -n2.wrap), 0 !== n2.pending ? m : 1);
	    }, r.deflateEnd = function(e2) {
	      var t2;
	      return e2 && e2.state ? (t2 = e2.state.status) !== C && 69 !== t2 && 73 !== t2 && 91 !== t2 && 103 !== t2 && t2 !== E && 666 !== t2 ? R(e2, _) : (e2.state = null, t2 === E ? R(e2, -3) : m) : _;
	    }, r.deflateSetDictionary = function(e2, t2) {
	      var r2, n2, i2, s2, a2, o2, h2, u2, l2 = t2.length;
	      if (!e2 || !e2.state) return _;
	      if (2 === (s2 = (r2 = e2.state).wrap) || 1 === s2 && r2.status !== C || r2.lookahead) return _;
	      for (1 === s2 && (e2.adler = d(e2.adler, t2, l2, 0)), r2.wrap = 0, l2 >= r2.w_size && (0 === s2 && (D(r2.head), r2.strstart = 0, r2.block_start = 0, r2.insert = 0), u2 = new c.Buf8(r2.w_size), c.arraySet(u2, t2, l2 - r2.w_size, r2.w_size, 0), t2 = u2, l2 = r2.w_size), a2 = e2.avail_in, o2 = e2.next_in, h2 = e2.input, e2.avail_in = l2, e2.next_in = 0, e2.input = t2, j(r2); r2.lookahead >= x; ) {
	        for (n2 = r2.strstart, i2 = r2.lookahead - (x - 1); r2.ins_h = (r2.ins_h << r2.hash_shift ^ r2.window[n2 + x - 1]) & r2.hash_mask, r2.prev[n2 & r2.w_mask] = r2.head[r2.ins_h], r2.head[r2.ins_h] = n2, n2++, --i2; ) ;
	        r2.strstart = n2, r2.lookahead = x - 1, j(r2);
	      }
	      return r2.strstart += r2.lookahead, r2.block_start = r2.strstart, r2.insert = r2.lookahead, r2.lookahead = 0, r2.match_length = r2.prev_length = x - 1, r2.match_available = 0, e2.next_in = o2, e2.input = h2, e2.avail_in = a2, r2.wrap = s2, m;
	    }, r.deflateInfo = "pako deflate (from Nodeca project)";
	  }, { "../utils/common": 41, "./adler32": 43, "./crc32": 45, "./messages": 51, "./trees": 52 }], 47: [function(e, t, r) {
	    t.exports = function() {
	      this.text = 0, this.time = 0, this.xflags = 0, this.os = 0, this.extra = null, this.extra_len = 0, this.name = "", this.comment = "", this.hcrc = 0, this.done = false;
	    };
	  }, {}], 48: [function(e, t, r) {
	    t.exports = function(e2, t2) {
	      var r2, n, i, s, a, o, h, u, l, f, c, d, p, m, _, g, b, v, y, w, k, x, S, z, C;
	      r2 = e2.state, n = e2.next_in, z = e2.input, i = n + (e2.avail_in - 5), s = e2.next_out, C = e2.output, a = s - (t2 - e2.avail_out), o = s + (e2.avail_out - 257), h = r2.dmax, u = r2.wsize, l = r2.whave, f = r2.wnext, c = r2.window, d = r2.hold, p = r2.bits, m = r2.lencode, _ = r2.distcode, g = (1 << r2.lenbits) - 1, b = (1 << r2.distbits) - 1;
	      e: do {
	        p < 15 && (d += z[n++] << p, p += 8, d += z[n++] << p, p += 8), v = m[d & g];
	        t: for (; ; ) {
	          if (d >>>= y = v >>> 24, p -= y, 0 === (y = v >>> 16 & 255)) C[s++] = 65535 & v;
	          else {
	            if (!(16 & y)) {
	              if (0 == (64 & y)) {
	                v = m[(65535 & v) + (d & (1 << y) - 1)];
	                continue t;
	              }
	              if (32 & y) {
	                r2.mode = 12;
	                break e;
	              }
	              e2.msg = "invalid literal/length code", r2.mode = 30;
	              break e;
	            }
	            w = 65535 & v, (y &= 15) && (p < y && (d += z[n++] << p, p += 8), w += d & (1 << y) - 1, d >>>= y, p -= y), p < 15 && (d += z[n++] << p, p += 8, d += z[n++] << p, p += 8), v = _[d & b];
	            r: for (; ; ) {
	              if (d >>>= y = v >>> 24, p -= y, !(16 & (y = v >>> 16 & 255))) {
	                if (0 == (64 & y)) {
	                  v = _[(65535 & v) + (d & (1 << y) - 1)];
	                  continue r;
	                }
	                e2.msg = "invalid distance code", r2.mode = 30;
	                break e;
	              }
	              if (k = 65535 & v, p < (y &= 15) && (d += z[n++] << p, (p += 8) < y && (d += z[n++] << p, p += 8)), h < (k += d & (1 << y) - 1)) {
	                e2.msg = "invalid distance too far back", r2.mode = 30;
	                break e;
	              }
	              if (d >>>= y, p -= y, (y = s - a) < k) {
	                if (l < (y = k - y) && r2.sane) {
	                  e2.msg = "invalid distance too far back", r2.mode = 30;
	                  break e;
	                }
	                if (S = c, (x = 0) === f) {
	                  if (x += u - y, y < w) {
	                    for (w -= y; C[s++] = c[x++], --y; ) ;
	                    x = s - k, S = C;
	                  }
	                } else if (f < y) {
	                  if (x += u + f - y, (y -= f) < w) {
	                    for (w -= y; C[s++] = c[x++], --y; ) ;
	                    if (x = 0, f < w) {
	                      for (w -= y = f; C[s++] = c[x++], --y; ) ;
	                      x = s - k, S = C;
	                    }
	                  }
	                } else if (x += f - y, y < w) {
	                  for (w -= y; C[s++] = c[x++], --y; ) ;
	                  x = s - k, S = C;
	                }
	                for (; 2 < w; ) C[s++] = S[x++], C[s++] = S[x++], C[s++] = S[x++], w -= 3;
	                w && (C[s++] = S[x++], 1 < w && (C[s++] = S[x++]));
	              } else {
	                for (x = s - k; C[s++] = C[x++], C[s++] = C[x++], C[s++] = C[x++], 2 < (w -= 3); ) ;
	                w && (C[s++] = C[x++], 1 < w && (C[s++] = C[x++]));
	              }
	              break;
	            }
	          }
	          break;
	        }
	      } while (n < i && s < o);
	      n -= w = p >> 3, d &= (1 << (p -= w << 3)) - 1, e2.next_in = n, e2.next_out = s, e2.avail_in = n < i ? i - n + 5 : 5 - (n - i), e2.avail_out = s < o ? o - s + 257 : 257 - (s - o), r2.hold = d, r2.bits = p;
	    };
	  }, {}], 49: [function(e, t, r) {
	    var I = e("../utils/common"), O = e("./adler32"), B = e("./crc32"), R = e("./inffast"), T = e("./inftrees"), D = 1, F = 2, N = 0, U = -2, P = 1, n = 852, i = 592;
	    function L(e2) {
	      return (e2 >>> 24 & 255) + (e2 >>> 8 & 65280) + ((65280 & e2) << 8) + ((255 & e2) << 24);
	    }
	    function s() {
	      this.mode = 0, this.last = false, this.wrap = 0, this.havedict = false, this.flags = 0, this.dmax = 0, this.check = 0, this.total = 0, this.head = null, this.wbits = 0, this.wsize = 0, this.whave = 0, this.wnext = 0, this.window = null, this.hold = 0, this.bits = 0, this.length = 0, this.offset = 0, this.extra = 0, this.lencode = null, this.distcode = null, this.lenbits = 0, this.distbits = 0, this.ncode = 0, this.nlen = 0, this.ndist = 0, this.have = 0, this.next = null, this.lens = new I.Buf16(320), this.work = new I.Buf16(288), this.lendyn = null, this.distdyn = null, this.sane = 0, this.back = 0, this.was = 0;
	    }
	    function a(e2) {
	      var t2;
	      return e2 && e2.state ? (t2 = e2.state, e2.total_in = e2.total_out = t2.total = 0, e2.msg = "", t2.wrap && (e2.adler = 1 & t2.wrap), t2.mode = P, t2.last = 0, t2.havedict = 0, t2.dmax = 32768, t2.head = null, t2.hold = 0, t2.bits = 0, t2.lencode = t2.lendyn = new I.Buf32(n), t2.distcode = t2.distdyn = new I.Buf32(i), t2.sane = 1, t2.back = -1, N) : U;
	    }
	    function o(e2) {
	      var t2;
	      return e2 && e2.state ? ((t2 = e2.state).wsize = 0, t2.whave = 0, t2.wnext = 0, a(e2)) : U;
	    }
	    function h(e2, t2) {
	      var r2, n2;
	      return e2 && e2.state ? (n2 = e2.state, t2 < 0 ? (r2 = 0, t2 = -t2) : (r2 = 1 + (t2 >> 4), t2 < 48 && (t2 &= 15)), t2 && (t2 < 8 || 15 < t2) ? U : (null !== n2.window && n2.wbits !== t2 && (n2.window = null), n2.wrap = r2, n2.wbits = t2, o(e2))) : U;
	    }
	    function u(e2, t2) {
	      var r2, n2;
	      return e2 ? (n2 = new s(), (e2.state = n2).window = null, (r2 = h(e2, t2)) !== N && (e2.state = null), r2) : U;
	    }
	    var l, f, c = true;
	    function j(e2) {
	      if (c) {
	        var t2;
	        for (l = new I.Buf32(512), f = new I.Buf32(32), t2 = 0; t2 < 144; ) e2.lens[t2++] = 8;
	        for (; t2 < 256; ) e2.lens[t2++] = 9;
	        for (; t2 < 280; ) e2.lens[t2++] = 7;
	        for (; t2 < 288; ) e2.lens[t2++] = 8;
	        for (T(D, e2.lens, 0, 288, l, 0, e2.work, { bits: 9 }), t2 = 0; t2 < 32; ) e2.lens[t2++] = 5;
	        T(F, e2.lens, 0, 32, f, 0, e2.work, { bits: 5 }), c = false;
	      }
	      e2.lencode = l, e2.lenbits = 9, e2.distcode = f, e2.distbits = 5;
	    }
	    function Z(e2, t2, r2, n2) {
	      var i2, s2 = e2.state;
	      return null === s2.window && (s2.wsize = 1 << s2.wbits, s2.wnext = 0, s2.whave = 0, s2.window = new I.Buf8(s2.wsize)), n2 >= s2.wsize ? (I.arraySet(s2.window, t2, r2 - s2.wsize, s2.wsize, 0), s2.wnext = 0, s2.whave = s2.wsize) : (n2 < (i2 = s2.wsize - s2.wnext) && (i2 = n2), I.arraySet(s2.window, t2, r2 - n2, i2, s2.wnext), (n2 -= i2) ? (I.arraySet(s2.window, t2, r2 - n2, n2, 0), s2.wnext = n2, s2.whave = s2.wsize) : (s2.wnext += i2, s2.wnext === s2.wsize && (s2.wnext = 0), s2.whave < s2.wsize && (s2.whave += i2))), 0;
	    }
	    r.inflateReset = o, r.inflateReset2 = h, r.inflateResetKeep = a, r.inflateInit = function(e2) {
	      return u(e2, 15);
	    }, r.inflateInit2 = u, r.inflate = function(e2, t2) {
	      var r2, n2, i2, s2, a2, o2, h2, u2, l2, f2, c2, d, p, m, _, g, b, v, y, w, k, x, S, z, C = 0, E = new I.Buf8(4), A = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
	      if (!e2 || !e2.state || !e2.output || !e2.input && 0 !== e2.avail_in) return U;
	      12 === (r2 = e2.state).mode && (r2.mode = 13), a2 = e2.next_out, i2 = e2.output, h2 = e2.avail_out, s2 = e2.next_in, n2 = e2.input, o2 = e2.avail_in, u2 = r2.hold, l2 = r2.bits, f2 = o2, c2 = h2, x = N;
	      e: for (; ; ) switch (r2.mode) {
	        case P:
	          if (0 === r2.wrap) {
	            r2.mode = 13;
	            break;
	          }
	          for (; l2 < 16; ) {
	            if (0 === o2) break e;
	            o2--, u2 += n2[s2++] << l2, l2 += 8;
	          }
	          if (2 & r2.wrap && 35615 === u2) {
	            E[r2.check = 0] = 255 & u2, E[1] = u2 >>> 8 & 255, r2.check = B(r2.check, E, 2, 0), l2 = u2 = 0, r2.mode = 2;
	            break;
	          }
	          if (r2.flags = 0, r2.head && (r2.head.done = false), !(1 & r2.wrap) || (((255 & u2) << 8) + (u2 >> 8)) % 31) {
	            e2.msg = "incorrect header check", r2.mode = 30;
	            break;
	          }
	          if (8 != (15 & u2)) {
	            e2.msg = "unknown compression method", r2.mode = 30;
	            break;
	          }
	          if (l2 -= 4, k = 8 + (15 & (u2 >>>= 4)), 0 === r2.wbits) r2.wbits = k;
	          else if (k > r2.wbits) {
	            e2.msg = "invalid window size", r2.mode = 30;
	            break;
	          }
	          r2.dmax = 1 << k, e2.adler = r2.check = 1, r2.mode = 512 & u2 ? 10 : 12, l2 = u2 = 0;
	          break;
	        case 2:
	          for (; l2 < 16; ) {
	            if (0 === o2) break e;
	            o2--, u2 += n2[s2++] << l2, l2 += 8;
	          }
	          if (r2.flags = u2, 8 != (255 & r2.flags)) {
	            e2.msg = "unknown compression method", r2.mode = 30;
	            break;
	          }
	          if (57344 & r2.flags) {
	            e2.msg = "unknown header flags set", r2.mode = 30;
	            break;
	          }
	          r2.head && (r2.head.text = u2 >> 8 & 1), 512 & r2.flags && (E[0] = 255 & u2, E[1] = u2 >>> 8 & 255, r2.check = B(r2.check, E, 2, 0)), l2 = u2 = 0, r2.mode = 3;
	        case 3:
	          for (; l2 < 32; ) {
	            if (0 === o2) break e;
	            o2--, u2 += n2[s2++] << l2, l2 += 8;
	          }
	          r2.head && (r2.head.time = u2), 512 & r2.flags && (E[0] = 255 & u2, E[1] = u2 >>> 8 & 255, E[2] = u2 >>> 16 & 255, E[3] = u2 >>> 24 & 255, r2.check = B(r2.check, E, 4, 0)), l2 = u2 = 0, r2.mode = 4;
	        case 4:
	          for (; l2 < 16; ) {
	            if (0 === o2) break e;
	            o2--, u2 += n2[s2++] << l2, l2 += 8;
	          }
	          r2.head && (r2.head.xflags = 255 & u2, r2.head.os = u2 >> 8), 512 & r2.flags && (E[0] = 255 & u2, E[1] = u2 >>> 8 & 255, r2.check = B(r2.check, E, 2, 0)), l2 = u2 = 0, r2.mode = 5;
	        case 5:
	          if (1024 & r2.flags) {
	            for (; l2 < 16; ) {
	              if (0 === o2) break e;
	              o2--, u2 += n2[s2++] << l2, l2 += 8;
	            }
	            r2.length = u2, r2.head && (r2.head.extra_len = u2), 512 & r2.flags && (E[0] = 255 & u2, E[1] = u2 >>> 8 & 255, r2.check = B(r2.check, E, 2, 0)), l2 = u2 = 0;
	          } else r2.head && (r2.head.extra = null);
	          r2.mode = 6;
	        case 6:
	          if (1024 & r2.flags && (o2 < (d = r2.length) && (d = o2), d && (r2.head && (k = r2.head.extra_len - r2.length, r2.head.extra || (r2.head.extra = new Array(r2.head.extra_len)), I.arraySet(r2.head.extra, n2, s2, d, k)), 512 & r2.flags && (r2.check = B(r2.check, n2, d, s2)), o2 -= d, s2 += d, r2.length -= d), r2.length)) break e;
	          r2.length = 0, r2.mode = 7;
	        case 7:
	          if (2048 & r2.flags) {
	            if (0 === o2) break e;
	            for (d = 0; k = n2[s2 + d++], r2.head && k && r2.length < 65536 && (r2.head.name += String.fromCharCode(k)), k && d < o2; ) ;
	            if (512 & r2.flags && (r2.check = B(r2.check, n2, d, s2)), o2 -= d, s2 += d, k) break e;
	          } else r2.head && (r2.head.name = null);
	          r2.length = 0, r2.mode = 8;
	        case 8:
	          if (4096 & r2.flags) {
	            if (0 === o2) break e;
	            for (d = 0; k = n2[s2 + d++], r2.head && k && r2.length < 65536 && (r2.head.comment += String.fromCharCode(k)), k && d < o2; ) ;
	            if (512 & r2.flags && (r2.check = B(r2.check, n2, d, s2)), o2 -= d, s2 += d, k) break e;
	          } else r2.head && (r2.head.comment = null);
	          r2.mode = 9;
	        case 9:
	          if (512 & r2.flags) {
	            for (; l2 < 16; ) {
	              if (0 === o2) break e;
	              o2--, u2 += n2[s2++] << l2, l2 += 8;
	            }
	            if (u2 !== (65535 & r2.check)) {
	              e2.msg = "header crc mismatch", r2.mode = 30;
	              break;
	            }
	            l2 = u2 = 0;
	          }
	          r2.head && (r2.head.hcrc = r2.flags >> 9 & 1, r2.head.done = true), e2.adler = r2.check = 0, r2.mode = 12;
	          break;
	        case 10:
	          for (; l2 < 32; ) {
	            if (0 === o2) break e;
	            o2--, u2 += n2[s2++] << l2, l2 += 8;
	          }
	          e2.adler = r2.check = L(u2), l2 = u2 = 0, r2.mode = 11;
	        case 11:
	          if (0 === r2.havedict) return e2.next_out = a2, e2.avail_out = h2, e2.next_in = s2, e2.avail_in = o2, r2.hold = u2, r2.bits = l2, 2;
	          e2.adler = r2.check = 1, r2.mode = 12;
	        case 12:
	          if (5 === t2 || 6 === t2) break e;
	        case 13:
	          if (r2.last) {
	            u2 >>>= 7 & l2, l2 -= 7 & l2, r2.mode = 27;
	            break;
	          }
	          for (; l2 < 3; ) {
	            if (0 === o2) break e;
	            o2--, u2 += n2[s2++] << l2, l2 += 8;
	          }
	          switch (r2.last = 1 & u2, l2 -= 1, 3 & (u2 >>>= 1)) {
	            case 0:
	              r2.mode = 14;
	              break;
	            case 1:
	              if (j(r2), r2.mode = 20, 6 !== t2) break;
	              u2 >>>= 2, l2 -= 2;
	              break e;
	            case 2:
	              r2.mode = 17;
	              break;
	            case 3:
	              e2.msg = "invalid block type", r2.mode = 30;
	          }
	          u2 >>>= 2, l2 -= 2;
	          break;
	        case 14:
	          for (u2 >>>= 7 & l2, l2 -= 7 & l2; l2 < 32; ) {
	            if (0 === o2) break e;
	            o2--, u2 += n2[s2++] << l2, l2 += 8;
	          }
	          if ((65535 & u2) != (u2 >>> 16 ^ 65535)) {
	            e2.msg = "invalid stored block lengths", r2.mode = 30;
	            break;
	          }
	          if (r2.length = 65535 & u2, l2 = u2 = 0, r2.mode = 15, 6 === t2) break e;
	        case 15:
	          r2.mode = 16;
	        case 16:
	          if (d = r2.length) {
	            if (o2 < d && (d = o2), h2 < d && (d = h2), 0 === d) break e;
	            I.arraySet(i2, n2, s2, d, a2), o2 -= d, s2 += d, h2 -= d, a2 += d, r2.length -= d;
	            break;
	          }
	          r2.mode = 12;
	          break;
	        case 17:
	          for (; l2 < 14; ) {
	            if (0 === o2) break e;
	            o2--, u2 += n2[s2++] << l2, l2 += 8;
	          }
	          if (r2.nlen = 257 + (31 & u2), u2 >>>= 5, l2 -= 5, r2.ndist = 1 + (31 & u2), u2 >>>= 5, l2 -= 5, r2.ncode = 4 + (15 & u2), u2 >>>= 4, l2 -= 4, 286 < r2.nlen || 30 < r2.ndist) {
	            e2.msg = "too many length or distance symbols", r2.mode = 30;
	            break;
	          }
	          r2.have = 0, r2.mode = 18;
	        case 18:
	          for (; r2.have < r2.ncode; ) {
	            for (; l2 < 3; ) {
	              if (0 === o2) break e;
	              o2--, u2 += n2[s2++] << l2, l2 += 8;
	            }
	            r2.lens[A[r2.have++]] = 7 & u2, u2 >>>= 3, l2 -= 3;
	          }
	          for (; r2.have < 19; ) r2.lens[A[r2.have++]] = 0;
	          if (r2.lencode = r2.lendyn, r2.lenbits = 7, S = { bits: r2.lenbits }, x = T(0, r2.lens, 0, 19, r2.lencode, 0, r2.work, S), r2.lenbits = S.bits, x) {
	            e2.msg = "invalid code lengths set", r2.mode = 30;
	            break;
	          }
	          r2.have = 0, r2.mode = 19;
	        case 19:
	          for (; r2.have < r2.nlen + r2.ndist; ) {
	            for (; g = (C = r2.lencode[u2 & (1 << r2.lenbits) - 1]) >>> 16 & 255, b = 65535 & C, !((_ = C >>> 24) <= l2); ) {
	              if (0 === o2) break e;
	              o2--, u2 += n2[s2++] << l2, l2 += 8;
	            }
	            if (b < 16) u2 >>>= _, l2 -= _, r2.lens[r2.have++] = b;
	            else {
	              if (16 === b) {
	                for (z = _ + 2; l2 < z; ) {
	                  if (0 === o2) break e;
	                  o2--, u2 += n2[s2++] << l2, l2 += 8;
	                }
	                if (u2 >>>= _, l2 -= _, 0 === r2.have) {
	                  e2.msg = "invalid bit length repeat", r2.mode = 30;
	                  break;
	                }
	                k = r2.lens[r2.have - 1], d = 3 + (3 & u2), u2 >>>= 2, l2 -= 2;
	              } else if (17 === b) {
	                for (z = _ + 3; l2 < z; ) {
	                  if (0 === o2) break e;
	                  o2--, u2 += n2[s2++] << l2, l2 += 8;
	                }
	                l2 -= _, k = 0, d = 3 + (7 & (u2 >>>= _)), u2 >>>= 3, l2 -= 3;
	              } else {
	                for (z = _ + 7; l2 < z; ) {
	                  if (0 === o2) break e;
	                  o2--, u2 += n2[s2++] << l2, l2 += 8;
	                }
	                l2 -= _, k = 0, d = 11 + (127 & (u2 >>>= _)), u2 >>>= 7, l2 -= 7;
	              }
	              if (r2.have + d > r2.nlen + r2.ndist) {
	                e2.msg = "invalid bit length repeat", r2.mode = 30;
	                break;
	              }
	              for (; d--; ) r2.lens[r2.have++] = k;
	            }
	          }
	          if (30 === r2.mode) break;
	          if (0 === r2.lens[256]) {
	            e2.msg = "invalid code -- missing end-of-block", r2.mode = 30;
	            break;
	          }
	          if (r2.lenbits = 9, S = { bits: r2.lenbits }, x = T(D, r2.lens, 0, r2.nlen, r2.lencode, 0, r2.work, S), r2.lenbits = S.bits, x) {
	            e2.msg = "invalid literal/lengths set", r2.mode = 30;
	            break;
	          }
	          if (r2.distbits = 6, r2.distcode = r2.distdyn, S = { bits: r2.distbits }, x = T(F, r2.lens, r2.nlen, r2.ndist, r2.distcode, 0, r2.work, S), r2.distbits = S.bits, x) {
	            e2.msg = "invalid distances set", r2.mode = 30;
	            break;
	          }
	          if (r2.mode = 20, 6 === t2) break e;
	        case 20:
	          r2.mode = 21;
	        case 21:
	          if (6 <= o2 && 258 <= h2) {
	            e2.next_out = a2, e2.avail_out = h2, e2.next_in = s2, e2.avail_in = o2, r2.hold = u2, r2.bits = l2, R(e2, c2), a2 = e2.next_out, i2 = e2.output, h2 = e2.avail_out, s2 = e2.next_in, n2 = e2.input, o2 = e2.avail_in, u2 = r2.hold, l2 = r2.bits, 12 === r2.mode && (r2.back = -1);
	            break;
	          }
	          for (r2.back = 0; g = (C = r2.lencode[u2 & (1 << r2.lenbits) - 1]) >>> 16 & 255, b = 65535 & C, !((_ = C >>> 24) <= l2); ) {
	            if (0 === o2) break e;
	            o2--, u2 += n2[s2++] << l2, l2 += 8;
	          }
	          if (g && 0 == (240 & g)) {
	            for (v = _, y = g, w = b; g = (C = r2.lencode[w + ((u2 & (1 << v + y) - 1) >> v)]) >>> 16 & 255, b = 65535 & C, !(v + (_ = C >>> 24) <= l2); ) {
	              if (0 === o2) break e;
	              o2--, u2 += n2[s2++] << l2, l2 += 8;
	            }
	            u2 >>>= v, l2 -= v, r2.back += v;
	          }
	          if (u2 >>>= _, l2 -= _, r2.back += _, r2.length = b, 0 === g) {
	            r2.mode = 26;
	            break;
	          }
	          if (32 & g) {
	            r2.back = -1, r2.mode = 12;
	            break;
	          }
	          if (64 & g) {
	            e2.msg = "invalid literal/length code", r2.mode = 30;
	            break;
	          }
	          r2.extra = 15 & g, r2.mode = 22;
	        case 22:
	          if (r2.extra) {
	            for (z = r2.extra; l2 < z; ) {
	              if (0 === o2) break e;
	              o2--, u2 += n2[s2++] << l2, l2 += 8;
	            }
	            r2.length += u2 & (1 << r2.extra) - 1, u2 >>>= r2.extra, l2 -= r2.extra, r2.back += r2.extra;
	          }
	          r2.was = r2.length, r2.mode = 23;
	        case 23:
	          for (; g = (C = r2.distcode[u2 & (1 << r2.distbits) - 1]) >>> 16 & 255, b = 65535 & C, !((_ = C >>> 24) <= l2); ) {
	            if (0 === o2) break e;
	            o2--, u2 += n2[s2++] << l2, l2 += 8;
	          }
	          if (0 == (240 & g)) {
	            for (v = _, y = g, w = b; g = (C = r2.distcode[w + ((u2 & (1 << v + y) - 1) >> v)]) >>> 16 & 255, b = 65535 & C, !(v + (_ = C >>> 24) <= l2); ) {
	              if (0 === o2) break e;
	              o2--, u2 += n2[s2++] << l2, l2 += 8;
	            }
	            u2 >>>= v, l2 -= v, r2.back += v;
	          }
	          if (u2 >>>= _, l2 -= _, r2.back += _, 64 & g) {
	            e2.msg = "invalid distance code", r2.mode = 30;
	            break;
	          }
	          r2.offset = b, r2.extra = 15 & g, r2.mode = 24;
	        case 24:
	          if (r2.extra) {
	            for (z = r2.extra; l2 < z; ) {
	              if (0 === o2) break e;
	              o2--, u2 += n2[s2++] << l2, l2 += 8;
	            }
	            r2.offset += u2 & (1 << r2.extra) - 1, u2 >>>= r2.extra, l2 -= r2.extra, r2.back += r2.extra;
	          }
	          if (r2.offset > r2.dmax) {
	            e2.msg = "invalid distance too far back", r2.mode = 30;
	            break;
	          }
	          r2.mode = 25;
	        case 25:
	          if (0 === h2) break e;
	          if (d = c2 - h2, r2.offset > d) {
	            if ((d = r2.offset - d) > r2.whave && r2.sane) {
	              e2.msg = "invalid distance too far back", r2.mode = 30;
	              break;
	            }
	            p = d > r2.wnext ? (d -= r2.wnext, r2.wsize - d) : r2.wnext - d, d > r2.length && (d = r2.length), m = r2.window;
	          } else m = i2, p = a2 - r2.offset, d = r2.length;
	          for (h2 < d && (d = h2), h2 -= d, r2.length -= d; i2[a2++] = m[p++], --d; ) ;
	          0 === r2.length && (r2.mode = 21);
	          break;
	        case 26:
	          if (0 === h2) break e;
	          i2[a2++] = r2.length, h2--, r2.mode = 21;
	          break;
	        case 27:
	          if (r2.wrap) {
	            for (; l2 < 32; ) {
	              if (0 === o2) break e;
	              o2--, u2 |= n2[s2++] << l2, l2 += 8;
	            }
	            if (c2 -= h2, e2.total_out += c2, r2.total += c2, c2 && (e2.adler = r2.check = r2.flags ? B(r2.check, i2, c2, a2 - c2) : O(r2.check, i2, c2, a2 - c2)), c2 = h2, (r2.flags ? u2 : L(u2)) !== r2.check) {
	              e2.msg = "incorrect data check", r2.mode = 30;
	              break;
	            }
	            l2 = u2 = 0;
	          }
	          r2.mode = 28;
	        case 28:
	          if (r2.wrap && r2.flags) {
	            for (; l2 < 32; ) {
	              if (0 === o2) break e;
	              o2--, u2 += n2[s2++] << l2, l2 += 8;
	            }
	            if (u2 !== (4294967295 & r2.total)) {
	              e2.msg = "incorrect length check", r2.mode = 30;
	              break;
	            }
	            l2 = u2 = 0;
	          }
	          r2.mode = 29;
	        case 29:
	          x = 1;
	          break e;
	        case 30:
	          x = -3;
	          break e;
	        case 31:
	          return -4;
	        case 32:
	        default:
	          return U;
	      }
	      return e2.next_out = a2, e2.avail_out = h2, e2.next_in = s2, e2.avail_in = o2, r2.hold = u2, r2.bits = l2, (r2.wsize || c2 !== e2.avail_out && r2.mode < 30 && (r2.mode < 27 || 4 !== t2)) && Z(e2, e2.output, e2.next_out, c2 - e2.avail_out) ? (r2.mode = 31, -4) : (f2 -= e2.avail_in, c2 -= e2.avail_out, e2.total_in += f2, e2.total_out += c2, r2.total += c2, r2.wrap && c2 && (e2.adler = r2.check = r2.flags ? B(r2.check, i2, c2, e2.next_out - c2) : O(r2.check, i2, c2, e2.next_out - c2)), e2.data_type = r2.bits + (r2.last ? 64 : 0) + (12 === r2.mode ? 128 : 0) + (20 === r2.mode || 15 === r2.mode ? 256 : 0), (0 == f2 && 0 === c2 || 4 === t2) && x === N && (x = -5), x);
	    }, r.inflateEnd = function(e2) {
	      if (!e2 || !e2.state) return U;
	      var t2 = e2.state;
	      return t2.window && (t2.window = null), e2.state = null, N;
	    }, r.inflateGetHeader = function(e2, t2) {
	      var r2;
	      return e2 && e2.state ? 0 == (2 & (r2 = e2.state).wrap) ? U : ((r2.head = t2).done = false, N) : U;
	    }, r.inflateSetDictionary = function(e2, t2) {
	      var r2, n2 = t2.length;
	      return e2 && e2.state ? 0 !== (r2 = e2.state).wrap && 11 !== r2.mode ? U : 11 === r2.mode && O(1, t2, n2, 0) !== r2.check ? -3 : Z(e2, t2, n2, n2) ? (r2.mode = 31, -4) : (r2.havedict = 1, N) : U;
	    }, r.inflateInfo = "pako inflate (from Nodeca project)";
	  }, { "../utils/common": 41, "./adler32": 43, "./crc32": 45, "./inffast": 48, "./inftrees": 50 }], 50: [function(e, t, r) {
	    var D = e("../utils/common"), F = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258, 0, 0], N = [16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 20, 20, 20, 20, 21, 21, 21, 21, 16, 72, 78], U = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577, 0, 0], P = [16, 16, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 21, 21, 22, 22, 23, 23, 24, 24, 25, 25, 26, 26, 27, 27, 28, 28, 29, 29, 64, 64];
	    t.exports = function(e2, t2, r2, n, i, s, a, o) {
	      var h, u, l, f, c, d, p, m, _, g = o.bits, b = 0, v = 0, y = 0, w = 0, k = 0, x = 0, S = 0, z = 0, C = 0, E = 0, A = null, I = 0, O = new D.Buf16(16), B = new D.Buf16(16), R = null, T = 0;
	      for (b = 0; b <= 15; b++) O[b] = 0;
	      for (v = 0; v < n; v++) O[t2[r2 + v]]++;
	      for (k = g, w = 15; 1 <= w && 0 === O[w]; w--) ;
	      if (w < k && (k = w), 0 === w) return i[s++] = 20971520, i[s++] = 20971520, o.bits = 1, 0;
	      for (y = 1; y < w && 0 === O[y]; y++) ;
	      for (k < y && (k = y), b = z = 1; b <= 15; b++) if (z <<= 1, (z -= O[b]) < 0) return -1;
	      if (0 < z && (0 === e2 || 1 !== w)) return -1;
	      for (B[1] = 0, b = 1; b < 15; b++) B[b + 1] = B[b] + O[b];
	      for (v = 0; v < n; v++) 0 !== t2[r2 + v] && (a[B[t2[r2 + v]]++] = v);
	      if (d = 0 === e2 ? (A = R = a, 19) : 1 === e2 ? (A = F, I -= 257, R = N, T -= 257, 256) : (A = U, R = P, -1), b = y, c = s, S = v = E = 0, l = -1, f = (C = 1 << (x = k)) - 1, 1 === e2 && 852 < C || 2 === e2 && 592 < C) return 1;
	      for (; ; ) {
	        for (p = b - S, _ = a[v] < d ? (m = 0, a[v]) : a[v] > d ? (m = R[T + a[v]], A[I + a[v]]) : (m = 96, 0), h = 1 << b - S, y = u = 1 << x; i[c + (E >> S) + (u -= h)] = p << 24 | m << 16 | _ | 0, 0 !== u; ) ;
	        for (h = 1 << b - 1; E & h; ) h >>= 1;
	        if (0 !== h ? (E &= h - 1, E += h) : E = 0, v++, 0 == --O[b]) {
	          if (b === w) break;
	          b = t2[r2 + a[v]];
	        }
	        if (k < b && (E & f) !== l) {
	          for (0 === S && (S = k), c += y, z = 1 << (x = b - S); x + S < w && !((z -= O[x + S]) <= 0); ) x++, z <<= 1;
	          if (C += 1 << x, 1 === e2 && 852 < C || 2 === e2 && 592 < C) return 1;
	          i[l = E & f] = k << 24 | x << 16 | c - s | 0;
	        }
	      }
	      return 0 !== E && (i[c + E] = b - S << 24 | 64 << 16 | 0), o.bits = k, 0;
	    };
	  }, { "../utils/common": 41 }], 51: [function(e, t, r) {
	    t.exports = { 2: "need dictionary", 1: "stream end", 0: "", "-1": "file error", "-2": "stream error", "-3": "data error", "-4": "insufficient memory", "-5": "buffer error", "-6": "incompatible version" };
	  }, {}], 52: [function(e, t, r) {
	    var i = e("../utils/common"), o = 0, h = 1;
	    function n(e2) {
	      for (var t2 = e2.length; 0 <= --t2; ) e2[t2] = 0;
	    }
	    var s = 0, a = 29, u = 256, l = u + 1 + a, f = 30, c = 19, _ = 2 * l + 1, g = 15, d = 16, p = 7, m = 256, b = 16, v = 17, y = 18, w = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0], k = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13], x = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 7], S = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15], z = new Array(2 * (l + 2));
	    n(z);
	    var C = new Array(2 * f);
	    n(C);
	    var E = new Array(512);
	    n(E);
	    var A = new Array(256);
	    n(A);
	    var I = new Array(a);
	    n(I);
	    var O, B, R, T = new Array(f);
	    function D(e2, t2, r2, n2, i2) {
	      this.static_tree = e2, this.extra_bits = t2, this.extra_base = r2, this.elems = n2, this.max_length = i2, this.has_stree = e2 && e2.length;
	    }
	    function F(e2, t2) {
	      this.dyn_tree = e2, this.max_code = 0, this.stat_desc = t2;
	    }
	    function N(e2) {
	      return e2 < 256 ? E[e2] : E[256 + (e2 >>> 7)];
	    }
	    function U(e2, t2) {
	      e2.pending_buf[e2.pending++] = 255 & t2, e2.pending_buf[e2.pending++] = t2 >>> 8 & 255;
	    }
	    function P(e2, t2, r2) {
	      e2.bi_valid > d - r2 ? (e2.bi_buf |= t2 << e2.bi_valid & 65535, U(e2, e2.bi_buf), e2.bi_buf = t2 >> d - e2.bi_valid, e2.bi_valid += r2 - d) : (e2.bi_buf |= t2 << e2.bi_valid & 65535, e2.bi_valid += r2);
	    }
	    function L(e2, t2, r2) {
	      P(e2, r2[2 * t2], r2[2 * t2 + 1]);
	    }
	    function j(e2, t2) {
	      for (var r2 = 0; r2 |= 1 & e2, e2 >>>= 1, r2 <<= 1, 0 < --t2; ) ;
	      return r2 >>> 1;
	    }
	    function Z(e2, t2, r2) {
	      var n2, i2, s2 = new Array(g + 1), a2 = 0;
	      for (n2 = 1; n2 <= g; n2++) s2[n2] = a2 = a2 + r2[n2 - 1] << 1;
	      for (i2 = 0; i2 <= t2; i2++) {
	        var o2 = e2[2 * i2 + 1];
	        0 !== o2 && (e2[2 * i2] = j(s2[o2]++, o2));
	      }
	    }
	    function W(e2) {
	      var t2;
	      for (t2 = 0; t2 < l; t2++) e2.dyn_ltree[2 * t2] = 0;
	      for (t2 = 0; t2 < f; t2++) e2.dyn_dtree[2 * t2] = 0;
	      for (t2 = 0; t2 < c; t2++) e2.bl_tree[2 * t2] = 0;
	      e2.dyn_ltree[2 * m] = 1, e2.opt_len = e2.static_len = 0, e2.last_lit = e2.matches = 0;
	    }
	    function M(e2) {
	      8 < e2.bi_valid ? U(e2, e2.bi_buf) : 0 < e2.bi_valid && (e2.pending_buf[e2.pending++] = e2.bi_buf), e2.bi_buf = 0, e2.bi_valid = 0;
	    }
	    function H(e2, t2, r2, n2) {
	      var i2 = 2 * t2, s2 = 2 * r2;
	      return e2[i2] < e2[s2] || e2[i2] === e2[s2] && n2[t2] <= n2[r2];
	    }
	    function G(e2, t2, r2) {
	      for (var n2 = e2.heap[r2], i2 = r2 << 1; i2 <= e2.heap_len && (i2 < e2.heap_len && H(t2, e2.heap[i2 + 1], e2.heap[i2], e2.depth) && i2++, !H(t2, n2, e2.heap[i2], e2.depth)); ) e2.heap[r2] = e2.heap[i2], r2 = i2, i2 <<= 1;
	      e2.heap[r2] = n2;
	    }
	    function K(e2, t2, r2) {
	      var n2, i2, s2, a2, o2 = 0;
	      if (0 !== e2.last_lit) for (; n2 = e2.pending_buf[e2.d_buf + 2 * o2] << 8 | e2.pending_buf[e2.d_buf + 2 * o2 + 1], i2 = e2.pending_buf[e2.l_buf + o2], o2++, 0 === n2 ? L(e2, i2, t2) : (L(e2, (s2 = A[i2]) + u + 1, t2), 0 !== (a2 = w[s2]) && P(e2, i2 -= I[s2], a2), L(e2, s2 = N(--n2), r2), 0 !== (a2 = k[s2]) && P(e2, n2 -= T[s2], a2)), o2 < e2.last_lit; ) ;
	      L(e2, m, t2);
	    }
	    function Y(e2, t2) {
	      var r2, n2, i2, s2 = t2.dyn_tree, a2 = t2.stat_desc.static_tree, o2 = t2.stat_desc.has_stree, h2 = t2.stat_desc.elems, u2 = -1;
	      for (e2.heap_len = 0, e2.heap_max = _, r2 = 0; r2 < h2; r2++) 0 !== s2[2 * r2] ? (e2.heap[++e2.heap_len] = u2 = r2, e2.depth[r2] = 0) : s2[2 * r2 + 1] = 0;
	      for (; e2.heap_len < 2; ) s2[2 * (i2 = e2.heap[++e2.heap_len] = u2 < 2 ? ++u2 : 0)] = 1, e2.depth[i2] = 0, e2.opt_len--, o2 && (e2.static_len -= a2[2 * i2 + 1]);
	      for (t2.max_code = u2, r2 = e2.heap_len >> 1; 1 <= r2; r2--) G(e2, s2, r2);
	      for (i2 = h2; r2 = e2.heap[1], e2.heap[1] = e2.heap[e2.heap_len--], G(e2, s2, 1), n2 = e2.heap[1], e2.heap[--e2.heap_max] = r2, e2.heap[--e2.heap_max] = n2, s2[2 * i2] = s2[2 * r2] + s2[2 * n2], e2.depth[i2] = (e2.depth[r2] >= e2.depth[n2] ? e2.depth[r2] : e2.depth[n2]) + 1, s2[2 * r2 + 1] = s2[2 * n2 + 1] = i2, e2.heap[1] = i2++, G(e2, s2, 1), 2 <= e2.heap_len; ) ;
	      e2.heap[--e2.heap_max] = e2.heap[1], function(e3, t3) {
	        var r3, n3, i3, s3, a3, o3, h3 = t3.dyn_tree, u3 = t3.max_code, l2 = t3.stat_desc.static_tree, f2 = t3.stat_desc.has_stree, c2 = t3.stat_desc.extra_bits, d2 = t3.stat_desc.extra_base, p2 = t3.stat_desc.max_length, m2 = 0;
	        for (s3 = 0; s3 <= g; s3++) e3.bl_count[s3] = 0;
	        for (h3[2 * e3.heap[e3.heap_max] + 1] = 0, r3 = e3.heap_max + 1; r3 < _; r3++) p2 < (s3 = h3[2 * h3[2 * (n3 = e3.heap[r3]) + 1] + 1] + 1) && (s3 = p2, m2++), h3[2 * n3 + 1] = s3, u3 < n3 || (e3.bl_count[s3]++, a3 = 0, d2 <= n3 && (a3 = c2[n3 - d2]), o3 = h3[2 * n3], e3.opt_len += o3 * (s3 + a3), f2 && (e3.static_len += o3 * (l2[2 * n3 + 1] + a3)));
	        if (0 !== m2) {
	          do {
	            for (s3 = p2 - 1; 0 === e3.bl_count[s3]; ) s3--;
	            e3.bl_count[s3]--, e3.bl_count[s3 + 1] += 2, e3.bl_count[p2]--, m2 -= 2;
	          } while (0 < m2);
	          for (s3 = p2; 0 !== s3; s3--) for (n3 = e3.bl_count[s3]; 0 !== n3; ) u3 < (i3 = e3.heap[--r3]) || (h3[2 * i3 + 1] !== s3 && (e3.opt_len += (s3 - h3[2 * i3 + 1]) * h3[2 * i3], h3[2 * i3 + 1] = s3), n3--);
	        }
	      }(e2, t2), Z(s2, u2, e2.bl_count);
	    }
	    function X(e2, t2, r2) {
	      var n2, i2, s2 = -1, a2 = t2[1], o2 = 0, h2 = 7, u2 = 4;
	      for (0 === a2 && (h2 = 138, u2 = 3), t2[2 * (r2 + 1) + 1] = 65535, n2 = 0; n2 <= r2; n2++) i2 = a2, a2 = t2[2 * (n2 + 1) + 1], ++o2 < h2 && i2 === a2 || (o2 < u2 ? e2.bl_tree[2 * i2] += o2 : 0 !== i2 ? (i2 !== s2 && e2.bl_tree[2 * i2]++, e2.bl_tree[2 * b]++) : o2 <= 10 ? e2.bl_tree[2 * v]++ : e2.bl_tree[2 * y]++, s2 = i2, u2 = (o2 = 0) === a2 ? (h2 = 138, 3) : i2 === a2 ? (h2 = 6, 3) : (h2 = 7, 4));
	    }
	    function V(e2, t2, r2) {
	      var n2, i2, s2 = -1, a2 = t2[1], o2 = 0, h2 = 7, u2 = 4;
	      for (0 === a2 && (h2 = 138, u2 = 3), n2 = 0; n2 <= r2; n2++) if (i2 = a2, a2 = t2[2 * (n2 + 1) + 1], !(++o2 < h2 && i2 === a2)) {
	        if (o2 < u2) for (; L(e2, i2, e2.bl_tree), 0 != --o2; ) ;
	        else 0 !== i2 ? (i2 !== s2 && (L(e2, i2, e2.bl_tree), o2--), L(e2, b, e2.bl_tree), P(e2, o2 - 3, 2)) : o2 <= 10 ? (L(e2, v, e2.bl_tree), P(e2, o2 - 3, 3)) : (L(e2, y, e2.bl_tree), P(e2, o2 - 11, 7));
	        s2 = i2, u2 = (o2 = 0) === a2 ? (h2 = 138, 3) : i2 === a2 ? (h2 = 6, 3) : (h2 = 7, 4);
	      }
	    }
	    n(T);
	    var q = false;
	    function J(e2, t2, r2, n2) {
	      P(e2, (s << 1) + (n2 ? 1 : 0), 3), function(e3, t3, r3, n3) {
	        M(e3), (U(e3, r3), U(e3, ~r3)), i.arraySet(e3.pending_buf, e3.window, t3, r3, e3.pending), e3.pending += r3;
	      }(e2, t2, r2);
	    }
	    r._tr_init = function(e2) {
	      q || (function() {
	        var e3, t2, r2, n2, i2, s2 = new Array(g + 1);
	        for (n2 = r2 = 0; n2 < a - 1; n2++) for (I[n2] = r2, e3 = 0; e3 < 1 << w[n2]; e3++) A[r2++] = n2;
	        for (A[r2 - 1] = n2, n2 = i2 = 0; n2 < 16; n2++) for (T[n2] = i2, e3 = 0; e3 < 1 << k[n2]; e3++) E[i2++] = n2;
	        for (i2 >>= 7; n2 < f; n2++) for (T[n2] = i2 << 7, e3 = 0; e3 < 1 << k[n2] - 7; e3++) E[256 + i2++] = n2;
	        for (t2 = 0; t2 <= g; t2++) s2[t2] = 0;
	        for (e3 = 0; e3 <= 143; ) z[2 * e3 + 1] = 8, e3++, s2[8]++;
	        for (; e3 <= 255; ) z[2 * e3 + 1] = 9, e3++, s2[9]++;
	        for (; e3 <= 279; ) z[2 * e3 + 1] = 7, e3++, s2[7]++;
	        for (; e3 <= 287; ) z[2 * e3 + 1] = 8, e3++, s2[8]++;
	        for (Z(z, l + 1, s2), e3 = 0; e3 < f; e3++) C[2 * e3 + 1] = 5, C[2 * e3] = j(e3, 5);
	        O = new D(z, w, u + 1, l, g), B = new D(C, k, 0, f, g), R = new D(new Array(0), x, 0, c, p);
	      }(), q = true), e2.l_desc = new F(e2.dyn_ltree, O), e2.d_desc = new F(e2.dyn_dtree, B), e2.bl_desc = new F(e2.bl_tree, R), e2.bi_buf = 0, e2.bi_valid = 0, W(e2);
	    }, r._tr_stored_block = J, r._tr_flush_block = function(e2, t2, r2, n2) {
	      var i2, s2, a2 = 0;
	      0 < e2.level ? (2 === e2.strm.data_type && (e2.strm.data_type = function(e3) {
	        var t3, r3 = 4093624447;
	        for (t3 = 0; t3 <= 31; t3++, r3 >>>= 1) if (1 & r3 && 0 !== e3.dyn_ltree[2 * t3]) return o;
	        if (0 !== e3.dyn_ltree[18] || 0 !== e3.dyn_ltree[20] || 0 !== e3.dyn_ltree[26]) return h;
	        for (t3 = 32; t3 < u; t3++) if (0 !== e3.dyn_ltree[2 * t3]) return h;
	        return o;
	      }(e2)), Y(e2, e2.l_desc), Y(e2, e2.d_desc), a2 = function(e3) {
	        var t3;
	        for (X(e3, e3.dyn_ltree, e3.l_desc.max_code), X(e3, e3.dyn_dtree, e3.d_desc.max_code), Y(e3, e3.bl_desc), t3 = c - 1; 3 <= t3 && 0 === e3.bl_tree[2 * S[t3] + 1]; t3--) ;
	        return e3.opt_len += 3 * (t3 + 1) + 5 + 5 + 4, t3;
	      }(e2), i2 = e2.opt_len + 3 + 7 >>> 3, (s2 = e2.static_len + 3 + 7 >>> 3) <= i2 && (i2 = s2)) : i2 = s2 = r2 + 5, r2 + 4 <= i2 && -1 !== t2 ? J(e2, t2, r2, n2) : 4 === e2.strategy || s2 === i2 ? (P(e2, 2 + (n2 ? 1 : 0), 3), K(e2, z, C)) : (P(e2, 4 + (n2 ? 1 : 0), 3), function(e3, t3, r3, n3) {
	        var i3;
	        for (P(e3, t3 - 257, 5), P(e3, r3 - 1, 5), P(e3, n3 - 4, 4), i3 = 0; i3 < n3; i3++) P(e3, e3.bl_tree[2 * S[i3] + 1], 3);
	        V(e3, e3.dyn_ltree, t3 - 1), V(e3, e3.dyn_dtree, r3 - 1);
	      }(e2, e2.l_desc.max_code + 1, e2.d_desc.max_code + 1, a2 + 1), K(e2, e2.dyn_ltree, e2.dyn_dtree)), W(e2), n2 && M(e2);
	    }, r._tr_tally = function(e2, t2, r2) {
	      return e2.pending_buf[e2.d_buf + 2 * e2.last_lit] = t2 >>> 8 & 255, e2.pending_buf[e2.d_buf + 2 * e2.last_lit + 1] = 255 & t2, e2.pending_buf[e2.l_buf + e2.last_lit] = 255 & r2, e2.last_lit++, 0 === t2 ? e2.dyn_ltree[2 * r2]++ : (e2.matches++, t2--, e2.dyn_ltree[2 * (A[r2] + u + 1)]++, e2.dyn_dtree[2 * N(t2)]++), e2.last_lit === e2.lit_bufsize - 1;
	    }, r._tr_align = function(e2) {
	      P(e2, 2, 3), L(e2, m, z), function(e3) {
	        16 === e3.bi_valid ? (U(e3, e3.bi_buf), e3.bi_buf = 0, e3.bi_valid = 0) : 8 <= e3.bi_valid && (e3.pending_buf[e3.pending++] = 255 & e3.bi_buf, e3.bi_buf >>= 8, e3.bi_valid -= 8);
	      }(e2);
	    };
	  }, { "../utils/common": 41 }], 53: [function(e, t, r) {
	    t.exports = function() {
	      this.input = null, this.next_in = 0, this.avail_in = 0, this.total_in = 0, this.output = null, this.next_out = 0, this.avail_out = 0, this.total_out = 0, this.msg = "", this.state = null, this.data_type = 2, this.adler = 0;
	    };
	  }, {}], 54: [function(e, t, r) {
	    (function(e2) {
	      !function(r2, n) {
	        if (!r2.setImmediate) {
	          var i, s, t2, a, o = 1, h = {}, u = false, l = r2.document, e3 = Object.getPrototypeOf && Object.getPrototypeOf(r2);
	          e3 = e3 && e3.setTimeout ? e3 : r2, i = "[object process]" === {}.toString.call(r2.process) ? function(e4) {
	            define_process_default.nextTick(function() {
	              c(e4);
	            });
	          } : function() {
	            if (r2.postMessage && !r2.importScripts) {
	              var e4 = true, t3 = r2.onmessage;
	              return r2.onmessage = function() {
	                e4 = false;
	              }, r2.postMessage("", "*"), r2.onmessage = t3, e4;
	            }
	          }() ? (a = "setImmediate$" + Math.random() + "$", r2.addEventListener ? r2.addEventListener("message", d, false) : r2.attachEvent("onmessage", d), function(e4) {
	            r2.postMessage(a + e4, "*");
	          }) : r2.MessageChannel ? ((t2 = new MessageChannel()).port1.onmessage = function(e4) {
	            c(e4.data);
	          }, function(e4) {
	            t2.port2.postMessage(e4);
	          }) : l && "onreadystatechange" in l.createElement("script") ? (s = l.documentElement, function(e4) {
	            var t3 = l.createElement("script");
	            t3.onreadystatechange = function() {
	              c(e4), t3.onreadystatechange = null, s.removeChild(t3), t3 = null;
	            }, s.appendChild(t3);
	          }) : function(e4) {
	            setTimeout(c, 0, e4);
	          }, e3.setImmediate = function(e4) {
	            "function" != typeof e4 && (e4 = new Function("" + e4));
	            for (var t3 = new Array(arguments.length - 1), r3 = 0; r3 < t3.length; r3++) t3[r3] = arguments[r3 + 1];
	            var n2 = { callback: e4, args: t3 };
	            return h[o] = n2, i(o), o++;
	          }, e3.clearImmediate = f;
	        }
	        function f(e4) {
	          delete h[e4];
	        }
	        function c(e4) {
	          if (u) setTimeout(c, 0, e4);
	          else {
	            var t3 = h[e4];
	            if (t3) {
	              u = true;
	              try {
	                !function(e5) {
	                  var t4 = e5.callback, r3 = e5.args;
	                  switch (r3.length) {
	                    case 0:
	                      t4();
	                      break;
	                    case 1:
	                      t4(r3[0]);
	                      break;
	                    case 2:
	                      t4(r3[0], r3[1]);
	                      break;
	                    case 3:
	                      t4(r3[0], r3[1], r3[2]);
	                      break;
	                    default:
	                      t4.apply(n, r3);
	                  }
	                }(t3);
	              } finally {
	                f(e4), u = false;
	              }
	            }
	          }
	        }
	        function d(e4) {
	          e4.source === r2 && "string" == typeof e4.data && 0 === e4.data.indexOf(a) && c(+e4.data.slice(a.length));
	        }
	      }("undefined" == typeof self ? void 0 === e2 ? this : e2 : self);
	    }).call(this, "undefined" != typeof commonjsGlobal ? commonjsGlobal : "undefined" != typeof self ? self : "undefined" != typeof window ? window : {});
	  }, {}] }, {}, [10])(10);
	}); 
} (jszip_min$1));

var jszip_minExports = jszip_min$1.exports;
const JSZip = /*@__PURE__*/getDefaultExportFromCjs(jszip_minExports);

const jszip_min = /*#__PURE__*/Object.freeze(/*#__PURE__*/Object.defineProperty({
  __proto__: null,
  default: JSZip
}, Symbol.toStringTag, { value: 'Module' }));

export { ArrayBufferTarget as A, Muxer as M, Muxer$1 as a, ArrayBufferTarget$1 as b, jszip_min as j };
