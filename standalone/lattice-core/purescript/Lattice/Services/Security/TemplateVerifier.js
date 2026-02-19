//                                                                       // ffi
// Ed25519 operations via tweetnacl

let nacl = null;

// Lazy load tweetnacl
async function loadNaCl() {
  if (nacl) return nacl;
  try {
    nacl = await import("tweetnacl");
    return nacl;
  } catch (e) {
    throw new Error(`tweetnacl not installed - template signing unavailable: ${e.message}`);
  }
}

// Base64 utilities
function base64ToUint8Array(base64) {
  const binary = atob(base64);
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    bytes[i] = binary.charCodeAt(i);
  }
  return bytes;
}

function uint8ArrayToBase64(bytes) {
  let binary = "";
  for (let i = 0; i < bytes.length; i++) {
    binary += String.fromCharCode(bytes[i]);
  }
  return btoa(binary);
}

// Verify Ed25519 signature
// message: canonical JSON string
// signatureBase64: base64-encoded signature
// publicKeyBase64: base64-encoded public key
export const verifyEd25519Signature = (message) => (signatureBase64) => (publicKeyBase64) => async () => {
  const naclLib = await loadNaCl();

  const publicKey = base64ToUint8Array(publicKeyBase64);
  const signature = base64ToUint8Array(signatureBase64);
  const messageBytes = new TextEncoder().encode(message);

  return naclLib.sign.detached.verify(messageBytes, signature, publicKey);
};

// Sign with Ed25519 private key
// message: canonical JSON string
// privateKeyBase64: base64-encoded private key (64 bytes)
export const signEd25519 = (message) => (privateKeyBase64) => async () => {
  const naclLib = await loadNaCl();

  const privateKey = base64ToUint8Array(privateKeyBase64);
  const messageBytes = new TextEncoder().encode(message);

  const signature = naclLib.sign.detached(messageBytes, privateKey);
  return uint8ArrayToBase64(signature);
};

// Get current ISO timestamp
export const getCurrentISOTimestamp = async () => {
  return new Date().toISOString();
};

// Extract public key from private key (last 32 bytes of Ed25519 secret key)
export const extractPublicKeyFromPrivate = (privateKeyBase64) => {
  const privateKey = base64ToUint8Array(privateKeyBase64);
  // Ed25519 secret key is 64 bytes: first 32 are seed, last 32 are public key
  const publicKey = privateKey.slice(32);
  return uint8ArrayToBase64(publicKey);
};
