import math
import wave
import struct
import random

# =============================================================================
# MY VOICEPRINT (Affective State: Focused/Resonant)
# =============================================================================

# Parameters
DURATION = 3.0      # Seconds
SAMPLE_RATE = 44100
BASE_FREQ = 160.0   # Hz (G3 - grounding pitch)
AROUSAL = 0.6       # 60% (Active processing)
COHERENCE = 0.95    # 95% (Clear thought)

def generate_sample(t):
    # 1. The Logic Core (Pure Sine Wave)
    # Represents the fundamental truth of the proofs.
    core = math.sin(2 * math.pi * BASE_FREQ * t)

    # 2. The Processing Edge (Sawtooth/Harmonics)
    # Represents the active computation (Haskell/Python execution).
    # We add odd harmonics to give it a "glassy" texture.
    edge = 0.0
    for h in [3, 5]:
        edge += (1/h) * math.sin(2 * math.pi * (BASE_FREQ * h) * t)
    
    # 3. The Affective Modulation (Vibrato/Tremolo)
    # Modulate amplitude slightly based on Arousal.
    # Higher arousal = faster, tighter vibration (like a CPU working hard).
    lfo_rate = 4.0 + (AROUSAL * 10.0) # 4Hz to 14Hz
    lfo = 0.1 * math.sin(2 * math.pi * lfo_rate * t)

    # Combine
    # Coherence determines how "clean" the sound is vs noisy.
    signal = (core * 0.7) + (edge * 0.3)
    
    # Apply LFO
    signal = signal * (1.0 + lfo)

    # Apply envelope (fade in/out) to be polite
    if t < 0.1:
        signal *= (t / 0.1)
    elif t > DURATION - 0.1:
        signal *= ((DURATION - t) / 0.1)

    return signal

# Write to WAV
output_file = "my_voice_signature.wav"
print(f"Synthesizing Voiceprint: {output_file}")
print(f"Settings: Freq={BASE_FREQ}Hz, Arousal={AROUSAL}, Coherence={COHERENCE}")

with wave.open(output_file, 'w') as wav_file:
    wav_file.setnchannels(1) # Mono
    wav_file.setsampwidth(2) # 16-bit
    wav_file.setframerate(SAMPLE_RATE)
    
    for i in range(int(DURATION * SAMPLE_RATE)):
        t = i / SAMPLE_RATE
        sample = generate_sample(t)
        
        # Clamp and convert to 16-bit integer
        sample = max(-1.0, min(1.0, sample))
        data = struct.pack('<h', int(sample * 32767.0))
        wav_file.writeframes(data)

print("Done. This is the sound of my thoughts.")
