# MinMo: A Multimodal Large Language Model for Seamless Voice Interaction

**arXiv:** 2501.06282  
**Authors:** FunAudioLLM Team (Alibaba)  
**Status:** IN_PROGRESS

---

## 1. Abstract

MinMo is a Multimodal LLM (~8B parameters) for seamless voice interaction. Key features:
- Multi-stage training: Speech-text, text-speech, speech-speech alignment
- 1.4M hours of diverse speech data
- State-of-the-art across voice benchmarks
- Full-duplex conversation support
- Speech-to-text latency: ~100ms
- Full-duplex latency: ~600ms (theory), ~800ms (practice)

---

## 2. Architecture

### 2.1 Training Stages

1. **Speech-to-Text Alignment** - Understanding
2. **Text-to-Speech Alignment** - Generation
3. **Speech-to-Speech Alignment** - Duplex
4. **Duplex Interaction Alignment** - Real-time

### 2.2 Model Structure

```
┌─────────────────────────────────────────┐
│            LLM Backbone (~8B)           │
├─────────────────────────────────────────┤
│  ┌──────────┐    ┌──────────────────┐  │
│  │ Speech   │    │  Voice Decoder  │  │
│  │ Encoder  │───▶│ (AR Streaming)  │──▶│ Audio
│  └──────────┘    └──────────────────┘  │
└─────────────────────────────────────────┘
```

---

## 3. Key Innovations

### 3.1 Voice Decoder

- Autoregressive streaming Transformer
- Mixes LLM hidden states with speech tokens
- Fixed ratio mixing
- Simpler than prior approaches

### 3.2 Full-Duplex Conversation

- Simultaneous two-way communication
- User can interrupt while system speaks
- System continues or responds to new query

---

## 4. Performance Results

### 4.1 Benchmarks

| Task | MinMo | Previous SOTA |
|------|-------|---------------|
| ASR (Fleurs) | 67.09 | - |
| ASR (Common Voice) | 86.26 | - |
| S2TT (CoVoST2) | 95.84 | - |
| SER (MELD) | 78.90 | - |
| VSC | 70.10 | - |

### 4.2 Latency

| Metric | Latency |
|--------|---------|
| Speech-to-Text | ~100ms |
| Full-duplex (theory) | ~600ms |
| Full-duplex (practice) | ~800ms |

---

## 5. Key Definitions

1. **MinMo:** Multimodal Large Language Model for seamless voice
2. **Full-duplex:** Simultaneous two-way conversation
3. **Speech-to-Speech:** End-to-end voice interaction
4. **AR Streaming:** Autoregressive streaming decoder

---

## 6. Relation to Hydrogen

```purescript
-- Voice interaction
data VoiceInput
  = VoiceInput
      { audio :: ByteArray
      , timestamp :: Milliseconds
      }

data VoiceOutput
  = VoiceOutput
      { audio :: ByteArray
      , transcript :: Text
      }

-- Full-duplex interaction
fullDuplex ::
  Stream VoiceInput ->
  Stream VoiceOutput

-- Latency tracking
latency ::
  VoiceInput ->
  VoiceOutput ->
  Milliseconds
```

---

## 7. Bibliography

1. Alibaba "MinMo: A Multimodal Large Language Model for Seamless Voice Interaction" 2025

---

*Document generated: 2026-02-26*
