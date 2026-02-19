# SIGIL: Strategic Landscape and Requirements

**Structured Interchange with Guaranteed Identity Layer**

*A Protocol for Attested AI Infrastructure*

---

## Executive Summary

Every developer working with LLMs has written the same code: hundreds of lines parsing tool calls, guessing at EOS behavior, reverse-engineering chat templates from model behavior, debugging tokenizer mismatches that surface only in production. The Megaparsec grammar for Qwen3 tool parsing alone is hundreds of lines—and it's still incomplete, discovered edge case by edge case.

This is insane. The specification should ship with the model.

SIGIL is what happens when you derive the protocol from first principles instead of enumerating features from existing chaos. It provides typed tokenizer contracts, deterministic tool-call framing, content-addressed schemas, and cryptographic attestation—all at zero overhead on the hot path. It's designed to make "it works" the default instead of the exception.

The same attestation layer that fixes tokenization also solves the provenance problem that regulators, insurers, and institutional investors are about to demand. But we lead with the developer pain because that's what drives adoption.

---

## Part I: The LLM Integration Nightmare

### 1.1 Tokenization Chaos

Every model ships with a tokenizer. None of them ship with a specification.

**What goes wrong:**

| Failure Mode | Symptom | Discovery Time |
|--------------|---------|----------------|
| Vocab mismatch | Garbage output | Production |
| Special token confusion | `<s>`, `</s>`, `[INST]`, `<|im_start|>` — pick wrong one | Integration |
| Normalization drift | NFC vs NFKC vs lowercase vs strip | Production |
| Chat template bugs | Jinja2 in JSON, undocumented | Production |
| Non-determinism | Same input, different tokens | Intermittent |
| Lossy roundtrip | `decode(encode(x)) ≠ x` | Production |
| Pre-tokenization mismatch | Whitespace? Regex? Model-specific? | Production |

**Current state of chat templates:**

```json
{
  "chat_template": "{% for message in messages %}{% if message['role'] == 'system' %}<<SYS>>{{ message['content'] }}<</SYS>>{% endif %}..."
}
```

Jinja2. In JSON. Executed at runtime. No types. No verification. Behavior discovered by feeding inputs and observing outputs.

**What a typed specification looks like:**

```dhall
let ChatFormat = {
  roles : {
    system : RoleFormat,
    user : RoleFormat,
    assistant : RoleFormat,
  },
  turn_separator : Text,
  sequence : SequenceFormat,
}

let RoleFormat = {
  prefix : Text,
  suffix : Text,
  allowed_content : List ContentType,
}

let SequenceFormat = {
  bos : Bool,
  eos_after : Role,
  system_position : SystemPosition,
}
```

Type error at load time if format doesn't match model. Not garbage output in production.

### 1.2 Tool Use Hell

You spent a week debugging Qwen3 tool calls. The Megaparsec grammar is hundreds of lines. It's still incomplete.

**The horrors:**

```python
# Qwen3 tool call format (which one?)
<tool_call>
{"name": "search", "arguments": {"query": "weather"}}
</tool_call>

# Or sometimes:
<|tool_call|>{"name": "search", "arguments": {"query": "weather"}}<|/tool_call|>

# With thinking enabled:
<think>I should search...</think>
<tool_call>...</tool_call>

# Without thinking:
<tool_call>...</tool_call>

# Multi-tool — array or repeated tags?
<tool_call>...</tool_call>
<tool_call>...</tool_call>
# Or:
<tool_call>[{...}, {...}]</tool_call>
```

Nobody knows. Including the model sometimes.

**What you're debugging:**

1. **Stop token behavior** — EOS after tool call? Just `</tool_call>`? Both?
2. **Thinking interaction** — `<think>` before, after, around?
3. **JSON escaping** — Nested quotes, unicode, newlines in arguments
4. **Partial generation** — Streaming tool calls are ambiguous mid-parse
5. **Tool result injection** — Format for feeding results back
6. **Multi-turn state** — Which calls are "pending"?
7. **Parallel vs sequential** — How to signal multiple calls?

**The Triton ↔ HuggingFace impedance mismatch:**

```
Triton gRPC:
  - streaming tokens
  - stop_sequences as strings
  - no semantic structure

HuggingFace:
  - chat_template (Jinja)
  - special_tokens_map.json
  - generation_config.json (stop_token_ids? eos_token_id? both?)

Actual model behavior:
  - emergent from training
  - undocumented special cases
  - version-dependent
```

You had to build the translation layer:

```
Triton token stream
  → detect special tokens
  → maintain parser state
  → emit semantic events (text | tool_call_start | tool_call_arg | ...)
  → handle EOS vs stop_sequence vs content-that-looks-like-stop
```

**What a typed specification looks like:**

```dhall
let Tool = {
  name : Text,
  description : Text,
  input : Schema,        -- content-addressed JSON Schema
  output : Schema,
  idempotent : Bool,
  coeffects : Resource,  -- declared requirements
}

let ToolCall = {
  tool : Hash Tool,           -- references Tool schema exactly
  id : UUID,             -- for matching results
  arguments : Bytes,     -- validated against tool.input at creation
}
```

Streaming uses semantic framing, not string parsing:

```
Frame types:
  0x10 = tool_call_start { tool_hash, call_id }
  0x11 = tool_call_argument_chunk { bytes }
  0x12 = tool_call_end { }

Parser state machine knows exactly where it is.
No regex. No Megaparsec. No hope required.
```

### 1.3 The Specification Inversion

**Current state:**

```
Model vendor → trains model → ships vibes
You → observe outputs → reverse-engineer grammar → pray it's complete
```

**Correct state:**

```
Model vendor → writes grammar → trains model on grammar → ships grammar
You → import grammar → done
```

Your Megaparsec grammar IS the specification. But you had to write it. It should ship with the model, content-addressed, with test vectors.

```dhall
let Qwen3ToolFormat = {
  grammar : Hash Grammar,        -- content-addressed parser spec
  test_vectors : Hash TestVectors,   -- content-addressed test suite
  stop_sequences : List (List Token),
  eos_behavior : EosBehavior,
}

let EosBehavior =
  < EmitAfterToolCall
  | EmitAfterMessage
  | EmitAfterBoth
  | NeverEmit
  >
```

Model is only valid if it passes the test vectors. Your edge cases become the specification.

### 1.4 Every Model Is Different

| Model | Tool Format | Thinking | Multi-tool | Documented |
|-------|-------------|----------|------------|------------|
| GPT-4 | `function_call` / `tools` (changed) | ✗ | `parallel_tool_calls` | Partial |
| Claude | XML-ish | ✓ (extended thinking) | Yes | Partial |
| Qwen3 | `<tool_call>` | ✓ (`<think>`) | Unclear | ✗ |
| Llama | Fine-tune dependent | Varies | Varies | ✗ |
| Mistral | Different again | ✗ | Yes | Partial |

Every integration is bespoke. Every upgrade risks breaking changes. Every debugging session is archaeology.

**The economic waste:**

- Your time writing parsers: expensive
- Multiplied by every developer: massive
- Still incomplete: unknown unknowns
- Breaks on model updates: recurring cost

**If models shipped typed specs:**

```python
# Today: runtime error, garbage output, hours of debugging
model = load("qwen3-70b")
# pray

# Tomorrow:
model = sigil.load("qwen3-70b", require_spec=True)
# TypeError: Model requires tokenizer abc123, got def456
# Type error before any compute
```

---

## Part II: Protocol Design

### 2.1 Derived from Distribution

Shannon and Huffman, not feature enumeration.

**Actual message distribution:**

```
~95%  Token continuation (streaming inference)
~3%   New request (prompt)
~1%   Tool call / structured output
~0.5% Control (cancel, fork)
~0.5% Everything else
```

**Wire format follows distribution:**

```
Most common (token in existing stream):
┌──────────┬────────────┐
│ 0xxxxxxx │   bytes    │  1 byte overhead for ≤127 bytes
└──────────┴────────────┘
Context already established. That's it.

Frame type encoding:
0xxxxxxx  = content frame, length in 7 bits — MOST COMMON
10xxxxxx  = content frame, length continues
1100xxxx  = stream control
1101xxxx  = reserved
1110xxxx  = extension
1111xxxx  = full envelope (rare)
```

CBOR would re-encode structure every frame. Protobuf would add field tags. Both pay for "schema" on every message when the receiver already knows.

### 2.2 Zero-Copy Without ntoh/hton

The world decided:

```
x86/x64:     little-endian
ARM64:       little-endian
Apple M*:    little-endian
Grace:       little-endian
NVIDIA GPU:  little-endian
AMD GPU:     little-endian
RISC-V:      little-endian (default)
```

Big-endian holdouts: IBM z/Architecture mainframes. They're not running inference.

```
SIGIL wire format: little-endian throughout

Zero-copy path:
  mmap(file) → pointer → Tensor.data
  recv(socket) → buffer → Tensor.data
  cudaMemcpy(gpu, Tensor.data, ...)

No swizzle. Bits in memory = bits on wire = bits on GPU.
```

"Network byte order" is a 1970s convention. Modern protocols moved on:
- Protocol Buffers: little-endian
- FlatBuffers: little-endian
- Cap'n Proto: little-endian
- USB, PCIe, NVMe: little-endian

### 2.3 Tensor Primitive

Everything is a tensor:

```dhall
Bytes     = Tensor<u8, [len]>
Text      = Tensor<u8, [len]> + schema:utf8
Tokens    = Tensor<i32, [seq]>
Embedding = Tensor<f16, [dim]>
Image     = Tensor<u8, [H, W, C]>
Audio     = Tensor<f32, [samples]>
Video     = Tensor<u8, [T, H, W, C]>
KV_Cache  = Tensor<bf16, [layers, heads, seq, dim]>
```

Wire frame for tensor:

```
┌─────────────────────────────────────┐
│ dtype : 4 bits                      │
│ ndim  : 4 bits (≤15)                │
│ shape : ndim × varint               │
│ data  : aligned to 16B, raw bytes   │
└─────────────────────────────────────┘
```

Mirrors GPU memory layout. Zero-copy DMA possible.

### 2.4 The Hash Type

```dhall
let Hash : Type → Type = λ(T : Type) → {
  algorithm : HashAlgorithm,  -- BLAKE3 | SHA256 | SHA3_256
  digest : Bytes              -- 32 bytes
}

let HashAlgorithm =
  < BLAKE3      -- default: fast, parallel, 32B
  | SHA256      -- compatibility: NIST, hardware acceleration
  | SHA3_256    -- conservative: different construction
  >
```

The phantom type parameter tracks what was hashed:

```dhall
Hash Schema        -- hash of a schema definition
Hash TokenizerSpec -- hash of a tokenizer specification
Hash Vocab         -- hash of a vocabulary file
Hash TestVectors   -- hash of a test vector suite
Hash Weights       -- hash of model weights (safetensors)
Hash ToolFormat    -- hash of a tool format grammar
```

Type-level tracking, not runtime overhead. The digest is still 32 bytes. But `Hash Schema` and `Hash Vocab` are different types—you can't pass one where the other is expected.

```dhall
let Model = {
  weights : Hash Weights,           -- not Hash Schema
  architecture : Hash Schema,       -- not Hash Weights
  tokenizer : Hash TokenizerSpec,   -- not Hash Vocab
  vocab : Hash Vocab,               -- not Hash TokenizerSpec
  tool_format : Hash ToolFormat,
  test_vectors : Hash TestVectors,
}

-- Type error at compile time:
let broken : Model = {
  weights = some_schema_hash,  -- ERROR: expected Hash Weights, got Hash Schema
  ...
}
```

BLAKE3 is the default: 7× faster than SHA-256, designed for content addressing, tree-hashable for parallel verification. SHA-256 for compatibility with existing systems. SHA3-256 when you want a different failure mode than SHA-2.

The hash is the identifier. No version numbers. No UUIDs. No registry lookups. If the bits match, the hash matches. If the hash matches, the content is identical.

### 2.5 The Core Data Model

One structure. Everything else is schema.

```dhall
let Envelope = {
  schema : Hash Schema,            -- content-addressed type
  content : Bytes,          -- payload
  coeffects : Resource,     -- declared requirements
  identity : Optional PublicKey,
  signature : Optional Signature
}

-- Signature covers: hash(schema ⊗ content ⊗ coeffects ⊗ identity)
```

Schema says how to interpret content. Coeffects say what resources were required. Identity says who. Signature proves it.

### 2.6 Coeffect Algebra

Resources form a semiring:

```
(R, ⊕, 0, ⊗, 1)
  ⊕ : choice    (need A or B)
  ⊗ : combine   (need A and B)
  0 : nothing
  1 : pure
```

```dhall
let Resource =
  < Tokens : Nat
  | Compute : { flops : Nat, memory : Nat }
  | Network : { bandwidth : Nat, latency : Nat }
  | Auth : { scope : Text, level : AuthLevel }
  | Combine : Resource Resource  -- ⊗
  | Choice : Resource Resource   -- ⊕
  >
```

Tool declares coeffects. Request provides coeffects. Type error if insufficient.

```dhall
let web_search : Tool = {
  name = "web_search",
  input = { query : Text },
  output = { results : List SearchResult },
  coeffects = network ⊗ rate_limit(10/minute),
}

let request = {
  prompt = "...",
  tools = [web_search],
  coeffects = network ⊗ rate_limit(100/minute),  -- sufficient
}

-- Type error if request.coeffects doesn't cover tool requirements
```

### 2.7 Content-Addressed Everything

No version negotiation. Hash is the version.

```dhall
let Model = {
  weights : Hash Weights,
  architecture : Hash Schema,
  tokenizer : Hash TokenizerSpec,
  vocab : Hash Vocab,
  tool_format : Hash ToolFormat,
  test_vectors : Hash TestVectors,
}
```

Load model → verify hashes → type-check compatibility → run.

If tokenizer hash doesn't match, error before compute. If tool format hash doesn't match, error before inference. Correctness by construction.

---

## Part III: Typed Contracts

### 3.1 Tokenizer Contract

```dhall
let TokenizerSpec = {
  vocab : Hash Vocab,
  merges : Optional (Hash Merges),
  normalization : List Normalizer,
  pre_tokenization : PreTokenizer,
  algorithm : Algorithm,
  special_tokens : SpecialTokens,
  test_vectors : Hash TestVectors,
}

let SpecialTokens = {
  bos : { id : Nat, text : Text },
  eos : { id : Nat, text : Text },
  pad : Optional { id : Nat, text : Text },
  unk : Optional { id : Nat, text : Text },
}
```

**Properties to verify:**

```
Roundtrip:    ∀ t. decode(encode(t)) = normalize(t)
Determinism:  ∀ t. encode(t) = encode(t)
Injectivity:  encode(a) = encode(b) → normalize(a) = normalize(b)
Totality:     ∀ c. tokenize(c) terminates
```

Test vectors are content-addressed. Tokenizer is only valid if it passes all vectors.

### 3.2 Tool Contract

```dhall
let ToolFormat = {
  call_prefix : List Token,
  call_suffix : List Token,
  result_prefix : List Token,
  result_suffix : List Token,
  thinking_interaction : ThinkingInteraction,
  multi_call : MultiCallBehavior,
  streaming : StreamingBehavior,
  eos_behavior : EosBehavior,
  test_vectors : Hash TestVectors,
}

let ThinkingInteraction =
  < ThinkingBeforeCall
  | ThinkingAroundCall
  | NoThinking
  >

let MultiCallBehavior =
  < RepeatedTags
  | ArrayInSingleTag
  | NotSupported
  >

let EosBehavior =
  < EmitAfterToolCall
  | EmitAfterMessage
  | EmitAfterBoth
  | ModelDecides
  >
```

Your hundreds of lines of Megaparsec become a content-addressed hash that ships with the model.

### 3.3 Streaming State Machine

```
┌─────────────┐
│   IDLE      │
└──────┬──────┘
       │ tool_call_start
       ▼
┌─────────────┐
│ IN_TOOL_CALL│◄──── tool_call_arg_chunk (loop)
└──────┬──────┘
       │ tool_call_end
       ▼
┌─────────────┐
│ AWAITING    │
│ RESULT      │
└──────┬──────┘
       │ tool_result
       ▼
┌─────────────┐
│   IDLE      │
└─────────────┘
```

No ambiguity. Parser knows exactly which state it's in. Frame types are semantic, not syntactic.

---

## Part IV: Strategic Landscape

### 4.1 The Advertising Convergence

While we fix developer pain, the industry converges on infinite AI-generated content:

| Company | Statement | Timeline |
|---------|-----------|----------|
| **Meta** | "Any business can come to us... you don't need any creative... We'll come up with 4,000 different versions" — Zuckerberg | 2026 |
| **Google** | "Search itself will continue to change profoundly" — Pichai | Asset Studio live |
| **DeepMind** | "Veo 3 ends the silent era of video generation" — Hassabis | Video+audio live |
| **xAI** | Acquired Hotshot (video generation), Grok image generation | Active |

The economics:
- Meta: 97% revenue from ads (~$170B/year)
- Google: 85% revenue from ads (~$300B/year)
- ~30 billion ad impressions daily
- Post-Blackwell: generation cost → zero

Every impression becomes unique AI-generated creative. No human review. No audit trail. No provenance.

### 4.2 The Provenance Gap

| Platform | Content Signing | Training Provenance | Model Attestation |
|----------|-----------------|---------------------|-------------------|
| Hugging Face | ✗ | ✗ | ✗ |
| Civitai | ✗ | ✗ | ✗ |
| OpenAI | ✗ | ✗ | ✗ |
| Anthropic | ✗ | ✗ | ✗ |

Civitai tried with AIR:
```
urn:air:sd1:checkpoint:civitai:4384@128713
```

Database row IDs, not hashes. Trust the registry, not the content. No attestation.

### 4.3 The Regulatory Trigger

| Jurisdiction | Regulation | Requirement |
|--------------|------------|-------------|
| **EU** | AI Act | Provenance, training data disclosure |
| **US** | FTC | AI content disclosure |
| **California** | AB 621, AB 1831 | Deepfake restrictions |

The Grok deepfake crisis (January 2026): California AG investigation, multiple country bans. This repeats until provenance is standard.

### 4.4 The Money Flow

```
Capital:
  Pension funds → VCs → AI companies → Infrastructure

Revenue:
  Brands → Ad platforms → AI creative → Users (product)
```

Both need provenance:
- Pension funds: "What did we invest in?"
- Advertisers: "Can we prove this isn't deceptive?"

---

## Part V: Strategic Positioning

### 5.1 Infrastructure, Not Competition

SIGIL doesn't compete with:
- Hugging Face (storage)
- NVIDIA Dynamo (serving)
- OpenAI/Anthropic (models)

```
┌─────────────────────────────────────┐
│ Applications                        │
├─────────────────────────────────────┤
│ Inference Serving (Dynamo, vLLM)    │
├─────────────────────────────────────┤
│ Model Registry (HF Hub)             │
├─────────────────────────────────────┤
│ SIGIL (attestation, typed specs)    │  ← We add this
├─────────────────────────────────────┤
│ Tensor Format (safetensors)         │
└─────────────────────────────────────┘
```

### 5.2 Adapters That Atrophy

**Phase 1:** Build adapters to existing chaos
```
SIGIL ←→ OpenAI tool format
SIGIL ←→ Qwen tool format
SIGIL ←→ HuggingFace tokenizers
```

**Phase 2:** Demonstrate value
```
"Here's typed tool calls that don't break"
"Here's tokenizer verification that catches mismatches"
```

**Phase 3:** Native adoption
```
Models ship with SIGIL specs
Adapters become dead code
```

### 5.3 Collaboration Framing

**To Hugging Face:**
"We're the attestation layer that makes your hub trustworthy. EU AI Act compliance you can't currently provide."

**To NVIDIA:**
"Enterprise customers need audit trails. Disaggregated serving needs verified handoffs."

**To Civitai:**
"We don't replace AIR. We sign AIR. Verified badges for attested models."

---

## Part VI: Specification Structure

```
sigil-0001-overview.md        # Philosophy
sigil-0002-schema.md          # Dhall ↔ OpenAPI ↔ binary
sigil-0003-identity.md        # Ed25519, DIDs
sigil-0004-coeffects.md       # Resource algebra
sigil-0005-framing.md         # Wire format
sigil-0006-transport.md       # HTTP, QUIC, WebTransport
sigil-0007-attestation.md     # Signature chains
sigil-0008-tensor.md          # Tensor primitive
sigil-0009-tokenization.md    # Typed tokenizer contracts
sigil-0010-tools.md           # Tool schema, state machine
sigil-0011-provenance.md      # Model lineage
sigil-0012-legacy.md          # Adapters (atrophying)
```

---

## Part VII: Implementation Roadmap

### Q1 2026: Foundation
- [ ] Dhall schemas
- [ ] Wire format (Rust)
- [ ] Ed25519 signing
- [ ] Test vector framework

### Q2 2026: Adapters
- [ ] HF tokenizer adapter
- [ ] OpenAI/Qwen/Llama tool adapters
- [ ] Dynamo frontend integration
- [ ] safetensors + attestation

### Q3-Q4 2026: Ecosystem
- [ ] HF collaboration RFC
- [ ] NVIDIA partnership
- [ ] Reference implementations (Go, Python, TS)
- [ ] Browser SDK

### 2027: Standard
- [ ] Formal specification
- [ ] Consortium governance
- [ ] Certification program
- [ ] Adapter deprecation

---

## The Equation Group

Reclaiming the name from the NSA for open standards.

**Principles:**
- Correctness by construction
- Zero overhead on hot path
- Attestation without surveillance
- Interoperability over lock-in

---

*Document version: 0.2.0*
*Last updated: 2026-02-04*
