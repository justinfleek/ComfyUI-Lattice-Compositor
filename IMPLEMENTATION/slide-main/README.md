# straylight / jaylene-slide

*Infrastructure for the sprawl.*

## Branch Protocol

| Branch | Purpose |
|--------|---------|
| `main` | Post-review, stable. All commits have been reviewed. |
| `dev` | Moving ref to unblock. Integration branch for active development. |
| `user/the-thing-<linear-id>` | Feature/fix branches. Named `b7r6/feature-name-SLI-123`. |

### Commit Message Convention

```
// project // area // description // 0x0N

Examples:
// slide // wire // add varint encoding // 0x01
// slide // provider // fix OpenRouter auth header // 0x02
// slide // tokenizer // implement identity tokenizer // 0x03
```

The `0x0N` suffix is a sequential counter within the branch for easy reference.

---

```
  ╷┌─┐┐ ┬┬  ┌─┐┌┐┐┌─┐  ┐─┐┬  o┬─┐┌─┐
  ││─┤└┬┘│  ├─ │││├─   └─┐│  ││ │├─ 
╶─┘┘ ┴ ┴ ┘─┘┴─┘┘└┘┴─┘  ──┘┘─┘┘┘─┘┴─┘

A square of cyberspace directly in front of him flipped sickeningly 
and he found himself in a pale blue graphic that seemed to represent 
a very spacious apartment, low shapes of furniture sketched in hair-fine 
lines of blue neon. A woman stood in front of him, a sort of glowing 
cartoon squiggle of a woman, the face a brown smudge.

"I'm Slide,” the figure said, hands on its hips, “Jaylene. You don't fuck 
with me. Nobody in L.A.” she gestured, a window suddenly snapping into existence 
behind her “fucks with me. You got that?”
```

## What

**jaylene-slide** is a console cowboy that jacks into OpenAI-compatible inference endpoints (Baseten, Together, Fireworks, etc.), parses their 650-byte-per-token SSE/JSON garbage, and emits clean SIGIL binary frames over ZMQ.

It supports:
*   **Semantic Chunking**: Splits streams intelligently on token boundaries, newlines, and special tags.
*   **Chain of Thought**: Natively handles reasoning models (DeepSeek R1, Kimi K2.5) with optional visualization.
*   **High Performance**: Uses HTTP/2 (via `http2-client`), optimized Tokenizer FFI (HuggingFace via `tokenizers-cpp`), and Zero-Copy ZMQ patterns.
*   **Structured Logging**: Observability via Katip (JSON or colored terminal output).

## Why

Every token from Baseten/OpenAI looks like this:

```
data: {"id":"chatcmpl-cf31...","choices":[{"index":0,"delta":{"content":" const"}}],"created":1770306640,"model":"...","usage":{...}}
```

That's ~650 bytes for the token `" const"`.

**jaylene-slide** emits:

```
[0x2A]
```

One byte. Because `" const"` is hot token #42.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                         Provider                                │
│  (Baseten, Together, Fireworks, local vLLM, etc.)               │
└─────────────────────────────────┬───────────────────────────────┘
                                  │ HTTP/2 SSE (~650 bytes/token)
                                  ▼
┌─────────────────────────────────────────────────────────────────┐
│                      jaylene-slide                              │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐              │
│  │ Jaylene.Jack│→ │Jaylene.Parse│→ │Jaylene.Wire │              │
│  │(http2-client)  │ (Tokenizer) │  │ (Frames)    │              │
│  └─────────────┘  └─────────────┘  └─────────────┘              │
└─────────────────────────────────┬───────────────────────────────┘
                                  │ SIGIL frames (~1.5 bytes/token)
                                  ▼
┌─────────────────────────────────────────────────────────────────┐
│                          ZMQ PUB                                │
│                      tcp://*:5555                               │
└─────────────────────────────────┬───────────────────────────────┘
                                  │
                                  ▼
                            [ clients ]
                       (opencode, your app, etc.)
```

## Quick Start

### Prerequisites

*   Nix (with flakes enabled)
*   OR Cabal + GHC 9.12 + `libtokenizers`

### Running the Ingress (Jack Mode)

This connects to the provider and publishes frames on ZMQ.

```bash
# 1. Get a tokenizer.json (e.g. for Kimi K2.5, use Qwen 2.5 tokenizer)
curl -L -o tokenizer.json https://huggingface.co/Qwen/Qwen2.5-7B-Instruct/resolve/main/tokenizer.json

# 2. Set your API key
export JAYLENE_API_KEY="your-api-key"

# 3. Jack in
nix run .#slide -- jack \
  https://inference.baseten.co/v1/chat/completions \
  --model moonshotai/Kimi-K2.5 \
  --tokenizer tokenizer.json \
  --zmq tcp://*:5555 \
  --metrics-port 9090 \
  --verbose
```

Type your prompt into stdin and hit Enter.

### Running the Client (Listen Mode)

This subscribes to ZMQ and prints decoded text to stdout.

```bash
nix run .#slide -- listen \
  --tokenizer tokenizer.json \
  --zmq tcp://localhost:5555 \
  --show-think  # Optional: Show reasoning blocks <think>...</think>
```

## Wire Format

SIGIL frames use a distribution-derived encoding:

```
0xxxxxxx        Hot token (ID 0-126 in lower 7 bits)
10xxxxxx        Extended token (varint follows)
1100xxxx        Stream control:
                  0xC0 = CHUNK_END
                  0xC1 = TOOL_CALL_START
                  0xC2 = TOOL_CALL_END
                  0xC3 = THINK_START
                  0xC4 = THINK_END
                  0xC5 = CODE_BLOCK_START
                  0xC6 = CODE_BLOCK_END
                  0xCF = STREAM_END
```

Hot tokens are the 127 most frequent tokens for the model. Everything else is escape + varint. Control frames mark semantic boundaries.

## Development

### Build

```bash
nix develop
cabal build all
```

### Formatting

The project uses `treefmt` to maintain consistent style:

```bash
nix fmt
```

This invokes `fourmolu`, `cabal-fmt`, and `nixpkgs-fmt`.

### The "Footgun" (Tokenizer Compatibility)

`tokenizers-cpp` (and the Rust `tokenizers` crate) typically load `tokenizer.json` (HuggingFace format).
Some models (like Kimi K2.5 or OpenAI models) distribute `tiktoken.model` or raw vocab files.

**Workaround**: Use a compatible `tokenizer.json` from a related model.
*   **Kimi K2.5**: Use **Qwen 2.5** tokenizer (`Qwen/Qwen2.5-7B-Instruct`). They share the same vocabulary structure.

### HTTP/2 Notes

This project strictly requires `http2-client` (which depends on `http2` < 5.0) to achieve robust, multiplexed streaming. The build configuration (`flake.nix` and `slide.cabal`) is pinned to ensure compatibility with GHC 9.12 and the Haskell ecosystem state.

## Logging & Observability

### Logging (Katip)
*   **Console**: Human-readable, colored logs on stderr.
*   **JSON**: Use `--json-logs` for machine-readable output (Datadog/CloudWatch friendly).
*   **Verbose**: Use `-v` or `--verbose` to see individual chunk arrivals ("flying messages").
*   **Context**: All logs include `slide_id` (process) and `http_id` (transaction) correlation IDs.

### Metrics (Prometheus)
Exposes metrics on a dedicated port (default 9090, configurable via `--metrics-port`).

Endpoint: `GET /` or `GET /metrics`

*   `slide_frames_emitted_total`: Counter
*   `slide_bytes_emitted_total`: Counter
*   `slide_tokens_processed_total`: Counter
*   GHC Runtime Metrics (GC, Heap, Threads)

## Style Guide

We follow the **Straylight Production Haskell** conventions:
*   Optimize for disambiguation (explicit types, full variable names).
*   Flat control flow (guards over nesting).
*   Strict warnings (`-Wall -Werror`).
*   Unicode delimiters (`// typographical // conventions`).

See `STYLE.md` (if it existed) or the codebase itself for examples.

## License

MIT / Apache 2.0
