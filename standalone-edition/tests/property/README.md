# Property-Based API Tests

This directory contains property-based tests for the Lattice APIs using
[haskemathesis](../../IMPLEMENTATION/haskemathesis-main/README.md).

## What is haskemathesis?

haskemathesis generates valid HTTP requests from OpenAPI specifications
and validates that responses conform to the schema. It's inspired by
Python's schemathesis but implemented in Haskell using Hedgehog for
property-based testing.

## Running Tests

### Validate OpenAPI spec only (no network)

```bash
cabal test render-api-property
```

### Test against live server

```bash
# Set your API token
export WEYL_API_TOKEN="your-token-here"

# Run against sync server
cabal run render-api-test -- --url https://sync.render.weyl.ai

# Or against async server
cabal run render-api-test -- --url https://async.render.weyl.ai
```

### Using haskemathesis CLI directly

```bash
# Validate the spec
cabal run haskemathesis-cli -- validate --spec NEWSPECS/render.openapi.yaml

# Generate curl commands for operations
cabal run haskemathesis-cli -- curl --spec NEWSPECS/render.openapi.yaml --url https://sync.render.weyl.ai

# Run full property tests
cabal run haskemathesis-cli -- test \
  --spec NEWSPECS/render.openapi.yaml \
  --url https://sync.render.weyl.ai \
  --count 50 \
  --auth-header "Bearer $WEYL_API_TOKEN"
```

## What Gets Tested

1. **Request Generation**: Valid requests are generated from the OpenAPI schema
2. **Status Code Conformance**: Response status matches declared responses
3. **Content-Type Conformance**: Response content-type matches schema
4. **Response Schema Validation**: Response body validates against declared schema
5. **Required Headers**: Required response headers are present
6. **No Server Errors**: 5xx responses fail the test

## Negative Testing

Enable negative testing to verify the API correctly rejects invalid inputs:

```bash
cabal run haskemathesis-cli -- test \
  --spec NEWSPECS/render.openapi.yaml \
  --url https://sync.render.weyl.ai \
  --negative \
  --auth-header "Bearer $WEYL_API_TOKEN"
```

This generates mutations (invalid JSON, wrong types, missing required fields)
and verifies the API returns 4xx errors.

## OpenAPI Specs

| Spec | Description |
|------|-------------|
| `NEWSPECS/render.openapi.yaml` | Weyl Render API (video/image generation) |
| `IMPLEMENTATION/render.openapi.yaml` | Alternate copy |

## Adding New API Tests

1. Add your OpenAPI spec to `NEWSPECS/` or appropriate location
2. Create a new test file in `tests/property/`
3. Add test-suite to `lattice.cabal`
4. Follow the pattern in `RenderApiSpec.hs`
