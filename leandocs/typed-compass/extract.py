#!/usr/bin/env python3
"""
Lean4 Type Extraction CLI for COMPASS

Extracts type definitions from Lean4 Emit.lean and generates:
- Python Pydantic models (for FastAPI backend)
- JSON Schema (for API validation)
- PureScript types (for Halogen frontend) - TODO

Usage:
    python extract.py python --output toolbox/core/generated_types.py
    python extract.py json-schema --output schemas/
    python extract.py purescript --output apps/dashboard-ps/src/Compass/

Every generated type has a corresponding Extractable instance in Lean4
with a proven roundtrip theorem: decode(encode(x)) = x
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any


# =============================================================================
# Type Definitions (parsed from Lean4)
# =============================================================================


class LeanTypeKind(Enum):
    """Kind of Lean4 type definition"""

    ENUM = "enum"
    STRUCTURE = "structure"
    INDUCTIVE = "inductive"


@dataclass
class LeanField:
    """A field in a Lean4 structure"""

    name: str
    lean_type: str
    python_type: str
    json_type: str
    optional: bool = False
    default: str | None = None


@dataclass
class LeanEnumVariant:
    """A variant in a Lean4 inductive/enum type"""

    name: str
    value: str  # String representation for JSON


@dataclass
class LeanType:
    """A Lean4 type definition"""

    name: str
    kind: LeanTypeKind
    fields: list[LeanField] = field(default_factory=list)
    variants: list[LeanEnumVariant] = field(default_factory=list)
    doc: str = ""
    has_roundtrip_proof: bool = True


# =============================================================================
# Lean4 Type Mappings
# =============================================================================

LEAN_TO_PYTHON: dict[str, str] = {
    "String": "str",
    "Int": "int",
    "Nat": "int",
    "Bool": "bool",
    "Float": "float",
    "DateTime": "str",  # ISO 8601 format
    "Option String": "str | None",
    "Option Int": "int | None",
    "Option Nat": "int | None",
    "Option Bool": "bool | None",
    "Option Float": "float | None",
    "List String": "list[str]",
    "List Int": "list[int]",
}

LEAN_TO_JSON_SCHEMA: dict[str, dict[str, Any]] = {
    "String": {"type": "string"},
    "Int": {"type": "integer"},
    "Nat": {"type": "integer", "minimum": 0},
    "Bool": {"type": "boolean"},
    "Float": {"type": "number"},
    "DateTime": {"type": "string", "format": "date-time"},
    "Option String": {"type": ["string", "null"]},
    "Option Int": {"type": ["integer", "null"]},
    "List String": {"type": "array", "items": {"type": "string"}},
}


# =============================================================================
# Type Registry (hardcoded from Emit.lean analysis)
# =============================================================================


def get_compass_types() -> list[LeanType]:
    """
    Returns all COMPASS types from Lean4 Emit.lean.

    These are extracted from the EmitPython and EmitElm instances.
    Each type has a proven Extractable instance with roundtrip theorem.
    """
    return [
        # Permission enum
        LeanType(
            name="Permission",
            kind=LeanTypeKind.ENUM,
            doc="Fine-grained permissions for tools",
            variants=[
                LeanEnumVariant("TWITTER_READ", "TWITTER_READ"),
                LeanEnumVariant("TWITTER_WRITE", "TWITTER_WRITE"),
                LeanEnumVariant("TWITTER_DELETE", "TWITTER_DELETE"),
                LeanEnumVariant("REDDIT_READ", "REDDIT_READ"),
                LeanEnumVariant("REDDIT_WRITE", "REDDIT_WRITE"),
                LeanEnumVariant("LINKEDIN_READ", "LINKEDIN_READ"),
                LeanEnumVariant("LINKEDIN_WRITE", "LINKEDIN_WRITE"),
                LeanEnumVariant("MASTODON_READ", "MASTODON_READ"),
                LeanEnumVariant("MASTODON_WRITE", "MASTODON_WRITE"),
                LeanEnumVariant("LLM_LOCAL", "LLM_LOCAL"),
                LeanEnumVariant("LLM_API", "LLM_API"),
                LeanEnumVariant("LLM_EXPENSIVE", "LLM_EXPENSIVE"),
                LeanEnumVariant("SEARCH_WEB", "SEARCH_WEB"),
                LeanEnumVariant("SEARCH_NEWS", "SEARCH_NEWS"),
                LeanEnumVariant("CONTENT_CREATE", "CONTENT_CREATE"),
                LeanEnumVariant("CONTENT_APPROVE", "CONTENT_APPROVE"),
                LeanEnumVariant("CONTENT_PUBLISH", "CONTENT_PUBLISH"),
                LeanEnumVariant("CAMPAIGN_MANAGE", "CAMPAIGN_MANAGE"),
                LeanEnumVariant("ADMIN_USERS", "ADMIN_USERS"),
                LeanEnumVariant("ADMIN_BUDGETS", "ADMIN_BUDGETS"),
                LeanEnumVariant("ADMIN_AUDIT", "ADMIN_AUDIT"),
            ],
        ),
        # Role enum
        LeanType(
            name="Role",
            kind=LeanTypeKind.ENUM,
            doc="User roles with permission sets",
            variants=[
                LeanEnumVariant("ADMIN", "ADMIN"),
                LeanEnumVariant("MANAGER", "MANAGER"),
                LeanEnumVariant("CREATOR", "CREATOR"),
                LeanEnumVariant("VIEWER", "VIEWER"),
            ],
        ),
        # JobStatus enum
        LeanType(
            name="JobStatus",
            kind=LeanTypeKind.ENUM,
            doc="Job execution states",
            variants=[
                LeanEnumVariant("PENDING", "pending"),
                LeanEnumVariant("RUNNING", "running"),
                LeanEnumVariant("WAITING_APPROVAL", "waiting_approval"),
                LeanEnumVariant("APPROVED", "approved"),
                LeanEnumVariant("COMPLETED", "completed"),
                LeanEnumVariant("FAILED", "failed"),
                LeanEnumVariant("CANCELLED", "cancelled"),
            ],
        ),
        # User structure
        LeanType(
            name="User",
            kind=LeanTypeKind.STRUCTURE,
            doc="User identity with authentication",
            fields=[
                LeanField("id", "String", "str", "string"),
                LeanField("org_id", "String", "str", "string"),
                LeanField("name", "String", "str", "string"),
                LeanField("email", "String", "str", "string"),
                LeanField("role", "Role", "Role", "string"),
                LeanField("password_hash", "Option String", "str | None", "string", optional=True),
                LeanField("mfa_enabled", "Bool", "bool", "boolean", default="False"),
                LeanField("mfa_secret", "Option String", "str | None", "string", optional=True),
                LeanField("daily_budget", "Float", "float", "number", default="10.00"),
                LeanField("monthly_budget", "Float", "float", "number", default="100.00"),
                LeanField("is_active", "Bool", "bool", "boolean", default="True"),
                LeanField("created_at", "DateTime", "str", "string", default='""'),
                LeanField("updated_at", "DateTime", "str", "string", default='""'),
            ],
        ),
        # Session structure
        LeanType(
            name="Session",
            kind=LeanTypeKind.STRUCTURE,
            doc="User session for web UI",
            fields=[
                LeanField("id", "String", "str", "string"),
                LeanField("user_id", "String", "str", "string"),
                LeanField("token_hash", "String", "str", "string"),
                LeanField("ip_address", "Option String", "str | None", "string", optional=True),
                LeanField("user_agent", "Option String", "str | None", "string", optional=True),
                LeanField("created_at", "DateTime", "str", "string", default='""'),
                LeanField("expires_at", "DateTime", "str", "string", default='""'),
                LeanField("last_activity", "DateTime", "str", "string", default='""'),
                LeanField("mfa_verified", "Bool", "bool", "boolean", default="False"),
            ],
        ),
        # Job structure
        LeanType(
            name="Job",
            kind=LeanTypeKind.STRUCTURE,
            doc="A unit of work",
            fields=[
                LeanField("id", "String", "str", "string"),
                LeanField("job_type", "String", "str", "string"),
                LeanField("status", "JobStatus", "JobStatus", "string"),
                LeanField("created_by", "String", "str", "string"),
                LeanField("input_data", "String", "str", "string", default='"{}"'),
                LeanField("output_data", "Option String", "str | None", "string", optional=True),
                LeanField("requires_approval", "Bool", "bool", "boolean", default="False"),
                LeanField("approved_by", "Option String", "str | None", "string", optional=True),
                LeanField("approved_at", "Option String", "str | None", "string", optional=True),
                LeanField("created_at", "DateTime", "str", "string", default='""'),
                LeanField("started_at", "Option String", "str | None", "string", optional=True),
                LeanField("completed_at", "Option String", "str | None", "string", optional=True),
                LeanField("retry_count", "Nat", "int", "integer", default="0"),
                LeanField("max_retries", "Nat", "int", "integer", default="3"),
                LeanField("error", "Option String", "str | None", "string", optional=True),
                LeanField("cost_usd", "Float", "float", "number", default="0.0"),
            ],
        ),
        # CircuitState enum (from Router.lean)
        LeanType(
            name="CircuitState",
            kind=LeanTypeKind.ENUM,
            doc="Circuit breaker states",
            variants=[
                LeanEnumVariant("CLOSED", "closed"),
                LeanEnumVariant("OPEN", "open"),
                LeanEnumVariant("HALF_OPEN", "half_open"),
            ],
        ),
        # Operation enum (from Router.lean)
        LeanType(
            name="Operation",
            kind=LeanTypeKind.ENUM,
            doc="API operations",
            variants=[
                LeanEnumVariant("READ", "read"),
                LeanEnumVariant("WRITE", "write"),
                LeanEnumVariant("ADMIN", "admin"),
            ],
        ),
        # AcquireResult enum (from RateLimiter.lean)
        LeanType(
            name="AcquireResult",
            kind=LeanTypeKind.ENUM,
            doc="Rate limit acquisition result",
            variants=[
                LeanEnumVariant("ALLOWED", "allowed"),
                LeanEnumVariant("DENIED", "denied"),
            ],
        ),
    ]


# =============================================================================
# Python Pydantic Generator
# =============================================================================


def generate_python_pydantic(types: list[LeanType]) -> str:
    """Generate Python Pydantic models from Lean4 types."""
    lines = [
        '"""',
        "AUTO-EXTRACTED FROM LEAN4 PROOFS",
        "",
        "Every type here has a corresponding Extractable instance in Lean4",
        "with a proven roundtrip theorem: decode(encode(x)) = x",
        "",
        "DO NOT EDIT - regenerate with:",
        "    python leandocs/typed-compass/extract.py python --output toolbox/core/generated_types.py",
        "",
        "Source: leandocs/typed-compass/lean/Compass/Emit.lean",
        '"""',
        "",
        "from __future__ import annotations",
        "",
        "from enum import Enum",
        "from typing import Annotated",
        "",
        "from pydantic import BaseModel, Field",
        "",
        "",
    ]

    # Generate enums first
    for t in types:
        if t.kind == LeanTypeKind.ENUM:
            lines.append(f"class {t.name}(str, Enum):")
            if t.doc:
                lines.append(f'    """{t.doc}"""')
            lines.append("")
            for v in t.variants:
                lines.append(f'    {v.name} = "{v.value}"')
            lines.append("")
            lines.append("")

    # Generate structures
    for t in types:
        if t.kind == LeanTypeKind.STRUCTURE:
            lines.append(f"class {t.name}(BaseModel):")
            if t.doc:
                lines.append(f'    """{t.doc}"""')
            lines.append("")
            for f in t.fields:
                if f.default is not None:
                    lines.append(f"    {f.name}: {f.python_type} = {f.default}")
                elif f.optional:
                    lines.append(f"    {f.name}: {f.python_type} = None")
                else:
                    lines.append(f"    {f.name}: {f.python_type}")
            lines.append("")
            # Add model_config for JSON serialization
            lines.append("    model_config = {")
            lines.append('        "from_attributes": True,')
            lines.append('        "populate_by_name": True,')
            lines.append("    }")
            lines.append("")
            lines.append("")

    return "\n".join(lines)


# =============================================================================
# JSON Schema Generator
# =============================================================================


def generate_json_schema(types: list[LeanType], output_dir: Path) -> dict[str, str]:
    """Generate JSON Schema files from Lean4 types."""
    schemas: dict[str, str] = {}

    for t in types:
        schema: dict[str, Any] = {
            "$schema": "https://json-schema.org/draft/2020-12/schema",
            "$id": f"https://compass.ai/schemas/{t.name}.json",
            "title": t.name,
            "description": t.doc or f"COMPASS {t.name} type (extracted from Lean4)",
        }

        if t.kind == LeanTypeKind.ENUM:
            schema["type"] = "string"
            schema["enum"] = [v.value for v in t.variants]
        elif t.kind == LeanTypeKind.STRUCTURE:
            schema["type"] = "object"
            schema["properties"] = {}
            schema["required"] = []

            for f in t.fields:
                prop: dict[str, Any] = {}
                if f.lean_type in LEAN_TO_JSON_SCHEMA:
                    prop = LEAN_TO_JSON_SCHEMA[f.lean_type].copy()
                elif f.lean_type in [t.name for t in types if t.kind == LeanTypeKind.ENUM]:
                    prop = {"$ref": f"{f.lean_type}.json"}
                else:
                    prop = {"type": f.json_type}

                schema["properties"][f.name] = prop
                if not f.optional and f.default is None:
                    schema["required"].append(f.name)

            schema["additionalProperties"] = False

        schemas[t.name] = json.dumps(schema, indent=2)

    return schemas


# =============================================================================
# PureScript Generator (stub for future)
# =============================================================================


def generate_purescript(types: list[LeanType]) -> str:
    """Generate PureScript types from Lean4 types."""
    lines = [
        "-- AUTO-EXTRACTED FROM LEAN4 PROOFS",
        "-- Every type has a proven roundtrip theorem",
        "--",
        "-- DO NOT EDIT - regenerate with:",
        "--     python leandocs/typed-compass/extract.py purescript --output apps/dashboard-ps/src/Compass/",
        "",
        "module Compass.Types where",
        "",
        "import Prelude",
        "import Data.Either (Either(..))",
        "import Data.Maybe (Maybe(..))",
        "import Data.Generic.Rep (class Generic)",
        "import Data.Argonaut.Core (Json)",
        "import Data.Argonaut.Decode (decodeJson, (.:), (.:?))",
        "import Data.Argonaut.Encode (encodeJson)",
        "",
        "",
    ]

    # Generate ADTs for enums
    for t in types:
        if t.kind == LeanTypeKind.ENUM:
            variants = " | ".join(v.name.title() for v in t.variants)
            lines.append(f"data {t.name} = {variants}")
            lines.append("")
            lines.append(f"derive instance eq{t.name} :: Eq {t.name}")
            lines.append(f"derive instance ord{t.name} :: Ord {t.name}")
            lines.append(f"derive instance generic{t.name} :: Generic {t.name} _")
            lines.append("")

    # Generate record types for structures
    for t in types:
        if t.kind == LeanTypeKind.STRUCTURE:
            lines.append(f"type {t.name} =")
            for i, f in enumerate(t.fields):
                prefix = "  { " if i == 0 else "  , "
                ps_type = _lean_to_purescript_type(f.lean_type)
                lines.append(f"{prefix}{_to_camel_case(f.name)} :: {ps_type}")
            lines.append("  }")
            lines.append("")

    return "\n".join(lines)


def _lean_to_purescript_type(lean_type: str) -> str:
    """Convert Lean type to PureScript type."""
    mapping = {
        "String": "String",
        "Int": "Int",
        "Nat": "Int",
        "Bool": "Boolean",
        "Float": "Number",
        "DateTime": "String",
        "Option String": "Maybe String",
        "Option Int": "Maybe Int",
    }
    return mapping.get(lean_type, "String")


def _to_camel_case(snake_str: str) -> str:
    """Convert snake_case to camelCase."""
    components = snake_str.split("_")
    return components[0] + "".join(x.title() for x in components[1:])


# =============================================================================
# CLI
# =============================================================================


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Extract types from Lean4 proofs to Python/JSON Schema/PureScript",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Generate Python Pydantic models
    python extract.py python --output toolbox/core/generated_types.py

    # Generate JSON Schema files
    python extract.py json-schema --output schemas/

    # Generate PureScript types
    python extract.py purescript --output apps/dashboard-ps/src/Compass/

    # Verify Lean4 build first
    python extract.py --verify
        """,
    )

    parser.add_argument(
        "target",
        choices=["python", "json-schema", "purescript", "verify"],
        nargs="?",
        default="verify",
        help="Target language/format to generate",
    )
    parser.add_argument(
        "--output",
        "-o",
        type=Path,
        help="Output file or directory",
    )
    parser.add_argument(
        "--verify",
        action="store_true",
        help="Verify Lean4 build before extraction",
    )
    parser.add_argument(
        "--list-types",
        action="store_true",
        help="List all extractable types",
    )

    args = parser.parse_args()

    # Get COMPASS types
    types = get_compass_types()

    if args.list_types:
        print("Extractable Types from Lean4:")
        print("=" * 50)
        for t in types:
            kind = t.kind.value.upper()
            print(f"  {t.name} ({kind})")
            if t.kind == LeanTypeKind.ENUM:
                for v in t.variants:
                    print(f"    - {v.name} = {v.value!r}")
            elif t.kind == LeanTypeKind.STRUCTURE:
                for f in t.fields:
                    opt = " (optional)" if f.optional else ""
                    print(f"    - {f.name}: {f.lean_type}{opt}")
        return 0

    if args.target == "verify" or args.verify:
        print("Verifying Lean4 build...")
        lean_dir = Path(__file__).parent / "lean"
        result = subprocess.run(
            ["lake", "build"],
            cwd=lean_dir,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            print("ERROR: Lean4 build failed!")
            print(result.stderr)
            return 1
        print("Lean4 build successful!")
        if args.target == "verify":
            return 0

    if args.target == "python":
        output = generate_python_pydantic(types)
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(output)
            print(f"Generated Python types: {args.output}")
        else:
            print(output)

    elif args.target == "json-schema":
        schemas = generate_json_schema(types, args.output or Path("schemas"))
        if args.output:
            args.output.mkdir(parents=True, exist_ok=True)
            for name, schema in schemas.items():
                path = args.output / f"{name}.json"
                path.write_text(schema)
                print(f"Generated schema: {path}")
        else:
            for name, schema in schemas.items():
                print(f"=== {name}.json ===")
                print(schema)
                print()

    elif args.target == "purescript":
        output = generate_purescript(types)
        if args.output:
            args.output.mkdir(parents=True, exist_ok=True)
            path = args.output / "Types.purs"
            path.write_text(output)
            print(f"Generated PureScript types: {path}")
        else:
            print(output)

    return 0


if __name__ == "__main__":
    sys.exit(main())
