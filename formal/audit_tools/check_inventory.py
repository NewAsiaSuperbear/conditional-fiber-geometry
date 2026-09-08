#!/usr/bin/env python3
"""Fail-closed validation for DeclarationInventory Lean output."""
from __future__ import annotations

import argparse
import json
import shutil
from pathlib import Path

ALLOW = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED_ENTRY = {
    "name", "type", "source_module", "kind", "is_theorem", "is_axiom",
    "is_private_or_generated", "recursive_axioms", "unresolved_direct_dependencies",
}


def source_modules(formal_root: Path) -> set[str]:
    root = formal_root.resolve()
    files = [root / "CFG.lean", *sorted((root / "CFG").rglob("*.lean"))]
    if not files[0].is_file() or not (root / "CFG").is_dir():
        raise ValueError("formal root must contain CFG.lean and CFG/")
    return {".".join(p.relative_to(root).with_suffix("").parts) for p in files}


def extract_json(text: str) -> dict:
    decoder = json.JSONDecoder()
    for i, char in enumerate(text):
        if char != "{":
            continue
        try:
            value, end = decoder.raw_decode(text[i:])
        except json.JSONDecodeError:
            continue
        if not isinstance(value, dict):
            raise ValueError("inventory JSON must be an object")
        if text[end + i :].strip():
            raise ValueError("non-whitespace trailing content after inventory JSON")
        return value
    raise ValueError("no complete inventory JSON found")


def validate(report: dict, expected_modules: set[str]) -> dict:
    required = {
        "status", "selection", "source_modules", "declarations", "declaration_count",
        "type_rendering",
    }
    missing = sorted(required - report.keys())
    if missing:
        raise ValueError(f"missing top-level fields: {', '.join(missing)}")
    if not isinstance(report["status"], str) or report["status"] != "ENVIRONMENT_INVENTORY":
        raise ValueError("unexpected inventory status")
    modules = report["source_modules"]
    if (not isinstance(modules, list) or any(not isinstance(m, str) for m in modules)
            or set(modules) != expected_modules or len(modules) != len(set(modules))):
        raise ValueError("source_modules does not exactly match CFG source files")
    declarations = report["declarations"]
    if not isinstance(declarations, list) or not declarations:
        raise ValueError("declarations must be non-empty")
    if not isinstance(report["declaration_count"], int) or isinstance(report["declaration_count"], bool):
        raise ValueError("declaration_count must be an integer")
    if report["declaration_count"] != len(declarations):
        raise ValueError("declaration_count mismatch")
    names: set[str] = set()
    non_cfg_namespace = 0
    private_or_generated = 0
    for entry in declarations:
        if not isinstance(entry, dict) or not REQUIRED_ENTRY <= set(entry):
            raise ValueError("declaration entry missing required fields")
        name = entry["name"]
        if not isinstance(name, str) or not name or name in names:
            raise ValueError("declaration names must be non-empty and unique")
        names.add(name)
        if not isinstance(entry["source_module"], str):
            raise ValueError("source_module must be a string")
        if entry["source_module"] not in expected_modules:
            raise ValueError("declaration references unknown source module")
        if not isinstance(entry["type"], str) or not isinstance(entry["kind"], str):
            raise ValueError("type and kind must be strings")
        if any(not isinstance(entry[key], bool) for key in ("is_theorem", "is_axiom", "is_private_or_generated")):
            raise ValueError("declaration boolean fields must be bool")
        axioms = entry["recursive_axioms"]
        if not isinstance(axioms, list) or any(a not in ALLOW for a in axioms):
            raise ValueError("recursive_axioms contains an unapproved axiom")
        unresolved = entry["unresolved_direct_dependencies"]
        if unresolved != []:
            raise ValueError("unresolved_direct_dependencies must be empty")
        if entry["is_private_or_generated"]:
            private_or_generated += 1
        if not name == "CFG" and not name.startswith("CFG."):
            non_cfg_namespace += 1
    return {
        "status": "PASS_INVENTORY",
        "declaration_count": len(declarations),
        "source_module_count": len(expected_modules),
        "private_or_generated_count": private_or_generated,
        "non_cfg_namespace_count": non_cfg_namespace,
        "allowlist": sorted(ALLOW),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("log", type=Path)
    ap.add_argument("--formal-root", type=Path, required=True)
    ap.add_argument("-o", "--output", type=Path, required=True)
    ap.add_argument("--preserve", type=Path)
    args = ap.parse_args()
    try:
        text = args.log.read_text(encoding="utf-8")
        result = validate(extract_json(text), source_modules(args.formal_root))
        if args.preserve:
            args.preserve.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(args.log, args.preserve)
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(result, indent=2))
        return 0
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        result = {"status": "FAIL", "error": str(exc)}
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(result, indent=2))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
