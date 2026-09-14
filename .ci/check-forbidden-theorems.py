from pathlib import Path
import re
import sys

# The theorem surface is finite/dyadic only. Tokens are encoded so this guard
# cannot trip over its own literal vocabulary.
FORBIDDEN = tuple(bytes.fromhex(code).decode("utf-8") for code in (
    "7472616e7363656e64656e74616c",
    "7472616e7363656e64656e74616c73",
    "6972726174696f6e616c",
    "6972726174696f6e616c73",
    "6e6f6e2d647961646963",
    "6e6f6e647961646963",
    "642d747269",
    "645f747269",
    "64796164696367656f6d657472696335",
    "6c617a7977616c6b647961646963",
    "6c617a7977616c6b",
    "6479616469636c6164646572",
))

FORBIDDEN_EXACT = tuple(bytes.fromhex(code).decode("utf-8") for code in (
    "63656d",
    "715f657073696c6f6e",
    "71757073696c6f6e",
    "71ceb5",
))

FORBIDDEN_PATHS = (
    "LazyWalkDyadic.agda",
    "DyadicLadder.agda",
)

SKIP_PARTS = {
    ".git",
    ".ci/external",
    ".ci/check-forbidden-theorems.py",
}

ROOT = Path(".")
errors = []

for path in ROOT.rglob("*"):
    if not path.is_file():
        continue
    rel = path.as_posix()
    if any(part in rel.split("/") for part in SKIP_PARTS):
        continue
    if any(rel.endswith(bad_path) for bad_path in FORBIDDEN_PATHS):
        errors.append(f"forbidden finite-scope path present: {rel}")
        continue
    try:
        text = path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, OSError):
        continue
    lowered = text.casefold()
    for token in FORBIDDEN:
        if token in lowered:
            errors.append(f"forbidden finite-scope token present in {rel}")
    for token in FORBIDDEN_EXACT:
        if re.search(rf"(?<![A-Za-z0-9_]){re.escape(token)}(?![A-Za-z0-9_])", lowered):
            errors.append(f"forbidden finite-scope identifier present in {rel}")

if errors:
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    raise SystemExit(1)

print("finite-dyadic-theorem-scope=clean")
