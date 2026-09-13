from pathlib import Path
import sys

FORBIDDEN = tuple(bytes.fromhex(code).decode("utf-8") for code in (
    "7472616e7363656e64656e74616c",
    "7472616e7363656e64656e74616c73",
    "6d756e6368617573656e",
    "6d756e636868617573656e",
    "6dc3bc6e636868617573656e",
))

SKIP_PARTS = {
    ".git",
    ".ci/external",
}

ROOT = Path(".")
errors = []

for path in ROOT.rglob("*"):
    if not path.is_file():
        continue
    rel = path.as_posix()
    if any(part in rel.split("/") for part in SKIP_PARTS):
        continue
    try:
        text = path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, OSError):
        continue
    lowered = text.casefold()
    for token in FORBIDDEN:
        if token in lowered:
            errors.append(f"forbidden theorem family token present in {rel}")

if errors:
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    raise SystemExit(1)

print("forbidden-theorem-families=absent")
