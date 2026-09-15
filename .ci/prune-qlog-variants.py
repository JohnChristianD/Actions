from pathlib import Path
import re
import sys

CANONICAL = Path("Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda")
SKIP_PARTS = {".git", ".ci/external"}
ACTIVE_SYMBOLS = (
    "finiteQLog8",
    "negativeFiniteQLog8",
    "negativeAlpha8",
    "canonicalQLogControl",
    "qLogSignal",
    "canonicalQLogStep",
)
IMPLEMENTATION_NAMES = re.compile(
    r"^(?:finiteQLog8|negativeFiniteQLog8|negativeAlpha8|canonicalQLogControl|qLogSignal|canonicalQLogStep)\s*:",
    re.MULTILINE,
)

if not CANONICAL.is_file():
    print(f"ERROR: canonical q-log surface missing: {CANONICAL}", file=sys.stderr)
    raise SystemExit(1)

canonical_text = CANONICAL.read_text(encoding="utf-8")
missing = [name for name in ACTIVE_SYMBOLS if name not in canonical_text]
if missing:
    print("ERROR: canonical q-log surface is incomplete: " + ", ".join(missing), file=sys.stderr)
    raise SystemExit(1)

# This is intentionally an audit, not a destructive deletion step.  While the
# canonical learner still uses a q-log shaping variant, automation should prune
# duplicate implementations only after they have been explicitly retired.
duplicates = []
for path in Path(".").rglob("*.agda"):
    rel = path.as_posix()
    if path == CANONICAL or any(part in rel.split("/") for part in SKIP_PARTS):
        continue
    try:
        text = path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, OSError):
        continue
    if IMPLEMENTATION_NAMES.search(text):
        duplicates.append(rel)

print("active-qlog-boundary=present")
print("canonical-qlog-implementation=" + CANONICAL.as_posix())
if duplicates:
    print("duplicate-qlog-implementations=")
    for path in sorted(duplicates):
        print("  " + path)
    print("prune-policy=manual-retirement-required")
else:
    print("duplicate-qlog-implementations=absent")
    print("prune-policy=clean")
