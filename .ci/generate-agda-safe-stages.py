from pathlib import Path
import re
import sys

SOURCE = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
OUT = Path('Exotic/ERL/FullCoupled/CI')

text = SOURCE.read_text()
lines = text.splitlines(keepends=True)
boundaries = []
for i, line in enumerate(lines):
    if re.fullmatch(r'-{72,}\s*\n?', line) and i > 0:
        boundaries.append(i)

# Keep a bounded ladder while preserving the final section boundary.
selected = list(boundaries)
if len(selected) > 18:
    step = max(1, len(selected) // 18)
    selected = selected[::step]
if boundaries and selected[-1] != boundaries[-1]:
    selected.append(boundaries[-1])

OUT.mkdir(parents=True, exist_ok=True)
for old in OUT.glob('Stage*.agda'):
    old.unlink()

written = []
for n, boundary in enumerate(selected, 1):
    prefix = ''.join(lines[:boundary])
    module_name = f'Exotic.ERL.FullCoupled.CI.Stage{n:02d}'
    prefix = re.sub(
        r'(?m)^(module\s+)Exotic\.ERL\.FullCoupled\.CompleteSafe_v147(\s+where\s*)$',
        lambda m: m.group(1) + module_name + m.group(2),
        prefix,
        count=1,
    )
    # Make the probe self-identifying without modifying the mathematical
    # declarations: CI can report exactly which source frontier failed.
    prefix += (
        '\n------------------------------------------------------------------------\n'
        f'-- SAFE STAGE {n:02d}: source frontier ends before original line {boundary + 1}.\n'
    )
    path = OUT / f'Stage{n:02d}.agda'
    path.write_text(prefix)
    written.append((path, boundary + 1))

print(f'safe-stage-count={len(written)}')
for path, source_line in written:
    print(f'safe-stage={path}:frontier-line={source_line}')
if not written:
    print('ERROR: no stage probes generated', file=sys.stderr)
    sys.exit(1)
