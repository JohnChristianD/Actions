from pathlib import Path
import re
import sys

SOURCE = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
OUT = Path('.ci/generated-agda-safe')

text = SOURCE.read_text()
lines = text.splitlines(keepends=True)

# A section delimiter is a safe declaration boundary in this source: every
# delimiter currently follows complete top-level declarations. Generate a
# cumulative module at each such boundary, plus the final complete module.
boundaries = []
for i, line in enumerate(lines):
    if re.fullmatch(r'-{72,}\s*\n?', line):
        if i > 0:
            boundaries.append(i)

# Keep the probe count bounded so CI remains diagnostic rather than wasteful.
# Always include the final source as an independent stage.
selected = []
for i in boundaries:
    prefix = ''.join(lines[:i])
    if prefix.strip():
        selected.append(i)
if len(selected) > 18:
    step = max(1, len(selected) // 18)
    selected = selected[::step]
if boundaries and selected[-1] != boundaries[-1]:
    selected.append(boundaries[-1])

OUT.mkdir(parents=True, exist_ok=True)

# Remove stale generated probes so a deleted stage cannot linger in CI.
for old in OUT.glob('Stage*.agda'):
    old.unlink()

written = []
for n, boundary in enumerate(selected, 1):
    prefix = ''.join(lines[:boundary])
    module_name = f'Exotic.ERL.FullCoupled.CI.Stage{n:02d}'
    prefix = re.sub(
        r'(?m)^(module\s+)Exotic\.ERL\.FullCoupled\.CompleteSafe_v147(\s+where\s*)$',
        rf'\\1{module_name}\\2',
        prefix,
        count=1,
    )
    # Prefix probes intentionally end before the next section heading.
    # They must retain --safe and all original local definitions.
    path = OUT / f'Stage{n:02d}.agda'
    path.write_text(prefix)
    written.append(path)

print(f'safe-stage-count={len(written)}')
print('safe-stage-files=' + ','.join(str(p) for p in written))
if not written:
    print('ERROR: no stage probes generated', file=sys.stderr)
    sys.exit(1)
