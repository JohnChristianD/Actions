from pathlib import Path
import re


def repair(path: Path) -> bool:
    lines = path.read_text().splitlines()
    changed = False
    out = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if 'accumulate i c (state s) = state (λ j with finDecEq j i' in line:
            indent = line.split('accumulate', 1)[0]
            out.extend([
                indent + 'accumulate i c (state s) = state (λ j → addAt j)',
                indent + '  where',
                indent + '  addAt : Fin n → R',
                indent + '  addAt j with finDecEq j i',
                indent + '  ... | yes _ = s j + c',
                indent + '  ... | no _ = s j',
            ])
            changed = True
            i += 1
            while i < len(lines) and not lines[i].lstrip().startswith('runBack'):
                i += 1
            continue
        if 'insertCVT_v142 D a i f = record { cell = λ j with finDecEq i j' in line:
            indent = line.split('insertCVT_v142', 1)[0]
            out.extend([
                indent + 'insertCVT_v142 D a i f = record { cell = choose i }',
                indent + '  where',
                indent + '  choose : Fin cells → CVTSlot_v142 S',
                indent + '  choose j with finDecEq i j',
                indent + '  ... | no _ = CVTArchive_v142.cell a j',
                indent + '  ... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)',
                indent + '  ...   | false = record { occupied = true ; fitness = f }',
                indent + '  ...   | true with QProjectionDecisionAlgebra_v140.ltDec D',
                indent + '        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f',
                indent + '  ...     | yes _ = record { occupied = true ; fitness = f }',
                indent + '  ...     | no _ = CVTArchive_v142.cell a j }',
            ])
            changed = True
            i += 1
            while i < len(lines) and not lines[i].startswith('record AntitheticSample_v142'):
                i += 1
            continue
        out.append(line)
        i += 1
    if changed:
        path.write_text('\n'.join(out) + '\n')
    return changed

changed = sum(repair(path) for path in Path('.').rglob('*.agda') if '.git' not in path.parts)

remaining = []
for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    for line_no, line in enumerate(path.read_text().splitlines(), 1):
        if re.search(r'λ[^\n]*\bwith\b', line):
            remaining.append(f'{path}:{line_no}:{line}')
if remaining:
    print('\n'.join(remaining))
    raise SystemExit(1)
print(f'repaired-agda-files={changed}')
