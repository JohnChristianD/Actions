from pathlib import Path
import re

ACCUMULATE = '''  accumulate i c (state s) = state (λ j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j)'''
ACCUMULATE_FIXED = '''  accumulate i c (state s) = state (λ j → addAt j)
    where
    addAt : Fin n → R
    addAt j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j'''

INSERT = '''insertCVT_v142 D a i f = record { cell = λ j with finDecEq i j
  ... | no _ = CVTArchive_v142.cell a j
  ... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)
  ...   | false = record { occupied = true ; fitness = f }
  ...   | true with QProjectionDecisionAlgebra_v140.ltDec D
        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f
  ...     | yes _ = record { occupied = true ; fitness = f }
  ...     | no _ = CVTArchive_v142.cell a j }'''
INSERT_FIXED = '''insertCVT_v142 D a i f = record { cell = choose i }
  where
  choose : Fin cells → CVTSlot_v142 S
  choose j with finDecEq i j
  ... | no _ = CVTArchive_v142.cell a j
  ... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)
  ...   | false = record { occupied = true ; fitness = f }
  ...   | true with QProjectionDecisionAlgebra_v140.ltDec D
        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f
  ...     | yes _ = record { occupied = true ; fitness = f }
  ...     | no _ = CVTArchive_v142.cell a j }'''

changed = 0
for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    text = path.read_text()
    new = text.replace(ACCUMULATE, ACCUMULATE_FIXED, 1)
    new = new.replace(INSERT, INSERT_FIXED, 1)
    if new != text:
        path.write_text(new)
        changed += 1

remaining = []
for path in Path('.').rglob('*.agda'):
    if '.git' not in path.parts:
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            if re.search(r'λ[^\n]*\bwith\b', line):
                remaining.append(f'{path}:{lineno}:{line}')

if remaining:
    print('\n'.join(remaining))
    raise SystemExit('unrepaired extended lambda syntax remains')

print(f'repaired-agda-files={changed}')
