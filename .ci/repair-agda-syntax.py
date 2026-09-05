from pathlib import Path
import re


def repair_file(path: Path) -> bool:
    lines = path.read_text().splitlines()
    changed = False
    out = []
    for line in lines:
        m = re.match(r'^(\s*)(leftNorm|rightNorm|lhs|rhs|hzero|hone|hdef|hcancel)(\s*:\s*.*)\s*=\s*$', line)
        if m:
            line = m.group(1) + m.group(2) + m.group(3)
            changed = True
        out.append(line)

    text = '\n'.join(out) + ('\n' if path.read_text().endswith('\n') else '')

    old_acc = '''  accumulate i c (state s) = state (λ j with finDecEq j i)
    ... | yes _ = s j + c
    ... | no _ = s j)'''
    new_acc = '''  accumulateAt : Fin n → R → Cot → Fin n → R
  accumulateAt i c s j with finDecEq j i
  ... | yes _ = s j + c
  ... | no _ = s j

  accumulate i c (state s) = state (λ j → accumulateAt i c s j)'''
    text2 = text.replace(old_acc, new_acc, 1)
    if text2 != text:
        text = text2
        changed = True

    old_cvt = '''insertCVT_v142 D a i f = record { cell = λ j with finDecEq i j
  ... | no _ = CVTArchive_v142.cell a j
  ... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)
  ...   | false = record { occupied = true ; fitness = f }
  ...   | true with QProjectionDecisionAlgebra_v140.ltDec D
        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f
  ...     | yes _ = record { occupied = true ; fitness = f }
  ...     | no _ = CVTArchive_v142.cell a j }'''
    new_cvt = '''insertCVT_v142 D a i f = record { cell = choose i }
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
    text2 = text.replace(old_cvt, new_cvt, 1)
    if text2 != text:
        text = text2
        changed = True

    text2 = re.sub(
        r'let hzero : alpha \+ Ring\.neg \(OrderedRing\.ring \(SmoothAlgebra\.orderedRing _\)\)\n'
        r'\s*\(mu \* \(hx \* hx\)\) ≡ alpha =\n\s*trans',
        'let\n      hzero : alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _))\n        (mu * (hx * hx)) ≡ alpha\n      hzero = trans', text, count=1)
    if text2 != text:
        text = text2
        changed = True

    if changed:
        path.write_text(text)
    return changed

changed = 0
for path in Path('.').rglob('*.agda'):
    if '.git' not in path.parts and repair_file(path):
        changed += 1

for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    for n, line in enumerate(path.read_text().splitlines(), 1):
        if ' λ ' in line and 'with' in line:
            print(f'{path}:{n}:{line}')
            raise SystemExit(1)
print(f'grammar-repaired-files={changed}')
