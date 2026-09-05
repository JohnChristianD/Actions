from pathlib import Path
import re


def replace_between(text: str, start_marker: str, end_marker: str, replacement: str) -> str:
    start = text.find(start_marker)
    if start < 0:
        return text
    end = text.find(end_marker, start)
    if end < 0:
        return text
    return text[:start] + replacement.rstrip() + '\n' + text[end:]


def repair(path: Path) -> bool:
    text = path.read_text()
    original = text

    old_acc = '''  accumulate i c (state s) = state (λ j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j)'''
    new_acc = '''  accumulateAt : Fin n → R → Cot → Cot
  accumulateAt i c s j with finDecEq j i
  ... | yes _ = s j + c
  ... | no _ = s j

  accumulate i c (state s) = state (accumulateAt i c s)'''
    text = text.replace(old_acc, new_acc, 1)

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
    text = text.replace(old_cvt, new_cvt, 1)

    residual_start = 'residualSquareNonzero_v140 ha hr hx =\n'
    residual_end = '\n------------------------------------------------------------------------\n-- The clean, reusable cross-multiplication theorem'
    residual_fixed = '''residualSquareNonzero_v140 ha hr hx = λ x0 →
  ⊥-elim (OrderedRing.notLtFromLe (SmoothAlgebra.orderedRing S) ha
    (subst (λ q → q < zero) hzero hr))
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  hzero : alpha + Ring.neg Rg (mu * (x * x)) ≡ alpha
  hzero = trans
    (cong (λ q → alpha + Ring.neg Rg q)
      (cong₂ (Ring._*_ Rg) x0 x0))
    (trans
      (cong (λ q → alpha + q)
        (Ring.negZero Rg))
      (Ring.addZeroR Rg alpha))'''
    text = replace_between(text, residual_start, residual_end, residual_fixed)

    remaining = []
    for lineno, line in enumerate(text.splitlines(), 1):
        if re.search(r'λ[^\n]*\bwith\b', line):
            remaining.append(f'{path}:{lineno}:{line}')
    if remaining:
        print('\n'.join(remaining))
        raise SystemExit(1)

    if text != original:
        path.write_text(text)
        return True
    return False

changed = sum(repair(path) for path in Path('.').rglob('*.agda') if '.git' not in path.parts)
print(f'repaired-agda-files={changed}')
