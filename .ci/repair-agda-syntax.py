from pathlib import Path
import re

ACC_OLD = '''  accumulate i c (state s) = state (λ j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j)'''
ACC_NEW = '''  accumulateAt : Fin n → R → Cot → Cot
  accumulateAt i c s j with finDecEq j i
  ... | yes _ = s j + c
  ... | no _ = s j

  accumulate i c (state s) = state (accumulateAt i c s)'''

CVT_OLD = '''insertCVT_v142 D a i f = record { cell = λ j with finDecEq i j
  ... | no _ = CVTArchive_v142.cell a j
  ... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)
  ...   | false = record { occupied = true ; fitness = f }
  ...   | true with QProjectionDecisionAlgebra_v140.ltDec D
        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f
  ...     | yes _ = record { occupied = true ; fitness = f }
  ...     | no _ = CVTArchive_v142.cell a j }'''
CVT_NEW = '''insertCVT_v142 D a i f = record { cell = choose i }
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

RESIDUAL_RE = re.compile(r'residualSquareNonzero_v140 ha hr hx =\n.*?(?=\n------------------------------------------------------------------------\n)', re.S)
RESIDUAL_NEW = '''residualSquareNonzero_v140 ha hr hx = λ x0 →
  OrderedRing.notLtFromLe (SmoothAlgebra.orderedRing S) ha
    (subst (λ q → q < Ring.zero Rg) hzero hr0)
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  hr0 = subst (λ q → alpha + Ring.neg Rg (mu * q) < Ring.zero Rg) x0 hr
  hxx = trans (cong₂ (Ring._*_ Rg) x0 x0) (Ring.mulZeroR Rg (Ring.zero Rg))
  hmux = trans (cong (Ring._*_ Rg mu) hxx) (Ring.mulZeroR Rg mu)
  hnegzero = trans (sym (Ring.addZeroR Rg (Ring.neg Rg (Ring.zero Rg)))) (Ring.addNegL Rg (Ring.zero Rg))
  hzero = trans (cong (λ q → alpha + Ring.neg Rg q) hmux)
    (trans (cong (λ q → alpha + q) hnegzero) (Ring.addZeroR Rg alpha))'''

changed = 0
for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    text = path.read_text()
    new = text.replace(ACC_OLD, ACC_NEW, 1).replace(CVT_OLD, CVT_NEW, 1)
    new, count = RESIDUAL_RE.subn(RESIDUAL_NEW, new, count=1)
    if new != text:
        path.write_text(new)
        changed += 1

remaining = []
for path in Path('.').rglob('*.agda'):
    if '.git' not in path.parts:
        for line_no, line in enumerate(path.read_text().splitlines(), 1):
            if re.search(r'λ[^\n]*\bwith\b', line):
                remaining.append(f'{path}:{line_no}:{line}')
if remaining:
    print('\n'.join(remaining))
    raise SystemExit(1)
print(f'repaired-agda-files={changed}')
