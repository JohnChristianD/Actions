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

RESIDUAL = '''residualSquareNonzero_v140 ha hr hx =
  let hzero : alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _))
        (mu * (hx * hx)) ≡ alpha =
      trans
        (cong (λ q → alpha + Ring.neg (OrderedRing.ring _) (mu * q))
          (cong₂ (Ring._*_ (OrderedRing.ring _)) hx hx))
        (Ring.addZeroR (OrderedRing.ring _) alpha)
  in ⊥-elim (OrderedRing.notLtFromLe ha (subst (λ q → zero ≤ q) hzero hr))'''
RESIDUAL_FIXED = '''residualSquareNonzero_v140 ha hr hx = λ hx0 →
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
      xsq : Ring._*_ Rg x x ≡ Ring.zero Rg =
        trans
          (cong₂ (Ring._*_ Rg) hx0 hx0)
          (Ring.zeroMulR Rg (Ring.zero Rg))
      muxsq : Ring._*_ Rg mu (Ring._*_ Rg x x) ≡ Ring.zero Rg =
        trans
          (cong (Ring._*_ Rg mu) xsq)
          (Ring.zeroMulR Rg mu)
      hnegzero : Ring.neg Rg (Ring.zero Rg) ≡ Ring.zero Rg =
        trans
          (sym (Ring.addZeroR Rg (Ring.neg Rg (Ring.zero Rg))))
          (Ring.addNegL Rg (Ring.zero Rg))
      hr0 : alpha + Ring.neg Rg (Ring._*_ Rg mu (Ring._*_ Rg x x)) < zero =
        subst (λ q → alpha + Ring.neg Rg (Ring._*_ Rg mu q) < zero) xsq hr
      hr1 : alpha + Ring.neg Rg (Ring.zero Rg) < zero =
        subst (λ q → alpha + Ring.neg Rg q < zero) muxsq hr0
      hr2 : alpha + Ring.zero Rg < zero =
        subst (λ q → alpha + q < zero) hnegzero hr1
      hr3 : alpha < zero =
        subst (λ q → q < zero) (Ring.addZeroR Rg alpha) hr2
  in (OrderedRing.notLtFromLe (SmoothAlgebra.orderedRing _) ha) hr3'''

changed = 0
for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    text = path.read_text()
    new = text.replace(ACCUMULATE, ACCUMULATE_FIXED, 1)
    new = new.replace(INSERT, INSERT_FIXED, 1)
    new = new.replace(RESIDUAL, RESIDUAL_FIXED, 1)
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