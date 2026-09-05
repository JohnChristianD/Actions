from pathlib import Path
import re

replacements = [
    (re.compile(r'  accumulate i c \(state s\) = state \(λ j with finDecEq j i\n    \.\.\. \| yes _ = s j \+ c\n    \.\.\. \| no _ = s j\)'), '''  accumulate i c (state s) = state (λ j → addAt j)
    where
    addAt : Fin n → R
    addAt j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j'''),
    (re.compile(r'insertCVT_v142 D a i f = record \{ cell = λ j with finDecEq i j\n.*?\.\.\.\s*\| no _ = CVTArchive_v142\.cell a j \}', re.S), '''insertCVT_v142 D a i f = record { cell = choose i }
  where
  choose : Fin cells → CVTSlot_v142 S
  choose j with finDecEq i j
  ... | no _ = CVTArchive_v142.cell a j
  ... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)
  ...   | false = record { occupied = true ; fitness = f }
  ...   | true with QProjectionDecisionAlgebra_v140.ltDec D
        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f
  ...     | yes _ = record { occupied = true ; fitness = f }
  ...     | no _ = CVTArchive_v142.cell a j }'''),
    (re.compile(r'residualSquareNonzero_v140 ha hr \(hx0\) =\n.*?(?=\n------------------------------------------------------------------------\n)', re.S), '''residualSquareNonzero_v140 ha hr hx0 =
  ⊥-elim (OrderedRing.notLtFromLe (SmoothAlgebra.orderedRing S) ha) hr3
  where
  Rg : Ring
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)

  hxx : Ring._*_ Rg x x ≡ Ring.zero Rg
  hxx = trans (cong₂ (Ring._*_ Rg) hx0 hx0)
    (Ring.zeroMulR Rg (Ring.zero Rg))

  hmuxx : Ring._*_ Rg mu (Ring._*_ Rg x x) ≡ Ring.zero Rg
  hmuxx = trans (cong (Ring._*_ Rg mu) hxx)
    (Ring.zeroMulR Rg mu)

  hnegzero : Ring.neg Rg (Ring.zero Rg) ≡ Ring.zero Rg
  hnegzero = trans
    (sym (Ring.addZeroR Rg (Ring.neg Rg (Ring.zero Rg))))
    (Ring.addNegL Rg (Ring.zero Rg))

  hr0 : alpha + Ring.neg Rg (Ring._*_ Rg mu (Ring._*_ Rg x x)) < Ring.zero Rg
  hr0 = subst
    (λ q → alpha + Ring.neg Rg (Ring._*_ Rg mu q) < Ring.zero Rg)
    hxx hr

  hr1 : alpha + Ring.neg Rg (Ring.zero Rg) < Ring.zero Rg
  hr1 = subst (λ q → alpha + Ring.neg Rg q < Ring.zero Rg)
    hmuxx hr0

  hr2 : alpha + Ring.zero Rg < Ring.zero Rg
  hr2 = subst (λ q → alpha + q < Ring.zero Rg)
    hnegzero hr1

  hr3 : alpha < Ring.zero Rg
  hr3 = subst (λ q → q < Ring.zero Rg)
    (Ring.addZeroR Rg alpha) hr2'''),
    (re.compile(r'orderedFieldCrossStrict_v142 a b d e hd he h =\n.*?(?=\n------------------------------------------------------------------------\n)', re.S), '''orderedFieldCrossStrict_v142 a b d e hd he h =
  OrderedRing.mulLtPosCancelLeft (transportLt_v142 leftNorm rightNorm h) hc
  where
  Rg : Ring
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  c : Scalar S
  c = d * e
  hc : zero < c
  hc = OrderedRing.mulPos hd he
  leftNorm : c * (a * SmoothAlgebra.recip _ d) ≡ a * e
  leftNorm = trans (Ring.mulComm Rg c (a * SmoothAlgebra.recip _ d))
    (trans (Ring.mulAssoc Rg a (SmoothAlgebra.recip _ d) c)
      (trans (cong (λ q → a * q)
        (trans (sym (Ring.mulAssoc Rg (SmoothAlgebra.recip _ d) d e))
          (trans (cong (λ q → q * e) (Ring.mulComm Rg (SmoothAlgebra.recip _ d) d))
            (trans (cong (λ q → q * e) (SmoothAlgebra.reciprocalLaw _ hd))
              (Ring.mulOneL Rg e))))) refl))
  rightNorm : c * (b * SmoothAlgebra.recip _ e) ≡ b * d
  rightNorm = trans (Ring.mulComm Rg c (b * SmoothAlgebra.recip _ e))
    (trans (Ring.mulAssoc Rg b (SmoothAlgebra.recip _ e) c)
      (trans (cong (λ q → b * q)
        (trans (sym (Ring.mulAssoc Rg (SmoothAlgebra.recip _ e) e d))
          (trans (cong (λ q → q * d) (Ring.mulComm Rg (SmoothAlgebra.recip _ e) e))
            (trans (cong (λ q → q * d) (SmoothAlgebra.reciprocalLaw _ he))
              (Ring.mulOneL Rg d))))) refl))'''),
    (re.compile(r'multiplierDeletionStrict_v142 n d y z hd he h =\n.*?(?=\n------------------------------------------------------------------------\n)', re.S), '''multiplierDeletionStrict_v142 n d y z hd he h =
  orderedFieldCrossStrict_v142 n (n + neg y) d (d + neg z) hd he cross'
  where
  Rg : Ring
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)

  base : Scalar S
  base = n * d

  lhs : n * (d + neg z) ≡ base + neg (n * z)
  lhs = trans (Ring.distrib Rg n d (neg z))
    (cong₂ _+_ refl (sym (Ring.negScale Rg n z)))

  rhs : (n + neg y) * d ≡ base + neg (y * d)
  rhs = trans (Ring.distrib Rg d n (neg y))
    (trans (cong₂ _+_ (Ring.mulComm Rg d n) refl)
      (cong₂ _+_ refl
        (trans (Ring.mulComm Rg (neg y) d)
          (sym (Ring.negScale Rg y d)))))

  cross : base + neg (n * z) < base + neg (y * d)
  cross = OrderedRing.addLtLeft (OrderedRing.negLt h) base

  cross' : n * (d + neg z) < (n + neg y) * d
  cross' = transportLt_v142 lhs rhs cross''')
]

changed = 0
for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    text = path.read_text()
    new = text
    for pattern, replacement in replacements:
        new = pattern.sub(replacement, new, count=1)
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