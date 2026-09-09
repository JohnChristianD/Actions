path = 'Exotic/ERL/FullCoupled/CompleteSafe_v147.agda'
s = File.read(path)

s.sub!('open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)',
       'open import Agda.Builtin.Nat using (Nat; suc)')

{
  'Vec A zero' => 'Vec A Nat.zero',
  'sumFin _ z zero _ = z' => 'sumFin _ z Nat.zero _ = z',
  'tabulateV {zero} f = []' => 'tabulateV {A = _} {n = Nat.zero} f = []',
  'tabulateVS {S} {zero} f = []' => 'tabulateVS {S} {Nat.zero} f = []',
  'zeroVector {S} {zero} = []' => 'zeroVector {S} {Nat.zero} = []',
  'zeroVecS {S} {zero} = []' => 'zeroVecS {S} {Nat.zero} = []',
  'vZero_v140 {S} {zero} = []' => 'vZero_v140 {S} {Nat.zero} = []',
  'maskAllFalse {zero} = []' => 'maskAllFalse {Nat.zero} = []',
  'qRunFuel_v142 zero r = r' => 'qRunFuel_v142 Nat.zero r = r',
  'shiftLV_v146 zero xs = xs' => 'shiftLV_v146 Nat.zero xs = xs',
  'shiftRV_v146 zero xs = xs' => 'shiftRV_v146 Nat.zero xs = xs',
  'qsaXorShiftDeterministic_v146 zero seed = []' => 'qsaXorShiftDeterministic_v146 Nat.zero seed = []'
}.each { |a, b| s.sub!(a, b) if s.include?(a) }

# The residual theorem uses SmoothAlgebra's dependent carrier explicitly.
s.sub!('residualSquareNonzero_v140 : ∀ {S}\n',
       'residualSquareNonzero_v140 : ∀ {S : SmoothAlgebra}\n')

# Agda local dependent lets use an equation binding directly here; the
# source's annotation was the remaining parser-sensitive shape.
s.sub!('  let hzero : alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _))\n        (mu * (hx * hx)) ≡ alpha =\n',
       '  let hzero =\n')

legacy = s.index('record SmoothAlgebra : Set₁ where')
canonical = s.index('-- Canonical SmoothAlgebra boundary.')
if legacy && canonical && legacy < canonical
  scalar = s.index("\nScalar : SmoothAlgebra → Set\n", legacy)
  abort 'legacy SmoothAlgebra block has no scalar boundary' unless scalar && scalar < canonical
  s = s[0...legacy] + s[(scalar + 1)..]
end

start_marker = "------------------------------------------------------------------------\n-- Canonical SmoothAlgebra boundary.\n"
end_marker = "------------------------------------------------------------------------\n-- Seven coupled parameter blocks and finite parameter indices\n"
first = s.index(start_marker)
abort 'canonical SmoothAlgebra start missing' unless first
last = s.index(end_marker, first + start_marker.length)
abort 'canonical SmoothAlgebra end missing' unless last
region = s[first...last]
record_token = 'record SmoothAlgebra : Set₁ where'
first_record = region.index(record_token)
abort 'canonical SmoothAlgebra record missing' unless first_record
while (second_record = region.index(record_token, first_record + record_token.length))
  scalar = region.index("\nScalar : SmoothAlgebra → Set\n", second_record)
  abort 'duplicate SmoothAlgebra has no scalar boundary' unless scalar
  region = region[0...second_record] + region[(scalar + 1)..]
end
s = s[0...first] + region + s[last..]

old_max = "    sqrt recip max min : R → R\n"
new_max = "    sqrt recip : R → R\n    max min : R → R → R\n"
if s.include?(old_max)
  s.sub!(old_max, new_max)
elif !s.include?('    max min : R → R → R')
  abort 'SmoothAlgebra max/min signature missing'
end

needle = "    reciprocalLaw : ∀ {d} → zero < d → Ring._*_ (Ring.R (OrderedRing.ring orderedRing)) d (recip d) ≡ one\n"
needle2 = "    reciprocalLaw : ∀ {d} → zero < d → Ring._*_ (OrderedRing.ring orderedRing) d (recip d) ≡ one\n"
unless s.include?('    sqrtDomain : R → Set\n')
  if s.include?(needle)
    s.sub!(needle, needle + "    sqrtDomain : R → Set\n    sqrtSquareLaw : ∀ x → sqrtDomain x →\n      Ring._*_ (OrderedRing.ring orderedRing) (sqrt x) (sqrt x) ≡ x\n")
  elsif s.include?(needle2)
    s.sub!(needle2, needle2 + "    sqrtDomain : R → Set\n    sqrtSquareLaw : ∀ x → sqrtDomain x →\n      Ring._*_ (OrderedRing.ring orderedRing) (sqrt x) (sqrt x) ≡ x\n")
  end
end

old_acc = <<~AGDA
  accumulate : Fin n → R → EState → EState
  accumulate i c (state s) = state (λ j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j)
AGDA
new_acc = <<~AGDA
  accumulateAt : Fin n → R → Cot → Fin n → R
  accumulateAt i c s j with finDecEq j i
  ... | yes _ = s j + c
  ... | no _ = s j

  accumulate : Fin n → R → EState → EState
  accumulate i c (state s) = state (accumulateAt i c s)
AGDA
s.sub!(old_acc, new_acc)

old_cvt = <<~AGDA
insertCVT_v142 : ∀ {S cells} → QProjectionDecisionAlgebra_v140 S →
  CVTArchive_v142 S cells → Fin cells → Scalar S → CVTArchive_v142 S cells
insertCVT_v142 D a i f = record { cell = λ j with finDecEq i j
  ... | no _ = CVTArchive_v142.cell a j
  ... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)
  ...   | false = record { occupied = true ; fitness = f }
  ...   | true with QProjectionDecisionAlgebra_v140.ltDec D
        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f
  ...     | yes _ = record { occupied = true ; fitness = f }
  ...     | no _ = CVTArchive_v142.cell a j }
AGDA
new_cvt = <<~AGDA
makeCVTSlot_v142 : ∀ {S} → Scalar S → CVTSlot_v142 S
makeCVTSlot_v142 f = record { occupied = true ; fitness = f }

insertCVTOccupied_v142 : ∀ {S} → QProjectionDecisionAlgebra_v140 S →
  CVTSlot_v142 S → Scalar S → CVTSlot_v142 S
insertCVTOccupied_v142 D slot f with QProjectionDecisionAlgebra_v140.ltDec D
  (CVTSlot_v142.fitness slot) f
... | yes _ = makeCVTSlot_v142 f
... | no _ = slot

insertCVTReplacement_v142 : ∀ {S} → QProjectionDecisionAlgebra_v140 S →
  CVTSlot_v142 S → Scalar S → CVTSlot_v142 S
insertCVTReplacement_v142 D slot f with CVTSlot_v142.occupied slot
... | false = makeCVTSlot_v142 f
... | true = insertCVTOccupied_v142 D slot f

insertCVTCell_v142 : ∀ {S cells} → QProjectionDecisionAlgebra_v140 S →
  CVTArchive_v142 S cells → Fin cells → Scalar S → Fin cells → CVTSlot_v142 S
insertCVTCell_v142 D a i f j with finDecEq i j
... | no _ = CVTArchive_v142.cell a j
... | yes _ = insertCVTReplacement_v142 D (CVTArchive_v142.cell a j) f

insertCVT_v142 : ∀ {S cells} → QProjectionDecisionAlgebra_v140 S →
  CVTArchive_v142 S cells → Fin cells → Scalar S → CVTArchive_v142 S cells
insertCVT_v142 D a i f = record
  { cell = insertCVTCell_v142 D a i f
  }
AGDA
s.sub!(old_cvt, new_cvt)

segment_start = s.index('record OrderedRing')
segment_end = s.index("\n------------------------------------------------------------------------", segment_start)
segment = s[segment_start...segment_end]
qualifications = {
  'a + c ≤ b + d' => 'Ring._+_ ring a c ≤ Ring._+_ ring b d',
  'a + neg b < zero' => 'Ring._+_ ring a (neg b) < zero',
  'zero < a * b' => 'zero < Ring._*_ ring a b',
  'zero ≤ a * b' => 'zero ≤ Ring._*_ ring a b',
  'c * a ≤ c * b' => 'Ring._*_ ring c a ≤ Ring._*_ ring c b',
  'c * a < c * b' => 'Ring._*_ ring c a < Ring._*_ ring c b',
  'a * e < b * d' => 'Ring._*_ ring a e < Ring._*_ ring b d',
  'zero < x * x' => 'zero < Ring._*_ ring x x',
  'zero ≤ x * x' => 'zero ≤ Ring._*_ ring x x',
  'a < b → c < d → a + c < b + d' => 'a < b → c < d → Ring._+_ ring a c < Ring._+_ ring b d',
  'a < b → c + a < c + b' => 'a < b → c < d → Ring._+_ ring c a < Ring._+_ ring c b',
  'abs (x + y) ≤ abs x + abs y' => 'abs (Ring._+_ ring x y) ≤ Ring._+_ ring (abs x) (abs y)',
  'abs (x * y) ≡ abs x * abs y' => 'abs (Ring._*_ ring x y) ≡ Ring._*_ ring (abs x) (abs y)'
}
qualifications.each { |a, b| segment.gsub!(a, b) }
s = s[0...segment_start] + segment + s[segment_end..]

marker = 'reciprocalNonnegative_v146 {S} {d} hd with'
start = s.index(marker)
if start
  ending = s.index("\n------------------------------------------------------------------------", start)
  replacement = <<~AGDA
reciprocalNonnegative_v146 {S} {d} hd with
  ltDec (SmoothAlgebra.orderedRing S)
    (SmoothAlgebra.recip S d) zero
... | yes hneg =
  ⊥-elim
    (OrderedRing.notLtFromLe
      (OrderedRing.ltLe (OrderedRing.zeroLtOne
        {orderedRing = SmoothAlgebra.orderedRing S}))
      (trans
        (sym (SmoothAlgebra.reciprocalLaw S hd))
        (trans
          (OrderedRing.mulLtPosLeft hneg hd)
          (Ring.mulZeroR
            (OrderedRing.ring (SmoothAlgebra.orderedRing S)) d))))
... | no h = h
AGDA
  s = s[0...start] + replacement + s[ending..]
end

s.gsub!('      hx : x ≠ zero =', '      hx =')
s.gsub!('      hxx : zero < x * x =', '      hxx =')
s.gsub!('      hlt : alpha < mu * (x * x) =', '      hlt =')
s.gsub!('      leftNorm : c * (a * SmoothAlgebra.recip _ d) ≡ a * e =', '      leftNorm =')
s.gsub!('      rightNorm : c * (b * SmoothAlgebra.recip _ e) ≡ b * d =', '      rightNorm =')
s.gsub!('        lhs : n * (d + neg z) ≡ base + neg (n * z) =', '        lhs =')
s.gsub!('        rhs : (n + neg y) * d ≡ base + neg (y * d) =', '        rhs =')
s.gsub!('        hzero : d * zero ≡ zero =', '        hzero =')
s.gsub!('        hone : zero < one =', '        hone =')
s.gsub!('      hdef : hb ≡ CoupledHyperParameters_v146.q h * e =', '      hdef =')
s.gsub!('      hcancel : e * SmoothAlgebra.recip _ e ≡ one =', '      hcancel =')

File.write(path, s)
abort 'duplicate SmoothAlgebra remained' unless s.scan('record SmoothAlgebra : Set₁ where').length == 1
abort 'unqualified Nat zero import remained' if s.include?('open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)')
abort 'dependent lambda-with remained' if s.include?('λ j with finDecEq')
puts 'v150 shell-free Ruby migration: PASS'
