from pathlib import Path
import re

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
record = 'record SmoothAlgebra : Set₁ where'
marker = "------------------------------------------------------------------------\n-- Canonical SmoothAlgebra boundary.\n"

first_record = s.find(record)
canonical = s.find(marker)
if first_record >= 0 and canonical >= 0 and first_record < canonical:
    tab = s.find('tabulateV :', first_record, canonical)
    if tab < 0:
        raise SystemExit('legacy tabulateV helper not found before canonical boundary')
    legacy_mat = s.find('\nmatVec :', tab, canonical)
    if legacy_mat < 0:
        raise SystemExit('legacy matVec declaration not found after tabulateV')
    tabulate_block = s[tab:legacy_mat]
    s = s[:first_record] + tabulate_block + '\n\n' + s[canonical:]

first = s.find(record)
second = s.find(record, first + len(record)) if first >= 0 else -1
if second >= 0:
    keep = s.find('vAddZeroL :', second)
    if keep < 0:
        raise SystemExit('vAddZeroL terminator not found after duplicate SmoothAlgebra')
    s = s[:second] + s[keep:]

s = s.replace('OrderedRing.base', 'OrderedRing.ring')

local_zip = '''  zipWithV : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
  zipWithV _ [] [] = []
  zipWithV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithV f xs ys
'''
s = s.replace(local_zip, '')

s = re.sub(r'(vAdd\s*\{S\}\s*=\s*zipWithV\s*\([^\n]+\))\n\s*where\n(?=\nvSub\s*:)', r'\1\n\n', s, count=1)
s = re.sub(r'(vHadamard\s*\{S\}\s*=\s*zipWithV\s*\([^\n]+\))\n\s*where\n(?=\nvSum\s*:)', r'\1\n\n', s, count=1)

sub_anchor = 'vSub {S} = zipWithV sub\n  where\n'
if sub_anchor in s:
    pos = s.index(sub_anchor) + len(sub_anchor)
    rest = s[pos:]
    local_block = rest.split('\n------------------------------------------------------------------------', 1)[0]
    if '  sub : Scalar S → Scalar S → Scalar S\n' not in local_block:
        m = re.match(r'(\s*Rg\s*=\s*[^\n]+\n)\s*(sub\s+x\s+y\s*=\s*[^\n]+\n)', rest)
        if not m:
            raise SystemExit('vSub local sub declaration shape not found')
        body = m.group(2).split('sub x y =', 1)[1].rstrip('\n')
        s = s[:pos] + rest.replace(m.group(0), m.group(1) + '  sub : Scalar S → Scalar S → Scalar S\n  sub x y = ' + body + '\n', 1)
else:
    raise SystemExit('vSub canonical declaration not found')

# Preserve the Gaussian log-normalization constant required downstream.
sa_start = s.find(record)
sa_end = s.find('\nopen SmoothAlgebra', sa_start)
if sa_start < 0 or sa_end < 0:
    raise SystemExit('canonical SmoothAlgebra block not found')
sa_block = s[sa_start:sa_end]
if '\n    pi : R\n' not in sa_block:
    from_nat = '    fromNat : Nat → R\n'
    if from_nat not in sa_block:
        raise SystemExit('SmoothAlgebra fromNat field not found for pi restoration')
    sa_block = sa_block.replace(from_nat, '    pi : R\n' + from_nat, 1)
    s = s[:sa_start] + sa_block + s[sa_end:]

old_ln = '''record LayerNorm (S : SmoothAlgebra) (d : Nat) : Set where
  field
    gain shift : VecS S d
    epsilon : Scalar S
    epsilonNonzero : epsilon ≠ Ring.zero (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    denominatorDomain : VecS S d → SmoothAlgebra.sqrtDomain S (layerNormVariance epsilon)
  where
  layerNormVariance : Scalar S → Scalar S
  layerNormVariance eps = eps
'''
new_ln = '''record LayerNorm (S : SmoothAlgebra) (d : Nat) : Set where
  field
    gain shift : VecS S d
    epsilon : Scalar S
    epsilonNonzero : epsilon ≠ Ring.zero (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    denominatorDomain : (xs : VecS S d) →
      SmoothAlgebra.sqrtDomain S (layerNormVariance xs epsilon)
'''
if old_ln in s:
    s = s.replace(old_ln, new_ln, 1)
elif 'denominatorDomain : (xs : VecS S d) →\n      SmoothAlgebra.sqrtDomain S (layerNormVariance xs epsilon)\n' not in s:
    raise SystemExit('LayerNorm malformed denominator-domain block not found uniquely')

top_level_variance_count = len(re.findall(r'(?m)^layerNormVariance\s*:', s))
if top_level_variance_count == 0:
    raise SystemExit('canonical top-level layerNormVariance declaration missing')
if top_level_variance_count != 1:
    raise SystemExit(f'layerNormVariance top-level definition count is {top_level_variance_count}, expected 1')

if s.count(record) != 1:
    raise SystemExit(f'SmoothAlgebra definition count is {s.count(record)}, expected 1')
if s.count('matVec :') != 1:
    raise SystemExit(f'matVec definition count is {s.count("matVec :")}, expected 1')
if s.count('matMul :') != 1:
    raise SystemExit(f'matMul definition count is {s.count("matMul :")}, expected 1')
if s.count('tabulateV :') != 1:
    raise SystemExit(f'tabulateV helper count is {s.count("tabulateV :")}, expected 1')
if s.count('zipWithV :') != 1:
    raise SystemExit(f'zipWithV definition count is {s.count("zipWithV :")}, expected 1')
if '\n    pi : R\n' not in s[sa_start:s.find('\nopen SmoothAlgebra', sa_start)]:
    raise SystemExit('pi restoration did not persist in canonical SmoothAlgebra')

p.write_text(s)
print('canonical algebra helper scope normalized: one SmoothAlgebra, one pi field, one top-level variance')
