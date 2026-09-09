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

old_ops = '    sqrt recip max min : R → R\n'
if old_ops in s:
    s = s.replace(old_ops, '    sqrt recip : R → R\n    max min : R → R → R\n', 1)

old_domain_anchor = '    reciprocalLaw : ∀ {d} → zero < d → Ring._*_ (OrderedRing.ring orderedRing) d (recip d) ≡ one\n'
if old_domain_anchor in s and '    sqrtDomain : R → Set\n' not in s:
    s = s.replace(old_domain_anchor, old_domain_anchor +
        '    sqrtDomain : R → Set\n'
        '    sqrtSquareLaw : ∀ x → sqrtDomain x →\n'
        '      Ring._*_ (OrderedRing.ring orderedRing) (sqrt x) (sqrt x) ≡ x\n', 1)

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
    if '  sub : Scalar S → Scalar S → Scalar S\n' not in rest.split('\n------------------------------------------------------------------------', 1)[0]:
        m = re.match(r'(\s*Rg\s*=\s*[^\n]+\n)\s*(sub\s+x\s+y\s*=\s*[^\n]+\n)', rest)
        if not m:
            raise SystemExit('vSub local sub declaration shape not found')
        body = m.group(2).split('sub x y =', 1)[1].rstrip('\n')
        s = s[:pos] + rest.replace(m.group(0), m.group(1) + '  sub : Scalar S → Scalar S → Scalar S\n  sub x y = ' + body + '\n', 1)
else:
    raise SystemExit('vSub canonical declaration not found')

# Preserve pi if the canonical algebra record has the simple scalar opener.
sa_start = s.find(record)
if sa_start < 0:
    raise SystemExit('SmoothAlgebra record not found')
sa_end = s.find('\nopen SmoothAlgebra', sa_start)
if sa_end < 0:
    # Some earlier normalizers consume the explicit `open` line. Find the
    # first declaration that follows the record instead; do not treat this as
    # a proof failure.
    sa_end = s.find('\nScalar :', sa_start)
if sa_end < 0:
    raise SystemExit('SmoothAlgebra block terminator not found')
sa_block = s[sa_start:sa_end]
if '\n    pi : R\n' not in sa_block:
    from_nat = '    fromNat : Nat → R\n'
    if from_nat in sa_block:
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

record_marker = 'record LayerNorm (S : SmoothAlgebra) (d : Nat) : Set where\n'
mean_marker = 'layerNormMean : ∀ {S d} → VecS S d → Scalar S\n'
inv_marker = 'layerNormInvRootLaw : ∀ {S d} (ln : LayerNorm S d) (xs : VecS S d) →\n'
if record_marker in s and mean_marker in s and inv_marker in s:
    record_pos = s.index(record_marker)
    mean_pos = s.index(mean_marker)
    if mean_pos > record_pos:
        inv_pos = s.index(inv_marker, mean_pos)
        block = s[mean_pos:inv_pos]
        s = s[:mean_pos] + s[inv_pos:]
        record_pos = s.index(record_marker)
        s = s[:record_pos] + block + s[record_pos:]

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
if s.count('sqrtDomain : R → Set') != 1:
    raise SystemExit(f'sqrt domain law count is {s.count("sqrtDomain : R → Set")}, expected 1')

p.write_text(s)
print('canonical algebra helper scope normalized: one SmoothAlgebra, binary max/min, domain-aware root, one pi field, one top-level variance')