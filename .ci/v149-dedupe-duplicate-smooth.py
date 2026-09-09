from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
record = 'record SmoothAlgebra : Set₁ where'
marker = "------------------------------------------------------------------------\n-- Canonical SmoothAlgebra boundary.\n"

# The canonical v149 boundary is authoritative. Any legacy SmoothAlgebra and
# its pre-canonical vector/matrix surface must be removed before checking the
# canonical definitions. Keep only the generic tabulateV helper from that old
# surface because the canonical matVec reuses it.
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

# Remove any later duplicated canonical SmoothAlgebra surface. The first is
# the retained authoritative definition.
first = s.find(record)
second = s.find(record, first + len(record)) if first >= 0 else -1
if second >= 0:
    keep = s.find('vAddZeroL :', second)
    if keep < 0:
        raise SystemExit('vAddZeroL terminator not found after duplicate SmoothAlgebra')
    s = s[:second] + s[keep:]

# A generic zipWithV already exists near the primitive vector helpers. The
# canonical vAdd/vSub/vHadamard blocks previously redeclared the same helper
# locally, which clashes at top-level scope under Agda 2.8.0. Reuse the single
# generic helper instead.
local_zip = '''  zipWithV : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
  zipWithV _ [] [] = []
  zipWithV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithV f xs ys
'''
s = s.replace(local_zip, '')

# Once the vAdd local zipWithV is removed, its where block can become empty;
# remove that block. Keep the surrounding vAdd definition unchanged.
vadd_empty_where = '''vAdd {S} = zipWithV (Ring._+_ (OrderedRing.ring (SmoothAlgebra.orderedRing S)))
  where

vSub :'''
s = s.replace(vadd_empty_where, '''vAdd {S} = zipWithV (Ring._+_ (OrderedRing.ring (SmoothAlgebra.orderedRing S)))

vSub :''')

# The vSub helper `sub` still needs a local type signature after local helper
# dedupe. Give it the exact scalar carrier type used by the surrounding S.
needle = '''vSub {S} = zipWithV sub
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  sub x y = Ring._+_ Rg x (Ring.neg Rg y)
'''
replacement = '''vSub {S} = zipWithV sub
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  sub : Scalar S → Scalar S → Scalar S
  sub x y = Ring._+_ Rg x (Ring.neg Rg y)
'''
if needle in s:
    s = s.replace(needle, replacement, 1)
else:
    if '  sub : Scalar S → Scalar S → Scalar S\n' not in s:
        raise SystemExit('vSub local sub declaration shape not found')

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
if 'vAdd {S} = zipWithV (Ring._+_ (OrderedRing.ring (SmoothAlgebra.orderedRing S)))\n  where\n' in s:
    raise SystemExit('empty vAdd where block remains')
p.write_text(s)
print('canonical vector helper dedupe normalized: global zipWithV, typed vSub sub, no empty vAdd where')