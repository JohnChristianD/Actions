from pathlib import Path
import re

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

# Accept either the legacy hidden binder or the canonical hiddenDim binder,
# then emit exactly one canonical record. Idempotent across repeated CI runs.
pattern = re.compile(
    r'record LSTMState \(S : SmoothAlgebra\) \((?:hidden|hiddenDim) : Nat\) : Set where\n'
    r'  field\n'
    r'    hidden : VecS S (?:hidden|hiddenDim)\n'
    r'    hidden : VecS S (?:hidden|hiddenDim)\n'
    r'    cell : VecS S (?:hidden|hiddenDim)\n',
    re.MULTILINE,
)
canonical = (
    'record LSTMState (S : SmoothAlgebra) (hiddenDim : Nat) : Set where\n'
    '  field\n'
    '    hidden : VecS S hiddenDim\n'
    '    cell : VecS S hiddenDim\n'
)

s2, count = pattern.subn(canonical, s, count=1)
if count == 0:
    # Canonical source may already be valid, or may use a single-field form.
    single = re.compile(
        r'record LSTMState \(S : SmoothAlgebra\) \((?:hidden|hiddenDim) : Nat\) : Set where\n'
        r'  field\n'
        r'    hidden cell : VecS S (?:hidden|hiddenDim)\n',
        re.MULTILINE,
    )
    s2, count = single.subn(canonical, s, count=1)

if count == 0:
    valid = re.search(
        r'record LSTMState \(S : SmoothAlgebra\) \(hiddenDim : Nat\) : Set where\n'
        r'  field\n'
        r'    hidden : VecS S hiddenDim\n'
        r'    cell : VecS S hiddenDim\n',
        s,
        re.MULTILINE,
    )
    if valid:
        s2 = s
        count = 1

if count != 1:
    raise SystemExit(f'LSTMState normalization expected canonicalizable record, found {count}')

p.write_text(s2)
print('lstm-state-normalization-v2=canonical-single-hidden-cell-record')