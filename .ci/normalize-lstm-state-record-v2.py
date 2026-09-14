from pathlib import Path
import re

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

pattern = re.compile(
    r'record LSTMState \(S : SmoothAlgebra\) \(hiddenDim : Nat\) : Set where\n'
    r'(?:  field\n)?'
    r'(?:    hidden : VecS S hidden(?:Dim)?\n)+'
    r'(?:    cell : VecS S hiddenDim\n)?',
    re.MULTILINE,
)
replacement = (
    'record LSTMState (S : SmoothAlgebra) (hiddenDim : Nat) : Set where\n'
    '  field\n'
    '    hidden : VecS S hiddenDim\n'
    '    cell : VecS S hiddenDim\n'
)
s2, count = pattern.subn(replacement, s, count=1)
if count != 1:
    raise SystemExit(f'LSTMState normalization expected one record, found {count}')
p.write_text(s2)
print('lstm-state-normalization-v2=canonical-single-hidden-cell-record')
