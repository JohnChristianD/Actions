from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

bad = '''record LSTMState (S : SmoothAlgebra) (hiddenDim : Nat) : Set where
  field
    hidden : VecS S hidden
    hidden : VecS S hidden
    cell : VecS S hidden
'''
good = '''record LSTMState (S : SmoothAlgebra) (hiddenDim : Nat) : Set where
  field
    hidden : VecS S hiddenDim
    cell : VecS S hiddenDim
'''
if bad in s:
    s = s.replace(bad, good, 1)

# Defensive repair for any remaining canonicalized record with stale field type.
s = s.replace('record LSTMState (S : SmoothAlgebra) (hiddenDim : Nat) : Set where\n  field\n    hidden cell : VecS S hidden',
              'record LSTMState (S : SmoothAlgebra) (hiddenDim : Nat) : Set where\n  field\n    hidden cell : VecS S hiddenDim')

p.write_text(s)
print('lstm-state-normalization=deduplicated-hidden-field-and-bound-to-hiddenDim')
