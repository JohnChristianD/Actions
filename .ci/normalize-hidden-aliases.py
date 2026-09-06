from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
old = '''record LSTMState (S : SmoothAlgebra) (hidden : Nat) : Set where
  field hidden cell : VecS S hidden
'''
new = '''record LSTMState (S : SmoothAlgebra) (hidden : Nat) : Set where
  field hiddenState cell : VecS S hidden
'''
changed = old in text
if changed:
    text = text.replace(old, new, 1)
text = text.replace('LSTMState.hidden ', 'LSTMState.hiddenState ')
text = text.replace('LSTMState.hidden\n', 'LSTMState.hiddenState\n')
text = text.replace('LSTMState.hidden)', 'LSTMState.hiddenState)')
# LSTMGates owns the four gate records; the enclosing LSTMBlock owns the field `gates`.
text = text.replace(
    'LSTMGates.gates (record { gates = g }) ≡ g',
    'LSTMBlock.gates (record { gates = g }) ≡ g',
    1,
)
path.write_text(text)
print(f'hidden-alias-normalized={changed};lstm-gates-owner-corrected=True')
