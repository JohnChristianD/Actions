from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
changed = False

# Known LSTMState collision: the record parameter is `hidden`, while a field
# pair was also declared as `hidden cell`. Rename the field only.
old_lstm = '''record LSTMState (S : SmoothAlgebra) (hidden : Nat) : Set where
  field hidden cell : VecS S hidden
'''
new_lstm = '''record LSTMState (S : SmoothAlgebra) (hidden : Nat) : Set where
  field hiddenState cell : VecS S hidden
'''
if old_lstm in text:
    text = text.replace(old_lstm, new_lstm, 1)
    changed = True
text2 = text.replace('LSTMState.hidden ', 'LSTMState.hiddenState ')
text2 = text2.replace('LSTMState.hidden\n', 'LSTMState.hiddenState\n')
text2 = text2.replace('LSTMState.hidden)', 'LSTMState.hiddenState)')
text2 = text2.replace('LSTMState.hidden}', 'LSTMState.hiddenState}')
changed = changed or text2 != text
text = text2

# RecurrentAffine has the same collision in older revisions.
start = text.find('record RecurrentAffine (S : SmoothAlgebra)')
if start >= 0:
    end = text.find('\n------------------------------------------------------------------------\n', start)
    if end < 0:
        end = len(text)
    block = text[start:end]
    if '    hidden : VecS S hidden\n' in block:
        block = block.replace('    hidden : VecS S hidden\n', '    hiddenState : VecS S hidden\n', 1)
        text = text[:start] + block + text[end:]
        text = text.replace('RecurrentAffine.hidden ', 'RecurrentAffine.hiddenState ')
        text = text.replace('RecurrentAffine.hidden\n', 'RecurrentAffine.hiddenState\n')
        text = text.replace('RecurrentAffine.hidden)', 'RecurrentAffine.hiddenState)')
        changed = True

if 'field hidden cell : VecS S hidden' in text:
    raise SystemExit('LSTMState hidden field collision remains')

path.write_text(text)
print(f'hidden-alias-normalized={changed}')
