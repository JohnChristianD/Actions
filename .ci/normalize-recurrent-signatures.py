from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
old = s

pairs = {
    '∀ {S input hidden} →': '∀ {S input hiddenDim} →',
    'RecurrentAffine S input hidden → VecS S input → VecS S hidden → VecS S hidden':
        'RecurrentAffine S input hiddenDim → VecS S input → VecS S hiddenDim → VecS S hiddenDim',
    'LSTMBlock S input hidden → LSTMState S hidden → VecS S input → LSTMState S hidden':
        'LSTMBlock S input hiddenDim → LSTMState S hiddenDim → VecS S input → LSTMState S hiddenDim',
    '(block : LSTMBlock S input hidden) →\n  LSTMState S hidden → Vec (VecS S input) n → LSTMState S hidden':
        '(block : LSTMBlock S input hiddenDim) →\n  LSTMState S hiddenDim → Vec (VecS S input) n → LSTMState S hiddenDim',
    '(block : LSTMBlock S input hidden)\n  (state : LSTMState S hidden)':
        '(block : LSTMBlock S input hiddenDim)\n  (state : LSTMState S hiddenDim)',
}
for a, b in pairs.items():
    s = s.replace(a, b)

if s == old:
    raise SystemExit('recurrent signature normalizer made no changes')
p.write_text(s)
print('recurrent-signatures=hiddenDim')