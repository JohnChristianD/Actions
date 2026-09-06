from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
needle = 'open import Agda.Builtin.Unit using (⊤; tt)\n\n'
insert = '''open import Agda.Builtin.Unit using (⊤; tt)\n\ncong : ∀ {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y\ncong f refl = refl\n\nsym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x\nsym refl = refl\n\ntrans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z\ntrans refl q = q\n\nsubst : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y\nsubst P refl px = px\n\n'''
if needle not in text:
    raise SystemExit('import insertion point not found')
if 'cong : ∀ {A B : Set}' not in text:
    text = text.replace(needle, insert, 1)
path.write_text(text)
print('equality-primitives-normalized=True')
