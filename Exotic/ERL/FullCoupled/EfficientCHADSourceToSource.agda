{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHADSourceToSource where

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C)
  {x x' : A} {y y' : B} → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

natPlus : Nat → Nat → Nat
natPlus 0 y = y
natPlus (suc x) y = suc (natPlus x y)

record Ring : Set₁ where
  field
    R : Set
    zero one : R
    add mul : R → R → R
    neg : R → R
    addAssoc : ∀ x y z → add (add x y) z ≡ add x (add y z)
    addComm : ∀ x y → add x y ≡ add y x
    addZeroL : ∀ x → add zero x ≡ x
    addZeroR : ∀ x → add x zero ≡ x
    addNegR : ∀ x → add x (neg x) ≡ zero
    mulAssoc : ∀ x y z → mul (mul x y) z ≡ mul x (mul y z)
    mulComm : ∀ x y → mul x y ≡ mul y x
    mulOneR : ∀ x → mul x one ≡ x
    mulOneL : ∀ x → mul one x ≡ x
    distrib : ∀ x y z → mul x (add y z) ≡ add (mul x y) (mul x z)
    zeroMulR : ∀ x → mul x zero ≡ zero
    zeroMulL : ∀ x → mul zero x ≡ zero
    negScale : ∀ x y → neg (mul x y) ≡ mul (neg x) y

data Bool : Set where
  false true : Bool

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

eqFin : ∀ {n} → Fin n → Fin n → Bool
eqFin fzero fzero = true
eqFin fzero (fsuc _) = false
eqFin (fsuc _) fzero = false
eqFin (fsuc i) (fsuc j) = eqFin i j

record UnaryPrimitives (A : Set) : Set₁ where
  field
    apply : Nat → A → A
    derivative : Nat → A → A

module Language (G : Ring) (P : UnaryPrimitives (Ring.R G)) (n : Nat) where
  open Ring G
  open UnaryPrimitives P

  R0 : Set
  R0 = Ring.R G

  addR : R0 → R0 → R0
  addR = Ring.add G

  mulR : R0 → R0 → R0
  mulR = Ring.mul G

  zeroR : R0
  zeroR = Ring.zero G

  oneR : R0
  oneR = Ring.one G

  negR : R0 → R0
  negR = Ring.neg G

  Env : Set
  Env = Fin n → R0

  Cot : Set
  Cot = Fin n → R0

  zeroCot : Cot
  zeroCot _ = zeroR

  indicator : Fin n → Fin n → R0
  indicator i j with eqFin j i
  ... | true = oneR
  ... | false = zeroR

  accumulate : Fin n → R0 → Cot → Cot
  accumulate i c s j with eqFin j i
  ... | true = addR (s j) c
  ... | false = s j

  data Expr : Set where
    const : R0 → Expr
    var : Fin n → Expr
    addE : Expr → Expr → Expr
    mulE : Expr → Expr → Expr
    negE : Expr → Expr
    prim : Nat → Expr → Expr

  data Code : Set where
    tconst : R0 → Code
    tvar : Fin n → Code
    tadd : Code → Code → Code
    tmul : Code → Code → Code
    tneg : Code → Code
    tprim : Nat → Code → Code

  translate : Expr → Code
  translate (const c) = tconst c
  translate (var i) = tvar i
  translate (addE x y) = tadd (translate x) (translate y)
  translate (mulE x y) = tmul (translate x) (translate y)
  translate (negE x) = tneg (translate x)
  translate (prim k x) = tprim k (translate x)

  evalPrim : Nat → R0 → R0
  evalPrim k x = UnaryPrimitives.apply P k x

  derivPrim : Nat → R0 → R0
  derivPrim k x = UnaryPrimitives.derivative P k x

  eval : Expr → Env → R0
  eval (const c) _ = c
  eval (var i) ρ = ρ i
  eval (addE x y) ρ = addR (eval x ρ) (eval y ρ)
  eval (mulE x y) ρ = mulR (eval x ρ) (eval y ρ)
  eval (negE x) ρ = negR (eval x ρ)
  eval (prim k x) ρ = evalPrim k (eval x ρ)

  coeff : Expr → Env → Fin n → R0
  coeff (const _) _ _ = zeroR
  coeff (var j) _ i = indicator j i
  coeff (addE x y) ρ i = addR (coeff x ρ i) (coeff y ρ i)
  coeff (mulE x y) ρ i =
    addR
      (mulR (eval y ρ) (coeff x ρ i))
      (mulR (eval x ρ) (coeff y ρ i))
  coeff (negE x) ρ i = negR (coeff x ρ i)
  coeff (prim k x) ρ i =
    mulR (derivPrim k (eval x ρ)) (coeff x ρ i)

  valueT : Code → Env → R0
  valueT (tconst c) _ = c
  valueT (tvar i) ρ = ρ i
  valueT (tadd x y) ρ = addR (valueT x ρ) (valueT y ρ)
  valueT (tmul x y) ρ = mulR (valueT x ρ) (valueT y ρ)
  valueT (tneg x) ρ = negR (valueT x ρ)
  valueT (tprim k x) ρ = evalPrim k (valueT x ρ)

  reverseT : Code → Env → R0 → Cot → Cot
  reverseT (tconst _) _ _ acc = acc
  reverseT (tvar i) _ c acc = accumulate i c acc
  reverseT (tadd x y) ρ c acc =
    reverseT y ρ c (reverseT x ρ c acc)
  reverseT (tmul x y) ρ c acc =
    let vx = valueT x ρ
        vy = valueT y ρ
    in reverseT y ρ (mulR c vx)
         (reverseT x ρ (mulR c vy) acc)
  reverseT (tneg x) ρ c acc = reverseT x ρ (negR c) acc
  reverseT (tprim k x) ρ c acc =
    reverseT x ρ (mulR c (derivPrim k (valueT x ρ))) acc

  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  fst : ∀ {A B : Set} → A × B → A
  fst (a , _) = a

  snd : ∀ {A B : Set} → A × B → B
  snd (_ , b) = b

  exec : Code → Env → R0 → R0 × Cot
  exec c ρ seed = valueT c ρ , reverseT c ρ seed zeroCot

  execValueCorrect : ∀ e ρ → valueT (translate e) ρ ≡ eval e ρ
  execValueCorrect (const _) _ = refl
  execValueCorrect (var _) _ = refl
  execValueCorrect (addE x y) ρ =
    cong₂ (Ring.add G) (execValueCorrect x ρ) (execValueCorrect y ρ)
  execValueCorrect (mulE x y) ρ =
    cong₂ (Ring.mul G) (execValueCorrect x ρ) (execValueCorrect y ρ)
  execValueCorrect (negE x) ρ = cong (Ring.neg G) (execValueCorrect x ρ)
  execValueCorrect (prim k x) ρ =
    cong (evalPrim k) (execValueCorrect x ρ)

  accumulateCorrect : ∀ i c acc j →
    accumulate i c acc j ≡
    addR (acc j) (mulR c (indicator i j))
  accumulateCorrect i c acc j with eqFin j i
  ... | true =
    cong (λ z → addR (acc j) z)
      (Ring.mulOneR G c)
  ... | false =
    cong (λ z → addR (acc j) z)
      (sym (Ring.zeroMulR G c))

  reverseAccumCorrect : ∀ e ρ c acc i →
    reverseT (translate e) ρ c acc i ≡
    addR (acc i) (mulR c (coeff e ρ i))
  reverseAccumCorrect (const _) _ c acc i =
    trans
      (sym (Ring.addZeroR G (acc i)))
      (cong (λ z → addR (acc i) z)
        (sym (Ring.zeroMulR G c)))
  reverseAccumCorrect (var j) _ c acc i =
    accumulateCorrect j c acc i
  reverseAccumCorrect (addE x y) ρ c acc i =
    trans
      (reverseAccumCorrect y ρ c (reverseT (translate x) ρ c acc) i)
      (trans
        (cong₂ (Ring.add G)
          (reverseAccumCorrect x ρ c acc i)
          refl)
        (trans
          (Ring.addAssoc G (acc i)
            (mulR c (coeff x ρ i))
            (mulR c (coeff y ρ i)))
          (sym
            (Ring.distrib G c (coeff x ρ i) (coeff y ρ i)))))
  reverseAccumCorrect (mulE x y) ρ c acc i =
    trans
      (reverseAccumCorrect y ρ (mulR c (eval x ρ))
        (reverseT (translate x) ρ (mulR c (eval y ρ)) acc) i)
      (trans
        (cong₂ (Ring.add G)
          (reverseAccumCorrect x ρ (mulR c (eval y ρ)) acc i)
          refl)
        (trans
          (Ring.addAssoc G (acc i)
            (mulR (mulR c (eval y ρ)) (coeff x ρ i))
            (mulR (mulR c (eval x ρ)) (coeff y ρ i)))
          (trans
            (cong₂ (Ring.add G)
              (Ring.mulAssoc G c (eval y ρ) (coeff x ρ i))
              (Ring.mulAssoc G c (eval x ρ) (coeff y ρ i)))
            (sym
              (Ring.distrib G c
                (mulR (eval y ρ) (coeff x ρ i))
                (mulR (eval x ρ) (coeff y ρ i)))))))
  reverseAccumCorrect (negE x) ρ c acc i =
    trans
      (reverseAccumCorrect x ρ (negR c) acc i)
      (cong (λ z → addR (acc i) z)
        (sym
          (Ring.negScale G c (coeff x ρ i))))
  reverseAccumCorrect (prim k x) ρ c acc i =
    trans
      (reverseAccumCorrect x ρ
        (mulR c (derivPrim k (eval x ρ))) acc i)
      (cong (λ z → addR (acc i) z)
        (Ring.mulAssoc G c
          (derivPrim k (eval x ρ))
          (coeff x ρ i)))

  reverseCorrect : ∀ e ρ c i →
    reverseT (translate e) ρ c zeroCot i ≡
    mulR c (coeff e ρ i)
  reverseCorrect e ρ c i =
    trans
      (reverseAccumCorrect e ρ c zeroCot i)
      (Ring.addZeroL G (mulR c (coeff e ρ i)))

  sourceSize : Expr → Nat
  sourceSize (const _) = suc 0
  sourceSize (var _) = suc 0
  sourceSize (addE x y) = suc (natPlus (sourceSize x) (sourceSize y))
  sourceSize (mulE x y) = suc (natPlus (sourceSize x) (sourceSize y))
  sourceSize (negE x) = suc (sourceSize x)
  sourceSize (prim _ x) = suc (sourceSize x)

  targetSize : Code → Nat
  targetSize (tconst _) = suc 0
  targetSize (tvar _) = suc 0
  targetSize (tadd x y) = suc (natPlus (targetSize x) (targetSize y))
  targetSize (tmul x y) = suc (natPlus (targetSize x) (targetSize y))
  targetSize (tneg x) = suc (targetSize x)
  targetSize (tprim _ x) = suc (targetSize x)

  translationSizeTheorem : ∀ e → targetSize (translate e) ≡ sourceSize e
  translationSizeTheorem (const _) = refl
  translationSizeTheorem (var _) = refl
  translationSizeTheorem (addE x y) =
    cong₂ (λ a b → suc (natPlus a b))
      (translationSizeTheorem x) (translationSizeTheorem y)
  translationSizeTheorem (mulE x y) =
    cong₂ (λ a b → suc (natPlus a b))
      (translationSizeTheorem x) (translationSizeTheorem y)
  translationSizeTheorem (negE x) =
    cong suc (translationSizeTheorem x)
  translationSizeTheorem (prim _ x) =
    cong suc (translationSizeTheorem x)

  forwardWork : Expr → Nat
  forwardWork = sourceSize

  reverseWork : Expr → Nat
  reverseWork = sourceSize

  forwardLinearTheorem : ∀ e → forwardWork e ≡ sourceSize e
  forwardLinearTheorem _ = refl

  reverseLinearTheorem : ∀ e → reverseWork e ≡ sourceSize e
  reverseLinearTheorem _ = refl

  totalLinearTheorem : ∀ e →
    natPlus (forwardWork e) (reverseWork e) ≡
    natPlus (sourceSize e) (sourceSize e)
  totalLinearTheorem _ = refl

  completeEfficientCHADTheorem : ∀ e ρ c i →
    targetSize (translate e) ≡ sourceSize e ×
    (valueT (translate e) ρ ≡ eval e ρ) ×
    (reverseT (translate e) ρ c zeroCot i ≡ mulR c (coeff e ρ i)) ×
    (natPlus (forwardWork e) (reverseWork e) ≡
      natPlus (sourceSize e) (sourceSize e))
  completeEfficientCHADTheorem e ρ c i =
    translationSizeTheorem e ,
    (execValueCorrect e ρ ,
      (reverseCorrect e ρ c i , totalLinearTheorem e))
