{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CompleteSafe_v147 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong; subst)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)


data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

data Bool : Set where
  false true : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

notB : Bool → Bool
notB true = false
notB false = true

record Maybe (A : Set) : Set where
  constructor just
  field value : A

data MaybeD (A : Set) : Set where
  nothing : MaybeD A
  justD : A → MaybeD A

cong₂ :
  {A B C : Set} →
  (f : A → B → C) →
  {x x' : A} →
  {y y' : B} →
  x ≡ x' →
  y ≡ y' →
  f x y ≡ f x' y'
cong₂ f refl refl = refl

------------------------------------------------------------------------
-- Finite data
------------------------------------------------------------------------

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

indexV : ∀ {A n} → Vec A n → Fin n → A
indexV [] ()
indexV (x ∷ xs) fzero = x
indexV (x ∷ xs) (fsuc i) = indexV xs i

finDecEq : ∀ {n} → (i j : Fin n) → Dec (i ≡ j)
finDecEq fzero fzero = yes refl
finDecEq fzero (fsuc _) = no (λ ())
finDecEq (fsuc _) fzero = no (λ ())
finDecEq (fsuc i) (fsuc j) with finDecEq i j
... | yes refl = yes refl
... | no h = no (λ { refl → h refl })

mapV : ∀ {A B n} → (A → B) → Vec A n → Vec B n
mapV _ [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

zipWithV : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipWithV _ [] [] = []
zipWithV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithV f xs ys

zipWith3V : ∀ {A B C D n} → (A → B → C → D) → Vec A n → Vec B n → Vec C n → Vec D n
zipWith3V _ [] [] [] = []
zipWith3V f (a ∷ as) (b ∷ bs) (c ∷ cs) = f a b c ∷ zipWith3V f as bs cs


sumFin : ∀ {A : Set} → (A → A → A) → A → ∀ n → (Fin n → A) → A
sumFin _ z zero _ = z
sumFin op z (suc n) f = op (f fzero) (sumFin op z n (λ i → f (fsuc i)))

------------------------------------------------------------------------
-- Algebraic scalar model
------------------------------------------------------------------------

record Ring : Set₁ where
  field
    R : Set
    zero one : R
    _+_ _*_ : R → R → R
    neg : R → R
    addAssoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    addComm : ∀ x y → x + y ≡ y + x
    addZeroL : ∀ x → zero + x ≡ x
    addZeroR : ∀ x → x + zero ≡ x
    addNegL : ∀ x → neg x + x ≡ zero
    addNegR : ∀ x → x + neg x ≡ zero
    mulAssoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    mulComm : ∀ x y → x * y ≡ y * x
    mulOneL : ∀ x → one * x ≡ x
    mulOneR : ∀ x → x * one ≡ x
    distrib : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
    zeroMulL : ∀ x → zero * x ≡ zero
    zeroMulR : ∀ x → x * zero ≡ zero
    negDistrib : ∀ x y → neg (x + y) ≡ neg x + neg y
    negScale : ∀ x y → neg (x * y) ≡ x * neg y
    negNeg : ∀ x → neg (neg x) ≡ x

open Ring

record OrderedRing : Set₁ where
  field
    ring : Ring
  open Ring ring public
  field
    _≤_ _<_ : R → R → Set
    refl≤ : ∀ x → x ≤ x
    trans≤ : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    antisym≤ : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
    addLe : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
    mulNonneg : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ a * b
    mulLeLeft : ∀ {a b c} → a ≤ b → zero ≤ c → c * a ≤ c * b
    ltLe : ∀ {x y} → x < y → x ≤ y
    leLt : ∀ {x y z} → x ≤ y → y < z → x < z
    ltTrans : ∀ {x y z} → x < y → y < z → x < z
    ltAdd : ∀ {a b c d} → a < b → c < d → a + c < b + d
    addLtLeft : ∀ {a b c} → a < b → c + a < c + b
    negLt : ∀ {a b} → a < b → neg b < neg a
    negLe : ∀ {a b} → a ≤ b → neg b ≤ neg a
    mulLtPosLeft : ∀ {a b c} → a < b → zero < c → c * a < c * b
    mulLtPosCancelLeft : ∀ {a b c} → c * a < c * b → zero < c → a < b
    mulPos : ∀ {a b} → zero < a → zero < b → zero < a * b
    notLtFromLe : ∀ {a b} → a ≤ b → ¬ (b < a)
    subLtZero : ∀ {a b} → a + neg b < zero → a < b
    squarePositive : ∀ {x} → x ≠ zero → zero < x * x
    squareNonnegative : ∀ x → zero ≤ x * x
    zeroLtOne : zero < one
    abs : R → R
    absNonneg : ∀ x → zero ≤ abs x
    absTriangle : ∀ x y → abs (x + y) ≤ abs x + abs y
    absMul : ∀ x y → abs (x * y) ≡ abs x * abs y

open OrderedRing

record SmoothAlgebra : Set₁ where
  field
    orderedRing : OrderedRing
  open OrderedRing orderedRing public
  field
    exp log tanh sigmoid : R → R
    dexp dlog dtanh dsigmoid : R → R
    sqrt recip max min : R → R
    maxNonnegative : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ max a b
    pi : R
    fromNat : Nat → R
    sqrtZero : sqrt zero ≡ zero
    recipZero : recip zero ≡ zero
    fromNatZero : fromNat zero ≡ zero
    fromNatSuc : ∀ n → fromNat (suc n) ≡ fromNat n + one
    reciprocalLaw : ∀ {d} → zero < d → Ring._*_ (OrderedRing.ring orderedRing) d (recip d) ≡ one

open SmoothAlgebra

Scalar : SmoothAlgebra → Set
Scalar S = Ring.R (OrderedRing.ring (SmoothAlgebra.orderedRing S))

VecS : SmoothAlgebra → Nat → Set
VecS S n = Vec (Scalar S) n

MatS : SmoothAlgebra → Nat → Nat → Set
MatS S m n = Fin m → Fin n → Scalar S

vAdd : ∀ {S n} → VecS S n → VecS S n → VecS S n
vAdd {S} = zipWithV (Ring._+_ Rg)
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)

vSub : ∀ {S n} → VecS S n → VecS S n → VecS S n
vSub {S} = zipWithV minus
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  minus x y = Ring._+_ Rg x (Ring.neg Rg y)

vScale : ∀ {S n} → Scalar S → VecS S n → VecS S n
vScale {S} a = mapV (Ring._*_ Rg a)
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)

vHadamard : ∀ {S n} → VecS S n → VecS S n → VecS S n
vHadamard {S} = zipWithV (Ring._*_ Rg)
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)

vDot : ∀ {S n} → VecS S n → VecS S n → Scalar S
vDot {S} {n} x y =
  sumFin (Ring._+_ Rg) (Ring.zero Rg) n (λ i → Ring._*_ Rg (indexV x i) (indexV y i))
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)

vSum : ∀ {S n} → VecS S n → Scalar S
vSum {S} {n} x = sumFin (Ring._+_ Rg) (Ring.zero Rg) n (λ i → indexV x i)
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)

tabulateV : ∀ {A n} → (Fin n → A) → Vec A n
tabulateV {zero} f = []
tabulateV {suc n} f = f fzero ∷ tabulateV (λ i → f (fsuc i))

matVec : ∀ {S m n} → MatS S m n → VecS S n → VecS S m
matVec {S} {m} {n} A x =
  tabulateV (λ i → sumFin (Ring._+_ Rg) (Ring.zero Rg) n
    (λ j → Ring._*_ Rg (A i j) (indexV x j)))
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)

matMul : ∀ {S a b c} → MatS S a b → MatS S b c → MatS S a c
matMul {S} {a} {b} {c} A B =
  λ i k → sumFin (Ring._+_ Rg) (Ring.zero Rg) b
    (λ j → Ring._*_ Rg (A i j) (B j k))
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)

------------------------------------------------------------------------
-- Seven coupled parameter blocks and finite parameter indices
------------------------------------------------------------------------


------------------------------------------------------------------------

data Block : Set where
  critic representation actor lstm trace idbd hyper : Block

record SevenBlockSizes : Set where
  field size : Block → Nat

ParamIndex : SevenBlockSizes → Set
ParamIndex s = Σ Block (λ b → Fin (SevenBlockSizes.size s b))

blockDecEq : (a b : Block) → Dec (a ≡ b)
blockDecEq critic critic = yes refl
blockDecEq critic representation = no (λ ())
blockDecEq critic actor = no (λ ())
blockDecEq critic lstm = no (λ ())
blockDecEq critic trace = no (λ ())
blockDecEq critic idbd = no (λ ())
blockDecEq critic hyper = no (λ ())
blockDecEq representation critic = no (λ ())
blockDecEq representation representation = yes refl
blockDecEq representation actor = no (λ ())
blockDecEq representation lstm = no (λ ())
blockDecEq representation trace = no (λ ())
blockDecEq representation idbd = no (λ ())
blockDecEq representation hyper = no (λ ())
blockDecEq actor critic = no (λ ())
blockDecEq actor representation = no (λ ())
blockDecEq actor actor = yes refl
blockDecEq actor lstm = no (λ ())
blockDecEq actor trace = no (λ ())
blockDecEq actor idbd = no (λ ())
blockDecEq actor hyper = no (λ ())
blockDecEq lstm critic = no (λ ())
blockDecEq lstm representation = no (λ ())
blockDecEq lstm actor = no (λ ())
blockDecEq lstm lstm = yes refl
blockDecEq lstm trace = no (λ ())
blockDecEq lstm idbd = no (λ ())
blockDecEq lstm hyper = no (λ ())
blockDecEq trace critic = no (λ ())
blockDecEq trace representation = no (λ ())
blockDecEq trace actor = no (λ ())
blockDecEq trace lstm = no (λ ())
blockDecEq trace trace = yes refl
blockDecEq trace idbd = no (λ ())
blockDecEq trace hyper = no (λ ())
blockDecEq idbd critic = no (λ ())
blockDecEq idbd representation = no (λ ())
blockDecEq idbd actor = no (λ ())
blockDecEq idbd lstm = no (λ ())
blockDecEq idbd trace = no (λ ())
blockDecEq idbd idbd = yes refl
blockDecEq idbd hyper = no (λ ())
blockDecEq hyper critic = no (λ ())
blockDecEq hyper representation = no (λ ())
blockDecEq hyper actor = no (λ ())
blockDecEq hyper lstm = no (λ ())
blockDecEq hyper trace = no (λ ())
blockDecEq hyper idbd = no (λ ())
blockDecEq hyper hyper = yes refl

paramIndexDecEq : (s : SevenBlockSizes) → (i j : ParamIndex s) → Dec (i ≡ j)
paramIndexDecEq s (b₁ , i₁) (b₂ , i₂) with blockDecEq b₁ b₂
... | no h = no (λ { refl → h refl })
... | yes refl with finDecEq i₁ i₂
...   | no h = no (λ { refl → h refl })
...   | yes refl = yes refl

------------------------------------------------------------------------
-- Efficient CHAD core: exact finite reverse pass + local accumulation state.
-- Only the efficient state-passing reverse layer is retained.
-- CHAD implementation is recreated.
------------------------------------------------------------------------

module EfficientCHAD (S : SmoothAlgebra) (n : Nat) where
  open SmoothAlgebra S
  Rg = OrderedRing.ring orderedRing
  R = Ring.R Rg
  Env = Fin n → R
  Cot = Fin n → R

  basis : Fin n → Cot
  basis j i with finDecEq i j
  ... | yes _ = one
  ... | no _ = zero

  zeroCot : Cot
  zeroCot _ = zero

  addCot : Cot → Cot → Cot
  addCot a b i = a i + b i

  scaleCot : R → Cot → Cot
  scaleCot a v i = a * v i

  negCot : Cot → Cot
  negCot v i = neg (v i)

  data Expr : Set where
    const : R → Expr
    var : Fin n → Expr
    add : Expr → Expr → Expr
    mul : Expr → Expr → Expr
    negE : Expr → Expr
    expE : Expr → Expr
    logE : Expr → Expr
    tanhE : Expr → Expr
    sigmoidE : Expr → Expr

  eval : Expr → Env → R
  eval (const c) _ = c
  eval (var i) ρ = ρ i
  eval (add x y) ρ = eval x ρ + eval y ρ
  eval (mul x y) ρ = eval x ρ * eval y ρ
  eval (negE x) ρ = neg (eval x ρ)
  eval (expE x) ρ = exp (eval x ρ)
  eval (logE x) ρ = log (eval x ρ)
  eval (tanhE x) ρ = tanh (eval x ρ)
  eval (sigmoidE x) ρ = sigmoid (eval x ρ)

  coeff : Expr → Env → Fin n → R
  coeff (const _) _ _ = zero
  coeff (var j) _ i with finDecEq i j
  ... | yes _ = one
  ... | no _ = zero
  coeff (add x y) ρ i = coeff x ρ i + coeff y ρ i
  coeff (mul x y) ρ i = eval y ρ * coeff x ρ i + eval x ρ * coeff y ρ i
  coeff (negE x) ρ i = neg (coeff x ρ i)
  coeff (expE x) ρ i = dexp (eval x ρ) * coeff x ρ i
  coeff (logE x) ρ i = dlog (eval x ρ) * coeff x ρ i
  coeff (tanhE x) ρ i = dtanh (eval x ρ) * coeff x ρ i
  coeff (sigmoidE x) ρ i = dsigmoid (eval x ρ) * coeff x ρ i

  record Pullback : Set where
    field
      value : R
      back : R → Cot

  open Pullback

  pull : Expr → Env → Pullback
  pull (const c) _ = record { value = c ; back = λ _ → zeroCot }
  pull (var i) ρ = record { value = ρ i ; back = λ c → scaleCot c (basis i) }
  pull (add x y) ρ =
    let px = pull x ρ
        py = pull y ρ
    in record
      { value = value px + value py
      ; back = λ c → addCot (back px c) (back py c)
      }
  pull (mul x y) ρ =
    let px = pull x ρ
        py = pull y ρ
        vx = value px
        vy = value py
    in record
      { value = vx * vy
      ; back = λ c → addCot (back px (c * vy)) (back py (c * vx))
      }
  pull (negE x) ρ =
    let px = pull x ρ
    in record { value = neg (value px) ; back = λ c → negCot (back px c) }
  pull (expE x) ρ =
    let px = pull x ρ
        vx = value px
    in record { value = exp vx ; back = λ c → back px (c * dexp vx) }
  pull (logE x) ρ =
    let px = pull x ρ
        vx = value px
    in record { value = log vx ; back = λ c → back px (c * dlog vx) }
  pull (tanhE x) ρ =
    let px = pull x ρ
        vx = value px
    in record { value = tanh vx ; back = λ c → back px (c * dtanh vx) }
  pull (sigmoidE x) ρ =
    let px = pull x ρ
        vx = value px
    in record { value = sigmoid vx ; back = λ c → back px (c * dsigmoid vx) }

  primalCorrect : ∀ e ρ → Pullback.value (pull e ρ) ≡ eval e ρ
  primalCorrect (const _) _ = refl
  primalCorrect (var _) _ = refl
  primalCorrect (add x y) ρ = cong₂ _+_ (primalCorrect x ρ) (primalCorrect y ρ)
  primalCorrect (mul x y) ρ = cong₂ _*_ (primalCorrect x ρ) (primalCorrect y ρ)
  primalCorrect (negE x) ρ = cong neg (primalCorrect x ρ)
  primalCorrect (expE x) ρ = cong exp (primalCorrect x ρ)
  primalCorrect (logE x) ρ = cong log (primalCorrect x ρ)
  primalCorrect (tanhE x) ρ = cong tanh (primalCorrect x ρ)
  primalCorrect (sigmoidE x) ρ = cong sigmoid (primalCorrect x ρ)

  vjpCoeff : ∀ e ρ c i → Pullback.back (pull e ρ) c i ≡ c * coeff e ρ i
  vjpCoeff (const _) _ c _ = sym (Ring.zeroMulR Rg c)
  vjpCoeff (var j) _ c i with finDecEq i j
  ... | yes _ = sym (Ring.mulOneR Rg c)
  ... | no _ = sym (Ring.zeroMulR Rg c)
  vjpCoeff (add x y) ρ c i =
    trans
      (cong₂ _+_ (vjpCoeff x ρ c i) (vjpCoeff y ρ c i))
      (sym (Ring.distrib Rg c (coeff x ρ i) (coeff y ρ i)))
  vjpCoeff (mul x y) ρ c i =
    trans
      (cong₂ _+_
        (vjpCoeff x ρ (c * eval y ρ) i)
        (vjpCoeff y ρ (c * eval x ρ) i))
      (sym (Ring.distrib Rg c (eval y ρ * coeff x ρ i) (eval x ρ * coeff y ρ i)))
  vjpCoeff (negE x) ρ c i =
    trans (cong neg (vjpCoeff x ρ c i)) (sym (Ring.negScale Rg c (coeff x ρ i)))
  vjpCoeff (expE x) ρ c i =
    trans (vjpCoeff x ρ (c * dexp (eval x ρ)) i)
      (Ring.mulAssoc Rg c (dexp (eval x ρ)) (coeff x ρ i))
  vjpCoeff (logE x) ρ c i =
    trans (vjpCoeff x ρ (c * dlog (eval x ρ)) i)
      (Ring.mulAssoc Rg c (dlog (eval x ρ)) (coeff x ρ i))
  vjpCoeff (tanhE x) ρ c i =
    trans (vjpCoeff x ρ (c * dtanh (eval x ρ)) i)
      (Ring.mulAssoc Rg c (dtanh (eval x ρ)) (coeff x ρ i))
  vjpCoeff (sigmoidE x) ρ c i =
    trans (vjpCoeff x ρ (c * dsigmoid (eval x ρ)) i)
      (Ring.mulAssoc Rg c (dsigmoid (eval x ρ)) (coeff x ρ i))

  data EState : Set where
    state : Cot → EState

  runState : EState → Cot
  runState (state c) = c

  accumulateAt : Fin n → R → Cot → Cot
  accumulateAt i c s j with finDecEq j i
  ... | yes _ = s j + c
  ... | no _ = s j

  accumulate : Fin n → R → EState → EState
  accumulate i c (state s) = state (accumulateAt i c s)

  runBack : ∀ e ρ c → EState → EState
  runBack e ρ c s =
    let b = Pullback.back (pull e ρ) c in
    state (λ i → runState s i + b i)

  runBackZero : ∀ e ρ c i →
    runState (runBack e ρ c (state zeroCot)) i ≡ c * coeff e ρ i
  runBackZero e ρ c i =
    trans (Ring.addZeroL Rg (Pullback.back (pull e ρ) c i))
      (vjpCoeff e ρ c i)


------------------------------------------------------------------------
-- Concrete neural network components
------------------------------------------------------------------------

record Affine (S : SmoothAlgebra) (din dout : Nat) : Set where
  field
    weight : MatS S dout din
    bias : VecS S dout

record LayerNorm (S : SmoothAlgebra) (d : Nat) : Set where
  field
    gain shift : VecS S d
    epsilon : Scalar S
    epsilonPositive : zero < epsilon

record RecurrentAffine (S : SmoothAlgebra) (input hidden : Nat) : Set where
  field
    inputWeight : MatS S hidden input
    recurrentWeight : MatS S hidden hidden
    bias : VecS S hidden
    norm : LayerNorm S hidden

record LSTMGates (S : SmoothAlgebra) (input hidden : Nat) : Set where
  field
    forgetGate inputGate outputGate candidateGate : RecurrentAffine S input hidden

record LSTMBlock (S : SmoothAlgebra) (input hidden : Nat) : Set where
  field gates : LSTMGates S input hidden

record LSTMState (S : SmoothAlgebra) (hidden : Nat) : Set where
  field hidden cell : VecS S hidden

record Actor (S : SmoothAlgebra) (stateDim actionDim : Nat) : Set where
  field
    weight : MatS S actionDim stateDim
    bias : VecS S actionDim

record Critic (S : SmoothAlgebra) (hiddenDim : Nat) : Set where
  field
    weight : VecS S hiddenDim
    bias : Scalar S

sigmoidV : ∀ {S n} → VecS S n → VecS S n
sigmoidV {S} = mapV (SmoothAlgebra.sigmoid S)

tanhV : ∀ {S n} → VecS S n → VecS S n
tanhV {S} = mapV (SmoothAlgebra.tanh S)

squareV : ∀ {S n} → VecS S n → VecS S n
squareV xs = vHadamard xs xs

layerNormalise : ∀ {S d} → LayerNorm S d → VecS S d → VecS S d
layerNormalise {S} {d} ln xs =
  shiftScale (scaleShift (mapV normalise xs) (LayerNorm.gain ln)) (LayerNorm.shift ln)
  where
  μ = vSum xs * SmoothAlgebra.recip S (SmoothAlgebra.fromNat S d)
  centered x = x + neg μ
  variance = vSum (squareV (mapV centered xs))
    * SmoothAlgebra.recip S (SmoothAlgebra.fromNat S d)
  invStd = SmoothAlgebra.recip S
    (SmoothAlgebra.sqrt S (variance + LayerNorm.epsilon ln))
  normalise x = centered x * invStd
  scaleShift : ∀ {m} → VecS S m → VecS S m → VecS S m
  scaleShift [] [] = []
  scaleShift (x ∷ xs) (g ∷ gs) =
    let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S) in
    (g * normalise x) ∷ scaleShift xs gs

  shiftScale : ∀ {m} → VecS S m → VecS S m → VecS S m
  shiftScale [] [] = []
  shiftScale (x ∷ xs) (b ∷ bs) =
    let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S) in
    (x + b) ∷ shiftScale xs bs


recurrentAffine : ∀ {S input hidden} →
  RecurrentAffine S input hidden → VecS S input → VecS S hidden → VecS S hidden
recurrentAffine layer x h =
  vAdd
    (vAdd
      (matVec (RecurrentAffine.inputWeight layer) x)
      (matVec (RecurrentAffine.recurrentWeight layer) h))
    (RecurrentAffine.bias layer)

sigmoidGate : ∀ {S input hidden} →
  RecurrentAffine S input hidden → VecS S input → VecS S hidden → VecS S hidden
sigmoidGate layer x h =
  sigmoidV (layerNormalise (RecurrentAffine.norm layer) (recurrentAffine layer x h))

tanhGate : ∀ {S input hidden} →
  RecurrentAffine S input hidden → VecS S input → VecS S hidden → VecS S hidden
tanhGate layer x h =
  tanhV (layerNormalise (RecurrentAffine.norm layer) (recurrentAffine layer x h))

lstmStep : ∀ {S input hidden} →
  LSTMBlock S input hidden → LSTMState S hidden → VecS S input → LSTMState S hidden
lstmStep block old x =
  let g = LSTMGates.gates (LSTMBlock.gates block)
      h = LSTMState.hidden old
      f = sigmoidGate (LSTMGates.forgetGate g) x h
      i = sigmoidGate (LSTMGates.inputGate g) x h
      o = sigmoidGate (LSTMGates.outputGate g) x h
      c = tanhGate (LSTMGates.candidateGate g) x h
      cell' = vAdd (vHadamard f (LSTMState.cell old)) (vHadamard i c)
      hidden' = vHadamard o (tanhV cell')
  in record { hidden = hidden' ; cell = cell' }

actorAction : ∀ {S stateDim actionDim} →
  Actor S stateDim actionDim → VecS S stateDim → VecS S actionDim
actorAction a s = tanhV (vAdd (matVec (Actor.weight a) s) (Actor.bias a))

criticValue : ∀ {S hiddenDim} →
  Critic S hiddenDim → VecS S hiddenDim → Scalar S
criticValue c h = vDot (Critic.weight c) h + Critic.bias c

appendV_v146 : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
appendV_v146 [] ys = ys
appendV_v146 (x ∷ xs) ys = x ∷ appendV_v146 xs ys

lstmRun_v146 : ∀ {S input hidden n}
  (block : LSTMBlock S input hidden) →
  LSTMState S hidden → Vec (VecS S input) n → LSTMState S hidden
lstmRun_v146 block state [] = state
lstmRun_v146 block state (x ∷ xs) = lstmRun_v146 block (lstmStep block state x) xs

lstmRunAppend_v146 : ∀ {S input hidden m n}
  (block : LSTMBlock S input hidden)
  (state : LSTMState S hidden)
  (xs : Vec (VecS S input) m)
  (ys : Vec (VecS S input) n) →
  lstmRun_v146 block state (appendV_v146 xs ys) ≡
  lstmRun_v146 block (lstmRun_v146 block state xs) ys
lstmRunAppend_v146 block state [] ys = refl
lstmRunAppend_v146 block state (x ∷ xs) ys =
  lstmRunAppend_v146 block (lstmStep block state x) xs ys

record GaussianShaping (S : SmoothAlgebra) (actionDim : Nat) : Set where
  field
    sigma : VecS S actionDim
    sigmaPositive : ∀ i → zero < indexV sigma i

gaussianCoordinateTerm : ∀ {S} → Scalar S → Scalar S → Scalar S → Scalar S
gaussianCoordinateTerm {S} sigma mu a =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
      d = Ring._+_ Rg a (Ring.neg Rg mu)
      s2 = Ring._*_ Rg sigma sigma
      quad = Ring._*_ Rg (Ring._*_ Rg d d)
        (SmoothAlgebra.recip S s2)
      normaliser = SmoothAlgebra.log S
        (Ring._*_ Rg
          (Ring._*_ Rg (SmoothAlgebra.fromNat S 2) (SmoothAlgebra.pi S)) s2)
  in Ring._+_ Rg quad normaliser

gaussianLogPiExp : ∀ {S d} →
  GaussianShaping S d → VecS S d → VecS S d → Scalar S
gaussianLogPiExp {S} g μ a =
  Ring.neg Rg
    (Ring._*_ Rg
      (SmoothAlgebra.recip S (SmoothAlgebra.fromNat S 2))
      (sumGaussian (GaussianShaping.sigma g) μ a))
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  sumGaussian : ∀ {m} → VecS S m → VecS S m → VecS S m → Scalar S
  sumGaussian [] [] [] = Ring.zero Rg
  sumGaussian (s ∷ ss) (m ∷ ms) (a' ∷ as) =
    Ring._+_ Rg (gaussianCoordinateTerm s m a')
      (sumGaussian ss ms as)



vNeg_v140 : ∀ {S n} → VecS S n → VecS S n
vNeg_v140 {S} = mapV (Ring.neg Rg)
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)

vZero_v140 : ∀ {S n} → VecS S n
vZero_v140 {S} {zero} = []
vZero_v140 {S} {suc n} =
  Ring.zero (OrderedRing.ring (SmoothAlgebra.orderedRing S)) ∷ vZero_v140

vAddZeroL_v140 : ∀ {S n} (x : VecS S n) → ∀ i →
  indexV (vAdd (vZero_v140 {S} {n}) x) i ≡ indexV x i
vAddZeroL_v140 [] ()
vAddZeroL_v140 (x ∷ xs) fzero = Ring.addZeroL (OrderedRing.ring _) x
vAddZeroL_v140 (x ∷ xs) (fsuc i) = vAddZeroL_v140 xs i

vAddZeroR_v140 : ∀ {S n} (x : VecS S n) → ∀ i →
  indexV (vAdd x (vZero_v140 {S} {n})) i ≡ indexV x i
vAddZeroR_v140 [] ()
vAddZeroR_v140 (x ∷ xs) fzero = Ring.addZeroR (OrderedRing.ring _) x
vAddZeroR_v140 (x ∷ xs) (fsuc i) = vAddZeroR_v140 xs i

vAddComm_v140 : ∀ {S n} (x y : VecS S n) → ∀ i →
  indexV (vAdd x y) i ≡ indexV (vAdd y x) i
vAddComm_v140 [] [] ()
vAddComm_v140 (x ∷ xs) (y ∷ ys) fzero = Ring.addComm (OrderedRing.ring _) x y
vAddComm_v140 (x ∷ xs) (y ∷ ys) (fsuc i) = vAddComm_v140 xs ys i

vAddAssoc_v140 : ∀ {S n} (x y z : VecS S n) → ∀ i →
  indexV (vAdd (vAdd x y) z) i ≡ indexV (vAdd x (vAdd y z)) i
vAddAssoc_v140 [] [] [] ()
vAddAssoc_v140 (x ∷ xs) (y ∷ ys) (z ∷ zs) fzero = Ring.addAssoc (OrderedRing.ring _) x y z
vAddAssoc_v140 (x ∷ xs) (y ∷ ys) (z ∷ zs) (fsuc i) = vAddAssoc_v140 xs ys zs i

vScaleZero_v140 : ∀ {S n} (x : VecS S n) → ∀ i →
  indexV (vScale (Ring.zero (OrderedRing.ring (SmoothAlgebra.orderedRing S))) x) i ≡
  Ring.zero (OrderedRing.ring (SmoothAlgebra.orderedRing S))
vScaleZero_v140 [] ()
vScaleZero_v140 (x ∷ xs) fzero = Ring.zeroMulL (OrderedRing.ring _) x
vScaleZero_v140 (x ∷ xs) (fsuc i) = vScaleZero_v140 xs i

vScaleOne_v140 : ∀ {S n} (x : VecS S n) → ∀ i →
  indexV (vScale (Ring.one (OrderedRing.ring (SmoothAlgebra.orderedRing S))) x) i ≡ indexV x i
vScaleOne_v140 [] ()
vScaleOne_v140 (x ∷ xs) fzero = Ring.mulOneL (OrderedRing.ring _) x
vScaleOne_v140 (x ∷ xs) (fsuc i) = vScaleOne_v140 xs i

vScaleMul_v140 : ∀ {S n} (a b : Scalar S) (x : VecS S n) → ∀ i →
  indexV (vScale (Ring._*_ (OrderedRing.ring (SmoothAlgebra.orderedRing S)) a b) x) i ≡
  indexV (vScale a (vScale b x)) i
vScaleMul_v140 a b [] ()
vScaleMul_v140 a b (x ∷ xs) fzero = Ring.mulAssoc (OrderedRing.ring _) a b x
vScaleMul_v140 a b (x ∷ xs) (fsuc i) = vScaleMul_v140 a b xs i

vScaleAdd_v140 : ∀ {S n} (a : Scalar S) (x y : VecS S n) → ∀ i →
  indexV (vScale a (vAdd x y)) i ≡ indexV (vAdd (vScale a x) (vScale a y)) i
vScaleAdd_v140 a [] [] ()
vScaleAdd_v140 a (x ∷ xs) (y ∷ ys) fzero = Ring.distrib (OrderedRing.ring _) a x y
vScaleAdd_v140 a (x ∷ xs) (y ∷ ys) (fsuc i) = vScaleAdd_v140 a xs ys i

vHadamardComm_v140 : ∀ {S n} (x y : VecS S n) → ∀ i →
  indexV (vHadamard x y) i ≡ indexV (vHadamard y x) i
vHadamardComm_v140 [] [] ()
vHadamardComm_v140 (x ∷ xs) (y ∷ ys) fzero = Ring.mulComm (OrderedRing.ring _) x y
vHadamardComm_v140 (x ∷ xs) (y ∷ ys) (fsuc i) = vHadamardComm_v140 xs ys i

vDotComm_v140 : ∀ {S n} (x y : VecS S n) → vDot x y ≡ vDot y x
vDotComm_v140 {S} {zero} [] [] = refl
vDotComm_v140 {S} {suc n} (x ∷ xs) (y ∷ ys) =
  trans
    (cong₂ (Ring._+_ (OrderedRing.ring (SmoothAlgebra.orderedRing S)))
      (Ring.mulComm (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x y)
      (vDotComm_v140 xs ys))
    refl

------------------------------------------------------------------------
-- Neural components: the exact finite functional core shared by the
-- baseline-family-style implementations inspected in the source ecosystem.
------------------------------------------------------------------------

data LSTMFamily_v140 : Set where
  Stoix : LSTMFamily_v140
  CleanRL : LSTMFamily_v140
  PureJaxQL : LSTMFamily_v140
  PureJaxRL : LSTMFamily_v140
  CraftaxBaselines : LSTMFamily_v140
  JaxRL : LSTMFamily_v140
  JaxBaselines : LSTMFamily_v140
  Rejax : LSTMFamily_v140

lstmGateRecord_v140 : ∀ {S input hidden}
  (g : LSTMGates S input hidden) →
  LSTMGates.gates (record { gates = g }) ≡ g
lstmGateRecord_v140 g = refl

actorAction_v140 : ∀ {S stateDim actionDim}
  (a : Actor S stateDim actionDim) (s : VecS S stateDim) →
  actorAction a s ≡
  tanhV (vAdd (matVec (Actor.weight a) s) (Actor.bias a))
actorAction_v140 _ _ = refl

criticValue_v140 : ∀ {S hiddenDim}
  (c : Critic S hiddenDim) (h : VecS S hiddenDim) →
  criticValue c h ≡ vDot (Critic.weight c) h + Critic.bias c
criticValue_v140 _ _ = refl

recurrentAffine_v140 : ∀ {S input hidden}
  (a : RecurrentAffine S input hidden)
  (x : VecS S input) (h : VecS S hidden) →
  recurrentAffine a x h ≡
  vAdd
    (vAdd (matVec (RecurrentAffine.inputWeight a) x)
      (matVec (RecurrentAffine.recurrentWeight a) h))
    (RecurrentAffine.bias a)
recurrentAffine_v140 _ _ _ = refl

------------------------------------------------------------------------
-- q-exposure projection: constructive finite coordinate algebra.
------------------------------------------------------------------------

record QProjectionDecisionAlgebra_v140 (S : SmoothAlgebra) : Set₁ where
  open SmoothAlgebra S
  field
    leDec : ∀ x y → Dec (x ≤ y)
    ltDec : ∀ x y → Dec (x < y)
    maxNonnegative : ∀ x → zero ≤ max zero x
    maxPositive : ∀ x → zero ≤ x → max zero x ≡ x
    maxZero : ∀ x → x ≤ zero → max zero x ≡ zero
    negNonnegative : ∀ x → x ≤ zero → zero ≤ neg x
    subNonpositive : ∀ a b → a + neg b ≤ zero → a ≤ b

residual_v140 : ∀ {S n} → Scalar S → VecS S n → VecS S n → Fin n → Scalar S
residual_v140 mu alpha x i =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  in Ring._+_ Rg (indexV alpha i)
       (Ring.neg Rg (Ring._*_ Rg mu (indexV x i * indexV x i)))

qProjectionNumerator_v140 : ∀ {S n} → Scalar S → VecS S n → VecS S n →
  Vec Bool n → Scalar S
qProjectionNumerator_v140 {S} budget alpha x m =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  in maskSum_v140 S m (λ i → Ring._*_ Rg (indexV alpha i) (indexV x i * indexV x i))
     + Ring.neg Rg budget
  where
  maskSum_v140 : ∀ {S n} → SmoothAlgebra S →
    Vec Bool n → (Fin n → Scalar S) → Scalar S
  maskSum_v140 S {zero} [] f = Ring.zero (OrderedRing.ring (SmoothAlgebra.orderedRing S))
  maskSum_v140 S {suc n} (b ∷ bs) f =
    let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S) in
    (if b then f fzero else Ring.zero Rg)
      + maskSum_v140 S bs (λ i → f (fsuc i))


qProjectionCandidate_v140 : ∀ {S n} →
  QProjectionDecisionAlgebra_v140 S → Scalar S → VecS S n → VecS S n →
  Vec Bool n → VecS S n
qProjectionCandidate_v140 {S} d mu alpha x m = candidate m alpha x
  where
  candidate : ∀ {k} → Vec Bool k → VecS S k → VecS S k → VecS S k
  candidate [] [] [] = []
  candidate (b ∷ bs) (a ∷ as) (xv ∷ xs) =
    if b then
      SmoothAlgebra.max S zero (residual_v140 mu (a ∷ as) (xv ∷ xs) fzero)
        ∷ candidate bs as xs
    else
      zero ∷ candidate bs as xs

qProjectionCandidateNonnegative_v140 : ∀ {S n}
  (d : QProjectionDecisionAlgebra_v140 S)
  (mu : Scalar S) (alpha x : VecS S n) (m : Vec Bool n) (i : Fin n) →
  zero ≤ indexV (qProjectionCandidate_v140 d mu alpha x m) i
qProjectionCandidateNonnegative_v140 d mu [] [] [] ()
qProjectionCandidateNonnegative_v140 d mu (a ∷ as) (x ∷ xs) (b ∷ bs) fzero with b
... | true = QProjectionDecisionAlgebra_v140.maxNonnegative d _
... | false = OrderedRing.refl≤ _
qProjectionCandidateNonnegative_v140 d mu (a ∷ as) (x ∷ xs) (b ∷ bs) (fsuc i) =
  qProjectionCandidateNonnegative_v140 d mu as xs bs i

qProjectionCandidateActive_v140 : ∀ {S n}
  (d : QProjectionDecisionAlgebra_v140 S)
  (mu : Scalar S) (alpha x : VecS S n) (m : Vec Bool n) (i : Fin n) →
  indexV m i ≡ true → zero ≤ residual_v140 mu alpha x i →
  indexV (qProjectionCandidate_v140 d mu alpha x m) i ≡ residual_v140 mu alpha x i
qProjectionCandidateActive_v140 d mu (a ∷ as) (x ∷ xs) (true ∷ bs) fzero refl h =
  QProjectionDecisionAlgebra_v140.maxPositive d _ h
qProjectionCandidateActive_v140 d mu (a ∷ as) (x ∷ xs) (false ∷ bs) fzero () h
qProjectionCandidateActive_v140 d mu (a ∷ as) (x ∷ xs) (b ∷ bs) (fsuc i) hm h =
  qProjectionCandidateActive_v140 d mu as xs bs i hm h

qProjectionCandidateInactive_v140 : ∀ {S n}
  (d : QProjectionDecisionAlgebra_v140 S)
  (mu : Scalar S) (alpha x : VecS S n) (m : Vec Bool n) (i : Fin n) →
  indexV m i ≡ false →
  indexV (qProjectionCandidate_v140 d mu alpha x m) i ≡ zero
qProjectionCandidateInactive_v140 d mu (a ∷ as) (x ∷ xs) (false ∷ bs) fzero refl = refl
qProjectionCandidateInactive_v140 d mu (a ∷ as) (x ∷ xs) (true ∷ bs) fzero ()
qProjectionCandidateInactive_v140 d mu (a ∷ as) (x ∷ xs) (b ∷ bs) (fsuc i) hm =
  qProjectionCandidateInactive_v140 d mu as xs bs i hm

------------------------------------------------------------------------
-- Exact finite deletion inequality: yd < nz for a negative residual.
------------------------------------------------------------------------

residualSquareNonzero_v140 : ∀ {S}
  {alpha mu x : Scalar S} →
  zero ≤ alpha →
  alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (mu * (x * x)) < zero → x ≠ zero
residualSquareNonzero_v140 ha hr hx =
  let hzero : alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _))
        (mu * (hx * hx)) ≡ alpha =
      trans
        (cong (λ q → alpha + Ring.neg (OrderedRing.ring _) (mu * q))
          (cong₂ (Ring._*_ (OrderedRing.ring _)) hx hx))
        (Ring.addZeroR (OrderedRing.ring _) alpha)
  in ⊥-elim (OrderedRing.notLtFromLe ha (subst (λ q → zero ≤ q) hzero hr))

------------------------------------------------------------------------
-- The clean, reusable cross-multiplication theorem is derived from the
-- already-derived finite projection algebra in the predecessor surface.
------------------------------------------------------------------------

qProjectionCross_v141 : ∀ {S}
  {alpha mu x : Scalar S} →
  zero ≤ alpha →
  alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (mu * (x * x)) < zero →
  alpha * (x * x) < mu * ((x * x) * (x * x))
qProjectionCross_v141 ha hr =
  let OR = SmoothAlgebra.orderedRing _
      Rg = OrderedRing.ring OR
      hx : x ≠ zero = residualSquareNonzero_v140 ha hr
      hxx : zero < x * x = OrderedRing.squarePositive hx
      hlt : alpha < mu * (x * x) = OrderedRing.subLtZero hr
      hmul = OrderedRing.mulLtPosLeft hlt hxx
  in trans
       (trans
         (sym (Ring.mulComm Rg alpha (x * x)))
         hmul)
       (trans
         (Ring.mulComm Rg (x * x) (mu * (x * x)))
         (sym (Ring.mulAssoc Rg mu (x * x) (x * x))))

------------------------------------------------------------------------
-- Total finite q-projection search. Each successful branch deletes exactly
-- one currently active negative-residual coordinate. The search is total by
-- fuel; all arithmetic quantities are recomputed from the current finite mask.
------------------------------------------------------------------------

maskAllFalse : ∀ {n} → Vec Bool n
maskAllFalse {zero} = []
maskAllFalse {suc n} = false ∷ maskAllFalse

maskRemove_v142 : ∀ {n} → Fin n → Vec Bool n → Vec Bool n
maskRemove_v142 {suc n} fzero (_ ∷ xs) = false ∷ xs
maskRemove_v142 {suc n} (fsuc i) (b ∷ bs) = b ∷ maskRemove_v142 i bs

maskSum_v142 : ∀ {S n} → Vec Bool n → (Fin n → Scalar S) → Scalar S
maskSum_v142 {S} {zero} [] f = Ring.zero (OrderedRing.ring (SmoothAlgebra.orderedRing S))
maskSum_v142 {S} {suc n} (b ∷ bs) f =
  (if b then f fzero else Ring.zero (OrderedRing.ring (SmoothAlgebra.orderedRing S)))
  + maskSum_v142 bs (λ i → f (fsuc i))

qDen_v142 : ∀ {S n} → Vec Bool n → VecS S n → Scalar S
qDen_v142 m x = maskSum_v142 m (λ i → fourth (indexV x i))
  where
  fourth : ∀ {S} → Scalar S → Scalar S
  fourth y = let z = y * y in z * z

qNum_v142 : ∀ {S n} → Scalar S → Vec Bool n → VecS S n → VecS S n → Scalar S
qNum_v142 budget m alpha x =
  maskSum_v142 m (λ i → indexV alpha i * (indexV x i * indexV x i)) + neg budget

qMu_v142 : ∀ {S n} → QProjectionDecisionAlgebra_v140 S → Scalar S → Vec Bool n → VecS S n → VecS S n → Scalar S
qMu_v142 D budget m alpha x with QProjectionDecisionAlgebra_v140.ltDec D zero (qNum_v142 budget m alpha x)
... | no _ = zero
... | yes _ with QProjectionDecisionAlgebra_v140.ltDec D zero (qDen_v142 m x)
...   | no _ = zero
...   | yes _ = qNum_v142 budget m alpha x * SmoothAlgebra.recip _ (qDen_v142 m x)

qResidual_v142 : ∀ {S} → Scalar S → Scalar S → Scalar S → Scalar S
qResidual_v142 mu alpha w = alpha + neg (mu * w)

qFirstNegative_v142 : ∀ {S n} → QProjectionDecisionAlgebra_v140 S →
  Vec Bool n → VecS S n → VecS S n → Scalar S → MaybeD (Fin n)
qFirstNegative_v142 {S} D [] [] [] mu = nothing
qFirstNegative_v142 {S} D (b ∷ bs) (a ∷ as) (x ∷ xs) mu with b
... | false = shift (qFirstNegative_v142 D bs as xs mu)
... | true with QProjectionDecisionAlgebra_v140.ltDec D zero (qResidual_v142 mu a (x * x))
...   | yes _ = justD fzero
...   | no _ = shift (qFirstNegative_v142 D bs as xs mu)
  where
  shift : ∀ {m} → MaybeD (Fin m) → MaybeD (Fin (suc m))
  shift nothing = nothing
  shift (justD i) = justD (fsuc i)

qCandidate_v142 : ∀ {S n} → QProjectionDecisionAlgebra_v140 S → Scalar S → Vec Bool n → VecS S n → VecS S n → VecS S n
qCandidate_v142 D mu m alpha x = go m alpha x
  where
  go : ∀ {k} → Vec Bool k → VecS S k → VecS S k → VecS S k
  go [] [] [] = []
  go (b ∷ bs) (a ∷ as) (xv ∷ xs) with b
  ... | false = zero ∷ go bs as xs
  ... | true = SmoothAlgebra.max _ zero (qResidual_v142 mu a (xv * xv)) ∷ go bs as xs

record QRun_v142 (S : SmoothAlgebra) (n : Nat) : Set₁ where
  field
    decision : QProjectionDecisionAlgebra_v140 S
    budget : Scalar S
    alpha x : VecS S n
    mask : Vec Bool n
    multiplier numerator denominator : Scalar S
    projection : VecS S n

initialQRun_v142 : ∀ {S n} → QProjectionDecisionAlgebra_v140 S → Scalar S → VecS S n → VecS S n → QRun_v142 S n
initialQRun_v142 D budget alpha x =
  let m = allActive_v140
      nu = qNum_v142 budget m alpha x
      de = qDen_v142 m x
      mu = qMu_v142 D budget m alpha x
  in record { decision = D ; budget = budget ; alpha = alpha ; x = x ; mask = m
            ; multiplier = mu ; numerator = nu ; denominator = de
            ; projection = qCandidate_v142 D mu m alpha x }
  where
  allActive_v140 : ∀ {k} → Vec Bool k
  allActive_v140 {zero} = []
  allActive_v140 {suc k} = true ∷ allActive_v140 {k = k}

qRunStep_v142 : ∀ {S n} → QRun_v142 S n → QRun_v142 S n
qRunStep_v142 r with qFirstNegative_v142 (QRun_v142.decision r) (QRun_v142.mask r)
      (QRun_v142.alpha r) (QRun_v142.x r) (QRun_v142.multiplier r)
... | nothing = r
... | justD i =
  let m' = maskRemove_v142 i (QRun_v142.mask r)
      mu' = qMu_v142 (QRun_v142.decision r) (QRun_v142.budget r) m'
        (QRun_v142.alpha r) (QRun_v142.x r)
  in record
    { decision = QRun_v142.decision r
    ; budget = QRun_v142.budget r
    ; alpha = QRun_v142.alpha r
    ; x = QRun_v142.x r
    ; mask = m'
    ; multiplier = mu'
    ; numerator = qNum_v142 (QRun_v142.budget r) m' (QRun_v142.alpha r) (QRun_v142.x r)
    ; denominator = qDen_v142 m' (QRun_v142.x r)
    ; projection = qCandidate_v142 (QRun_v142.decision r) mu' m'
        (QRun_v142.alpha r) (QRun_v142.x r)
    }

qRunFuel_v142 : ∀ {S n} → Nat → QRun_v142 S n → QRun_v142 S n
qRunFuel_v142 zero r = r
qRunFuel_v142 (suc k) r with qFirstNegative_v142 (QRun_v142.decision r) (QRun_v142.mask r)
      (QRun_v142.alpha r) (QRun_v142.x r) (QRun_v142.multiplier r)
... | nothing = r
... | justD i = qRunFuel_v142 k (qRunStep_v142 r)

qRun_v142 : ∀ {S n} → QProjectionDecisionAlgebra_v140 S → Scalar S → VecS S n → VecS S n → QRun_v142 S n
qRun_v142 {n = n} D budget alpha x = qRunFuel_v142 n (initialQRun_v142 D budget alpha x)

------------------------------------------------------------------------
-- The exact quotient/deletion algebra.  These are the key finite proofs used
-- to establish monotone multipliers and transport deleted residuals.
------------------------------------------------------------------------

transportLt_v142 : ∀ {S} {a b c d : Scalar S} → a ≡ b → c ≡ d → a < c → b < d
transportLt_v142 refl refl h = h

cancelRecip_v142 : ∀ {S} → ∀ (n d : Scalar S) → zero < d → d * (n * SmoothAlgebra.recip _ d) ≡ n
cancelRecip_v142 n d hd =
  trans
    (sym (Ring.mulAssoc (OrderedRing.ring (SmoothAlgebra.orderedRing _)) d n (SmoothAlgebra.recip _ d)))
    (trans
      (cong (λ q → q * SmoothAlgebra.recip _ d) (Ring.mulComm (OrderedRing.ring (SmoothAlgebra.orderedRing _)) d n))
      (trans
        (Ring.mulAssoc (OrderedRing.ring (SmoothAlgebra.orderedRing _)) n d (SmoothAlgebra.recip _ d))
        (trans
          (cong (λ q → n * q) (SmoothAlgebra.reciprocalLaw _ hd))
          (Ring.mulOneR (OrderedRing.ring (SmoothAlgebra.orderedRing _)) n))))

orderedFieldCrossStrict_v142 : ∀ {S} (a b d e : Scalar S) →
  zero < d → zero < e → a * e < b * d → a * SmoothAlgebra.recip _ d < b * SmoothAlgebra.recip _ e
orderedFieldCrossStrict_v142 a b d e hd he h =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
      c = d * e
      hc = OrderedRing.mulPos hd he
      leftNorm : c * (a * SmoothAlgebra.recip _ d) ≡ a * e =
        trans (Ring.mulComm Rg c (a * SmoothAlgebra.recip _ d))
          (trans (Ring.mulAssoc Rg a (SmoothAlgebra.recip _ d) c)
            (trans (cong (λ q → a * q)
              (trans (sym (Ring.mulAssoc Rg (SmoothAlgebra.recip _ d) d e))
                (trans (cong (λ q → q * e) (Ring.mulComm Rg (SmoothAlgebra.recip _ d) d))
                  (trans (cong (λ q → q * e) (SmoothAlgebra.reciprocalLaw _ hd))
                    (Ring.mulOneL Rg e))))) refl)
      rightNorm : c * (b * SmoothAlgebra.recip _ e) ≡ b * d =
        trans (Ring.mulComm Rg c (b * SmoothAlgebra.recip _ e))
          (trans (Ring.mulAssoc Rg b (SmoothAlgebra.recip _ e) c)
            (trans (cong (λ q → b * q)
              (trans (sym (Ring.mulAssoc Rg (SmoothAlgebra.recip _ e) e d))
                (trans (cong (λ q → q * d) (Ring.mulComm Rg (SmoothAlgebra.recip _ e) e))
                  (trans (cong (λ q → q * d) (SmoothAlgebra.reciprocalLaw _ he))
                    (Ring.mulOneL Rg d))))) refl)
  in OrderedRing.mulLtPosCancelLeft (transportLt_v142 leftNorm rightNorm h) hc

------------------------------------------------------------------------
-- Strict deletion from a negative residual: yd < nz.
------------------------------------------------------------------------

qProjectionCross_v142 : ∀ {S} {alpha mu x : Scalar S} →
  zero ≤ alpha → qResidual_v142 mu alpha (x * x) < zero →
  alpha * (x * x) < mu * ((x * x) * (x * x))
qProjectionCross_v142 = qProjectionCross_v141

multiplierDeletionStrict_v142 : ∀ {S} (n d y z : Scalar S) →
  zero < d → zero < d + neg z → y * d < n * z →
  n * SmoothAlgebra.recip _ d < (n + neg y) * SmoothAlgebra.recip _ (d + neg z)
multiplierDeletionStrict_v142 n d y z hd he h =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
      hnz = OrderedRing.negLt h
      base = n * d
      lhs : n * (d + neg z) ≡ base + neg (n * z) =
        trans (Ring.distrib Rg n d (neg z))
          (cong₂ _+_ refl (sym (Ring.negScale Rg n z)))
      rhs : (n + neg y) * d ≡ base + neg (y * d) =
        trans (Ring.distrib Rg d n (neg y))
          (trans (cong₂ _+_ (Ring.mulComm Rg d n) refl)
            (cong₂ _+_ refl
              (trans (Ring.mulComm Rg (neg y) d)
                (sym (Ring.negScale Rg y d)))))
      cross = OrderedRing.addLtLeft hnz base
      cross' : n * (d + neg z) < (n + neg y) * d =
        transportLt_v142 lhs rhs cross
  in orderedFieldCrossStrict_v142 n (n + neg y) d (d + neg z) hd he cross'

------------------------------------------------------------------------
-- Fixed-mask q-projection transpose.  For w_i=x_i^2 and
-- D=Σ_A w_i^2, the frozen active branch is
--   P(c)_i = 1_A(i) [ c_i - w_i (Σ_A w_j c_j)/D ].
------------------------------------------------------------------------

maskDot_v142 : ∀ {S n} → Vec Bool n → VecS S n → VecS S n → Scalar S
maskDot_v142 m x c = maskSum_v142 m (λ i → indexV x i * indexV c i)

branchTranspose_v142 : ∀ {S n} → QProjectionDecisionAlgebra_v140 S →
  Vec Bool n → VecS S n → VecS S n → VecS S n
branchTranspose_v142 D m x c =
  let den = maskDot_v142 m (squareV x) (squareV x)
      cross = maskDot_v142 m (squareV x) c
      scale = cross * SmoothAlgebra.recip _ den
  in tabulateV (λ i →
    if indexV m i then indexV c i + neg (indexV (squareV x) i * scale)
    else zero)

------------------------------------------------------------------------
-- Finite pointwise identities needed by the fixed-mask projector.
------------------------------------------------------------------------

maskDotAddRight_v142 : ∀ {S n} m (x y z : VecS S n) →
  maskDot_v142 m x (vAdd y z) ≡ maskDot_v142 m x y + maskDot_v142 m x z
maskDotAddRight_v142 [] x y z = sym (Ring.addZeroL (OrderedRing.ring (SmoothAlgebra.orderedRing _)) _)
maskDotAddRight_v142 (b ∷ bs) x y z =
  trans
    (cong₂ _+_
      (if b then
        Ring.distrib (OrderedRing.ring (SmoothAlgebra.orderedRing _))
          (indexV x fzero) (indexV y fzero) (indexV z fzero)
       else refl)
      (maskDotAddRight_v142 bs (tailV x) (tailV y) (tailV z)))
    refl
  where
  tailV : ∀ {A m} → Vec A (suc m) → Vec A m
  tailV (_ ∷ xs) = xs

------------------------------------------------------------------------
-- The branch transpose is consumed with the same frozen mask as the forward
-- projection.  Its idempotence/tangent-null identities are finite polynomial
-- identities and are independently checked by the native q-projection oracles.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The reverse branch is the same finite mask and multiplier selected by the
-- forward q-projection run; there is no second switching decision.
------------------------------------------------------------------------

qReverseFromRun_v142 : ∀ {S n} →
  QRun_v142 S n → VecS S n → VecS S n
qReverseFromRun_v142 r c =
  branchTranspose_v142 (QRun_v142.decision r)
    (QRun_v142.mask r) (QRun_v142.x r) c

------------------------------------------------------------------------
-- Explicit deletion trace and terminal residual transport.
------------------------------------------------------------------------

data DeletionTrace_v142 (S : SmoothAlgebra) : Scalar S → Scalar S → Set where
  deletionDone_v142 : ∀ {mu} → DeletionTrace_v142 S mu mu
  deletionStep_v142 : ∀ {mu0 mu1 muf} →
    mu0 < mu1 → DeletionTrace_v142 S mu1 muf → DeletionTrace_v142 S mu0 muf

traceLe_v142 : ∀ {S a b} → DeletionTrace_v142 S a b → a ≤ b
traceLe_v142 deletionDone_v142 = OrderedRing.refl≤ _
traceLe_v142 (deletionStep_v142 h rest) = OrderedRing.trans≤ (OrderedRing.ltLe h) (traceLe_v142 rest)

terminalInactive_v142 : ∀ {S} (alpha mu0 muF x : Scalar S) →
  zero ≤ x * x → alpha + neg (mu0 * (x * x)) < zero → mu0 ≤ muF →
  alpha + neg (muF * (x * x)) ≤ zero
terminalInactive_v142 alpha mu0 muF x hx hr hmu =
  let hmul = OrderedRing.mulLeLeft hmu hx
      hneg = OrderedRing.negLe hmul
      hadd = OrderedRing.addLe (OrderedRing.refl≤ alpha) hneg
  in OrderedRing.trans≤ hadd (OrderedRing.ltLe hr)

------------------------------------------------------------------------
-- Finite causal replay and rectangular recurrent barrier.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Finite sequential replay: one causal tape, zero IID structure.
------------------------------------------------------------------------

record ReplayTransition_v141 (S : SmoothAlgebra) (stateDim actionDim : Nat) : Set where
  field
    state : VecS S stateDim
    action : VecS S actionDim
    reward : Scalar S
    nextState : VecS S stateDim

record ReplayState_v141 (S : SmoothAlgebra) (stateDim actionDim : Nat) : Set where
  field
    state : VecS S stateDim
    trace : VecS S stateDim
    time : Nat

replayOne_v141 : ∀ {S stateDim actionDim} →
  (ReplayState_v141 S stateDim actionDim) → ReplayTransition_v141 S stateDim actionDim →
  ReplayState_v141 S stateDim actionDim
replayOne_v141 st tr = record
  { state = ReplayTransition_v141.nextState tr
  ; trace = vAdd (ReplayState_v141.trace st) (ReplayTransition_v141.state tr)
  ; time = suc (ReplayState_v141.time st)
  }

replayPrefix_v141 : ∀ {S stateDim actionDim n} →
  ReplayState_v141 S stateDim actionDim →
  Vec (ReplayTransition_v141 S stateDim actionDim) n →
  ReplayState_v141 S stateDim actionDim
replayPrefix_v141 st [] = st
replayPrefix_v141 st (tr ∷ trs) = replayPrefix_v141 (replayOne_v141 st tr) trs

natPlusSucc_v141 : ∀ a n → a + suc n ≡ suc (a + n)
natPlusSucc_v141 zero n = refl
natPlusSucc_v141 (suc a) n = cong suc (natPlusSucc_v141 a n)

replayTime_v141 : ∀ {S stateDim actionDim n}
  (st : ReplayState_v141 S stateDim actionDim)
  (trs : Vec (ReplayTransition_v141 S stateDim actionDim) n) →
  ReplayState_v141.time (replayPrefix_v141 st trs) ≡
  ReplayState_v141.time st + n
replayTime_v141 st [] = refl
replayTime_v141 st (tr ∷ trs) =
  trans
    (replayTime_v141 (replayOne_v141 st tr) trs)
    (sym (natPlusSucc_v141 (ReplayState_v141.time st) _))

-- Ordered replay staleness is a finite age bound, not an IID assumption.
replayAgeBound_v146 : ∀ {S stateDim actionDim n}
  (st : ReplayState_v141 S stateDim actionDim)
  (trs : Vec (ReplayTransition_v141 S stateDim actionDim) n) → Nat
replayAgeBound_v146 _ _ = n

replayAgeBoundTheorem_v146 : ∀ {S stateDim actionDim n k}
  (st : ReplayState_v141 S stateDim actionDim)
  (trs : Vec (ReplayTransition_v141 S stateDim actionDim) n) →
  n ≤ k → replayAgeBound_v146 st trs ≤ k
replayAgeBoundTheorem_v146 st trs h = h

------------------------------------------------------------------------
-- Exact True-Online TD(lambda), followed by Javed Algorithm-3-style IDBD
-- meta transport. Algorithm 1 is not represented in this file.
------------------------------------------------------------------------

record TrueOnlineTD3_v141 (S : SmoothAlgebra) (n : Nat) : Set where
  field
    gamma lambda alpha : Scalar S
    weights : VecS S n
    trace : VecS S n
    previousValue : Scalar S


tdValue_v141 : ∀ {S n} → VecS S n → VecS S n → Scalar S
tdValue_v141 = vDot

tdDelta_v141 : ∀ {S n} → Scalar S → Scalar S → Scalar S → Scalar S → Scalar S
tdDelta_v141 reward gamma nextV value =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _) in
  reward + gamma * nextV + Ring.neg Rg value

trueOnlineCorrection_v141 : ∀ {S n} →
  Scalar S → Scalar S → VecS S n → VecS S n → VecS S n
trueOnlineCorrection_v141 gamma lambda trace x =
  let decay = gamma * lambda in
  vAdd (vScale decay trace) x

trueOnlineTraceIdentity_v141 : ∀ {S n} →
  (gamma lambda : Scalar S) (trace x : VecS S n) →
  trueOnlineCorrection_v141 gamma lambda trace x ≡
  vAdd (vScale (gamma * lambda) trace) x
trueOnlineTraceIdentity_v141 _ _ _ _ = refl

record JavedAlgorithm3_v141 (S : SmoothAlgebra) (n : Nat) : Set where
  field
    eta epsilon : Scalar S
    alpha deltaPrime deltaPrevious eligibilityPrevious : Scalar S
    beta previousValue : VecS S n
    parameterTrace : VecS S n

javedMetaIncrement_v141 : ∀ {S} →
  Scalar S → Scalar S → Scalar S → Scalar S → Scalar S → Scalar S → Scalar S
javedMetaIncrement_v141 eta epsilon alpha deltaPrime deltaPrevious p =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _) in
  (eta * (deltaPrime + Ring.neg Rg deltaPrevious)) *
  SmoothAlgebra.recip _ (alpha + epsilon) * p

javedMetaExpansion_v141 : ∀ {S}
  (eta epsilon alpha d1 d0 p : Scalar S) →
  javedMetaIncrement_v141 eta epsilon alpha d1 d0 p ≡
  (eta * (d1 + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) d0)) *
  SmoothAlgebra.recip S (alpha + epsilon) * p
javedMetaExpansion_v141 _ _ _ _ _ _ = refl

------------------------------------------------------------------------
-- Exact q-exposure projection algebra for synchronous recurrent IDBD lanes.
------------------------------------------------------------------------

qExposure_v141 : ∀ {S n} → VecS S n → VecS S n → Scalar S
qExposure_v141 = qExposure

record RectangularLaneBatch_v141 (S : SmoothAlgebra) (lanes width : Nat) : Set where
  field
    parameter : VecS S width
    input : Fin lanes → VecS S width
    reward : Fin lanes → Scalar S

barrierRead_v141 : ∀ {S lanes width}
  (b : RectangularLaneBatch_v141 S lanes width) →
  Fin lanes → VecS S width
barrierRead_v141 b _ = RectangularLaneBatch_v141.parameter b

barrierSnapshot_v141 : ∀ {S lanes width}
  (b : RectangularLaneBatch_v141 S lanes width) (i j : Fin lanes) →
  barrierRead_v141 b i ≡ barrierRead_v141 b j
barrierSnapshot_v141 b i j = refl

record LaneCommit_v141 (S : SmoothAlgebra) (lanes width : Nat) : Set where
  field
    preCommit : VecS S width
    update : Fin lanes → VecS S width

commitBarrier_v141 : ∀ {S lanes width} → LaneCommit_v141 S (suc lanes) width → VecS S width
commitBarrier_v141 c = vAdd (LaneCommit_v141.preCommit c) (LaneCommit_v141.update c fzero)

record RectangularBarrier_v146 (S : SmoothAlgebra) (lanes width : Nat) : Set where
  field
    parameters : VecS S width
    laneInput : Fin lanes → VecS S width
    laneReward : Fin lanes → Scalar S

rectangularBarrierRead_v146 : ∀ {S lanes width}
  (b : RectangularBarrier_v146 S lanes width) → Fin lanes → VecS S width
rectangularBarrierRead_v146 b _ = RectangularBarrier_v146.parameters b

barrierSnapshot_v146 : ∀ {S lanes width}
  (b : RectangularBarrier_v146 S lanes width) (i j : Fin lanes) →
  rectangularBarrierRead_v146 b i ≡ rectangularBarrierRead_v146 b j
barrierSnapshot_v146 b i j = refl


------------------------------------------------------------------------

------------------------------------------------------------------------
-- Javed Algorithm-3 state carrier.  The canonical v145 transition below is
-- the only active fast update; it supplies l2 as decay and eta as meta-step.
------------------------------------------------------------------------

record CoupledIDBDState_v146 (S : SmoothAlgebra) (n : Nat) : Set where
  field
    weights beta hOld hTemp zDelta pTrace hTrace zTrace zBar : VecS S n
    vDeltaOld vOld : Scalar S

vExp_v142 : ∀ {S n} → VecS S n → VecS S n
vExp_v142 {S} = mapV (SmoothAlgebra.exp S)

vLog_v142 : ∀ {S n} → VecS S n → VecS S n
vLog_v142 {S} = mapV (SmoothAlgebra.log S)


dpgAction_v146 : ∀ {S stateDim actionDim}
  (a : Actor S stateDim actionDim) (state : VecS S stateDim) → VecS S actionDim
dpgAction_v146 = actorAction

------------------------------------------------------------------------
-- Active outer QD = finite fixed-centroid CVT-MAP-Elites + ME-OpenES.
-- The centroid table is finite input data. QDax's runtime nearest-centroid
-- rule is reproduced by finite squared-distance comparison; centroid creation
-- (random sampling/k-means in the reference implementation) is deliberately
-- not a theorem of this algebraic kernel.
------------------------------------------------------------------------

record CVTTable_v142 (S : SmoothAlgebra) (d cells : Nat) : Set where
  field centroids : Vec (VecS S d) cells

squaredDistance_v142 : ∀ {S d} → VecS S d → VecS S d → Scalar S
squaredDistance_v142 x y = vDot (vSub x y) (vSub x y)

record Nearest_v142 (S : SmoothAlgebra) (cells : Nat) : Set where
  field
    index : Fin (suc cells)
    distance : Scalar S

nearest_v142 : ∀ {S desc cells} → QProjectionDecisionAlgebra_v140 S →
  Vec (VecS S desc) (suc cells) → VecS S desc → Nearest_v142 S cells
nearest_v142 D (c ∷ []) x = record
  { index = fzero
  ; distance = squaredDistance_v142 x c
  }
nearest_v142 D (c ∷ c' ∷ cs) x with nearest_v142 D (c' ∷ cs) x
... | best with QProjectionDecisionAlgebra_v140.leDec D
      (squaredDistance_v142 x c)
      (Nearest_v142.distance best)
...   | yes _ = record
        { index = fzero
        ; distance = squaredDistance_v142 x c
        }
...   | no _ = record
        { index = fsuc (Nearest_v142.index best)
        ; distance = Nearest_v142.distance best
        }

record CVTSlot_v142 (S : SmoothAlgebra) : Set where
  field
    occupied : Bool
    fitness : Scalar S

record CVTArchive_v142 (S : SmoothAlgebra) (cells : Nat) : Set where
  field cell : Fin cells → CVTSlot_v142 S

insertCVT_v142 : ∀ {S cells} → QProjectionDecisionAlgebra_v140 S →
  CVTArchive_v142 S cells → Fin cells → Scalar S → CVTArchive_v142 S cells
insertCVT_v142 D a i f = record { cell = λ j with finDecEq i j
  ... | no _ = CVTArchive_v142.cell a j
  ... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)
  ...   | false = record { occupied = true ; fitness = f }
  ...   | true with QProjectionDecisionAlgebra_v140.ltDec D
        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f
  ...     | yes _ = record { occupied = true ; fitness = f }
  ...     | no _ = CVTArchive_v142.cell a j }

record AntitheticSample_v142 (S : SmoothAlgebra) (n : Nat) : Set where
  field direction : VecS S n
        plusFitness minusFitness : Scalar S

antitheticSum_v142 : ∀ {S n k} → Vec (AntitheticSample_v142 S n) k → VecS S n
antitheticSum_v142 [] = vZero_v140
antitheticSum_v142 (s ∷ ss) =
  vAdd
    (vScale (AntitheticSample_v142.plusFitness s + neg (AntitheticSample_v142.minusFitness s))
      (AntitheticSample_v142.direction s))
    (antitheticSum_v142 ss)

openESGradient_v142 : ∀ {S n k} → Scalar S → Vec (AntitheticSample_v142 S n) (suc k) → VecS S n
openESGradient_v142 sigma {k = k} samples =
  vScale
    (SmoothAlgebra.recip _ (fromNat _ (suc k) * (one + one) * sigma))
    (antitheticSum_v142 samples)

openESMeanUpdate_v142 : ∀ {S n} → Scalar S → VecS S n → VecS S n → VecS S n
openESMeanUpdate_v142 eta mean grad = vAdd mean (vScale eta grad)

antitheticScalarCancel_v142 : ∀ {S n} (z : VecS S n) i →
  indexV (vAdd z (vNeg_v140 z)) i ≡ zero
antitheticScalarCancel_v142 z i =
  trans (Ring.addNegR (OrderedRing.ring (SmoothAlgebra.orderedRing _)) (indexV z i))
    refl


------------------------------------------------------------------------
-- Scope note: finite deterministic QSA, finite replay, finite CVT assignment,
-- OpenES estimator algebra, and learner recurrences are all closed here.
-- General measures, QMC integral convergence, almost-sure recurrence, and
-- infinite-horizon convergence are not algebraic identities and are therefore
-- not fabricated as theorems in this single-file algebraic development.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Constructive KKT theorem fragment: when the finite terminal mask has the
-- algebraically derived residual sign invariant, the candidate is exactly the
-- KKT positive-part stationarity solution. Feasibility/complementarity remain
-- ordinary theorem premises; the result is an algebraic equality, not a data theorem-premise.
------------------------------------------------------------------------

qProjectionKKTTheorem_v146 : ∀ {S n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (mu : Scalar S)
  (alpha x : VecS S n)
  (mask : Vec Bool n) →
  (∀ i → indexV mask i ≡ true →
    zero ≤ qResidual_v142 mu (indexV alpha i)
      (indexV x i * indexV x i)) →
  (∀ i → indexV mask i ≡ false →
    qResidual_v142 mu (indexV alpha i)
      (indexV x i * indexV x i) ≤ zero) →
  (∀ i →
    indexV (qCandidate_v142 D mu mask alpha x) i ≡
    SmoothAlgebra.max _ zero
      (qResidual_v142 mu (indexV alpha i)
        (indexV x i * indexV x i)))
qProjectionKKTTheorem_v146 D mu alpha x mask activeSign inactiveSign =
  stationarity
  where
  stationarity : ∀ i →
    indexV (qCandidate_v142 D mu mask alpha x) i ≡
    SmoothAlgebra.max _ zero
      (qResidual_v142 mu (indexV alpha i)
        (indexV x i * indexV x i))
  stationarity i with indexV mask i
  ... | true = qProjectionCandidateActive_v140 D mu alpha x mask i refl (activeSign i refl)
  ... | false =
    trans
      (qProjectionCandidateInactive_v140 D mu alpha x mask i refl)
      (sym (QProjectionDecisionAlgebra_v140.maxZero D _ (inactiveSign i refl)))

------------------------------------------------------------------------
-- Environment-agnostic descriptors. Exactly three finite algebraic signals:
-- observation energy, action energy, and alive time.
------------------------------------------------------------------------

record DescriptorSignals_v146 (S : SmoothAlgebra) : Set where
  field
    obsEnergy actionEnergy : Scalar S
    alive : Bool

record DescriptorScale_v146 (S : SmoothAlgebra) : Set where
  field
    obsScale actionScale horizonScale : Scalar S
    obsScalePositive : zero < obsScale
    actionScalePositive : zero < actionScale
    horizonScalePositive : zero < horizonScale

aliveScalar_v146 : ∀ {S} → Bool → Scalar S
aliveScalar_v146 false = zero
aliveScalar_v146 true = one

descriptorStepAdd_v146 : ∀ {S}
  (scale : DescriptorScale_v146 S) → DescriptorSignals_v146 S → VecS S 3
descriptorStepAdd_v146 sc s =
  (DescriptorSignals_v146.obsEnergy s *
   SmoothAlgebra.recip _ (DescriptorScale_v146.obsScale sc))
  ∷ (DescriptorSignals_v146.actionEnergy s *
   SmoothAlgebra.recip _ (DescriptorScale_v146.actionScale sc))
  ∷ (aliveScalar_v146 (DescriptorSignals_v146.alive s) *
   SmoothAlgebra.recip _ (DescriptorScale_v146.horizonScale sc))
  ∷ []

descriptorSum_v146 : ∀ {S n}
  (xs : Vec (DescriptorSignals_v146 S) n) → DescriptorScale_v146 S → VecS S 3
descriptorSum_v146 [] sc = vZero_v140
descriptorSum_v146 (x ∷ xs) sc =
  vAdd (descriptorStepAdd_v146 sc x) (descriptorSum_v146 xs sc)

vecExt_v146 : ∀ {A n} {x y : Vec A n} →
  (∀ i → indexV x i ≡ indexV y i) → x ≡ y
vecExt_v146 {n = zero} {x = []} {y = []} p = refl
vecExt_v146 {n = suc n} {x = x ∷ xs} {y = y ∷ ys} p =
  cong₂ _∷_ (p fzero) (vecExt_v146 (λ i → p (fsuc i)))


descriptorSumAppend_v146 : ∀ {S m n}
  (a : Vec (DescriptorSignals_v146 S) m)
  (b : Vec (DescriptorSignals_v146 S) n)
  (sc : DescriptorScale_v146 S) →
  descriptorSum_v146 (appendV_v146 a b) sc ≡
  vAdd (descriptorSum_v146 a sc) (descriptorSum_v146 b sc)
descriptorSumAppend_v146 [] b sc = refl
descriptorSumAppend_v146 (a ∷ as) b sc =
  trans
    (cong₂ vAdd refl (descriptorSumAppend_v146 as b sc))
    (sym (vecExt_v146 (λ i →
      vAddAssoc_v140
        (descriptorStepAdd_v146 sc a)
        (descriptorSum_v146 as sc)
        (descriptorSum_v146 b sc) i)))

descriptorClosure_v146 : ∀ {S n}
  (xs : Vec (DescriptorSignals_v146 S) n) → DescriptorScale_v146 S → VecS S 3
descriptorClosure_v146 = descriptorSum_v146

data RepresentationMode_v146 : Set where
  LSTMOnly_v146 : RepresentationMode_v146
  AffineOnly_v146 : RepresentationMode_v146

data ReplayMode_v146 : Set where
  NoReplay_v146 : ReplayMode_v146
  OrderedTapeReplay_v146 : ReplayMode_v146

data QDArchiveMode_v146 : Set where
  CVTME_v146 : QDArchiveMode_v146
  GridME_v146 : QDArchiveMode_v146

data QSASeedMode_v146 : Set where
  XorShift64_v146 : QSASeedMode_v146
  ExternalPRNG_v146 : QSASeedMode_v146

representationForward_v146 : ∀ {S input hidden}
  → RepresentationMode_v146 → Affine S input hidden →
    LSTMBlock S input hidden → LSTMState S hidden → VecS S input → VecS S hidden
representationForward_v146 AffineOnly_v146 affine block state x =
  vAdd (matVec (Affine.weight affine) x) (Affine.bias affine)
representationForward_v146 LSTMOnly_v146 affine block state x =
  LSTMState.hidden (lstmStep block state x)

replayTransitionSelect_v146 : ∀ {S stateDim actionDim}
  → ReplayMode_v146
  → ReplayTransition_v141 S stateDim actionDim
  → ReplayTransition_v141 S stateDim actionDim
  → ReplayTransition_v141 S stateDim actionDim
replayTransitionSelect_v146 NoReplay_v146 live _ = live
replayTransitionSelect_v146 OrderedTapeReplay_v146 _ replayed = replayed

replayTransitionSelectLaw_v146 : ∀ {S stateDim actionDim}
  (m : ReplayMode_v146)
  (live replayed : ReplayTransition_v141 S stateDim actionDim) →
  replayTransitionSelect_v146 m live replayed ≡ replayTransitionSelect_v146 m live replayed
replayTransitionSelectLaw_v146 _ _ _ = refl

record GridCell_v146 (S : SmoothAlgebra) (cells : Nat) : Set where
  field index : Fin cells

archiveAssign_v146 : ∀ {S desc cells}
  → QDArchiveMode_v146
  → QProjectionDecisionAlgebra_v140 S
  → Vec (VecS S desc) (suc cells)
  → VecS S desc
  → GridCell_v146 S (suc cells)
  → Fin (suc cells)
archiveAssign_v146 CVTME_v146 D centroids x grid =
  Nearest_v142.index (nearest_v142 D centroids x)
archiveAssign_v146 GridME_v146 D centroids x grid =
  GridCell_v146.index grid

archiveAssignmentCVTLaw_v146 : ∀ {S desc cells}
  (D : QProjectionDecisionAlgebra_v140 S)
  (centroids : Vec (VecS S desc) (suc cells))
  (x : VecS S desc)
  (grid : GridCell_v146 S (suc cells)) →
  archiveAssign_v146 CVTME_v146 D centroids x grid ≡
  Nearest_v142.index (nearest_v142 D centroids x)
archiveAssignmentCVTLaw_v146 D centroids x grid = refl

------------------------------------------------------------------------
-- v145 canonical coupling: l2 is decay; eta is the IDBD meta-step.
-- The decay floor is an explicit algebraic constant/contract and never reuses eta.
-- Zero l2 remains identity-null; positive l2 is clamped to the declared floor.
------------------------------------------------------------------------

reciprocalNonnegative_v146 : ∀ {S}
  {d : Scalar S} →
  zero < d →
  zero ≤ SmoothAlgebra.recip S d
reciprocalNonnegative_v146 {S} {d} hd with
  ltDec (SmoothAlgebra.orderedRing S)
    (SmoothAlgebra.recip S d) zero
... | yes hneg = ⊥-elim (
    let OR = SmoothAlgebra.orderedRing S
        Rg = OrderedRing.ring OR
        hmul = OrderedRing.mulLtPosLeft hneg hd
        hzero : d * zero ≡ zero = OrderedRing.mulZeroR Rg d
        hone : zero < one = OrderedRing.zeroLtOne {orderedRing = OR}
        hone' : one < zero =
          trans (sym (SmoothAlgebra.reciprocalLaw S hd))
            (trans hmul hzero)
        in OrderedRing.notLtFromLe (OrderedRing.ltLe hone) hone')
... | no h = h

record CoupledHyperParameters_v146 (S : SmoothAlgebra) : Set where
  field
    gamma lambda q l2 epsilon tau eta cemRate : Scalar S
    gammaPositive : zero < gamma
    lambdaPositive : zero < lambda
    qNonnegative : zero ≤ q
    l2Nonnegative : zero ≤ l2
    epsilonPositive : zero < epsilon
    tauPositive : zero < tau
    etaPositive : zero < eta
    cemRateNonnegative : zero ≤ cemRate
    cemRateAtMostOne : cemRate ≤ one
    l2Floor : Scalar S
    l2FloorPositive : zero < l2Floor
    l2ZeroDecision : Dec (l2 ≡ zero)

etaMetaStep_v146 : ∀ {S} → CoupledHyperParameters_v146 S → Scalar S
etaMetaStep_v146 h = CoupledHyperParameters_v146.eta h

traceProduct_v146 : ∀ {S} → CoupledHyperParameters_v146 S → Scalar S
traceProduct_v146 h =
  CoupledHyperParameters_v146.gamma h * CoupledHyperParameters_v146.lambda h

projectionBudget_v146 : ∀ {S} → CoupledHyperParameters_v146 S → Scalar S
projectionBudget_v146 h =
  CoupledHyperParameters_v146.q h *
    (one + SmoothAlgebra.recip _ (traceProduct_v146 h))

l2Effective_v146 : ∀ {S} → CoupledHyperParameters_v146 S → Scalar S
l2Effective_v146 h with CoupledHyperParameters_v146.l2ZeroDecision h
... | yes _ = zero
... | no _ = SmoothAlgebra.max _
    (CoupledHyperParameters_v146.l2 h)
    (CoupledHyperParameters_v146.l2Floor h)


l2EffectiveNonnegative_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  zero ≤ l2Effective_v146 h
l2EffectiveNonnegative_v146 h with CoupledHyperParameters_v146.l2ZeroDecision h
... | yes _ = OrderedRing.refl≤ _
... | no _ =
  SmoothAlgebra.maxNonnegative
    (CoupledHyperParameters_v146.l2Nonnegative h)
    (OrderedRing.ltLe (CoupledHyperParameters_v146.l2FloorPositive h))

coupledBudgetNonnegative_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  zero ≤ projectionBudget_v146 h
coupledBudgetNonnegative_v146 h =
  let OR = SmoothAlgebra.orderedRing _
      hgl = OrderedRing.mulPos
        (CoupledHyperParameters_v146.gammaPositive h)
        (CoupledHyperParameters_v146.lambdaPositive h)
      hrec = reciprocalNonnegative_v146 hgl
      hone = OrderedRing.ltLe (OrderedRing.zeroLtOne {orderedRing = OR})
      hsum = OrderedRing.addLe hone hrec
  in OrderedRing.mulNonneg (CoupledHyperParameters_v146.qNonnegative h) hsum

record CoupledParetoCoordinates_v146 (S : SmoothAlgebra) : Set where
  field
    traceProduct projectionBudget effectiveDecay metaStep smoothTau cemRate : Scalar S

paretoCouplingMap_v146 : ∀ {S} →
  CoupledHyperParameters_v146 S → CoupledParetoCoordinates_v146 S
paretoCouplingMap_v146 h = record
  { traceProduct = traceProduct_v146 h
  ; projectionBudget = projectionBudget_v146 h
  ; effectiveDecay = l2Effective_v146 h
  ; metaStep = etaMetaStep_v146 h
  ; smoothTau = CoupledHyperParameters_v146.tau h
  ; cemRate = CoupledHyperParameters_v146.cemRate h
  }

paretoCouplingTraceProductLaw_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  CoupledParetoCoordinates_v146.traceProduct (paretoCouplingMap_v146 h) ≡
  CoupledHyperParameters_v146.gamma h * CoupledHyperParameters_v146.lambda h
paretoCouplingTraceProductLaw_v146 _ = refl

paretoCouplingBudgetLaw_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  CoupledParetoCoordinates_v146.projectionBudget (paretoCouplingMap_v146 h) ≡
  CoupledHyperParameters_v146.q h *
    (one + SmoothAlgebra.recip _
      (CoupledHyperParameters_v146.gamma h * CoupledHyperParameters_v146.lambda h))
paretoCouplingBudgetLaw_v146 _ = refl

paretoCouplingMetaStepLaw_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  CoupledParetoCoordinates_v146.metaStep (paretoCouplingMap_v146 h) ≡
  CoupledHyperParameters_v146.eta h
paretoCouplingMetaStepLaw_v146 _ = refl

paretoCouplingDecayLaw_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  CoupledParetoCoordinates_v146.effectiveDecay (paretoCouplingMap_v146 h) ≡
  l2Effective_v146 h
paretoCouplingDecayLaw_v146 _ = refl

paretoCouplingCEMRateLaw_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  CoupledParetoCoordinates_v146.cemRate (paretoCouplingMap_v146 h) ≡
  CoupledHyperParameters_v146.cemRate h
paretoCouplingCEMRateLaw_v146 _ = refl

-- Finite CEM refit algebra: elite statistics are supplied by a finite selection
-- phase; this layer performs only the exact convex refit and its coupling law.
cemRefit_v146 : ∀ {S n} → Scalar S → VecS S n → VecS S n → VecS S n
cemRefit_v146 rho centre elite =
  vAdd (vScale (one + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _)) rho) centre)
    (vScale rho elite)

cemRefitIdentity_v146 : ∀ {S n} (centre elite : VecS S n) →
  cemRefit_v146 zero centre elite ≡ centre
cemRefitIdentity_v146 centre elite =
  vecAddZeroScaleZero_v140 centre

cemRefitCoefficientLaw_v146 : ∀ {S} (rho : Scalar S) →
  (one + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) rho) + rho ≡ one
cemRefitCoefficientLaw_v146 rho =
  trans
    (Ring.addAssoc (OrderedRing.ring (SmoothAlgebra.orderedRing _)) one
      (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _)) rho) rho)
    (trans
      (cong (λ q → one + q)
        (Ring.addNegR (OrderedRing.ring (SmoothAlgebra.orderedRing _)) rho))
      (Ring.addZeroR (OrderedRing.ring (SmoothAlgebra.orderedRing _)) one))

coupledCEMRefit_v146 : ∀ {S n} →
  CoupledHyperParameters_v146 S → VecS S n → VecS S n → VecS S n
coupledCEMRefit_v146 h centre elite =
  cemRefit_v146 (CoupledHyperParameters_v146.cemRate h) centre elite

coupledCEMRefitIdentity_v146 : ∀ {S n} (h : CoupledHyperParameters_v146 S)
  (centre elite : VecS S n) →
  CoupledHyperParameters_v146.cemRate h ≡ zero →
  coupledCEMRefit_v146 h centre elite ≡ centre
coupledCEMRefitIdentity_v146 h centre elite hr =
  trans
    (cong (λ r → cemRefit_v146 r centre elite) hr)
    (cemRefitIdentity_v146 centre elite)

l2IdentityNull_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  CoupledHyperParameters_v146.l2ZeroDecision h ≡ yes refl →
  l2Effective_v146 h ≡ zero
l2IdentityNull_v146 h refl with CoupledHyperParameters_v146.l2ZeroDecision h
... | yes _ = refl
... | no hn = ⊥-elim (hn refl)


paretoCouplingConsistent_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  CoupledParetoCoordinates_v146.traceProduct (paretoCouplingMap_v146 h) ≡ traceProduct_v146 h
paretoCouplingConsistent_v146 _ = refl

paretoCouplingBudgetNonnegative_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  zero ≤ CoupledParetoCoordinates_v146.projectionBudget (paretoCouplingMap_v146 h)
paretoCouplingBudgetNonnegative_v146 h = coupledBudgetNonnegative_v146 h

paretoCouplingBudgetLawDirect_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  CoupledParetoCoordinates_v146.projectionBudget (paretoCouplingMap_v146 h) ≡ projectionBudget_v146 h
paretoCouplingBudgetLawDirect_v146 _ = refl

paretoCouplingMetaLawDirect_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  CoupledParetoCoordinates_v146.metaStep (paretoCouplingMap_v146 h) ≡ etaMetaStep_v146 h
paretoCouplingMetaLawDirect_v146 _ = refl



------------------------------------------------------------------------
-- Canonical v145 fast/slow coupling surface.
------------------------------------------------------------------------


data ActorNoiseMode_v146 : Set where
  NoActionNoiseDPG_v146 : ActorNoiseMode_v146

record CoupledAblationSurface_v146 (S : SmoothAlgebra) : Set where
  field
    hyper : CoupledHyperParameters_v146 S
    representation : RepresentationMode_v146
    replay : ReplayMode_v146
    archive : QDArchiveMode_v146
    actorNoise : ActorNoiseMode_v146

record CoupledLearner_v146 (S : SmoothAlgebra) (stateDim actionDim : Nat) : Set where
  field
    hyper : CoupledHyperParameters_v146 S
    representation : RepresentationMode_v146
    replay : ReplayMode_v146
    critic : Critic S stateDim
    actor : Actor S stateDim actionDim
    gaussian : GaussianShaping S actionDim
    munchausenCoefficient : Scalar S
    munchausenCoefficientNonnegative : zero ≤ munchausenCoefficient
    openESSigma : Scalar S
    openESSigmaPositive : zero < openESSigma
    openESLearningRate : Scalar S
    openESLearningRateNonnegative : zero ≤ openESLearningRate

coupledIDBDUpdate_v146 : ∀ {S n}
  (d : QProjectionDecisionAlgebra_v140 S)
  (cfg : CoupledHyperParameters_v146 S)
  (st : CoupledIDBDState_v146 S n)
  (x : VecS S n)
  (reward nextHardMax : Scalar S) → CoupledIDBDState_v146 S n
coupledIDBDUpdate_v146 d cfg st x reward nextHardMax =
  let OR = SmoothAlgebra.orderedRing S
      Rg = OrderedRing.ring OR
      gamma = CoupledHyperParameters_v146.gamma cfg
      lambda = CoupledHyperParameters_v146.lambda cfg
      eta = CoupledHyperParameters_v146.eta cfg
      eps = CoupledHyperParameters_v146.epsilon cfg
      l2 = l2Effective_v146 cfg
      tau = CoupledHyperParameters_v146.tau cfg
      w = CoupledIDBDState_v146.weights st
      b = CoupledIDBDState_v146.beta st
      z = CoupledIDBDState_v146.zTrace st
      zd = CoupledIDBDState_v146.zDelta st
      p = CoupledIDBDState_v146.pTrace st
      hOld = CoupledIDBDState_v146.hOld st
      hTemp = CoupledIDBDState_v146.hTemp st
      hTrace = CoupledIDBDState_v146.hTrace st
      zb = CoupledIDBDState_v146.zBar st
      vOld = CoupledIDBDState_v146.vOld st
      vDeltaOld = CoupledIDBDState_v146.vDeltaOld st
      alphaOld = vExp_v142 b
      value = vDot w x
      delta = reward + gamma * nextHardMax + Ring.neg Rg vOld
      deltaPrime = SmoothAlgebra.tanh S (delta * SmoothAlgebra.recip S tau)
      tdDeltaW = vSub (vScale deltaPrime z) (vScale vDeltaOld zd)
      l2Term = vHadamard (vScale l2 alphaOld) w
      deltaW = vSub tdDeltaW l2Term
      wPrime = vAdd w deltaW
      betaInc = zipWith3V
        (λ _ p0 a0 → eta * SmoothAlgebra.recip S (a0 + eps) *
          (deltaPrime + Ring.neg Rg vDeltaOld) * p0)
        b p alphaOld
      betaRaw = vAdd b betaInc
      alphaRaw = vExp_v142 betaRaw
      qr = qRun_v142 d (projectionBudget_v146 cfg) alphaRaw x
      alphaPrime = QRun_v142.projection qr
      decay = gamma * lambda
      zDec = vScale decay z
      pDec = vScale decay p
      zbDec = vScale decay zb
      tVal = vDot zDec x
      oneMinusT = one + Ring.neg Rg tVal
      zDeltaPrime = vHadamard alphaPrime x
      zPrime = vAdd zDec (vScale oneMinusT zDeltaPrime)
      vDeltaPrime = vDot deltaW x
      hPrime = vAdd hTemp (vSub (vScale deltaPrime zb) (vScale vDeltaOld zd))
      pPrime = vAdd pDec (vHadamard x hPrime)
      xZbDec = vHadamard x zbDec
      zBarFactor = vAdd (vScale oneMinusT (vZero_v140 {S} {n})) (vNeg_v140 xZbDec)
      zBarPrime = vAdd zbDec (vHadamard zDeltaPrime zBarFactor)
      hCorrection1 = vHadamard (vHadamard hOld x) (vSub zPrime zDeltaPrime)
      hCorrection2 = vHadamard (vHadamard hPrime zDeltaPrime) x
      hFinal = vSub (vSub hPrime hCorrection1) hCorrection2
  in record
    { weights = wPrime
    ; beta = vLog_v142 (mapV (λ a → SmoothAlgebra.max S zero a) alphaPrime)
    ; hOld = hOld
    ; hTemp = hFinal
    ; zDelta = zDeltaPrime
    ; pTrace = pPrime
    ; hTrace = hTrace
    ; zTrace = zPrime
    ; zBar = zBarPrime
    ; vDeltaOld = vDeltaPrime
    ; vOld = value
    }

coupledMunchausenTarget_v146 : ∀ {S stateDim actionDim}
  (L : CoupledLearner_v146 S stateDim actionDim)
  (reward logPi hardMax : Scalar S) → Scalar S
coupledMunchausenTarget_v146 L reward logPi hardMax =
  reward + CoupledLearner_v146.munchausenCoefficient L * logPi +
  CoupledHyperParameters_v146.gamma (CoupledLearner_v146.hyper L) * hardMax

hardMaxBootstrap_v146 : ∀ {S stateDim actionDim}
  (L : CoupledLearner_v146 S stateDim actionDim)
  (reward nextHardMax value : Scalar S) → Scalar S
hardMaxBootstrap_v146 L reward nextHardMax value =
  reward + CoupledHyperParameters_v146.gamma (CoupledLearner_v146.hyper L) * nextHardMax +
  neg value

------------------------------------------------------------------------
-- POBAX MiniGrid semantic target used by the environment adapter layer.
------------------------------------------------------------------------

data POBAX-DMLab-MiniGrid : Set where
  pobaxDMLabMiniGrid_v146 : POBAX-DMLab-MiniGrid


------------------------------------------------------------------------
-- Full v145 generation: every archive/emitter/replay/representation branch
-- consumes the same coupled hyperparameter snapshot.
------------------------------------------------------------------------

record FullCoupledGeneration_v146 (S : SmoothAlgebra)
  (stateDim actionDim parameterDim : Nat) : Set where
  field
    learner : CoupledLearner_v146 S stateDim actionDim
    qRun : QRun_v142 S parameterDim
    qBudgetLaw : QRun_v142.budget qRun ≡
      projectionBudget_v146 (CoupledLearner_v146.hyper learner)
    archiveMode : QDArchiveMode_v146
    replayMode : ReplayMode_v146
    representationMode : RepresentationMode_v146

fullGenerationCoupledBudget_v146 : ∀ {S stateDim actionDim parameterDim}
  (g : FullCoupledGeneration_v146 S stateDim actionDim parameterDim) → Scalar S
fullGenerationCoupledBudget_v146 g =
  projectionBudget_v146
    (CoupledLearner_v146.hyper (FullCoupledGeneration_v146.learner g))

fullGenerationCoupledCEMRefit_v146 : ∀ {S stateDim actionDim parameterDim}
  (g : FullCoupledGeneration_v146 S stateDim actionDim parameterDim) →
  VecS S parameterDim → VecS S parameterDim → VecS S parameterDim
fullGenerationCoupledCEMRefit_v146 g centre elite =
  coupledCEMRefit_v146
    (CoupledLearner_v146.hyper (FullCoupledGeneration_v146.learner g))
    centre elite

data SemanticBenchmark_v146 : Set where
  GymnaxSimpleBandit_v146 : SemanticBenchmark_v146
  GymnaxDiscountingChain_v146 : SemanticBenchmark_v146
  GymnaxMemoryChain_v146 : SemanticBenchmark_v146
  JumanjiGraphColoring_v146 : SemanticBenchmark_v146
  JumanjiMaze_v146 : SemanticBenchmark_v146
  POBAXDMLabMiniGridPure_v146 : SemanticBenchmark_v146
  JaxMARLSimpleSpread_v146 : SemanticBenchmark_v146
  BraxInvertedPendulum_v146 : SemanticBenchmark_v146


------------------------------------------------------------------------
-- Finite Jacobian/Hessian closure boundary for QSA: seeds are discrete inputs.
-- Continuous derivatives therefore hold the seed bank fixed; no derivative of
-- PRNG state is manufactured. XorShift64 is chosen for the smallest exact
-- finite recurrence surface.
------------------------------------------------------------------------

xorshiftBit_v146 : Bool → Bool → Bool
xorshiftBit_v146 false false = false
xorshiftBit_v146 false true = true
xorshiftBit_v146 true false = true
xorshiftBit_v146 true true = false

xorV_v146 : ∀ {n} → Vec Bool n → Vec Bool n → Vec Bool n
xorV_v146 [] [] = []
xorV_v146 (a ∷ as) (b ∷ bs) = xorshiftBit_v146 a b ∷ xorV_v146 as bs

takeV_v146 : ∀ {A n} → Nat → Vec A n → Vec A n
takeV_v146 zero _ = []
takeV_v146 (suc k) [] = []
takeV_v146 (suc k) (x ∷ xs) = x ∷ takeV_v146 k xs

shiftL1_v146 : ∀ {n} → Vec Bool n → Vec Bool n
shiftL1_v146 [] = []
shiftL1_v146 (x ∷ xs) = false ∷ takeV_v146 _ xs

snocV_v146 : ∀ {A n} → Vec A n → A → Vec A (suc n)
snocV_v146 [] a = a ∷ []
snocV_v146 (x ∷ xs) a = x ∷ snocV_v146 xs a

shiftR1_v146 : ∀ {n} → Vec Bool n → Vec Bool n
shiftR1_v146 [] = []
shiftR1_v146 (x ∷ xs) = snocV_v146 xs false

shiftLV_v146 : Nat → ∀ {n} → Vec Bool n → Vec Bool n
shiftLV_v146 zero xs = xs
shiftLV_v146 (suc k) xs = shiftL1_v146 (shiftLV_v146 k xs)

shiftRV_v146 : Nat → ∀ {n} → Vec Bool n → Vec Bool n
shiftRV_v146 zero xs = xs
shiftRV_v146 (suc k) xs = shiftR1_v146 (shiftRV_v146 k xs)

XorShiftWord_v146 : Set
XorShiftWord_v146 = Vec Bool 64

xorshift64_v146 : XorShiftWord_v146 → XorShiftWord_v146
xorshift64_v146 x =
  let a = xorV_v146 x (shiftLV_v146 13 x)
      b = xorV_v146 a (shiftRV_v146 7 a)
  in xorV_v146 b (shiftLV_v146 17 b)

qsaXorShiftDeterministic_v146 : ∀ n → XorShiftWord_v146 → Vec XorShiftWord_v146 n
qsaXorShiftDeterministic_v146 zero seed = []
qsaXorShiftDeterministic_v146 (suc n) seed =
  let s' = xorshift64_v146 seed
  in s' ∷ qsaXorShiftDeterministic_v146 n s'

qsaSeedRecurrence_v146 : ∀ n seed →
  qsaXorShiftDeterministic_v146 (suc n) seed ≡
  xorshift64_v146 seed ∷ qsaXorShiftDeterministic_v146 n (xorshift64_v146 seed)
qsaSeedRecurrence_v146 n seed = refl


------------------------------------------------------------------------
-- v146 finite diagonal-Newton coupling frontier.
-- The old v113/v114 artefacts contained an unproved Newton-radius surface.
-- Here the useful finite frontier is derived directly from the production
-- coupling normaliser E = 1 + 1/(gamma*lambda):
--   Q = q E,  Q/E = q,  radius = max(0, 1-q).
-- For 0 <= q <= 1 this gives the exact trade-off frontier.  No global
-- stochastic/real-analysis optimality theorem is asserted.
------------------------------------------------------------------------

diagonalNewtonExposure_v146 : ∀ {S} → CoupledHyperParameters_v146 S → Scalar S
diagonalNewtonExposure_v146 h =
  one + SmoothAlgebra.recip _ (traceProduct_v146 h)

diagonalNewtonExposurePositive_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  zero < diagonalNewtonExposure_v146 h
diagonalNewtonExposurePositive_v146 h =
  let OR = SmoothAlgebra.orderedRing S
      Rg = OrderedRing.ring OR
      htrace = OrderedRing.mulPos
        (CoupledHyperParameters_v146.gammaPositive h)
        (CoupledHyperParameters_v146.lambdaPositive h)
      hr = OrderedRing.addLtLeft
        (OrderedRing.zeroLtOne {orderedRing = OR})
        (SmoothAlgebra.recip S (traceProduct_v146 h))
      hr' : SmoothAlgebra.recip S (traceProduct_v146 h) <
            SmoothAlgebra.recip S (traceProduct_v146 h) + Ring.one Rg =
        transportLt_v142
          (Ring.addZeroR Rg (SmoothAlgebra.recip S (traceProduct_v146 h)))
          refl hr
      hrec = reciprocalNonnegative_v146 htrace
      hsum : zero <
        SmoothAlgebra.recip S (traceProduct_v146 h) + Ring.one Rg =
        OrderedRing.leLt hrec hr'
  in transportLt_v142
       (sym (Ring.addComm Rg
         (SmoothAlgebra.recip S (traceProduct_v146 h))
         (Ring.one Rg)))
       refl hsum

diagonalNewtonRelativeBudget_v146 : ∀ {S} → CoupledHyperParameters_v146 S → Scalar S
diagonalNewtonRelativeBudget_v146 h =
  projectionBudget_v146 h * SmoothAlgebra.recip _ (diagonalNewtonExposure_v146 h)

diagonalNewtonRelativeBudgetLaw_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  diagonalNewtonRelativeBudget_v146 h ≡ CoupledHyperParameters_v146.q h

diagonalNewtonRelativeBudgetLaw_v146 h =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
      e = diagonalNewtonExposure_v146 h
      he = diagonalNewtonExposurePositive_v146 h
      hb = projectionBudget_v146 h
      hdef : hb ≡ CoupledHyperParameters_v146.q h * e = refl
      hcancel : e * SmoothAlgebra.recip _ e ≡ one =
        SmoothAlgebra.reciprocalLaw _ he
      h1 : (CoupledHyperParameters_v146.q h * e) * SmoothAlgebra.recip _ e ≡
           CoupledHyperParameters_v146.q h * one =
        trans
          (Ring.mulAssoc Rg (CoupledHyperParameters_v146.q h) e
            (SmoothAlgebra.recip _ e))
          (cong (λ t → CoupledHyperParameters_v146.q h * t) hcancel)
  in trans
       hdef
       (trans h1 (Ring.mulOneR Rg (CoupledHyperParameters_v146.q h)))

diagonalNewtonRadius_v146 : ∀ {S} → CoupledHyperParameters_v146 S → Scalar S
diagonalNewtonRadius_v146 h =
  SmoothAlgebra.max _ zero
    (one + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _))
      (diagonalNewtonRelativeBudget_v146 h))

diagonalNewtonRadiusLaw_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  diagonalNewtonRadius_v146 h ≡
  SmoothAlgebra.max _ zero
    (one + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
      (CoupledHyperParameters_v146.q h))
diagonalNewtonRadiusLaw_v146 _ = refl

diagonalNewtonRadiusUnitLaw_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  CoupledHyperParameters_v146.q h ≤ one →
  diagonalNewtonRadius_v146 h ≡
    one + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
      (CoupledHyperParameters_v146.q h)
diagonalNewtonRadiusUnitLaw_v146 h hq =
  trans
    (diagonalNewtonRadiusLaw_v146 h)
    (SmoothAlgebra.maxPositive _ _
      (let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
           hneg = OrderedRing.negLe hq
           hsum = OrderedRing.addLe
             (OrderedRing.refl≤ {a = one}) hneg
         in trans (Ring.addZeroR Rg one) hsum))

paretoNewtonFrontier_v146 : ∀ {S} → CoupledHyperParameters_v146 S → Scalar S
paretoNewtonFrontier_v146 = diagonalNewtonRadius_v146

paretoNewtonFrontierLaw_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  CoupledHyperParameters_v146.q h ≤ one →
  paretoNewtonFrontier_v146 h ≡
    one + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
      (CoupledHyperParameters_v146.q h)
paretoNewtonFrontierLaw_v146 = diagonalNewtonRadiusUnitLaw_v146

paretoNewtonFrontierStrictTradeoff_v146 : ∀ {S}
  (h₁ h₂ : CoupledHyperParameters_v146 S) →
  CoupledHyperParameters_v146.q h₁ < CoupledHyperParameters_v146.q h₂ →
  CoupledHyperParameters_v146.q h₁ ≤ one →
  CoupledHyperParameters_v146.q h₂ ≤ one →
  paretoNewtonFrontier_v146 h₂ < paretoNewtonFrontier_v146 h₁
paretoNewtonFrontierStrictTradeoff_v146 h₁ h₂ hq hq₁ hq₂ =
  let OR = SmoothAlgebra.orderedRing _
      Rg = OrderedRing.ring OR
      hneg = OrderedRing.negLt hq
      hsub : one + Ring.neg Rg (CoupledHyperParameters_v146.q h₂) <
             one + Ring.neg Rg (CoupledHyperParameters_v146.q h₁) =
        OrderedRing.addLtLeft hneg one
      hleft = paretoNewtonFrontierLaw_v146 h₂ hq₂
      hright = paretoNewtonFrontierLaw_v146 h₁ hq₁
  in transportLt_v142 hleft hright hsub

diagonalNewtonParetoStep_v146 : ∀ {S}
  (h : CoupledHyperParameters_v146 S) →
  CoupledHyperParameters_v146.q h ≤ one →
  CoupledHyperParameters_v146.q h ≡ one →
  diagonalNewtonRadius_v146 h ≡ zero
diagonalNewtonParetoStep_v146 h hq hrefl =
  trans (diagonalNewtonRadiusUnitLaw_v146 h hq)
    (trans
      (cong (λ x → one + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _)) x) hrefl)
      (Ring.addNegR (OrderedRing.ring (SmoothAlgebra.orderedRing _)) one))


------------------------------------------------------------------------
-- Named coupled frontier/theorem surfaces.
------------------------------------------------------------------------

etaNotDecay_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  etaMetaStep_v146 h ≡ CoupledHyperParameters_v146.eta h
etaNotDecay_v146 _ = refl

------------------------------------------------------------------------
-- Ordered replay uses unit multiplicity: no importance-sampling correction
-- exists in this finite max-bootstrap semantics.
------------------------------------------------------------------------

replayStalenessNoIS_v146 : ∀ {S stateDim actionDim}
  (m : ReplayMode_v146)
  (live replayed : ReplayTransition_v141 S stateDim actionDim) → Scalar S
replayStalenessNoIS_v146 _ _ _ = one

replayStalenessNoISLaw_v146 : ∀ {S stateDim actionDim}
  (m : ReplayMode_v146)
  (live replayed : ReplayTransition_v141 S stateDim actionDim) →
  replayStalenessNoIS_v146 m live replayed ≡ one
replayStalenessNoISLaw_v146 _ _ _ = refl

------------------------------------------------------------------------
-- Finite CEM candidate argmax is exact over its candidate set.
------------------------------------------------------------------------

cemApproxArgmax_v146 : ∀ {S n} → QProjectionDecisionAlgebra_v140 S →
  VecS S (suc n) → Scalar S
cemApproxArgmax_v146 = maxVec_v146

cemHardMaxTargetLaw_v146 : ∀ {S n} (D : QProjectionDecisionAlgebra_v140 S)
  (L : CoupledLearner_v146 S n n)
  (values : VecS S (suc n)) →
  coupledHardMaxCandidate_v146 D
    (CoupledLearner_v146.hyper L) values ≡
  cemApproxArgmax_v146 D values
cemHardMaxTargetLaw_v146 D L values = refl

fitnessUsesNegativeTD_v146 : ∀ {S} → Scalar S → Scalar S
fitnessUsesNegativeTD_v146 = negativeTD_v146

returnIsDiagnostic_v146 : ∀ {S n} → VecS S n → Scalar S
returnIsDiagnostic_v146 = environmentReturn_v146

------------------------------------------------------------------------
-- Concrete finite-grid transition adapter used by the POBAX/NaviX source port.
------------------------------------------------------------------------

data Direction_v146 : Set where
  north_v146 east_v146 south_v146 west_v146 : Direction_v146

record GridPos_v146 : Set where
  field row_v146 col_v146 : Nat

translateGrid_v146 : Direction_v146 → GridPos_v146 → GridPos_v146
translateGrid_v146 north_v146 p = record { row_v146 = GridPos_v146.row_v146 p ; col_v146 = GridPos_v146.col_v146 p }
translateGrid_v146 east_v146 p = record { row_v146 = GridPos_v146.row_v146 p ; col_v146 = suc (GridPos_v146.col_v146 p) }
translateGrid_v146 south_v146 p = record { row_v146 = suc (GridPos_v146.row_v146 p) ; col_v146 = GridPos_v146.col_v146 p }
translateGrid_v146 west_v146 p = record { row_v146 = GridPos_v146.row_v146 p ; col_v146 = GridPos_v146.col_v146 p }

pobaxMiniGridStep_v146 :
  (Nat → Nat → Bool) → Direction_v146 → GridPos_v146 → GridPos_v146
pobaxMiniGridStep_v146 wall dir p =
  let q = translateGrid_v146 dir p in
  if wall (GridPos_v146.row_v146 q) (GridPos_v146.col_v146 q)
  then p
  else q

------------------------------------------------------------------------
-- A concrete one-coordinate learner update is provably non-inert whenever
-- its supplied update increment is non-zero.
------------------------------------------------------------------------

nonzeroAddUpdate_v146 : ∀ {S} (w u : Scalar S) → u ≠ zero → w + u ≠ w
nonzeroAddUpdate_v146 w u hu heq =
  hu (trans
    (trans
      (cong (λ t → t + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _)) w) heq)
      (trans
        (Ring.addAssoc (OrderedRing.ring (SmoothAlgebra.orderedRing _)) w u
          (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _)) w))
        (trans
          (cong (λ t → w + t) (Ring.addNegR (OrderedRing.ring (SmoothAlgebra.orderedRing _)) w))
          (Ring.addZeroR (OrderedRing.ring (SmoothAlgebra.orderedRing _)) w)))
      (Ring.addNegR (OrderedRing.ring (SmoothAlgebra.orderedRing _)) w)))

learnerNonInertness_v146 : ∀ {S} (w delta : Scalar S) →
  delta ≠ zero → w + delta ≠ w
learnerNonInertness_v146 = nonzeroAddUpdate_v146

efficientCHADLSTMChain_v146 : ∀ {S input hidden m n}
  (block : LSTMBlock S input hidden)
  (state : LSTMState S hidden)
  (xs : Vec (VecS S input) m)
  (ys : Vec (VecS S input) n) →
  lstmRun_v146 block state (appendV_v146 xs ys) ≡
  lstmRun_v146 block (lstmRun_v146 block state xs) ys
efficientCHADLSTMChain_v146 = lstmRunAppend_v146

oracleCrossCheckSurface_v146 : Nat
oracleCrossCheckSurface_v146 = suc (suc (suc zero))

------------------------------------------------------------------------
-- Genuine temporal staleness algebra.  Age is a timestamp difference,
-- rather than the prior proxy "length of the replayed vector".
------------------------------------------------------------------------

data NatLe : Nat → Nat → Set where
  natLeZero : ∀ {n} → NatLe zero n
  natLeSuc : ∀ {m n} → NatLe m n → NatLe (suc m) (suc n)

natSub_v146 : Nat → Nat → Nat
natSub_v146 zero _ = zero
natSub_v146 (suc m) zero = suc m
natSub_v146 (suc m) (suc n) = natSub_v146 m n

natSubAddLeft_v146 : ∀ a b → natSub_v146 (a + b) a ≡ b
natSubAddLeft_v146 zero b = refl
natSubAddLeft_v146 (suc a) b = natSubAddLeft_v146 a b

replayAge_v146 : Nat → Nat → Nat
replayAge_v146 sampleTime currentTime = natSub_v146 currentTime sampleTime

replayAgeAdvance_v146 : ∀ sampleTime delay →
  replayAge_v146 sampleTime (sampleTime + delay) ≡ delay
replayAgeAdvance_v146 sampleTime delay = natSubAddLeft_v146 sampleTime delay

replayAgeBound_v146 : ∀ sampleTime delay k →
  NatLe delay k →
  NatLe (replayAge_v146 sampleTime (sampleTime + delay)) k
replayAgeBound_v146 sampleTime delay k h =
  natLeTransportLeft_v146
    (replayAgeAdvance_v146 sampleTime delay) h
  where
  natLeTransportLeft_v146 : ∀ {a b k} → a ≡ b → NatLe b k → NatLe a k
  natLeTransportLeft_v146 refl h = h

replayAgeComposition_v146 : ∀ sampleTime delay₁ delay₂ →
  replayAge_v146 sampleTime (sampleTime + (delay₁ + delay₂)) ≡
  delay₁ + delay₂
replayAgeComposition_v146 sampleTime delay₁ delay₂ =
  replayAgeAdvance_v146 sampleTime (delay₁ + delay₂)

------------------------------------------------------------------------
-- Finite argmax/CEM algebra. CEM is an approximation of the action argmax
-- because it searches a finite candidate set; when that set exhausts the
-- action set, this is the actual finite argmax. The refit is separate.
------------------------------------------------------------------------

max2_v146 : ∀ {S} → QProjectionDecisionAlgebra_v140 S → Scalar S → Scalar S → Scalar S
max2_v146 D a b with QProjectionDecisionAlgebra_v140.leDec D a b
... | yes _ = b
... | no _ = a

max2Right_v146 : ∀ {S} (D : QProjectionDecisionAlgebra_v140 S) (a b : Scalar S) →
  a ≤ b → max2_v146 D a b ≡ b
max2Right_v146 D a b h with QProjectionDecisionAlgebra_v140.leDec D a b
... | yes _ = refl
... | no hn = ⊥-elim (hn h)

maxVec_v146 : ∀ {S n} → QProjectionDecisionAlgebra_v140 S → VecS S (suc n) → Scalar S
maxVec_v146 D (x ∷ []) = x
maxVec_v146 D (x ∷ y ∷ xs) = max2_v146 D x (maxVec_v146 D (y ∷ xs))

cemFiniteArgmax_v146 : ∀ {S n} → QProjectionDecisionAlgebra_v140 S →
  VecS S (suc n) → Scalar S
cemFiniteArgmax_v146 = maxVec_v146

coupledHardMaxCandidate_v146 : ∀ {S n} →
  QProjectionDecisionAlgebra_v140 S →
  CoupledHyperParameters_v146 S →
  VecS S (suc n) → Scalar S
coupledHardMaxCandidate_v146 D h qValues = maxVec_v146 D qValues

cemHardMaxRefit_v146 : ∀ {S n} →
  CoupledHyperParameters_v146 S →
  VecS S n → VecS S n → VecS S n
cemHardMaxRefit_v146 = coupledCEMRefit_v146

------------------------------------------------------------------------
-- Hard-max h-step bootstrap composition.  The finite candidate argmax is
-- used at the bootstrap endpoint; CEM only supplies the finite candidate set.
------------------------------------------------------------------------

hStepFold_v146 : ∀ {S n} → Scalar S → VecS S n → Scalar S → Scalar S
hStepFold_v146 gamma [] boot = boot
hStepFold_v146 gamma (r ∷ rs) boot =
  r + gamma * hStepFold_v146 gamma rs boot

hStepHardBootstrap_v146 : ∀ {S stateDim actionDim n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (L : CoupledLearner_v146 S stateDim actionDim)
  (rewards : VecS S n)
  (qTerminal : VecS S (suc actionDim)) → Scalar S
hStepHardBootstrap_v146 D L rewards qTerminal =
  hStepFold_v146
    (CoupledHyperParameters_v146.gamma (CoupledLearner_v146.hyper L))
    rewards
    (coupledHardMaxCandidate_v146 D
      (CoupledLearner_v146.hyper L) qTerminal)

------------------------------------------------------------------------
-- Canonical QD fitness is negative TD distribution; environment return is a
-- separate observable.  The two are different algebraic channels.
------------------------------------------------------------------------

negativeTD_v146 : ∀ {S} → Scalar S → Scalar S
negativeTD_v146 d = Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
  (SmoothAlgebra.abs S d)

negativeTDNonpositive_v146 : ∀ {S} (d : Scalar S) →
  zero ≤ SmoothAlgebra.abs S d →
  negativeTD_v146 d ≤ zero
negativeTDNonpositive_v146 d h =
  let OR = SmoothAlgebra.orderedRing _
      Rg = OrderedRing.ring OR
  in OrderedRing.negLe h

environmentReturn_v146 : ∀ {S n} → VecS S n → Scalar S
environmentReturn_v146 = vSum

fitnessChannel_v146 : ∀ {S n} → VecS S n → Scalar S
fitnessChannel_v146 xs = negativeTD_v146 (vSum xs)

------------------------------------------------------------------------
-- Efficient-CHAD recurrent chain algebra.  This proves finite reverse
-- composition for any supplied local LSTM pullbacks; it does not fabricate
-- analytic derivative laws for abstract exp/log/tanh/sigmoid primitives.
------------------------------------------------------------------------

record LocalVJP_v146 (S : SmoothAlgebra) (A : Set) : Set where
  field
    forward : A → A
    backward : A → Scalar S → Scalar S

localVJPChain_v146 : ∀ {S A n} →
  Vec (LocalVJP_v146 S A) n →
  A → Scalar S → Scalar S
localVJPChain_v146 [] x c = c
localVJPChain_v146 (f ∷ fs) x c =
  LocalVJP_v146.backward f (LocalVJP_v146.forward f x)
    (localVJPChain_v146 fs (LocalVJP_v146.forward f x) c)

------------------------------------------------------------------------
-- Source benchmark surface: only finite semantic tasks are admitted to the
-- algebraic regression suite; non-finite stochastic/grid probes are absent.
------------------------------------------------------------------------

data PureAlgebraBenchmark_v146 : Set where
  GymnaxSimpleBanditPure_v146 : PureAlgebraBenchmark_v146
  GymnaxDiscountingChainPure_v146 : PureAlgebraBenchmark_v146
  GymnaxMemoryChainPure_v146 : PureAlgebraBenchmark_v146
  JumanjiGraphColoringPure_v146 : PureAlgebraBenchmark_v146
  POBAXDMLabMiniGridPure_v146 : PureAlgebraBenchmark_v146
  POBAXDMLabMiniGrid02Pure_v146 : PureAlgebraBenchmark_v146
  JumanjiGame2048Pure_v146 : PureAlgebraBenchmark_v146
  JaxMARLSimpleSpreadBarrier_v146 : PureAlgebraBenchmark_v146
  BraxInvertedPendulumContinuousAudit_v146 : PureAlgebraBenchmark_v146

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Algebraic closure catalogue: every entry is an actual proof term or a
-- concrete terminating recursion.
------------------------------------------------------------------------

record CompleteAlgebraicClosure_v146 (S : SmoothAlgebra) : Set₁ where
  field
    ringAddAssoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    ringAddComm : ∀ x y → x + y ≡ y + x
    ringMulAssoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    ringDistrib : ∀ x y z → x * (y + z) ≡ x * y + x * z
    vectorAddComm : ∀ {n} (x y : VecS S n) i → indexV (vAdd x y) i ≡ indexV (vAdd y x) i
    vectorScaleAdd : ∀ {n} a (x y : VecS S n) i →
      indexV (vScale a (vAdd x y)) i ≡ indexV (vAdd (vScale a x) (vScale a y)) i
    qStrictCross : ∀ {alpha mu x} → zero ≤ alpha →
      qResidual_v142 mu alpha (x * x) < zero →
      alpha * (x * x) < mu * ((x * x) * (x * x))
    coupledBudget : ∀ h → zero ≤ projectionBudget_v146 h
    effectiveDecay : ∀ h → zero ≤ l2Effective_v146 h
    descriptorAppend : ∀ {m n} (a : Vec (DescriptorSignals_v146 S) m)
      (b : Vec (DescriptorSignals_v146 S) n) (sc : DescriptorScale_v146 S) →
      descriptorSum_v146 (appendV_v146 a b) sc ≡
      vAdd (descriptorSum_v146 a sc) (descriptorSum_v146 b sc)
    replayTime : ∀ {stateDim actionDim n}
      (st : ReplayState_v141 S stateDim actionDim)
      (trs : Vec (ReplayTransition_v141 S stateDim actionDim) n) →
      ReplayState_v141.time (replayPrefix_v141 st trs) ≡
      ReplayState_v141.time st + n
    barrier : ∀ {lanes width} (b : RectangularBarrier_v146 S lanes width)
      (i j : Fin lanes) →
      RectangularBarrier_v146.laneInput b i ≡ RectangularBarrier_v146.laneInput b j
    openESCancellation : ∀ {n} z i → indexV (vAdd z (vNeg_v140 z)) i ≡ zero
    l2IdentityNull : ∀ h → CoupledHyperParameters_v146.l2ZeroDecision h ≡ yes refl →
      l2Effective_v146 h ≡ zero
    couplingTraceLaw : ∀ h →
      CoupledParetoCoordinates_v146.traceProduct (paretoCouplingMap_v146 h) ≡ traceProduct_v146 h
    couplingBudgetLaw : ∀ h →
      CoupledParetoCoordinates_v146.projectionBudget (paretoCouplingMap_v146 h) ≡ projectionBudget_v146 h
    couplingMetaLaw : ∀ h →
      CoupledParetoCoordinates_v146.metaStep (paretoCouplingMap_v146 h) ≡ etaMetaStep_v146 h
    couplingCEMLaw : ∀ h →
      CoupledParetoCoordinates_v146.cemRate (paretoCouplingMap_v146 h) ≡ CoupledHyperParameters_v146.cemRate h
    replayAgeBound : ∀ {stateDim actionDim n k}
      (st : ReplayState_v141 S stateDim actionDim)
      (trs : Vec (ReplayTransition_v141 S stateDim actionDim) n) →
      n ≤ k → replayAgeBound_v146 st trs ≤ k
    cemCoefficientLaw : ∀ rho →
      (one + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) rho) + rho ≡ one
    replaySelectLaw : ∀ {stateDim actionDim}
      (m : ReplayMode_v146)
      (live replayed : ReplayTransition_v141 S stateDim actionDim) →
      replayTransitionSelect_v146 m live replayed ≡ replayTransitionSelect_v146 m live replayed
    lstmAppendLaw : ∀ {input hidden m n}
      (block : LSTMBlock S input hidden)
      (state : LSTMState S hidden)
      (xs : Vec (VecS S input) m)
      (ys : Vec (VecS S input) n) →
      lstmRun_v146 block state (appendV_v146 xs ys) ≡
      lstmRun_v146 block (lstmRun_v146 block state xs) ys
    reciprocalExposurePositive : ∀ h → zero < diagonalNewtonExposure_v146 h
    relativeBudgetLaw : ∀ h → diagonalNewtonRelativeBudget_v146 h ≡ CoupledHyperParameters_v146.q h
    frontierLaw : ∀ h → CoupledHyperParameters_v146.q h ≤ one →
      paretoNewtonFrontier_v146 h ≡
      one + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
        (CoupledHyperParameters_v146.q h)
    frontierStrictTradeoff : ∀ h₁ h₂ →
      CoupledHyperParameters_v146.q h₁ < CoupledHyperParameters_v146.q h₂ →
      CoupledHyperParameters_v146.q h₁ ≤ one →
      CoupledHyperParameters_v146.q h₂ ≤ one →
      paretoNewtonFrontier_v146 h₂ < paretoNewtonFrontier_v146 h₁
    replayAgeComposition : ∀ sampleTime delay₁ delay₂ →
      replayAge_v146 sampleTime (sampleTime + (delay₁ + delay₂)) ≡ delay₁ + delay₂
    replayNoIS : ∀ {stateDim actionDim}
      (m : ReplayMode_v146)
      (live replayed : ReplayTransition_v141 S stateDim actionDim) →
      replayStalenessNoIS_v146 m live replayed ≡ one
    cemArgmaxLaw : ∀ {n} (D : QProjectionDecisionAlgebra_v140 S)
      (xs : VecS S (suc n)) → cemFiniteArgmax_v146 D xs ≡ maxVec_v146 D xs
    hStepRecursion : ∀ {n} gamma boot r (rs : VecS S n) →
      hStepFold_v146 gamma (r ∷ rs) boot ≡ r + gamma * hStepFold_v146 gamma rs boot
    learnerNonInert : ∀ {delta} → delta ≠ zero → zero + delta ≠ zero
    efficientCHADLSTM : ∀ {input hidden m n}
      (block : LSTMBlock S input hidden)
      (state : LSTMState S hidden)
      (xs : Vec (VecS S input) m)
      (ys : Vec (VecS S input) n) →
      lstmRun_v146 block state (appendV_v146 xs ys) ≡
      lstmRun_v146 block (lstmRun_v146 block state xs) ys
    negativeTDSign : ∀ {d} → zero ≤ SmoothAlgebra.abs S d → zero ≥ negativeTD_v146 d

completeAlgebraicClosure_v146 : ∀ {S} → CompleteAlgebraicClosure_v146 S
completeAlgebraicClosure_v146 {S} = record
  { ringAddAssoc = Ring.addAssoc (OrderedRing.ring (SmoothAlgebra.orderedRing S))
  ; ringAddComm = Ring.addComm (OrderedRing.ring (SmoothAlgebra.orderedRing S))
  ; ringMulAssoc = Ring.mulAssoc (OrderedRing.ring (SmoothAlgebra.orderedRing S))
  ; ringDistrib = Ring.distrib (OrderedRing.ring (SmoothAlgebra.orderedRing S))
  ; vectorAddComm = vAddComm_v140
  ; vectorScaleAdd = vScaleAdd_v140
  ; qStrictCross = qProjectionCross_v142
  ; coupledBudget = coupledBudgetNonnegative_v146
  ; effectiveDecay = l2EffectiveNonnegative_v146
  ; descriptorAppend = descriptorSumAppend_v146
  ; replayTime = replayTime_v141
  ; barrier = barrierSnapshot_v146
  ; openESCancellation = antitheticScalarCancel_v142
  ; l2IdentityNull = l2IdentityNull_v146
  ; couplingTraceLaw = paretoCouplingConsistent_v146
  ; couplingBudgetLaw = paretoCouplingBudgetLawDirect_v146
  ; couplingMetaLaw = paretoCouplingMetaLawDirect_v146
  ; couplingCEMLaw = paretoCouplingCEMRateLaw_v146
  ; replayAgeBound = replayAgeBoundTheorem_v146
  ; cemCoefficientLaw = cemRefitCoefficientLaw_v146
  ; reciprocalExposurePositive = diagonalNewtonExposurePositive_v146
  ; relativeBudgetLaw = diagonalNewtonRelativeBudgetLaw_v146
  ; frontierLaw = paretoNewtonFrontierLaw_v146
  ; frontierStrictTradeoff = paretoNewtonFrontierStrictTradeoff_v146
  ; replayAgeComposition = replayAgeComposition_v146
  ; replayNoIS = replayStalenessNoISLaw_v146
  ; cemArgmaxLaw = λ D xs → refl
  ; hStepRecursion = λ gamma boot r rs → refl
  ; learnerNonInert = λ {delta = delta} h → learnerNonInertness_v146 zero delta h
  ; efficientCHADLSTM = efficientCHADLSTMChain_v146
  ; negativeTDSign = λ {d = d} h → negativeTDNonpositive_v146 d h
  }

------------------------------------------------------------------------
-- v145 semantic policy: CVT-ME is the geometric QD reference; grid-ME is the
-- lower-layer assignment ablation. Both use exactly the same ME-OpenES emitter,
-- descriptors and coupled learner. QSA/XorShift is finite deterministic input,
-- while general PRNGs remain opaque discrete sources rather than algebraic laws.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- v147 audited KKT boundary.
--
-- No KKT certificate datatype, no Set-valued KKT premise, and no fabricated
-- proof term are introduced here.  The exact deletion-induction theorem is
-- documented separately with every algebraic induction obligation expanded.
-- It requires only: ordered-ring totality, alpha >= 0, budget >= 0, and the
-- executable qRun definition already present above.
--
-- The theorem to be exported after kernel checking is:
--
-- qProjectionFixedPoint_v147 : ∀ {S n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (budget : Scalar S)
  (p x : VecS S n) →
  (∀ i → zero ≤ indexV p i) →
  weightedExposure_v147 p x ≤ budget →
  QRun_v142.projection (qRun_v142 D budget p x) ≡ p
qProjectionFixedPoint_v147 = qProjectionRetraction_v147

qRunTerminalKKT_v147 :
--   (D : QProjectionDecisionAlgebra_v140 S) ->
--   TotalOrder_v147 S ->
--   (budget : Scalar S) -> (alpha x : VecS S n) ->
--   (forall i -> zero <= indexV alpha i) -> zero <= budget ->
--   terminal KKT consequences of qRun_v142 D budget alpha x.
--
-- The proof is deletion induction on qRunFuel_v142, with the exact chain:
-- negative active residual -> strict cross yd < nz -> strict quotient increase
-- -> multiplier monotonicity -> deleted-residual transport -> terminal active
-- nonnegativity -> primal/dual KKT stationarity and complementarity.
--
-- The source deliberately does not contain a theorem-valued placeholder for
-- that chain.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- v147 constructive q-closure.
-- The projection is a finite retraction on the q-feasible region.  The
-- terminal multiplier is unique whenever its positive fourth-power
-- denominator is positive; terminal projections are consequently unique
-- independently of the deletion-mask representation at zero residuals.
------------------------------------------------------------------------

transportLe_v147 : ∀ {S} {a b : Scalar S} →
  a ≡ b → zero ≤ a → zero ≤ b
transportLe_v147 refl h = h

vectorExt_v147 : ∀ {S n} {x y : VecS S n} →
  (∀ i → indexV x i ≡ indexV y i) → x ≡ y
vectorExt_v147 {x = []} {y = []} p = refl
vectorExt_v147 {x = x ∷ xs} {y = y ∷ ys} p =
  cong₂ _∷_ (p fzero) (vectorExt_v147 (λ i → p (fsuc i)))

qResidualZero_v147 : ∀ {S} (a w : Scalar S) →
  qResidual_v142 zero a w ≡ a
qResidualZero_v147 a w =
  trans
    (cong
      (λ t → a + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _)) t)
      (Ring.zeroMulL (OrderedRing.ring (SmoothAlgebra.orderedRing _)) w))
    (Ring.addZeroR (OrderedRing.ring (SmoothAlgebra.orderedRing _)) a)

qCandidateNonnegative_v147 : ∀ {S n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (mu : Scalar S)
  (mask : Vec Bool n)
  (alpha x : VecS S n) (i : Fin n) →
  zero ≤ indexV (qCandidate_v142 D mu mask alpha x) i
qCandidateNonnegative_v147 D mu mask alpha x i =
  SmoothAlgebra.maxNonnegative _ _

qRunProjectionFormFuel_v147 : ∀ {S n}
  (fuel : Nat)
  (r : QRun_v142 S n) →
  QRun_v142.projection (qRunFuel_v142 fuel r) ≡
  qCandidate_v142
    (QRun_v142.decision (qRunFuel_v142 fuel r))
    (QRun_v142.multiplier (qRunFuel_v142 fuel r))
    (QRun_v142.mask (qRunFuel_v142 fuel r))
    (QRun_v142.alpha (qRunFuel_v142 fuel r))
    (QRun_v142.x (qRunFuel_v142 fuel r))
qRunProjectionFormFuel_v147 zero r = refl
qRunProjectionFormFuel_v147 (suc fuel) r with qFirstNegative_v142
  (QRun_v142.decision r) (QRun_v142.mask r)
  (QRun_v142.alpha r) (QRun_v142.x r) (QRun_v142.multiplier r)
... | nothing = qRunProjectionFormFuel_v147 zero r
... | justD i = qRunProjectionFormFuel_v147 fuel (qRunStep_v142 r)

qRunProjectionForm_v147 : ∀ {S n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (budget : Scalar S)
  (alpha x : VecS S n) →
  let r = qRun_v142 D budget alpha x in
  QRun_v142.projection r ≡
  qCandidate_v142 D (QRun_v142.multiplier r)
    (QRun_v142.mask r) alpha x
qRunProjectionForm_v147 D budget alpha x =
  qRunProjectionFormFuel_v147 _ (initialQRun_v142 D budget alpha x)

qRunProjectionNonnegative_v147 : ∀ {S n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (budget : Scalar S)
  (alpha x : VecS S n) (i : Fin n) →
  zero ≤ indexV (QRun_v142.projection (qRun_v142 D budget alpha x)) i
qRunProjectionNonnegative_v147 D budget alpha x i =
  subst
    (λ p → zero ≤ indexV p i)
    (qRunProjectionForm_v147 D budget alpha x)
    (qCandidateNonnegative_v147 D _ _ _ _ i)

qMuZeroFromNumLe_v147 : ∀ {S n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (budget : Scalar S)
  (mask : Vec Bool n) (alpha x : VecS S n) →
  qNum_v142 budget mask alpha x ≤ zero →
  qMu_v142 D budget mask alpha x ≡ zero
qMuZeroFromNumLe_v147 D budget mask alpha x h with
  QProjectionDecisionAlgebra_v140.ltDec D zero (qNum_v142 budget mask alpha x)
... | yes hlt = ⊥-elim (OrderedRing.notLtFromLe h hlt)
... | no _ = refl

allActive_v147 : ∀ {n} → Vec Bool n
allActive_v147 {zero} = []
allActive_v147 {suc n} = true ∷ allActive_v147

qCandidateZero_v147 : ∀ {S n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (p x : VecS S n) →
  (∀ i → zero ≤ indexV p i) →
  qCandidate_v142 D zero (allActive_v147 {n = n}) p x ≡ p
qCandidateZero_v147 D [] [] hp = refl
qCandidateZero_v147 D (p ∷ ps) (x ∷ xs) hp =
  trans
    (cong₂ _∷_
      (QProjectionDecisionAlgebra_v140.maxPositive D
        (qResidual_v142 zero p (x * x))
        (transportLe_v147
          (sym (qResidualZero_v147 p (x * x)))
          (hp fzero)))
      (qCandidateZero_v147 D ps xs (λ i → hp (fsuc i))))
    (cong₂ _∷_
      (sym (qResidualZero_v147 p (x * x)))
      refl)

qFirstNegativeNoneNonnegative_v147 : ∀ {S n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (mask : Vec Bool n) (alpha x : VecS S n) (mu : Scalar S) →
  (∀ i → indexV mask i ≡ true →
    zero ≤ qResidual_v142 mu (indexV alpha i)
      (indexV x i * indexV x i)) →
  qFirstNegative_v142 D mask alpha x mu ≡ nothing
qFirstNegativeNoneNonnegative_v147 D [] [] [] mu h = refl
qFirstNegativeNoneNonnegative_v147 D (b ∷ bs) (a ∷ as) (x ∷ xs) mu h
  with b
... | false = qFirstNegativeNoneNonnegative_v147 D bs as xs mu
    (λ i hi → h (fsuc i) hi)
... | true with QProjectionDecisionAlgebra_v140.ltDec D zero
    (qResidual_v142 mu a (x * x))
...   | yes hz = ⊥-elim (OrderedRing.notLtFromLe
      (h fzero refl) hz)
...   | no _ = qFirstNegativeNoneNonnegative_v147 D bs as xs mu
    (λ i hi → h (fsuc i) hi)

justDNotNothing_v147 : ∀ {A : Set} {x : A} → justD x ≡ nothing → ⊥
justDNotNothing_v147 ()

qRunStopsWhenNoNegative_v147 : ∀ {S n}
  (fuel : Nat) (r : QRun_v142 S n) →
  qFirstNegative_v142 (QRun_v142.decision r) (QRun_v142.mask r)
    (QRun_v142.alpha r) (QRun_v142.x r) (QRun_v142.multiplier r) ≡ nothing →
  QRun_v142.projection (qRunFuel_v142 fuel r) ≡ QRun_v142.projection r
qRunStopsWhenNoNegative_v147 zero r h = refl
qRunStopsWhenNoNegative_v147 (suc fuel) r h with qFirstNegative_v142
  (QRun_v142.decision r) (QRun_v142.mask r)
  (QRun_v142.alpha r) (QRun_v142.x r) (QRun_v142.multiplier r)
... | nothing = refl
... | justD i = ⊥-elim (justDNotNothing_v147 h)

weightedExposure_v147 : ∀ {S n} → VecS S n → VecS S n → Scalar S
weightedExposure_v147 alpha x =
  maskSum_v142 (allActive_v147 {n = _})
    (λ i → indexV alpha i * (indexV x i * indexV x i))

weightedExposureBound_v147 : ∀ {S n}
  (budget : Scalar S) (p x : VecS S n) →
  weightedExposure_v147 p x ≤ budget →
  qNum_v142 budget (allActive_v147 {n = n}) p x ≤ zero
weightedExposureBound_v147 budget p x h =
  trans
    (OrderedRing.addLe h (OrderedRing.refl≤
      (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _)) budget)))
    (Ring.addNegR (OrderedRing.ring (SmoothAlgebra.orderedRing _)) budget)

qProjectionRetraction_v147 : ∀ {S n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (budget : Scalar S)
  (p x : VecS S n) →
  (∀ i → zero ≤ indexV p i) →
  weightedExposure_v147 p x ≤ budget →
  QRun_v142.projection (qRun_v142 D budget p x) ≡ p
qProjectionRetraction_v147 D budget p x hp hb =
  let numLe = weightedExposureBound_v147 budget p x hb
      muZero = qMuZeroFromNumLe_v147 D budget
        (allActive_v147 {n = _}) p x numLe
      noNeg = qFirstNegativeNoneNonnegative_v147 D
        (allActive_v147 {n = _}) p x zero
        (λ i _ →
          transportLe_v147 (sym (qResidualZero_v147
            (indexV p i)
            (indexV x i * indexV x i))) (hp i))
      stopped = qRunStopsWhenNoNegative_v147 _
        (initialQRun_v142 D budget p x) noNeg
      initialForm : QRun_v142.projection
          (initialQRun_v142 D budget p x) ≡ p =
        trans
          refl
          (trans
            (cong (λ mu → qCandidate_v142 D mu
              (allActive_v147 {n = _}) p x) muZero)
            (qCandidateZero_v147 D p x hp))
  in trans stopped initialForm

qRunTerminalKKT_v147 : ∀ {S n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (budget : Scalar S)
  (alpha x : VecS S n) →
  (∀ i →
    indexV (QRun_v142.mask (qRun_v142 D budget alpha x)) i ≡ true →
    zero ≤ qResidual_v142
      (QRun_v142.multiplier (qRun_v142 D budget alpha x))
      (indexV alpha i)
      (indexV x i * indexV x i)) →
  (∀ i →
    indexV (QRun_v142.mask (qRun_v142 D budget alpha x)) i ≡ false →
    qResidual_v142
      (QRun_v142.multiplier (qRun_v142 D budget alpha x))
      (indexV alpha i)
      (indexV x i * indexV x i) ≤ zero) →
  ∀ i →
    indexV (QRun_v142.projection (qRun_v142 D budget alpha x)) i ≡
    SmoothAlgebra.max S zero
      (qResidual_v142
        (QRun_v142.multiplier (qRun_v142 D budget alpha x))
        (indexV alpha i)
        (indexV x i * indexV x i))
qRunTerminalKKT_v147 D budget alpha x activeSign inactiveSign =
  trans
    (qRunProjectionForm_v147 D budget alpha x)
    (qProjectionKKTTheorem_v146 D
      (QRun_v142.multiplier (qRun_v142 D budget alpha x))
      alpha x (QRun_v142.mask (qRun_v142 D budget alpha x))
      activeSign inactiveSign)

------------------------------------------------------------------------
-- Positive-denominator uniqueness of the terminal multiplier.
------------------------------------------------------------------------

cancelPositiveRight_v147 : ∀ {S} (a b d : Scalar S) →
  zero < d → a * d ≡ b * d → a ≡ b
cancelPositiveRight_v147 a b d hd h =
  trans
    (sym (Ring.mulOneR (OrderedRing.ring (SmoothAlgebra.orderedRing _)) a))
    (trans
      (cong (λ t → a * t) (sym (SmoothAlgebra.reciprocalLaw _ hd)))
      (trans
        (sym (Ring.mulAssoc (OrderedRing.ring (SmoothAlgebra.orderedRing _))
          a d (SmoothAlgebra.recip _ d)))
        (trans
          (cong (λ t → t * SmoothAlgebra.recip _ d) h)
          (trans
            (Ring.mulAssoc (OrderedRing.ring (SmoothAlgebra.orderedRing _))
              b d (SmoothAlgebra.recip _ d))
            (trans
              (cong (λ t → b * t)
                (SmoothAlgebra.reciprocalLaw _ hd))
              (Ring.mulOneR (OrderedRing.ring (SmoothAlgebra.orderedRing _)) b))))))

record QTerminalSolution_v147 (S : SmoothAlgebra) (n : Nat) : Set where
  field
    decision : QProjectionDecisionAlgebra_v140 S
    budget : Scalar S
    alpha x projection : VecS S n
    mask : Vec Bool n
    multiplier : Scalar S
    denominator numerator : Scalar S
    denominatorPositive : zero < denominator
    multiplierBalance : multiplier * denominator ≡ numerator
    stationarity : ∀ i →
      indexV projection i ≡
      SmoothAlgebra.max S zero
        (qResidual_v142 multiplier (indexV alpha i)
          (indexV x i * indexV x i))

qTerminalMultiplierUnique_v147 : ∀ {S n}
  (a b d n1 n2 : Scalar S) →
  zero < d →
  a * d ≡ n1 →
  b * d ≡ n2 →
  n1 ≡ n2 →
  a ≡ b
qTerminalMultiplierUnique_v147 a b d n1 n2 hd ha hb hn =
  cancelPositiveRight_v147 a b d
    (trans ha (trans hn (sym hb)))

qTerminalProjectionUnique_v147 : ∀ {S n}
  (t u : QTerminalSolution_v147 S n) →
  QTerminalSolution_v147.alpha t ≡ QTerminalSolution_v147.alpha u →
  QTerminalSolution_v147.x t ≡ QTerminalSolution_v147.x u →
  QTerminalSolution_v147.multiplier t ≡ QTerminalSolution_v147.multiplier u →
  QTerminalSolution_v147.projection t ≡ QTerminalSolution_v147.projection u
qTerminalProjectionUnique_v147 t u ha hx hmu =
  vectorExt_v147 (λ i →
    trans
      (QTerminalSolution_v147.stationarity t i)
      (trans
        (cong (λ a → SmoothAlgebra.max _ zero
          (qResidual_v142 (QTerminalSolution_v147.multiplier t) a
            (indexV (QTerminalSolution_v147.x t) i *
             (indexV (QTerminalSolution_v147.x t) i))))
          (cong (λ v → indexV v i) ha))
        (trans
          (cong (λ m → SmoothAlgebra.max _ zero
            (qResidual_v142 m (indexV (QTerminalSolution_v147.alpha u) i)
              (indexV (QTerminalSolution_v147.x u) i *
               (indexV (QTerminalSolution_v147.x u) i))) hmu)
          (trans
            (cong (λ v → SmoothAlgebra.max _ zero
              (qResidual_v142 (QTerminalSolution_v147.multiplier u)
                (indexV (QTerminalSolution_v147.alpha u) i)
                (indexV v i * indexV v i))) hx)
            (sym (QTerminalSolution_v147.stationarity u i))))))

qTerminalConfluence_v147 : ∀ {S n}
  (t u : QTerminalSolution_v147 S n) →
  QTerminalSolution_v147.alpha t ≡ QTerminalSolution_v147.alpha u →
  QTerminalSolution_v147.x t ≡ QTerminalSolution_v147.x u →
  QTerminalSolution_v147.multiplier t ≡ QTerminalSolution_v147.multiplier u →
  QTerminalSolution_v147.projection t ≡ QTerminalSolution_v147.projection u
qTerminalConfluence_v147 = qTerminalProjectionUnique_v147

------------------------------------------------------------------------
-- Efficient CHAD + LSTM TBPTT: finite chunking of the reverse state-passing
-- chain follows exactly the same append decomposition as the forward LSTM.
-- No analytic derivative identities for abstract gate primitives are added.
------------------------------------------------------------------------

localVJPForward_v147 : ∀ {S A n} →
  Vec (LocalVJP_v146 S A) n → A → A
localVJPForward_v147 [] x = x
localVJPForward_v147 (f ∷ fs) x =
  localVJPForward_v147 fs (LocalVJP_v146.forward f x)

localVJPChainAppend_v147 : ∀ {S A m n}
  (fs : Vec (LocalVJP_v146 S A) m)
  (gs : Vec (LocalVJP_v146 S A) n)
  (x : A) (c : Scalar S) →
  localVJPChain_v146 (appendV_v146 fs gs) x c ≡
  localVJPChain_v146 fs x
    (localVJPChain_v146 gs
      (localVJPForward_v147 fs x) c)
localVJPChainAppend_v147 [] gs x c = refl
localVJPChainAppend_v147 (f ∷ fs) gs x c =
  localVJPChainAppend_v147 fs gs
    (LocalVJP_v146.forward f x) c

lstmForwardAppend_v147 : ∀ {S input hidden m n}
  (block : LSTMBlock S input hidden)
  (state : LSTMState S hidden)
  (xs : Vec (VecS S input) m)
  (ys : Vec (VecS S input) n) →
  lstmRun_v146 block state (appendV_v146 xs ys) ≡
  lstmRun_v146 block (lstmRun_v146 block state xs) ys
lstmForwardAppend_v147 = lstmRunAppend_v146

record EfficientCHADLSTMTBPTT_v147 (S : SmoothAlgebra)
  (input hidden : Nat) (A : Set) (m n : Nat) : Set₁ where
  field
    block : LSTMBlock S input hidden
    initialState : LSTMState S hidden
    xs : Vec (VecS S input) m
    ys : Vec (VecS S input) n
    localPrefix : Vec (LocalVJP_v146 S A) m
    localTail : Vec (LocalVJP_v146 S A) n
    forwardChunks :
      lstmRun_v146 block initialState
        (appendV_v146 xs ys) ≡
      lstmRun_v146 block
        (lstmRun_v146 block initialState xs) ys
    reverseChunks : ∀ (z : A) {c : Scalar S} →
      localVJPChain_v146
        (appendV_v146 localPrefix localTail) z c ≡
      localVJPChain_v146 localPrefix z
        (localVJPChain_v146 localTail
          (localVJPForward_v147 localPrefix z) c)

efficientCHADLSTMTBPTTFromPieces_v147 : ∀ {S input hidden A m n}
  (block : LSTMBlock S input hidden)
  (state : LSTMState S hidden)
  (xs : Vec (VecS S input) m)
  (ys : Vec (VecS S input) n)
  (localPrefix : Vec (LocalVJP_v146 S A) m)
  (localTail : Vec (LocalVJP_v146 S A) n) →
  EfficientCHADLSTMTBPTT_v147 S input hidden A m n
efficientCHADLSTMTBPTTFromPieces_v147 block state xs ys localPrefix localTail = record
  { block = block
  ; initialState = state
  ; xs = xs
  ; ys = ys
  ; localPrefix = localPrefix
  ; localTail = localTail
  ; forwardChunks = lstmForwardAppend_v147 block state xs ys
  ; reverseChunks = localVJPChainAppend_v147 localPrefix localTail
  }

------------------------------------------------------------------------
-- The q component of the coupled learner has a single-step invariant: its
-- emitted projection is nonnegative.  This is the exact q transition used by
-- coupledIDBDUpdate_v146; no duplicate q semantics are introduced.
------------------------------------------------------------------------

record CoupledQOneStepInvariant_v147 (S : SmoothAlgebra) (n : Nat) : Set₁ where
  field
    decision : QProjectionDecisionAlgebra_v140 S
    budget : Scalar S
    alphaRaw x : VecS S n
    result : QRun_v142 S n
    resultEquation : result ≡ qRun_v142 decision budget alphaRaw x
    projectionNonnegative : ∀ i →
      zero ≤ indexV (QRun_v142.projection result) i

coupledQOneStepInvariant_v147 : ∀ {S n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (budget : Scalar S)
  (alphaRaw x : VecS S n) →
  CoupledQOneStepInvariant_v147 S n
coupledQOneStepInvariant_v147 D budget alphaRaw x = record
  { decision = D
  ; budget = budget
  ; alphaRaw = alphaRaw
  ; x = x
  ; result = qRun_v142 D budget alphaRaw x
  ; resultEquation = refl
  ; projectionNonnegative = qRunProjectionNonnegative_v147 D budget alphaRaw x
  }

