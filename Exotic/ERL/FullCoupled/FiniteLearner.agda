{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.FiniteLearner where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Fin as F
open F using (Fin; toℕ)
open import Data.Nat using (ℕ; _+_; _*_; _∸_)
open import Data.Nat.DivMod using (_/_)
open import Data.Nat.Properties using (_≤?_; yes; no)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8OfNat
  ; int8Add
  ; int8Mul
  ; zero8
  ; one8
  ; max8
  )

data Cmp : Set where
  less equal greater : Cmp

compareNat : ℕ → ℕ → Cmp
compareNat zero zero = equal
compareNat zero (suc n) = less
compareNat (suc m) zero = greater
compareNat (suc m) (suc n) = compareNat m n

minusNat : ℕ → ℕ → ℕ
minusNat zero n = zero
minusNat m zero = m
minusNat (suc m) (suc n) = minusNat m n

parity : ℕ → Bool
parity zero = false
parity (suc zero) = true
parity (suc (suc n)) = parity n

walshSign : Bool → Int8
walshSign false = one8
walshSign true = max8

walshRadamacher1 : Int8 → Int8
walshRadamacher1 x = walshSign (parity (toℕ (code x)))

negate8 : Int8 → Int8
negate8 x = int8OfNat (256 ∸ toℕ (code x))

rope2 : Int8 × Int8 → Int8 × Int8
rope2 (x , y) = y , negate8 x

record SparseWeight : Set where
  constructor sparseWeight
  field code5 : Fin 5

open SparseWeight public

q0 q1 q2 q3 q4 : SparseWeight
q0 = sparseWeight F.zero
q1 = sparseWeight (F.suc F.zero)
q2 = sparseWeight (F.suc (F.suc F.zero))
q3 = sparseWeight (F.suc (F.suc (F.suc F.zero)))
q4 = sparseWeight (F.suc (F.suc (F.suc (F.suc F.zero))))

weightNat : SparseWeight → ℕ
weightNat q0 = zero
weightNat q1 = suc zero
weightNat q2 = suc (suc zero)
weightNat q3 = suc (suc (suc zero))
weightNat q4 = suc (suc (suc (suc zero)))

mirror : SparseWeight → SparseWeight
mirror q0 = q4
mirror q1 = q3
mirror q2 = q2
mirror q3 = q1
mirror q4 = q0

sparsemax2Weight : ℕ → ℕ → SparseWeight
sparsemax2Weight a b with compareNat a b
... | equal = q2
... | greater with minusNat a b
...   | zero = q2
...   | suc zero = q3
...   | suc (suc n) = q4
... | less with minusNat b a
...   | zero = q2
...   | suc zero = q1
...   | suc (suc n) = q0

sparsemax2Complement : ∀ a b →
  weightNat (sparsemax2Weight a b) +
  weightNat (mirror (sparsemax2Weight a b)) ≡ 4
sparsemax2Complement a b with sparsemax2Weight a b
... | q0 = refl
... | q1 = refl
... | q2 = refl
... | q3 = refl
... | q4 = refl

sparsemax2 : Int8 → Int8 → Int8 × Int8
sparsemax2 a b =
  let p = sparsemax2Weight (toℕ (code a)) (toℕ (code b))
      q = mirror p
      pa = weightNat p
      pb = weightNat q
      va = toℕ (code a)
      vb = toℕ (code b)
  in int8OfNat ((pa * va + pb * vb) / 4) , int8OfNat ((pb * va + pa * vb) / 4)

scaledMagnitude : Int8 → ℕ
scaledMagnitude x with toℕ (code x) ≤? 127
... | yes _ = toℕ (code x)
... | no _ = 256 ∸ toℕ (code x)

negEncode8 : ℕ → Int8
negEncode8 n = int8OfNat (256 ∸ n)

signReLU8 : Int8 → Int8
signReLU8 x with toℕ (code x) ≤? 127
... | yes _ = x
... | no _ = negEncode8 ((128 * scaledMagnitude x) / suc (scaledMagnitude x))

softsign8 : Int8 → Int8
softsign8 x with toℕ (code x) ≤? 127
... | yes _ = int8OfNat ((128 * toℕ (code x)) / suc (toℕ (code x)))
... | no _ = negEncode8 ((128 * scaledMagnitude x) / suc (scaledMagnitude x))

fixedHaar2 : Int8 × Int8 → Int8 × Int8
fixedHaar2 (x , y) = int8Add x y , int8Add x (negate8 y)

fixedFastfood2 : Int8 × Int8 → Int8 × Int8
fixedFastfood2 (x , y) with fixedHaar2 (x , y)
... | a , b with fixedHaar2 (a , b)
...   | c , d = d , c

qε : ℕ → Int8 → Int8
qε tau x with scaledMagnitude x ≤? tau
... | yes _ = zero8
... | no _ = x

record Token : Set where
  constructor token
  field
    observation previousAction reward nextObservation : Int8

open Token public

record Window2 : Set where
  constructor window2
  field
    previous current : Token

open Window2 public

tokenCode : Token → Int8
tokenCode t = int8Add
  (int8Add (observation t) (previousAction t))
  (int8Add (reward t) (nextObservation t))

record Parameters : Set where
  constructor parameters
  field
    w1 w2 w3 w4 w5 outputProjection : Int8

open Parameters public

record LearnerState : Set where
  constructor learnerState
  field
    parameters : Parameters
    critic trace : Int8

open LearnerState public

attentionStep : Token → Token → Int8
attentionStep a b =
  let xa = walshRadamacher1 (tokenCode a)
      xb = walshRadamacher1 (tokenCode b)
      (ra , rb) = rope2 (xa , xb)
      (ya , yb) = sparsemax2 ra rb
  in int8Add ya yb

ffn1 : Parameters → Int8 → Int8
ffn1 p x = int8Mul (w2 p) (signReLU8 (int8Mul (w1 p) x))

ffn2 : Parameters → Int8 → Int8
ffn2 p x = int8Mul (w4 p) (signReLU8 (int8Mul (w3 p) x))

learnForward : Parameters → Window2 → Int8
learnForward p w =
  let h = attentionStep (previous w) (current w)
      a = ffn1 p h
      (u , v) = fixedFastfood2 (a , h)
      b = int8Add (ffn2 p u) v
      g = softsign8 (int8Mul (w5 p) b)
      z = qε 3 g
  in int8Mul (outputProjection p) z

learnStep : LearnerState → Window2 → LearnerState
learnStep s w = learnerState
  (parameters s)
  (learnForward (parameters s) w)
  (trace s)
