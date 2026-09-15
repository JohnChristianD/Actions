{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ConnectedGRUSemidirectQSA where

open import Agda.Builtin.Equality using (_≡_; refl; subst; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (_<_; _≤_; z≤n; s≤s)
open import Exotic.efficient_chad.Int8 using (Int8; zero8)
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; gruState
  ; hidden
  ; GRUMatrices
  ; GRUNoise
  ; GlobalControl
  ; gruStep
  ; gruMatrices
  ; gruNoise
  ; globalControl
  ; optimizerToken
  ; l2Token
  ; signReLU8
  ; apply
  )
open import Exotic.ERL.FullCoupled.FiniteSemidirectComposition using
  ( Monoid
  ; monoid
  ; Action
  ; action
  ; Semidirect
  ; semidirect
  ; semidirectMul
  )
open import Exotic.ERL.FullCoupled.SignReLUSemidirectCycleComposition using
  ( SemidirectCycleEmbedding
  ; semidirectCycleEmbedding
  )
open import Exotic.ERL.FullCoupled.Int8StabilityComposition using
  ( LyapunovCertificate
  ; iterate
  ; noNontrivialFiniteCycle
  ; OrbitNonFixed
  )
open import Exotic.ERL.FullCoupled.DeterministicQSA using
  ( ConvergesTo
  ; DeterministicQSAStyleCertificate
  ; deterministicQSAStyleConvergence
  ; deterministicQSAStyleNoNontrivialCycle
  )

record HiddenEndo : Set where
  constructor hiddenEndo
  field runHidden : Int8 → Int8
open HiddenEndo public

hiddenId : HiddenEndo
hiddenId = hiddenEndo (λ x → x)

hiddenMul : HiddenEndo → HiddenEndo → HiddenEndo
hiddenMul f g = hiddenEndo (λ x → runHidden g (runHidden f x))

hidden-assoc : ∀ f g h → hiddenMul (hiddenMul f g) h ≡ hiddenMul f (hiddenMul g h)
hidden-assoc (hiddenEndo f) (hiddenEndo g) (hiddenEndo h) = refl

hidden-left-id : ∀ f → hiddenMul hiddenId f ≡ f
hidden-left-id (hiddenEndo f) = refl

hidden-right-id : ∀ f → hiddenMul f hiddenId ≡ f
hidden-right-id (hiddenEndo f) = refl

hiddenMonoid : Monoid HiddenEndo
hiddenMonoid = monoid hiddenId hiddenMul hidden-assoc hidden-left-id hidden-right-id

PersistentGRU : Set
PersistentGRU = GRUMatrices × (GRUNoise × GlobalControl)

persistentGRU : GRUState → PersistentGRU
persistentGRU (gruState h m n g) = m , (n , g)

persistentState : PersistentGRU → Int8 → GRUState
persistentState (m , (n , g)) h = gruState h m n g

persistent-preservation :
  ∀ (s : GRUState) (x : Int8) → persistentGRU (gruStep s x) ≡ persistentGRU s
persistent-preservation (gruState h m n g) x = refl

record EndoPersistent : Set where
  constructor endoPersistent
  field runPersistent : PersistentGRU → PersistentGRU
open EndoPersistent public

endoUnit : EndoPersistent
endoUnit = endoPersistent (λ p → p)

endoMul : EndoPersistent → EndoPersistent → EndoPersistent
endoMul f g = endoPersistent (λ p → runPersistent g (runPersistent f p))

endo-assoc : ∀ f g h → endoMul (endoMul f g) h ≡ endoMul f (endoMul g h)
endo-assoc (endoPersistent f) (endoPersistent g) (endoPersistent h) = refl

endo-left-id : ∀ f → endoMul endoUnit f ≡ f
endo-left-id (endoPersistent f) = refl

endo-right-id : ∀ f → endoMul f endoUnit ≡ f
endo-right-id (endoPersistent f) = refl

endoMonoid : Monoid EndoPersistent
endoMonoid = monoid endoUnit endoMul endo-assoc endo-left-id endo-right-id

HiddenFamily : Set
HiddenFamily = PersistentGRU → HiddenEndo

hiddenFamilyId : HiddenFamily
hiddenFamilyId _ = hiddenId

hiddenFamilyMul : HiddenFamily → HiddenFamily → HiddenFamily
hiddenFamilyMul f g p = hiddenMul (f p) (g p)

hiddenFamily-assoc : ∀ f g h → hiddenFamilyMul (hiddenFamilyMul f g) h ≡ hiddenFamilyMul f (hiddenFamilyMul g h)
hiddenFamily-assoc f g h = refl

hiddenFamily-left-id : ∀ f → hiddenFamilyMul hiddenFamilyId f ≡ f
hiddenFamily-left-id f = refl

hiddenFamily-right-id : ∀ f → hiddenFamilyMul f hiddenFamilyId ≡ f
hiddenFamily-right-id f = refl

hiddenFamilyMonoid : Monoid HiddenFamily
hiddenFamilyMonoid = monoid hiddenFamilyId hiddenFamilyMul hiddenFamily-assoc hiddenFamily-left-id hiddenFamily-right-id

reindex : EndoPersistent → HiddenFamily → HiddenFamily
reindex b f p = f (runPersistent b p)

reindex-unit : ∀ f → reindex endoUnit f ≡ f
reindex-unit f = refl

reindex-unit-preserving : ∀ b → reindex b hiddenFamilyId ≡ hiddenFamilyId
reindex-unit-preserving b = refl

reindex-mul : ∀ b₁ b₂ f → reindex (endoMul b₁ b₂) f ≡ reindex b₁ (reindex b₂ f)
reindex-mul b₁ b₂ f = refl

reindex-hom : ∀ b f g → reindex b (hiddenFamilyMul f g) ≡ hiddenFamilyMul (reindex b f) (reindex b g)
reindex-hom b f g = refl

hiddenPersistentAction : Action HiddenFamily EndoPersistent hiddenFamilyMonoid endoMonoid
hiddenPersistentAction = action reindex reindex-unit reindex-unit-preserving reindex-mul reindex-hom

hiddenPersistentSemidirect : Semidirect HiddenFamily EndoPersistent
hiddenPersistentSemidirect = semidirect hiddenFamilyMonoid endoMonoid hiddenPersistentAction

hiddenConstant : Int8 → HiddenFamily
hiddenConstant h _ = hiddenEndo (λ _ → h)

persistentConstant : PersistentGRU → EndoPersistent
persistentConstant p = endoPersistent (λ _ → p)

zeroMatrices : GRUMatrices
zeroMatrices = gruMatrices zero8 zero8 zero8

zeroNoise : GRUNoise
zeroNoise = gruNoise zero8 zero8 zero8

zeroGlobal : GlobalControl
zeroGlobal = globalControl zero8 zero8

basePersistent : PersistentGRU
basePersistent = zeroMatrices , (zeroNoise , zeroGlobal)

decodeFamily : HiddenFamily × EndoPersistent → GRUState
decodeFamily (f , b) = let p = runPersistent b basePersistent; h = runHidden (f p) zero8 in persistentState p h

encodeFamily : GRUState → HiddenFamily × EndoPersistent
encodeFamily (gruState h m n g) = hiddenConstant h , persistentConstant (m , (n , g))

decode-encode : ∀ s → decodeFamily (encodeFamily s) ≡ s
decode-encode (gruState h m n g) = refl

signReLUHidden : HiddenEndo
signReLUHidden = hiddenEndo (apply signReLU8)

signReLUHidden-law : ∀ x → runHidden signReLUHidden x ≡ apply signReLU8 x
signReLUHidden-law x = refl

stepFamily : Int8 → HiddenFamily
stepFamily x p = hiddenEndo (λ h → hidden (gruStep (persistentState p h) x))

fixedStepElement : Int8 → HiddenFamily × EndoPersistent
fixedStepElement x = stepFamily x , endoUnit

carrierStep : Int8 → (HiddenFamily × EndoPersistent) → (HiddenFamily × EndoPersistent)
carrierStep x p = semidirectMul hiddenPersistentSemidirect p (fixedStepElement x)

carrierStep-law : ∀ x p → carrierStep x p ≡ semidirectMul hiddenPersistentSemidirect p (fixedStepElement x)
carrierStep-law x p = refl

carrierStep-encodes-gruStep : ∀ x s → decodeFamily (carrierStep x (encodeFamily s)) ≡ gruStep s x
carrierStep-encodes-gruStep x (gruState h m n g) = refl

hiddenPersistentEmbedding : ∀ x → SemidirectCycleEmbedding hiddenPersistentSemidirect GRUState
hiddenPersistentEmbedding x = semidirectCycleEmbedding encodeFamily decodeFamily decode-encode (carrierStep x) (fixedStepElement x) (carrierStep-law x) (λ s → gruStep s x) (λ s → refl)

hiddenPersistent-gruStep-law : ∀ x s → decodeFamily (semidirectMul hiddenPersistentSemidirect (encodeFamily s) (fixedStepElement x)) ≡ gruStep s x
hiddenPersistent-gruStep-law x s = carrierStep-encodes-gruStep x s

ConnectedQSAState : Set
ConnectedQSAState = Int8

ConnectedMonolithState : Set
ConnectedMonolithState = GRUState × ConnectedQSAState

connectedStep : Int8 → (ConnectedQSAState → ConnectedQSAState) → ConnectedMonolithState → ConnectedMonolithState
connectedStep x qStep (s , q) = gruStep s x , qStep q

record WholeCouplingEnergy : Set₁ where
  constructor wholeCouplingEnergy
  field
    hiddenEnergy : Int8 → Nat
    qsaEnergy : ConnectedQSAState → Nat
    optimizerEnergy : Int8 → Nat
    l2Energy : Int8 → Nat
    pathEnergy : PersistentGRU → Nat
    l1Energy : PersistentGRU → Nat
open WholeCouplingEnergy public

persistentOptimizer : PersistentGRU → Int8
persistentOptimizer (m , (n , g)) = optimizerToken g

persistentL2 : PersistentGRU → Int8
persistentL2 (m , (n , g)) = l2Token g

auxEnergy : WholeCouplingEnergy → PersistentGRU → Nat
auxEnergy E p = optimizerEnergy E (persistentOptimizer p) + l2Energy E (persistentL2 p) + pathEnergy E p + l1Energy E p

restEnergy : WholeCouplingEnergy → ConnectedMonolithState → Nat
restEnergy E (s , q) = qsaEnergy E q + auxEnergy E (persistentGRU s)

wholeEnergy : WholeCouplingEnergy → ConnectedMonolithState → Nat
wholeEnergy E (s , q) = restEnergy E (s , q) + hiddenEnergy E (hidden s)

record WholeCouplingCertificate (E : WholeCouplingEnergy) (x : Int8) (qStep : ConnectedQSAState → ConnectedQSAState) : Set₁ where
  constructor wholeCouplingCertificate
  field
    hiddenNonIncrease : ∀ s → hiddenEnergy E (hidden (gruStep s x)) ≤ hiddenEnergy E (hidden s)
    hiddenStrict : ∀ s → hidden (gruStep s x) ≢ hidden s → hiddenEnergy E (hidden (gruStep s x)) < hiddenEnergy E (hidden s)
    qsaNonIncrease : ∀ q → qsaEnergy E (qStep q) ≤ qsaEnergy E q
    qsaStrict : ∀ q → qStep q ≢ q → qsaEnergy E (qStep q) < qsaEnergy E q
    dynamicSource : ∀ {s q} → connectedStep x qStep (s , q) ≢ (s , q) → (hidden (gruStep s x) ≢ hidden s) ⊎ (qStep q ≢ q)
open WholeCouplingCertificate public

add-left-le : ∀ a {b c : Nat} → b ≤ c → a + b ≤ a + c
add-left-le a z≤n = z≤n
add-left-le a (s≤s p) = s≤s (add-left-le a p)

add-right-le : ∀ a {b c : Nat} → b ≤ c → b + a ≤ c + a
add-right-le a z≤n = z≤n
add-right-le a (s≤s p) = s≤s (add-right-le a p)

le-trans-nat : ∀ {a b c : Nat} → a ≤ b → b ≤ c → a ≤ c
le-trans-nat z≤n r = r
le-trans-nat (s≤s l) (s≤s r) = s≤s (le-trans-nat l r)

lt-le-trans' : ∀ {a b c : Nat} → a < b → b ≤ c → a < c
lt-le-trans' (s≤s p) (s≤s q) = s≤s (le-trans-nat p q)
lt-le-trans' {b = zero} p z≤n = p

le-lt-trans' : ∀ {a b c : Nat} → a ≤ b → b < c → a < c
le-lt-trans' z≤n q = q
le-lt-trans' (s≤s p) (s≤s q) = s≤s (le-lt-trans' p q)

lt-add-left : ∀ {a b c : Nat} → a < b → a + c < b + c
lt-add-left (s≤s p) = s≤s (add-right-le _ p)

lt-add-right : ∀ {a b c : Nat} → a < b → c + a < c + b
lt-add-right (s≤s p) = s≤s (add-left-le _ p)

persistent-aux-invariant : ∀ E s x → auxEnergy E (persistentGRU (gruStep s x)) ≡ auxEnergy E (persistentGRU s)
persistent-aux-invariant E s x = cong (auxEnergy E) (persistent-preservation s x)

rest-nonIncrease :
  ∀ {x : Int8} {qStep : ConnectedQSAState → ConnectedQSAState}
  (E : WholeCouplingEnergy) (C : WholeCouplingCertificate E x qStep)
  (s : GRUState) (q : ConnectedQSAState) → restEnergy E (connectedStep x qStep (s , q)) ≤ restEnergy E (s , q)
rest-nonIncrease {x} E C s q = subst
  (λ a → qsaEnergy E (qStep C q) + a ≤ qsaEnergy E q + auxEnergy E (persistentGRU s))
  (persistent-aux-invariant E s x)
  (add-right-le (auxEnergy E (persistentGRU s)) (qsaNonIncrease C q))

whole-coupling-strict :
  ∀ {x : Int8} {qStep : ConnectedQSAState → ConnectedQSAState}
  (E : WholeCouplingEnergy) (C : WholeCouplingCertificate E x qStep)
  (s : ConnectedMonolithState) → connectedStep x qStep s ≢ s → wholeEnergy E (connectedStep x qStep s) < wholeEnergy E s
whole-coupling-strict {x} {qStep} E C (s , q) moving with dynamicSource C moving
... | inj₁ hiddenMove =
  let strictHidden = hiddenStrict C s hiddenMove
      strictTotalAtRestNew = lt-add-right strictHidden
      restLe = rest-nonIncrease {x = x} E C s q
      restLift = add-right-le (hiddenEnergy E (hidden s)) restLe
  in lt-le-trans' strictTotalAtRestNew restLift
... | inj₂ qsaMove =
  let strictQ = qsaStrict C q qsaMove
      auxEq = persistent-aux-invariant E s x
      strictRest = lt-add-left (subst (λ a → qsaEnergy E (qStep q) + a < qsaEnergy E q + a) auxEq strictQ)
      hiddenLe = hiddenNonIncrease C s
      hiddenLift = add-left-le (restEnergy E (connectedStep x qStep (s , q))) hiddenLe
  in le-lt-trans' hiddenLift (lt-add-left strictRest)

connectedWholeLyapunov :
  ∀ {x : Int8} {qStep : ConnectedQSAState → ConnectedQSAState}
  (E : WholeCouplingEnergy) (C : WholeCouplingCertificate E x qStep) → LyapunovCertificate ConnectedMonolithState (connectedStep x qStep)
connectedWholeLyapunov E C = record { energy = wholeEnergy E ; strictDecrease = λ s moving → whole-coupling-strict E C s moving }

connectedWholeNoNontrivialFiniteCycle :
  ∀ {x : Int8} {qStep : ConnectedQSAState → ConnectedQSAState}
  (E : WholeCouplingEnergy) (C : WholeCouplingCertificate E x qStep)
  {s : ConnectedMonolithState} (n : Nat) → iterate (connectedStep x qStep) (suc n) s ≡ s → OrbitNonFixed s → ⊥
connectedWholeNoNontrivialFiniteCycle E C n = noNontrivialFiniteCycle (connectedWholeLyapunov E C) n

connectedQSAConvergence :
  ∀ {x : Int8} {qStep : ConnectedQSAState → ConnectedQSAState}
  (C : DeterministicQSAStyleCertificate ConnectedMonolithState (connectedStep x qStep))
  (s : ConnectedMonolithState) → ConvergesTo (connectedStep x qStep) (DeterministicQSAStyleCertificate.target C) s
connectedQSAConvergence = deterministicQSAStyleConvergence

connectedQSANoNontrivialCycle :
  ∀ {x : Int8} {qStep : ConnectedQSAState → ConnectedQSAState}
  (C : DeterministicQSAStyleCertificate ConnectedMonolithState (connectedStep x qStep))
  {s : ConnectedMonolithState} (n : Nat) → iterate (connectedStep x qStep) (suc n) s ≡ s → OrbitNonFixed s → ⊥
connectedQSANoNontrivialCycle C = deterministicQSAStyleNoNontrivialCycle C

record ContributionAudit (s : GRUState) (x : Int8) : Set₁ where
  constructor contributionAudit
  field
    optimizerZero : ∀ (F : Int8 → Nat) → F (persistentOptimizer (persistentGRU (gruStep s x))) ≡ F (persistentOptimizer (persistentGRU s))
    l2Zero : ∀ (F : Int8 → Nat) → F (persistentL2 (persistentGRU (gruStep s x))) ≡ F (persistentL2 (persistentGRU s))
    normZero : ∀ (F : PersistentGRU → Nat) → F (persistentGRU (gruStep s x)) ≡ F (persistentGRU s)

contributionAuditWitness : ∀ s x → ContributionAudit s x
contributionAuditWitness s x = contributionAudit
  (λ F → cong F (persistent-preservation s x))
  (λ F → cong F (persistent-preservation s x))
  (λ F → cong F (persistent-preservation s x))
