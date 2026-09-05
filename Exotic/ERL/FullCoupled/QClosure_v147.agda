{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.QClosure_v147 where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong)
open import Exotic.ERL.FullCoupled.CompleteSafe_v147

------------------------------------------------------------------------
-- v147 constructive q-closure.
-- The projection is a finite retraction on the q-feasible region. The
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
          (indexV x i * (indexV x i)))

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
-- emitted projection is nonnegative. This is the exact q transition used by
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
