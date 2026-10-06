module FullCoupled.KalmanLinearAttentionTest where




-- BEGIN MIRTH-SYNC CANONICAL COMMAND
-- "$AGDA_COMMAND" -i .
-- END MIRTH-SYNC CANONICAL COMMAND

open import FullCoupled.KalmanLinearAttention using
  ( KLAConcept
  ; KLALaw
  ; KLAPlan
  ; klaAStarPlan
  ; klaMobiusPrefixScan
  ; klaMeanPrefixScan
  )

test-mobius-plan-nonempty : KLAPlan
test-mobius-plan-nonempty = klaAStarPlan

test-mobius-prefix-scan : KLAConcept
test-mobius-prefix-scan = klaMobiusPrefixScan

test-mean-prefix-scan : KLAConcept
test-mean-prefix-scan = klaMeanPrefixScan

test-law-record : KLALaw
test-law-record = recordLaw

recordLaw : KLALaw
recordLaw = {!!}


-- BEGIN MIRTH-SYNC CANONICAL COMMAND
-- "$AGDA_COMMAND" -i .
-- END MIRTH-SYNC CANONICAL COMMAND

open import FullCoupled.KalmanLinearAttention using
  ( KLAConcept
  ; KLAPlan
  ; KLAMobius
  ; KLAAffine
  ; concepts
  ; klaMobiusPrefixPlan
  ; klaMeanPrefixPlan
  ; klaMobiusPath
  ; klaMeanPath
  ; klaPrecisionMatrix
  ; klaMeanAffine
  )

test-mobius-plan : KLAPlan
test-mobius-plan = klaMobiusPrefixPlan

test-mean-plan : KLAPlan
test-mean-plan = klaMeanPrefixPlan

test-mobius-cost : cost klaMobiusPrefixPlan ≡ suc (suc (suc zero))
test-mobius-cost = refl

test-mean-cost : cost klaMeanPrefixPlan ≡ suc (suc zero)
test-mean-cost = refl

test-mobius-path : List KLAConcept
test-mobius-path = klaMobiusPath

test-mean-path : List KLAConcept
test-mean-path = klaMeanPath

test-precision-matrix : KLAMobius
test-precision-matrix = klaPrecisionMatrix (+ 2) (+ 3) (+ 5)

test-mean-affine : KLAAffine
test-mean-affine = klaMeanAffine (+ 2) (+ 3) (+ 7)
