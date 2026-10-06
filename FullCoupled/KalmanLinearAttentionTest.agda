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
