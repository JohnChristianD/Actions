path = "Exotic/ERL/FullCoupled/EfficientCHAD_StoSignSGDv2_Tsallis2_v151.agda"
text = File.read!(path) |> String.replace("\r\n", "\n")

repairs = [
  {"open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)\n", ""},
  {"∀ {A n} → DyadicRing A →", "∀ {A : DyadicRing} {n} →"},
  {"∀ {A m n} → DyadicRing A →", "∀ {A : DyadicRing} {m n} →"},
  {"∀ {A} → DyadicRing A →", "∀ {A : DyadicRing} →"},
  {"∀ {A w} (A0 : DyadicRing A)", "∀ {A : DyadicRing} {w} (A0 : A)"},
  {"∀ {A n} (A0 : DyadicRing A)", "∀ {A : DyadicRing} {n} (A0 : A)"},
  {"∀ {A} (A0 : DyadicRing A)", "∀ {A : DyadicRing} (A0 : A)"},
  {"beta115_128_code", "betaDyadicCode"},
  {"onePathVector : ∀ {A : DyadicRing} {d} → Vec (Matrix A d d) Nat → Vector A d", "onePathVector : ∀ {A : DyadicRing} {d L} → Vec (Matrix A d d) L → Vector A d"},
  {"onePathNorm : ∀ {A : DyadicRing} {d} → Vec (Matrix A d d) Nat → DyadicRing.R A", "onePathNorm : ∀ {A : DyadicRing} {d L} → Vec (Matrix A d d) L → DyadicRing.R A"},
  {"    neg abs : R → R\n    max : R → R → R", "    neg abs sign : R → R\n    max : R → R → R"},
  {"    signIdempotent : ∀ x →\n      let p = max zero x\n          n = max zero (neg x)\n      in max zero (neg n) ≡ max zero (neg n)", "    signIdempotent : ∀ x → sign (sign x) ≡ sign x\n    signZero : sign zero ≡ zero\n    signNegOne : ∀ {x} → x < zero → sign x ≡ neg one\n    signPosOne : ∀ {x} → zero < x → sign x ≡ one"},
  {"cReLUReconstruct : ∀ {A : DyadicRing} (A0 : A) x → signScalar {A} x ≡ x", "cReLUReconstruct : ∀ {A : DyadicRing} (x : DyadicRing.R A) →"},
  {"cReLUReconstruct A0 x = DyadicRing.cReLULaw A0 x", "cReLUReconstruct {A} x = DyadicRing.cReLULaw A x"},
  {"cReLUMagnitudeProof : ∀ {A : DyadicRing} (A0 : A) x →", "cReLUMagnitudeProof : ∀ {A : DyadicRing} (x : DyadicRing.R A) →"},
  {"cReLUMagnitudeProof A0 x = DyadicRing.cReLUMagnitude A0 x", "cReLUMagnitudeProof {A} x = DyadicRing.cReLUMagnitude A x"},
  {"antitheticCancel : ∀ {A : DyadicRing} (A0 : A) x →", "antitheticCancel : ∀ {A : DyadicRing} (x : DyadicRing.R A) →"},
  {"antitheticCancel A0 x = DyadicRing.addNegR A0 x", "antitheticCancel {A} x = DyadicRing.addNegR A x"},
  {"signQIDBDNormalForm : ∀ {A : DyadicRing} (A0 : A) x →", "signQIDBDNormalForm : ∀ {A : DyadicRing} (x : DyadicRing.R A) →"},
  {"signQIDBDNormalForm A0 x = DyadicRing.signIdempotent A0 x", "signQIDBDNormalForm {A} x = DyadicRing.signIdempotent A x"}
]

text = Enum.reduce(repairs, text, fn {old, new}, acc -> String.replace(acc, old, new) end)
text = Regex.replace(~r/cReLUPair\s*:\s*∀ \{A : DyadicRing\}.*?cReLUPair \{A\} x = .*?\n\n/s, text, "")

forbidden = [
  "LayerNorm", "BatchNorm", "BatchRenorm", "CReLUCertificate",
  "noMomentum", "beta1Zero", "python3", "setup-python", "ruby/setup-ruby", "Σ"
]
Enum.each(forbidden, fn token -> if String.contains?(text, token), do: raise "forbidden v151 token remains: #{token}" end)

required = [
  "sign-q-IDBD", "Tsallis2", "onePathNorm", "weightL1", "beta1Numerator",
  "beta1Exponent", "metaExponent", "Munchausen", "overestimation", "CVT",
  "OpenES", "parameterSign", "signIdempotent"
]
Enum.each(required, fn token -> unless String.contains?(text, token), do: raise "required v151 token missing: #{token}" end)

File.write!(path, text)
IO.puts("v151 Elixir normalisation/hygiene: PASS")
