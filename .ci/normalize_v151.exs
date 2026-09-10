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
  {"    signIdempotent : ∀ x →\n      let p = max zero x\n          n = max zero (neg x)\n      in max zero (neg n) ≡ max zero (neg n)", "    signIdempotent : ∀ x → sign (sign x) ≡ sign x\n    signZero : sign zero ≡ zero\n    signNegOne : ∀ {x} → x < zero → sign x ≡ neg one\n    signPosOne : ∀ {x} → zero < x → sign x ≡ one"}
]

text = Enum.reduce(repairs, text, fn {old, new}, acc -> String.replace(acc, old, new) end)

text = Regex.replace(~r/signScalar\s*:\s*∀ \{A : DyadicRing\} → DyadicRing\.R A → DyadicRing\.R A\s*signScalar \{A\} x = .*?(?=\n\n)/s,
  text,
  "parameterSign : ∀ {A : DyadicRing} → DyadicRing.R A → DyadicRing.R A\nparameterSign {A} x = DyadicRing.sign A x")

text = Regex.replace(~r/cReLUReconstruct\s*:\s*∀ \{A : DyadicRing\}.*?cReLUReconstruct A0 x = .*?(?=\n\ncReLUMagnitudeProof)/s,
  text,
  "cReLUReconstruct : ∀ {A : DyadicRing} (x : DyadicRing.R A) →\n  cPlus {A} x + DyadicRing.neg A (cMinus {A} x) ≡ x\ncReLUReconstruct {A} x = DyadicRing.cReLULaw A x")

text = Regex.replace(~r/cReLUMagnitudeProof\s*:\s*∀ \{A : DyadicRing\}.*?cReLUMagnitudeProof A0 x = .*?(?=\n\n)/s,
  text,
  "cReLUMagnitudeProof : ∀ {A : DyadicRing} (x : DyadicRing.R A) →\n  cPlus {A} x + cMinus {A} x ≡ DyadicRing.abs A x\ncReLUMagnitudeProof {A} x = DyadicRing.cReLUMagnitude A x")

text = Regex.replace(~r/antitheticCancel\s*:\s*∀ \{A : DyadicRing\}.*?antitheticCancel A0 x = .*?(?=\n\nsignQIDBDNormalForm)/s,
  text,
  "antitheticCancel : ∀ {A : DyadicRing} (x : DyadicRing.R A) →\n  DyadicRing._+_ A x (DyadicRing.neg A x) ≡ DyadicRing.zero A\nantitheticCancel {A} x = DyadicRing.addNegR A x")

text = Regex.replace(~r/signQIDBDNormalForm\s*:\s*∀ \{A : DyadicRing\}.*?signQIDBDNormalForm A0 x = .*?(?=\n\ndata DegreeRecurrence)/s,
  text,
  "signQIDBDNormalForm : ∀ {A : DyadicRing} (x : DyadicRing.R A) →\n  parameterSign {A} (parameterSign {A} x) ≡ parameterSign {A} x\nsignQIDBDNormalForm {A} x = DyadicRing.signIdempotent A x")

text = Regex.replace(~r/\(A0 : A\) x →/, "(x : DyadicRing.R A) →", text)
text = Regex.replace(~r/\bDyadicRing\.(cReLULaw|cReLUMagnitude|addNegR|signIdempotent) A0 x/, "DyadicRing.\\1 A x", text)
text = Regex.replace(~r/signQIDBDDirection \{A\} \(x ∷ xs\) = signScalar \{A\} x ∷ signQIDBDDirection xs/, text,
  "signQIDBDDirection {A} (x ∷ xs) = parameterSign {A} x ∷ signQIDBDDirection xs")
text = String.replace(text,
  "parameterDirectionOnly : ∀ i → index signedDirection i ≡ signScalar {A} (index rawDirection i)",
  "parameterDirectionOnly : ∀ i → index signedDirection i ≡ parameterSign {A} (index rawDirection i)")

text = Regex.replace(~r/cReLUPair\s*:\s*∀ \{A : DyadicRing\}.*?cReLUPair \{A\} x = .*?\n\n/s, text, "")
text = String.replace(text, "-- Finite emergent composition target.", "-- Finite emergent composition target.\n-- default update channel: sign-q-IDBD = parameterSign after q-style projection.")

forbidden = [
  "LayerNorm", "BatchNorm", "BatchRenorm", "CReLUCertificate",
  "noMomentum", "beta1Zero", "python3", "setup-python", "ruby/setup-ruby", "Σ"
]
Enum.each(forbidden, fn token -> if String.contains?(text, token), do: raise "forbidden v151 token remains: #{token}" end)

required = [
  "parameterSign", "Tsallis2", "onePathNorm", "weightL1", "beta1Numerator",
  "beta1Exponent", "metaExponent", "Munchausen", "overestimation", "CVT",
  "OpenES", "signIdempotent"
]
Enum.each(required, fn token -> unless String.contains?(text, token), do: raise "required v151 token missing: #{token}" end)

File.write!(path, text)
IO.puts("v151 Elixir normalisation/hygiene: PASS")
