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
  {"cReLUPair : ∀ {A : DyadicRing} → DyadicRing.R A →\n  Σ (DyadicRing.R A) (λ _ → DyadicRing.R A)\ncReLUPair {A} x = _,_ (cPlus {A} x) (cMinus {A} x)", "record CReLUPair (A : DyadicRing) : Set where\n  constructor mkCReLUPair\n  field\n    pos neg : DyadicRing.R A\n\ncReLUPair : ∀ {A : DyadicRing} → DyadicRing.R A → CReLUPair A\ncReLUPair {A} x = mkCReLUPair (cPlus {A} x) (cMinus {A} x)"},
  {"cReLUReconstruct : ∀ {A : DyadicRing} (A0 : A) x →", "cReLUReconstruct : ∀ {A : DyadicRing} (A0 : A) (x : DyadicRing.R A) →"},
  {"cReLUMagnitudeProof : ∀ {A : DyadicRing} (A0 : A) x →", "cReLUMagnitudeProof : ∀ {A : DyadicRing} (A0 : A) (x : DyadicRing.R A) →"},
  {"antitheticCancel : ∀ {A : DyadicRing} (A0 : A) x →", "antitheticCancel : ∀ {A : DyadicRing} (A0 : A) (x : DyadicRing.R A) →"},
  {"signQIDBDNormalForm : ∀ {A : DyadicRing} (A0 : A) x →", "signQIDBDNormalForm : ∀ {A : DyadicRing} (A0 : A) (x : DyadicRing.R A) →"}
]

text = Enum.reduce(repairs, text, fn {old, new}, acc ->
  String.replace(acc, old, new)
end)

forbidden = [
  "LayerNorm",
  "BatchNorm",
  "BatchRenorm",
  "CReLUCertificate",
  "noMomentum",
  "beta1Zero",
  "python3",
  "setup-python",
  "ruby/setup-ruby"
]

Enum.each(forbidden, fn token ->
  if String.contains?(text, token) do
    raise "forbidden v151 token remains: #{token}"
  end
end)

required = [
  "sign-q-IDBD",
  "Tsallis2",
  "onePathNorm",
  "weightL1",
  "beta1Numerator",
  "beta1Exponent",
  "metaExponent",
  "Munchausen",
  "overestimation",
  "CVT",
  "OpenES"
]

Enum.each(required, fn token ->
  unless String.contains?(text, token) do
    raise "required v151 token missing: #{token}"
  end
end)

File.write!(path, text)
IO.puts("v151 Elixir normalisation/hygiene: PASS")
