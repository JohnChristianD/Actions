path = "Exotic/ERL/FullCoupled/EfficientCHAD_StoSignSGDv2_Tsallis2_v151.agda"
text = File.read!(path) |> String.replace("\r\n", "\n")

repairs = [
  {"∀ {A n} → DyadicRing A →", "∀ {A : DyadicRing} {n} →"},
  {"∀ {A m n} → DyadicRing A →", "∀ {A : DyadicRing} {m n} →"},
  {"∀ {A} → DyadicRing A →", "∀ {A : DyadicRing} →"},
  {"∀ {A w} (A0 : DyadicRing A)", "∀ {A : DyadicRing} {w} (A0 : A)"},
  {"∀ {A n} (A0 : DyadicRing A)", "∀ {A : DyadicRing} {n} (A0 : A)"},
  {"∀ {A} (A0 : DyadicRing A)", "∀ {A : DyadicRing} (A0 : A)"}
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
