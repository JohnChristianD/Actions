path = "Exotic/ERL/FullCoupled/EfficientCHAD_v158.agda"
raw = File.read!(path)
text = String.replace(raw, "\r\n", "\n")

expected_header = "{-# OPTIONS --safe #-}\nmodule Exotic.ERL.FullCoupled.EfficientCHAD_v158 where"
unless String.starts_with?(text, expected_header) do
  raise("v158 source header/module mismatch")
end

forbidden = [
  "StoSignSGDv2",
  "StoSignSGD",
  "LayerNorm",
  "BatchNorm",
  "BatchRenorm",
  "Newton",
  "Certificate",
  "postulate",
  "{!!}",
  "CReLU"
]

Enum.each(forbidden, fn token ->
  if String.contains?(text, token), do: raise("forbidden v158 token remains: #{token}")
end)

if String.contains?(text, "SmoothAlgebra.exp") or String.contains?(text, "SmoothAlgebra.log") do
  raise("legacy natural exp/log remains in the canonical v158 learner surface")
end

IO.puts("v158 Elixir validation-only normalization/hygiene: PASS")
