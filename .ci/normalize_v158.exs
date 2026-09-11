path = "Exotic/ERL/FullCoupled/EfficientCHAD_v159.agda"
raw = File.read!(path)
text = String.replace(raw, "\r\n", "\n")

expected_header = "{-# OPTIONS --safe #-}\nmodule Exotic.ERL.FullCoupled.EfficientCHAD_v159 where"
unless String.starts_with?(text, expected_header) do
  raise("v159 source header/module mismatch")
end

code = Regex.replace(~r/--[^\n]*/, "", text)

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
  if String.contains?(code, token), do: raise("forbidden canonical token remains: #{token}")
end)

if String.contains?(code, "SmoothAlgebra.exp") or String.contains?(code, "SmoothAlgebra.log") do
  raise("legacy natural exp/log remains in the canonical learner surface")
end

IO.puts("v159 Elixir validation-only normalization/hygiene: PASS")
