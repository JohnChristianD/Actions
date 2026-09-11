source = "Exotic/ERL/FullCoupled/EfficientCHAD_v159.agda"
target = ".ci/kernel/Canonical/ERL/FullCoupled/EfficientCHAD_v159.agda"
test_source = "Exotic/ERL/FullCoupled/EfficientCHAD_v159_test.agda"
test_target = ".ci/kernel/Canonical/ERL/FullCoupled/EfficientCHAD_v159_test.agda"

raw = File.read!(source) |> String.replace("\r\n", "\n")
expected = "{-# OPTIONS --safe #-}\nmodule Exotic.ERL.FullCoupled.EfficientCHAD_v159 where"
unless String.starts_with?(raw, expected), do: raise("v159 source header/module mismatch")

code = Regex.replace(~r/--[^\n]*/, "", raw)
forbidden = ["StoSignSGDv2", "StoSignSGD", "LayerNorm", "BatchNorm", "BatchRenorm", "Newton", "Certificate", "postulate", "{!!}", "CReLU"]
Enum.each(forbidden, fn token ->
  if String.contains?(code, token), do: raise("forbidden canonical token remains: #{token}")
end)
if String.contains?(code, "SmoothAlgebra.exp") or String.contains?(code, "SmoothAlgebra.log"), do: raise("legacy natural exp/log remains")

kernel = raw
|> String.replace("module Exotic.ERL.FullCoupled.EfficientCHAD_v159 where", "module Canonical.ERL.FullCoupled.EfficientCHAD_v159 where")
|> String.replace("open import Agda.Builtin.Nat using (Nat; zero; suc)", "open import Agda.Builtin.Nat using (Nat)")
|> String.replace("≡ suc (rank (next s))", "≡ Nat.suc (rank (next s))")

test = File.read!(test_source)
|> String.replace("module Exotic.ERL.FullCoupled.EfficientCHAD_v159_test where", "module Canonical.ERL.FullCoupled.EfficientCHAD_v159_test where")
|> String.replace("open import Exotic.ERL.FullCoupled.EfficientCHAD_v159", "open import Canonical.ERL.FullCoupled.EfficientCHAD_v159")

unless length(String.split(kernel, "\n")) == length(String.split(raw, "\n")), do: raise("kernel normalization changed line structure")
File.mkdir_p!(Path.dirname(target))
File.mkdir_p!(Path.dirname(test_target))
File.write!(target, kernel)
File.write!(test_target, test)
IO.puts("v159 source hygiene PASS; generated unique-namespace kernel copy PASS")
