source = "Exotic/ERL/FullCoupled/EfficientCHAD_v161.agda"
raw = File.read!(source) |> String.replace("\r\n", "\n")
expected = "{-# OPTIONS --safe #-}\nmodule Exotic.ERL.FullCoupled.EfficientCHAD_v161 where"
unless String.starts_with?(raw, expected), do: raise("v161 source header/module mismatch")

forbidden = [
  "StoSignSGD",
  "StoSignSGDv2",
  "Munchausen",
  "munchausen",
  "Lion",
  "lion",
  "Adam",
  "AdaMax",
  "RAdam",
  "beta1",
  "beta2",
  "LayerNorm",
  "BatchNorm",
  "BatchRenorm",
  "Newton",
  "DiagonalNewton",
  "NewtonRaphson",
  "Certificate",
  "postulate",
  "{!!}",
  "CReLU",
  "SmoothAlgebra.exp",
  "SmoothAlgebra.log",
  "clamp",
  "squash"
]

if Enum.any?(forbidden, &String.contains?(raw, &1)), do: raise("forbidden retired formulation remains in v161")

unless String.contains?(raw, "softsignQIDBDStep"), do: raise("canonical softsign-q-IDBD missing")
unless String.contains?(raw, "dyadicEpsilon"), do: raise("canonical dyadic threshold missing")
unless String.contains?(raw, "idbdPow2") and String.contains?(raw, "idbdLog2"), do: raise("base-2 IDBD surface missing")
unless String.contains?(raw, "critic actor transformer representation"), do: raise("four canonical parameter groups missing")
unless String.contains?(raw, "unsquashedActor"), do: raise("unsquashed actor mode missing")

IO.puts("v161 canonical source hygiene: PASS")