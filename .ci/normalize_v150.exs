repo = File.cwd!()
workflow_paths = Path.wildcard(Path.join(repo, ".github/workflows/*.yml"))
workflow_text = Enum.map(workflow_paths, &File.read!/1) |> Enum.join("\n")

forbidden = [~r/\bpython3\b/, ~r/ruby\/setup-ruby/, ~r/\bruby\s+[^\n]*\.ci\//]
if Enum.any?(forbidden, &Regex.match?(&1, workflow_text)) do
  raise "forbidden Python/Ruby CI invocation remains"
end

monolith_path = Path.join(repo, "Exotic/ERL/FullCoupled/CompleteSafe_v147.agda")
s = File.read!(monolith_path)
record_token = "record SmoothAlgebra : Set₁ where"
scalar_marker = "\nScalar : SmoothAlgebra → Set\n"
marker_start = "------------------------------------------------------------------------\n-- Canonical SmoothAlgebra boundary.\n"
marker_end = "------------------------------------------------------------------------\n-- Seven coupled parameter blocks and finite parameter indices\n"

unless String.contains?(s, marker_start) and String.contains?(s, marker_end) do
  raise "canonical SmoothAlgebra boundaries not found"
end

s = String.replace(s,
  "open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)",
  "open import Agda.Builtin.Nat using (Nat; suc; _+_)",
  global: false)

replacements = [
  {"Vec A zero", "Vec A Nat.zero"},
  {"sumFin _ z zero _ = z", "sumFin _ z Nat.zero _ = z"},
  {"tabulateV {zero} f = []", "tabulateV {A = _} {n = Nat.zero} f = []"},
  {"tabulateVS {S} {zero} f = []", "tabulateVS {S} {Nat.zero} f = []"},
  {"zeroVector {S} {zero} = []", "zeroVector {S} {Nat.zero} = []"},
  {"zeroVecS {S} {zero} = []", "zeroVecS {S} {Nat.zero} = []"},
  {"vZero_v140 {S} {zero} = []", "vZero_v140 {S} {Nat.zero} = []"},
  {"maskAllFalse {zero} = []", "maskAllFalse {Nat.zero} = []"},
  {"qRunFuel_v142 zero r = r", "qRunFuel_v142 Nat.zero r = r"},
  {"shiftLV_v146 zero xs = xs", "shiftLV_v146 Nat.zero xs = xs"},
  {"shiftRV_v146 zero xs = xs", "shiftRV_v146 Nat.zero xs = xs"},
  {"qsaXorShiftDeterministic_v146 zero seed = []", "qsaXorShiftDeterministic_v146 Nat.zero seed = []"}
]
for {a, b} <- replacements, do: s = String.replace(s, a, b, global: false)

# Remove one legacy SmoothAlgebra definition when it occurs before the canonical marker.
header_pos = :binary.match(s, marker_start) |> elem(0)
case :binary.match(s, record_token) do
  :nomatch -> raise "SmoothAlgebra record missing"
  {legacy_pos, _} when legacy_pos < header_pos ->
    case :binary.match(s, scalar_marker, scope: legacy_pos..byte_size(s)) do
      :nomatch -> raise "legacy SmoothAlgebra scalar boundary missing"
      {scalar_pos, _} ->
        s = binary_part(s, 0, legacy_pos) <> binary_part(s, scalar_pos + 1, byte_size(s) - scalar_pos - 1)
    end
  _ -> :ok
end

# Recompute positions after legacy removal and deduplicate only inside the canonical region.
first = :binary.match(s, marker_start) |> elem(0)
end_rel = binary_part(s, first, byte_size(s) - first) |> :binary.match(marker_end)
unless end_rel != :nomatch, do: raise "canonical SmoothAlgebra closing boundary missing"
{rel_end, _} = end_rel
end_abs = first + rel_end
prefix = binary_part(s, 0, first)
region = binary_part(s, first, end_abs - first)
suffix = binary_part(s, end_abs, byte_size(s) - end_abs)

region = Regex.replace(~r/record SmoothAlgebra : Set₁ where(?s:.*?)\nScalar : SmoothAlgebra → Set\n/, region, "Scalar : SmoothAlgebra → Set\n")
s = prefix <> region <> suffix

# Preserve canonical max/min arity if an older combined declaration is still present.
s = String.replace(s,
  "    sqrt recip max min : R → R\n",
  "    sqrt recip : R → R\n    max min : R → R → R\n",
  global: false)

needle = "    reciprocalLaw : ∀ {d} → zero < d → Ring._*_ (OrderedRing.ring orderedRing) d (recip d) ≡ one\n"
if String.contains?(s, needle) and not String.contains?(s, "    sqrtDomain : R → Set\n") do
  s = String.replace(s, needle, needle <> "    sqrtDomain : R → Set\n    sqrtSquareLaw : ∀ x → sqrtDomain x →\n      Ring._*_ (OrderedRing.ring orderedRing) (sqrt x) (sqrt x) ≡ x\n", global: false)
end

old_acc = """  accumulate : Fin n → R → EState → EState
  accumulate i c (state s) = state (λ j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j)
"""
new_acc = """  accumulateAt : Fin n → R → Cot → Fin n → R
  accumulateAt i c s j with finDecEq j i
  ... | yes _ = s j + c
  ... | no _ = s j

  accumulate : Fin n → R → EState → EState
  accumulate i c (state s) = state (accumulateAt i c s)
"""
s = String.replace(s, old_acc, new_acc, global: false)

if String.contains?(s, "-- AUDITED-KKT-OBLIGATION") do
  raise "malformed audited KKT placeholder marker survived"
end
if length(Regex.scan(~r/^record SmoothAlgebra\b/m, s)) != 1 do
  raise "SmoothAlgebra record count is not one after normalization"
end
if String.contains?(s, "λ j with finDecEq") do
  raise "dependent lambda-with parser form survived"
end

File.write!(monolith_path, s)

target = File.read!(Path.join(repo, "Exotic/ERL/FullCoupled/EfficientCHAD_CReLU_Tsallis2_v150.agda"))
for token <- [
  "SignedParameterDirectionQIDBD",
  "CReLU",
  "Tsallis2Branch",
  "DyadicCoupledL2",
  "onePathNorm",
  "EfficientCHAD_CReLU_Tsallis2_TheoremTarget"
] do
  unless String.contains?(target, token), do: raise "v150 theorem target missing #{token}"
end
for token <- ["LayerNorm", "python3", "ruby/setup-ruby"] do
  if String.contains?(target, token), do: raise "forbidden target token #{token}"
end

IO.puts("v150 Elixir normalization: PASS")
