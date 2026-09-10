repo = File.cwd!()
workflow_text = Path.wildcard(Path.join(repo, ".github/workflows/*.yml")) |> Enum.map(&File.read!/1) |> Enum.join("\n")

unless not Regex.match?(~r/\bpython3\b/, workflow_text) and
       not Regex.match?(~r/ruby\/setup-ruby/, workflow_text) and
       not Regex.match?(~r/\bruby\s+[^\n]*\.ci\//, workflow_text) do
  raise "forbidden Python/Ruby CI invocation remains"
end

monolith_path = Path.join(repo, "Exotic/ERL/FullCoupled/CompleteSafe_v147.agda")
s0 = File.read!(monolith_path)
record_token = "record SmoothAlgebra : Set₁ where"
scalar_marker = "\nScalar : SmoothAlgebra → Set\n"
marker_start = "------------------------------------------------------------------------\n-- Canonical SmoothAlgebra boundary.\n"

unless String.contains?(s0, marker_start) do
  raise "canonical SmoothAlgebra boundary missing"
end

s1 = String.replace(s0,
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
s2 = Enum.reduce(replacements, s1, fn {a, b}, acc -> String.replace(acc, a, b, global: false) end)

header_pos = :binary.match(s2, marker_start) |> elem(0)
s3 =
  case :binary.match(s2, record_token) do
    :nomatch -> raise "SmoothAlgebra record missing"
    {record_pos, _} when record_pos < header_pos ->
      tail = binary_part(s2, record_pos, byte_size(s2) - record_pos)
      case :binary.match(tail, scalar_marker) do
        :nomatch -> raise "legacy SmoothAlgebra scalar boundary missing"
        {scalar_rel, _} ->
          scalar_pos = record_pos + scalar_rel
          binary_part(s2, 0, record_pos) <>
            binary_part(s2, scalar_pos + byte_size(scalar_marker), byte_size(s2) - scalar_pos - byte_size(scalar_marker))
      end
    _ -> s2
  end

s4 = String.replace(s3,
  "    sqrt recip max min : R → R\n",
  "    sqrt recip : R → R\n    max min : R → R → R\n",
  global: false)

needle = "    reciprocalLaw : ∀ {d} → zero < d → Ring._*_ (OrderedRing.ring orderedRing) d (recip d) ≡ one\n"
s5 = if String.contains?(s4, needle) and not String.contains?(s4, "    sqrtDomain : R → Set\n") do
  String.replace(s4, needle, needle <> "    sqrtDomain : R → Set\n    sqrtSquareLaw : ∀ x → sqrtDomain x →\n      Ring._*_ (OrderedRing.ring orderedRing) (sqrt x) (sqrt x) ≡ x\n", global: false)
else
  s4
end

# The legacy accumulate parser form is replaced without relying on a multiline heredoc.
old_acc_re = ~r/  accumulate : Fin n → R → EState → EState\n  accumulate i c \(state s\) = state \(λ j with finDecEq j i\n    \.\.\. \| yes _ = s j \+ c\n    \.\.\. \| no _ = s j\)\n/
new_acc = "  accumulateAt : Fin n → R → Cot → Fin n → R\n  accumulateAt i c s j with finDecEq j i\n  ... | yes _ = s j + c\n  ... | no _ = s j\n\n  accumulate : Fin n → R → EState → EState\n  accumulate i c (state s) = state (accumulateAt i c s)\n"
s6 = Regex.replace(old_acc_re, s5, new_acc, global: true)

unless length(Regex.scan(~r/^record SmoothAlgebra\b/m, s6)) == 1 do
  raise "SmoothAlgebra record count is not one after normalization"
end
if Regex.match?(old_acc_re, s6) or String.contains?(s6, "λ j with finDecEq") do
  raise "dependent lambda-with parser form survived"
end
if String.contains?(s6, "-- AUDITED-KKT-OBLIGATION") do
  raise "audited KKT placeholder survived"
end

File.write!(monolith_path, s6)

target = File.read!(Path.join(repo, "Exotic/ERL/FullCoupled/EfficientCHAD_CReLU_Tsallis2_v150.agda"))
for token <- ["SignedParameterDirectionQIDBD", "CReLU", "Tsallis2Branch", "DyadicCoupledL2", "onePathNorm", "EfficientCHAD_CReLU_Tsallis2_TheoremTarget"] do
  unless String.contains?(target, token), do: raise "v150 theorem target missing #{token}"
end
for token <- ["LayerNorm", "python3", "ruby/setup-ruby"] do
  if String.contains?(target, token), do: raise "forbidden target token #{token}"
end

IO.puts("v150 Elixir normalization: PASS")
