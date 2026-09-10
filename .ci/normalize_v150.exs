repo = File.cwd!()
workflow_paths = Path.wildcard(Path.join(repo, ".github/workflows/*.yml"))
workflow_text = Enum.map(workflow_paths, &File.read!/1) |> Enum.join("\n")

unless not String.contains?(workflow_text, "python3") and not String.contains?(workflow_text, "ruby/") and not Regex.match?(~r/\bruby\s+[^\n]*\.ci\//, workflow_text) do
  raise "forbidden Python/Ruby CI invocation remains"
end

monolith = File.read!(Path.join(repo, "Exotic/ERL/FullCoupled/CompleteSafe_v147.agda"))
if length(Regex.scan(~r/^record SmoothAlgebra\b/m, monolith)) != 1 do
  raise "SmoothAlgebra is not structurally unique"
end

target = File.read!(Path.join(repo, "Exotic/ERL/FullCoupled/EfficientCHAD_CReLU_Tsallis2_v150.agda"))
for token <- [
  "SignedParameterDirectionQIDBD",
  "CReLU",
  "Tsallis2Branch",
  "DyadicCoupledL2",
  "onePathNorm",
  "EfficientCHAD_CReLU_Tsallis2_TheoremTarget"
] do
  unless String.contains?(target, token) do
    raise "v150 theorem target missing #{token}"
  end
end

for token <- ["LayerNorm", "python3", "ruby/setup-ruby"] do
  unless not String.contains?(target, token) do
    raise "forbidden target token #{token}"
  end
end

IO.puts("v150 Elixir normalization: PASS")
