required = [
  ".github/workflows/agda.yml",
  ".github/workflows/oracle-crosscheck.yml",
  "Exotic/ERL/FullCoupled/SignQIDBDComposed_v153.agda",
  "Exotic/ERL/FullCoupled/ConjectureGeneration_v153.agda",
  "Exotic/ERL/FullCoupled/NormaliseAgda_v153.agda"
]

Enum.each(required, fn path ->
  unless File.exists?(path), do: Mix.raise("missing required path: #{path}")
end)

oracle = File.read!(".github/workflows/oracle-crosscheck.yml") |> String.downcase()
if String.contains?(oracle, "python") or String.contains?(oracle, "ruby") do
  Mix.raise("legacy CI runtime reference in oracle workflow")
end

canonical = File.read!("Exotic/ERL/FullCoupled/SignQIDBDComposed_v153.agda")
unless String.contains?(canonical, "{-# OPTIONS --safe #-}") do
  Mix.raise("canonical theorem is not --safe")
end

IO.puts("normalise-agda=PASS")
