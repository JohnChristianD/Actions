required = [
  ".github/workflows/agda.yml",
  ".github/workflows/oracle-crosscheck.yml",
  "Exotic/ERL/FullCoupled/SignQIDBDComposed_v153.agda"
]

Enum.each(required, fn path ->
  unless File.exists?(path), do: Mix.raise("missing required path: #{path}")
end)

workflows = Enum.filter(required, &String.ends_with?(&1, ".yml"))
Enum.each(workflows, fn path ->
  text = File.read!(path) |> String.downcase()
  if String.contains?(text, "python") or String.contains?(text, "ruby") do
    Mix.raise("legacy CI runtime reference: #{path}")
  end
end)

canonical = File.read!("Exotic/ERL/FullCoupled/SignQIDBDComposed_v153.agda")
unless String.contains?(canonical, "{-# OPTIONS --safe #-}") do
  Mix.raise("canonical theorem is not --safe")
end

IO.puts("normalise-agda=PASS")
