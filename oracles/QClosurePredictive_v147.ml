let positive n = n

let weighted h x = h * x

let rec cap budget value =
  match budget, value with
  | 0, _ -> 0
  | _, 0 -> 0
  | b, v -> 1 + cap (b - 1) (v - 1)

let project budget h x = cap budget (weighted h x)

let oracle_identity n = positive n = n

let () =
  assert (oracle_identity 7)
