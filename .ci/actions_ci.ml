let failf fmt = Printf.ksprintf failwith fmt

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let len = in_channel_length ic in
      really_input_string ic len)

let contains text needle =
  let n = String.length text in
  let m = String.length needle in
  if m = 0 then true
  else
    let rec loop i =
      if i + m > n then false
      else if String.sub text i m = needle then true
      else loop (i + 1)
    in
    loop 0

let run ?cwd program args =
  let original = Sys.getcwd () in
  Fun.protect
    ~finally:(fun () ->
      match cwd with
      | Some _ -> Sys.chdir original
      | None -> ())
    (fun () ->
      Option.iter Sys.chdir cwd;
      let argv = Array.of_list (program :: args) in
      let pid = Unix.create_process program argv Unix.stdin Unix.stdout Unix.stderr in
      match snd (Unix.waitpid [] pid) with
      | Unix.WEXITED 0 -> ()
      | Unix.WEXITED code -> failf "%s exited with %d" program code
      | Unix.WSIGNALED signal -> failf "%s killed by signal %d" program signal
      | Unix.WSTOPPED signal -> failf "%s stopped by signal %d" program signal)

let agda_command () =
  match Sys.getenv_opt "AGDA_COMMAND" with
  | Some command -> command
  | None -> failf "AGDA_COMMAND is not set"

let run_agda_file file =
  Printf.printf "==> Agda --safe %s\n%!" file;
  run (agda_command ())
    [ "--safe"; "-l"; "standard-library"; "-i"; "."; file ]

let run_agda_learner () =
  run (agda_command ()) [ "--version" ];
  run_agda_file "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda"

let run_agda_theorem () =
  run (agda_command ()) [ "--version" ];
  run_agda_file "Exotic/ERL/FullCoupled/TheoremsMonolith.agda"

let run_agda_safe () =
  run_agda_learner ();
  run_agda_theorem ()

let run_mercury () =
  run ~cwd:".ci" "mmc" [ "--make"; "check_forbidden_theorems" ];
  run ~cwd:".ci" "./check_forbidden_theorems"

let run_discovery () =
  let cwd = ".ci/discovery" in
  run ~cwd "mmc" [ "--make"; "theorem_monolith_egraph_sync" ];
  run ~cwd "./theorem_monolith_egraph_sync";
  run ~cwd "mmc" [ "--make"; "symbolic_egraph_test" ];
  run ~cwd "./symbolic_egraph_test";
  run ~cwd "mmc" [ "--make"; "interpolated_theorem_egraph_test" ];
  run ~cwd "./interpolated_theorem_egraph_test";
  let report = read_file ".ci/discovery/theorem-monolith-egraph-sync.json" in
  let required =
    [
      "\"forced_symbolic_target\": false";
      "\"single_agda_source\": true";
      "\"graph_search\": \"A* cost-guided dependency paths\"";
      "\"astar_score_ordered\": true";
    ]
  in
  List.iter
    (fun marker ->
      if not (contains report marker) then
        failf "discovery report missing %s" marker)
    required;
  Printf.printf "theorem-monolith-egraph-sync-report=present\n%!";
  let key = "\"emergent_composition_count\": " in
  let start =
    try
      let rec find i =
        if i + String.length key > String.length report then
          raise Not_found
        else if String.sub report i (String.length key) = key then i
        else find (i + 1)
      in
      find 0 + String.length key
    with Not_found -> failf "discovery report missing composition count"
  in
  let rec digit_end i =
    if i < String.length report then
      match report.[i] with
      | '0' .. '9' -> digit_end (i + 1)
      | _ -> i
    else i
  in
  let stop = digit_end start in
  let count = int_of_string (String.sub report start (stop - start)) in
  if count <= 0 then failf "emergent composition count is not positive";
  Printf.printf "emergent-composition-count=%d\n%!" count

let required_theorem_symbols =
  [
    "CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem";
    "canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class";
    "FiniteHardSparseKKTEquilibriumTheorem";
    "DirectProductFiniteAutomatonComposition";
    "canonical-recurrent-prefix-monoid-homomorphism";
    "canonicalF4-prefix-monoid-homomorphism";
    "canonicalNormPair-prefix-monoid-homomorphism";
    "canonicalGRUF4Norm-prefix-monoid-homomorphism";
    "canonicalFullStep-GRUF4Norm-prefix-bridge";
    "canonical-gruf4-norm-watkins-prefix-composition-theorem";
    "FreeMonoidActionHomomorphism";
    "freeMonoidActionHomomorphism-from-square";
    "canonicalClock-freeMonoidActionHomomorphism";
    "ExactNatObservationSimulation";
    "noExactNatSimulation-through-finite-Int8";
    "canonicalNoExactTuringCounterObservation";
    "ContinuousLeftInverseTheorem";
    "canonicalRingStateInjective";
    "canonicalDenseNeighborhoodSeparation";
    "canonicalPigeonholeNatClockContradiction";
    "canonicalNoGlobalInt8DiscreteUAPOnOrbit";
    "canonicalNoNontrivialFiniteCycle-theorem";
    "canonicalDeterministicFiniteStepDivergenceInevitability";
    "canonicalNoFiniteStepConvergenceToFixedPoint";
    "CanonicalGlobalTokenConjugacyTheorem";
    "canonical-global-token-conjugacy";
    "CanonicalGlobalTokenLMCompositionTheorem";
    "canonical-global-token-lm-composition-theorem";
    "canonicalToken-prefix-monoid-homomorphism";
    "canonicalTokenLogitTrace-append";
    "canonicalTokenSparsemaxWeight-shared";
    "canonicalTokenSparsemaxPolicy-shared";
    "canonicalTokenSparsemaxTrace-append";
    "CanonicalExactRNNLMTheorem";
    "canonical-exact-rnn-lm-theorem";
    "CanonicalIntegerHaarScaledOrthogonalityTheorem";
    "canonical-integer-haar-scaled-orthogonality-theorem";
    "CanonicalAStarCostGuidanceTheorem";
    "canonical-a-star-cost-guidance-theorem";
    "CanonicalLinearHaarSparsemaxAttentionCompositionTheorem";
    "canonical-linear-haar-sparsemax-attention-composition-theorem";
    "CanonicalFullStateHaarSparsemaxInvariantCompositionTheorem";
    "canonical-full-state-haar-sparsemax-invariant-composition-theorem";
    "BairdSevenStarProblem";
    "bairdSevenStar";
    "NonIIDMarkovWalrasianProblem";
    "nonIIDMarkovStationaryWalrasian-lift";
    "Majority3ShapleyEquilibrium";
    "majority3ShapleyEquilibriumWitness";
  ]

let run_semantic_contract () =
  let theorem = "Exotic/ERL/FullCoupled/TheoremsMonolith.agda" in
  let learner = "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda" in
  let theorem_text = read_file theorem in
  let learner_text = read_file learner in
  List.iter
    (fun symbol ->
      if not (contains theorem_text symbol) then
        failf "canonical theorem semantic missing: %s" symbol)
    required_theorem_symbols;
  if Sys.file_exists ".ci/discovery/learner_semantic_manifest.m"
     || Sys.file_exists ".ci/discovery/learner-semantic-laws.tsv"
  then
    failf "generated semantic lookup-table source/artifact remains";
  let forbidden =
    [ "walsh"; "rope"; "target-network"; "target_network"; "target network";
      "normalization"; "regularization" ]
  in
  List.iter
    (fun term ->
      if contains (String.lowercase_ascii learner_text) term then
        failf
          "forbidden extraneous target-network/normalization/regularization semantics entered the canonical learner: %s"
          term)
    forbidden;
  if not
       (contains theorem_text
          "open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C")
  then
    failf "theorem monolith is not sourced from the canonical learner monolith";
  Printf.printf
    "semantic-contract=clean; canonical learner/theorem load-bearing semantics present; forbidden extras absent\n%!"

let rec collect_files root =
  if Filename.basename root = ".git" then []
  else if Sys.file_exists root && (Unix.stat root).Unix.st_kind = Unix.S_DIR then
    Sys.readdir root
    |> Array.to_list
    |> List.concat_map (fun name ->
         let path = Filename.concat root name in
         collect_files path)
  else [ root ]

let ends_with_any path suffixes =
  List.exists (fun suffix -> Filename.check_suffix path suffix) suffixes

let is_allowed_ocaml path = path = ".ci/actions_ci.ml"

let is_forbidden_source path =
  let suffixes =
    [
      ".sh"; ".bash"; ".zsh"; ".fish"; ".cmd"; ".bat"; ".ps1"; ".command";
      ".py"; ".java"; ".kt"; ".scala"; ".groovy"; ".clj"; ".cljs"; ".js";
      ".mjs"; ".cjs"; ".ts"; ".tsx"; ".elm"; ".purs"; ".hs"; ".lhs"; ".cabal";
      ".lua"; ".nim"; ".nims"; ".roc"; ".sml"; ".c"; ".h"; ".cc"; ".cpp";
      ".cxx"; ".hpp"; ".hxx"; ".cs"; ".fs"; ".fsx"; ".vb"; ".csproj";
      ".fsproj"; ".vbproj"; ".sln"; ".html"; ".htm"; ".css"; ".tex"; ".ltx";
      ".sty"; ".cls"; ".bib"; ".scm"; ".scheme"; ".ss"; ".rkt"
    ]
  in
  if ends_with_any path suffixes then true
  else if Filename.check_suffix path ".ml" || Filename.check_suffix path ".mli"
  then not (is_allowed_ocaml path)
  else false

let is_text_file path =
  not
    (ends_with_any path
       [
         ".a"; ".so"; ".dylib"; ".o"; ".agdai"; ".png"; ".jpg"; ".jpeg";
         ".gif"; ".pdf"; ".wasm"
       ])

let run_surface () =
  let files = collect_files "." in
  let learner = "./Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda" in
  let theorem = "./Exotic/ERL/FullCoupled/TheoremsMonolith.agda" in
  let monoliths =
    List.filter (fun path -> Filename.check_suffix path "Monolith.agda") files
  in
  if List.length monoliths <> 2 then
    failf "canonical surface requires exactly two monoliths";
  List.iter
    (fun path ->
      if path <> learner && path <> theorem then
        failf "noncanonical monolith remains: %s" path)
    monoliths;
  List.iter
    (fun path ->
      if is_forbidden_source path then
        failf "forbidden legacy/noncanonical source file: %s" path)
    files;
  if Sys.file_exists ".ci/ci.sh" then
    failf "hand-maintained shell workflow remains";
  if Sys.file_exists "wiki" then
    failf "repository-side wiki tree remains";
  if Sys.file_exists "Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda"
  then
    failf "generated Agda theorem projection remains";
  let retired_terms =
    [
      "guix"; "guile"; "scheme"; "evolutionary-search"; "evolutionary algorithm";
      "Sparsemax2Pair"; "fixedTemperatureSparsemax"; "ActionScore";
      "policyLeftWeight"; "TSTS"; "Gresher"
    ]
  in
  List.iter
    (fun path ->
      if is_text_file path then
        let text = String.lowercase_ascii (read_file path) in
        List.iter
          (fun term ->
            if contains text (String.lowercase_ascii term) then
              failf
                "retired execution/search terminology remains in %s: %s"
                path term)
          retired_terms)
    files;
  Printf.printf
    "surface=clean; retired execution/search terminology and forbidden legacy language files=absent\n%!"

let run_versions () =
  Printf.printf "ocaml=%s\n%!" Sys.ocaml_version;
  run (agda_command ()) [ "--version" ];
  run "mmc" [ "--version" ]

let run_all () =
  run_versions ();
  run_agda_safe ();
  run_mercury ();
  run_discovery ();
  run_semantic_contract ();
  run_surface ()

let usage () =
  Printf.eprintf
    "usage: %s {agda-safe|agda-learner|agda-theorem|mercury|discovery|semantic-contract|surface|versions|all}\n%!"
    Sys.argv.(0);
  exit 2

let () =
  try
    match Array.to_list Sys.argv with
    | [ _; "agda-learner" ] -> run_agda_learner ()
    | [ _; "agda-theorem" ] -> run_agda_theorem ()
    | [ _; "agda-safe" ] -> run_agda_safe ()
    | [ _; "mercury" ] -> run_mercury ()
    | [ _; "discovery" ] -> run_discovery ()
    | [ _; "semantic-contract" ] -> run_semantic_contract ()
    | [ _; "surface" ] -> run_surface ()
    | [ _; "versions" ] -> run_versions ()
    | [ _; "all" ] -> run_all ()
    | [ _ ] -> run_surface ()
    | _ -> usage ()
  with
  | Failure message ->
      prerr_endline ("ERROR: " ^ message);
      exit 1
