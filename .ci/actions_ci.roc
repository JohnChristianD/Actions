app [main!] {
    cli: platform "https://github.com/roc-lang/basic-cli/releases/download/0.20.0/X73hGh05nNTkDHU06FHC0YfFaQB1pimX7gncRcao5mU.tar.br",
}

import cli.Arg exposing [Arg]
import cli.Cmd
import cli.Env
import cli.File
import cli.OsStr
import cli.Stderr
import cli.Stdout

required_theorem_symbols : List Str
required_theorem_symbols = [
    "CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem",
    "canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class",
    "FiniteHardSparseKKTEquilibriumTheorem",
    "DirectProductFiniteAutomatonComposition",
    "canonical-recurrent-prefix-monoid-homomorphism",
    "canonicalF4-prefix-monoid-homomorphism",
    "canonicalNormPair-prefix-monoid-homomorphism",
    "canonicalGRUF4Norm-prefix-monoid-homomorphism",
    "canonicalFullStep-GRUF4Norm-prefix-bridge",
    "canonical-gruf4-norm-watkins-prefix-composition-theorem",
    "FreeMonoidActionHomomorphism",
    "freeMonoidActionHomomorphism-from-square",
    "canonicalClock-freeMonoidActionHomomorphism",
    "ExactNatObservationSimulation",
    "noExactNatSimulation-through-finite-Int8",
    "canonicalNoExactTuringCounterObservation",
    "ContinuousLeftInverseTheorem",
    "canonicalRingStateInjective",
    "canonicalDenseNeighborhoodSeparation",
    "canonicalPigeonholeNatClockContradiction",
    "canonicalNoGlobalInt8DiscreteUAPOnOrbit",
    "canonicalNoNontrivialFiniteCycle-theorem",
    "canonicalDeterministicFiniteStepDivergenceInevitability",
    "canonicalNoFiniteStepConvergenceToFixedPoint",
    "CanonicalGlobalTokenConjugacyTheorem",
    "canonical-global-token-conjugacy",
    "CanonicalGlobalTokenLMCompositionTheorem",
    "canonical-global-token-lm-composition-theorem",
    "canonicalToken-prefix-monoid-homomorphism",
    "canonicalTokenLogitTrace-append",
    "canonicalTokenSparsemaxWeight-shared",
    "canonicalTokenSparsemaxPolicy-shared",
    "canonicalTokenSparsemaxTrace-append",
    "CanonicalExactRNNLMTheorem",
    "canonical-exact-rnn-lm-theorem",
    "CanonicalIntegerHaarScaledOrthogonalityTheorem",
    "canonical-integer-haar-scaled-orthogonality-theorem",
    "CanonicalAStarCostGuidanceTheorem",
    "canonical-a-star-cost-guidance-theorem",
    "CanonicalLinearHaarSparsemaxAttentionCompositionTheorem",
    "canonical-linear-haar-sparsemax-attention-composition-theorem",
    "CanonicalFullStateHaarSparsemaxInvariantCompositionTheorem",
    "canonical-full-state-haar-sparsemax-invariant-composition-theorem",
    "BairdSevenStarProblem",
    "bairdSevenStar",
    "NonIIDMarkovWalrasianProblem",
    "nonIIDMarkovStationaryWalrasian-lift",
    "Majority3ShapleyEquilibrium",
    "majority3ShapleyEquilibriumWitness",
]

forbidden_source_suffixes : List Str
forbidden_source_suffixes = [
    ".sh", ".bash", ".zsh", ".fish", ".cmd", ".bat", ".ps1", ".command",
    ".py", ".java", ".kt", ".scala", ".groovy", ".clj", ".cljs", ".js",
    ".mjs", ".cjs", ".ts", ".tsx", ".elm", ".purs", ".hs", ".lhs", ".cabal",
    ".lua", ".nim", ".nims", ".rocx", ".ml", ".mli", ".sml",
    ".c", ".h", ".cc", ".cpp", ".cxx", ".hpp", ".hxx", ".cs", ".fs", ".fsx",
    ".vb", ".csproj", ".fsproj", ".vbproj", ".sln",
    ".html", ".htm", ".css", ".tex", ".ltx", ".sty", ".cls", ".bib",
    ".scm", ".scheme", ".ss", ".rkt",
]

text_suffixes : List Str
text_suffixes = [
    ".agda", ".md", ".nix", ".roc", ".m", ".yml", ".yaml", ".toml", ".json", ".txt",
]

retired_terms : List Str
retired_terms = [
    "guix", "guile", "scheme", "evolutionary-search", "evolutionary algorithm",
    "sparsemax2pair", "fixedtemperaturesparsemax", "actionscore",
    "policyleftweight", "tsts", "gresher",
]

run! : Str, List Str => Try({}, _)
run! = |program, args| Cmd.exec!(program, args)

agda_program! : {} => Try(Str, _)
agda_program! = |{}| {
    env_value = Env.var!(OsStr.from_str("AGDA_COMMAND"))?
    Ok(OsStr.display(env_value))
}

run_agda_file! : Str => Try({}, _)
run_agda_file! = |file_path| {
    agda = agda_program!({})?
    Stdout.line!("==> Agda --safe \${file_path}")?
    run!(agda, ["--safe", "-l", "standard-library", "-i", ".", file_path])?
    Ok({})
}

run_agda_learner! : {} => Try({}, _)
run_agda_learner! = |{}| {
    run_agda_file!("Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda")?
    Ok({})
}

run_agda_theorem! : {} => Try({}, _)
run_agda_theorem! = |{}| {
    run_agda_file!("Exotic/ERL/FullCoupled/TheoremsMonolith.agda")?
    Ok({})
}

run_agda_safe! : {} => Try({}, _)
run_agda_safe! = |{}| {
    run_agda_learner!({})?
    run_agda_theorem!({})?
    Ok({})
}

run_mercury! : {} => Try({}, _)
run_mercury! = |{}| {
    run!("mmc", ["--make", ".ci/check_forbidden_theorems"])?
    run!("./.ci/check_forbidden_theorems", [])?
    Ok({})
}

run_discovery! : {} => Try({}, _)
run_discovery! = |{}| {
    run!("mmc", ["--make", ".ci/discovery/theorem_monolith_egraph_sync"])?
    run!("./.ci/discovery/theorem_monolith_egraph_sync", [])?
    run!("mmc", ["--make", ".ci/discovery/symbolic_egraph_test"])?
    run!("./.ci/discovery/symbolic_egraph_test", [])?
    run!("mmc", ["--make", ".ci/discovery/interpolated_theorem_egraph_test"])?
    run!("./.ci/discovery/interpolated_theorem_egraph_test", [])?

    report = File.read_utf8!(".ci/discovery/theorem-monolith-egraph-sync.json")?
    if Str.contains(report, "\"forced_symbolic_target\": true") then
        Err(ForcedSymbolicTarget)
    else if Str.contains(report, "\"single_agda_source\": false") then
        Err(NonCanonicalAgdaSource)
    else if !Str.contains(report, "\"graph_search\": \"A* cost-guided dependency paths\"") then
        Err(MissingAStarGraphLabel)
    else if !Str.contains(report, "\"astar_score_ordered\": true") then
        Err(AStarOrderGateFailed)
    else if Str.contains(report, "\"emergent_composition_count\": 0") then
        Err(NoEmergentComposition)
    else
        Ok({})
}

check_symbols! : List Str, Str => Result {}, _
check_symbols! = |symbols, source| {
    when symbols is
        [] -> Ok({})
        [symbol, ..rest] ->
            if Str.contains(source, symbol) then
                check_symbols!(rest, source)
            else
                Err(MissingTheoremSymbol(symbol))
}

path_has_suffix! : Str, List Str -> Bool
path_has_suffix! = |path, suffixes| {
    suffixes.any(|suffix| Str.ends_with(path, suffix))
}

is_text_path! : Str -> Bool
is_text_path! = |path| {
    path_has_suffix!(path, text_suffixes)
}

validate_source_path! : Str => Result {}, _
validate_source_path! = |path| {
    if path_has_suffix!(path, forbidden_source_suffixes) then
        Err(ForbiddenSource(path))
    else
        Ok({})
}

check_source_paths! : List Str => Result {}, _
check_source_paths! = |paths| {
    when paths is
        [] -> Ok({})
        [path, ..rest] ->
            validate_source_path!(path)?
            check_source_paths!(rest)
}

check_retired_terms_in_file! : Str => Result {}, _
check_retired_terms_in_file! = |path| {
    if !is_text_path!(path) then
        Ok({})
    else
        text = File.read_utf8!(path)?
        check_retired_terms_in_text!(retired_terms, path, text)
}

check_retired_terms_in_text! : List Str, Str, Str => Result {}, _
check_retired_terms_in_text! = |terms, path, text| {
    when terms is
        [] -> Ok({})
        [term, ..rest] ->
            lower_text = Str.with_ascii_lowercased(text)
            lower_term = Str.with_ascii_lowercased(term)
            if Str.contains(lower_text, lower_term) then
                Err(RetiredTerm(path, term))
            else
                check_retired_terms_in_text!(rest, path, text)
}

check_retired_terms_in_files! : List Str => Result {}, _
check_retired_terms_in_files! = |files| {
    when files is
        [] -> Ok({})
        [path, ..rest] ->
            check_retired_terms_in_file!(path)?
            check_retired_terms_in_files!(rest)
}

run_semantic_contract! : {} => Try({}, _)
run_semantic_contract! = |{}| {
    theorem_path = "Exotic/ERL/FullCoupled/TheoremsMonolith.agda"
    learner_path = "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda"
    theorem_text = File.read_utf8!(theorem_path)?
    learner_text = File.read_utf8!(learner_path)?

    check_symbols!(required_theorem_symbols, theorem_text)?

    if File.is_file!(".ci/discovery/learner_semantic_manifest.m")? then
        Err(GeneratedSemanticLookupTable)
    else if File.is_file!(".ci/discovery/learner-semantic-laws.tsv")? then
        Err(GeneratedSemanticLawArtifact)
    else if Str.contains(Str.with_ascii_lowercased(learner_text), "walsh") then
        Err(ForbiddenWalsh)
    else if Str.contains(Str.with_ascii_lowercased(learner_text), "rope") then
        Err(ForbiddenRope)
    else if Str.contains(Str.with_ascii_lowercased(learner_text), "target-network") then
        Err(ForbiddenTargetNetwork)
    else if Str.contains(Str.with_ascii_lowercased(learner_text), "target_network") then
        Err(ForbiddenTargetNetwork)
    else if Str.contains(Str.with_ascii_lowercased(learner_text), "target network") then
        Err(ForbiddenTargetNetwork)
    else if Str.contains(Str.with_ascii_lowercased(learner_text), "normalization") then
        Err(ForbiddenNormalization)
    else if Str.contains(Str.with_ascii_lowercased(learner_text), "regularization") then
        Err(ForbiddenRegularization)
    else if !Str.contains(theorem_text, "open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C") then
        Err(NonCanonicalTheoremSource)
    else
        Ok({})
}

run_surface! : {} => Try({}, _)
run_surface! = |{}| {
    listing = Cmd.new("git") |> Cmd.args(["ls-files"]) |> Cmd.exec_output!()?
    files = Str.split_on(Str.trim(listing.stdout_utf8), "\n")

    monoliths = files.keep_if(|path| Str.ends_with(path, "Monolith.agda"))
    if monoliths.len() != 2 then
        Err(NonCanonicalMonolithCount)
    else
        check_source_paths!(files)?
        check_retired_terms_in_files!(files)?

        if !files.contains(".ci/actions_ci.roc") then
            Err(MissingRocOrchestrator)
        else
            Ok({})
}

run_versions! : {} => Try({}, _)
run_versions! = |{}| {
    agda = agda_program!({})?
    run!(agda, ["--version"])?
    run!("mmc", ["--version"])?
    Ok({})
}

run_lane! : Str => Try({}, _)
run_lane! = |lane| {
    when lane is
        "agda-learner" -> run_agda_learner!({})
        "agda-theorem" -> run_agda_theorem!({})
        "agda-safe" -> run_agda_safe!({})
        "mercury" -> run_mercury!({})
        "discovery" -> run_discovery!({})
        "semantic-contract" -> run_semantic_contract!({})
        "surface" -> run_surface!({})
        "versions" -> run_versions!({})
        "all" -> {
            run_versions!({})?
            run_agda_safe!({})?
            run_mercury!({})?
            run_discovery!({})?
            run_semantic_contract!({})?
            run_surface!({})
        }
        _ -> Err(UnknownLane(lane))
}

main! : List Arg => Try({}, [Exit(I32), ..])
main! = |raw_args| {
    args = raw_args.map(Arg.display)

    lane = List.get(args, 1) ? |{}|
        Err(InvalidInvocation)

    run_lane!(lane)?
    Stdout.line!("lane=\${lane}")?
    Ok({})
}
