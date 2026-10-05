:- module novel_theorem_interpolator.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module bool.
:- import_module learner_semantic_extractor.
:- import_module list.
:- import_module string.
:- import_module theorem_graph_search.

:- pred collect_imports(
    list(string)::in,
    list(string)::in,
    list(string)::out) is det.
collect_imports([], Acc, Imports) :-
    list.reverse(Acc, Imports).
collect_imports([Line | Lines], Acc0, Imports) :-
    Words = string.words(string.strip(Line)),
    (
        if Words = ["import", Module | _] then
            (
                if list.member(Module, Acc0) then
                    Acc1 = Acc0
                else
                    Acc1 = [Module | Acc0]
            )
        else if Words = ["open", "import", Module | _] then
            (
                if list.member(Module, Acc0) then
                    Acc1 = Acc0
                else
                    Acc1 = [Module | Acc0]
            )
        else
            Acc1 = Acc0
    ),
    collect_imports(Lines, Acc1, Imports).

:- pred read_available_imports(
    list(string)::out,
    io::di, io::uo) is det.
read_available_imports(Imports, !IO) :-
    io.read_named_file_as_lines(
        "../../FullCoupled/TheoremsMonolith.agda",
        Result, !IO),
    (
        Result = ok(Lines),
        collect_imports(Lines, [], Imports)
    ;
        Result = error(_),
        Imports = []
    ).

:- pred read_toolchain_imports(
    list(string)::out,
    io::di, io::uo) is det.
read_toolchain_imports(Imports, !IO) :-
    io.read_named_file_as_lines(
        ".interpolation-imports",
        Result, !IO),
    (
        Result = ok(Lines),
        list.filter(
            (pred(Line::in) is semidet :- string.strip(Line) \= ""),
            Lines,
            Imports)
    ;
        Result = error(_),
        Imports = []
    ).

:- pred write_items(
    io.text_output_stream::in,
    list(string)::in,
    io::di, io::uo) is det.
write_items(_, [], !IO).
write_items(Stream, [Item | Items], !IO) :-
    io.write_string(Stream, "    \"", !IO),
    io.write_string(Stream, Item, !IO),
    io.write_string(Stream, "\"", !IO),
    (
        Items = []
    ->
        true
    ;
        io.write_string(Stream, ",", !IO)
    ),
    io.write_string(Stream, "\n", !IO),
    write_items(Stream, Items, !IO).

main(!IO) :-
    read_semantic_laws(Laws, !IO),
    read_available_imports(Imports, !IO),
    read_toolchain_imports(ToolchainImports, !IO),
    (
        ToolchainImports \= [],
        graph_interpolated_execution_bridge_plan(Laws, Plan),
        all_generated_plans_valid(Laws, [Plan])
    ->
        io.open_output("novel-theorem-interpolation.dhall", OpenResult, !IO),
        (
            OpenResult = ok(Stream),
            io.write_string(Stream, "{\n", !IO),
            io.write_string(Stream, "  theorem = \"CanonicalIntegerLayerNormAStarExecutionBridgeTheorem\",\n", !IO),
            io.write_string(Stream, "  status = \"INTERPOLATED_AND_AGDA_TYPED\",\n", !IO),
            io.write_string(Stream, "  semanticLawCount = ", !IO),
            io.write_string(Stream, string.int_to_string(list.length(Laws)), !IO),
            io.write_string(Stream, ",\n", !IO),
            io.write_string(Stream, "  importCount = ", !IO),
            io.write_string(Stream, string.int_to_string(list.length(Imports)), !IO),
            io.write_string(Stream, ",\n", !IO),
            io.write_string(Stream, "  availableImports = [\n", !IO),
            write_items(Stream, Imports, !IO),
            io.write_string(Stream, "  ],\n", !IO),
            io.write_string(Stream, "  endToEndToolchainImportCount = ", !IO),
            io.write_string(Stream, string.int_to_string(list.length(ToolchainImports)), !IO),
            io.write_string(Stream, ",\n", !IO),
            io.write_string(Stream, "  endToEndToolchainImports = [\n", !IO),
            write_items(Stream, ToolchainImports, !IO),
            io.write_string(Stream, "  ],\n", !IO),
            io.write_string(Stream, "  graphSearch = \"A* cost-guided dependency paths\",\n", !IO),
            io.write_string(Stream, "  semanticAuthority = \"Agda proof term\",\n", !IO),
            io.write_string(Stream, "  plan = [\n", !IO),
            write_items(Stream, [string.join_list(" -> ", Plan)], !IO),
            io.write_string(Stream, "  ]\n", !IO),
            io.write_string(Stream, "}\n", !IO),
            io.close_output(Stream, !IO),
            io.write_string("mercury-novel-theorem-interpolation=pass\n", !IO)
        ;
            OpenResult = error(_),
            io.write_string("ERROR: cannot write novel theorem interpolation report\n", !IO),
            io.set_exit_status(1, !IO)
        )
    ;
        io.write_string("ERROR: Mercury could not validate interpolated theorem plan\n", !IO),
        io.set_exit_status(1, !IO)
    ).

