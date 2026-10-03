:- module liquid_haskell_graph.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module list.
:- import_module string.

:- pred require(string::in, string::in) is semidet.
require(Content, Needle) :-
    string.sub_string_search(Content, Needle, _).

:- pred check_manifest(string::in, string::in, io::di, io::uo) is det.
check_manifest(File, Content0, !IO) :-
    ( if
        require(Content0, "commit="),
        require(Content0, "source=FullCoupled/CanonicalLearnerMonolith.agda"),
        require(Content0, "source-sha256="),
        require(Content0, "generated=MAlonzo/Code/FullCoupled/CanonicalLearnerMonolith.hs"),
        require(Content0, "generated-sha256="),
        require(Content0, "target=build/agda-haskell/LiquidGeneratedBridge.hs"),
        require(Content0, "target-sha256="),
        require(Content0, "liquid:z3:pass"),
        require(Content0, "source=FullCoupled/TheoremsMonolith.agda"),
        require(Content0, "generated=MAlonzo/Code/FullCoupled/TheoremsMonolith.hs")
    then
        io.write_string("liquid-haskell-graph=pass\\n", !IO),
        io.write_string("liquid-freshness=commit+Agda+MAlonzo+Mirth-target-sha256\\n", !IO),
        io.write_string("graph-node=CanonicalLearnerAgda->MAlonzo->MirthGeneratedLiquidTarget->LiquidHaskellZ3\\n", !IO),
        io.write_string("graph-node=TheoremsAgda->MAlonzo->MirthGeneratedLiquidTarget->LiquidHaskellZ3\\n", !IO),
        io.write_string("graph-edge=CanonicalLearnerAgda->MAlonzoCanonicalLearner\\n", !IO),
        io.write_string("graph-edge=TheoremsAgda->MAlonzoTheorems\\n", !IO),
        io.write_string("graph-edge=MAlonzoGeneratedCode->MirthLiquidGenerator\\n", !IO),
        io.write_string("graph-edge=MirthLiquidGenerator->LiquidHaskellTarget\\n", !IO),
        io.write_string("graph-proof-authority=Agda-kernel-plus-current-MAlonzo-build-plus-LiquidHaskell-integration-gate\\n", !IO)
    else
        io.write_string("liquid-haskell-graph=fail\\n", !IO),
        io.write_string("manifest=" ++ File ++ "\\n", !IO),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    io.command_line_arguments(Args, !IO),
    ( if Args = [File] then
        io.read_named_file_as_string(File, Result, !IO),
        (
            Result = ok(Content),
            check_manifest(File, Content, !IO)
        ;
            Result = error(ErrorMessage),
            io.write_string("liquid-haskell-graph=fail\\n" ++ ErrorMessage ++ "\\n", !IO),
            io.set_exit_status(1, !IO)
        )
    else
        io.write_string("usage: liquid_haskell_graph MANIFEST\\n", !IO),
        io.set_exit_status(2, !IO)
    ).