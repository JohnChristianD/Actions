:- module algebra_law_registry.

:- interface.

:- import_module list.
:- import_module string.

:- type law_kind
    ---> primitive_law
    ;   composition_law(int).

:- type algebra_law
    ---> algebra_law(
        string,      % name
        string,      % source module
        string,      % lhs signature
        string,      % rhs signature
        law_kind,
        list(string)
    ).

:- func algebra_law_registry = list(algebra_law).

:- pred registry_valid is semidet.
:- pred lookup_law(string::in, algebra_law::out) is semidet.
:- pred law_is_composition(algebra_law::in) is semidet.
:- pred law_is_nonreflexive(algebra_law::in) is semidet.

:- implementation.

algebra_law_registry = [
    algebra_law(
        "canonicalPolicy-norm-invariant",
        "Exotic.ERL.FullCoupled.CanonicalLearnerMonolith",
        "canonicalPolicy K (replaceNorm s n)",
        "canonicalPolicy K s",
        primitive_law,
        []),
    algebra_law(
        "canonicalCountStep-norm-invariant",
        "Exotic.ERL.FullCoupled.TheoremsMonolith",
        "canonicalCountStep K (replaceNorm s n)",
        "canonicalCountStep K s",
        primitive_law,
        []),
    algebra_law(
        "canonicalQLogStep-norm-invariant",
        "Exotic.ERL.FullCoupled.TheoremsMonolith",
        "canonicalQLogStep K (replaceNorm s n)",
        "canonicalQLogStep K s",
        primitive_law,
        []),
    algebra_law(
        "canonicalAttentionMix-clock-period4",
        "Exotic.ERL.FullCoupled.TheoremsMonolith",
        "canonicalAttentionMix K (replaceClock s (clock + 4))",
        "canonicalAttentionMix K s",
        primitive_law,
        []),
    algebra_law(
        "novel-clockPlus4-endogenousFeedback-invariant",
        "Exotic.ERL.FullCoupled.TheoremsMonolith",
        "canonicalEndogenousFeedback K (replaceClock s (clock + 4))",
        "canonicalEndogenousFeedback K s",
        primitive_law,
        ["canonicalAttentionMix-clock-period4"]),
    algebra_law(
        "canonicalWatkinsTarget-law",
        "Exotic.ERL.FullCoupled.CanonicalLearnerMonolith",
        "canonicalWatkinsTarget K s",
        "canonicalWatkinsExpanded K s",
        primitive_law,
        []),
    algebra_law(
        "endomorphismAssociative",
        "Exotic.ERL.FullCoupled.CanonicalLearnerMonolith",
        "compose (compose f g) h",
        "compose f (compose g h)",
        primitive_law,
        []),
    algebra_law(
        "recurrentPrefix-split",
        "Exotic.ERL.FullCoupled.CanonicalLearnerMonolith",
        "prefix (m + n)",
        "prefix n (prefix m)",
        primitive_law,
        []),
    algebra_law(
        "finiteReservoir-leftInverse",
        "Exotic.ERL.FullCoupled.TheoremsMonolith",
        "inverse (observe s)",
        "s",
        primitive_law,
        []),
    algebra_law(
        "int8-no-countably-unbounded-injective",
        "Exotic.ERL.FullCoupled.CanonicalLearnerMonolith",
        "injective Nat-to-Int8",
        "false",
        primitive_law,
        []),
    algebra_law(
        "canonicalPolicy-learnerReplacement-invariant",
        "Exotic.ERL.FullCoupled.TheoremsMonolith",
        "policy (applyLearnerReplacement r s)",
        "policy s",
        primitive_law,
        ["canonicalPolicy-norm-invariant"]),
    algebra_law(
        "canonicalPolicy-learnerReplacement-composition",
        "Exotic.ERL.FullCoupled.TheoremsMonolith",
        "policy (applyLearnerReplacements rs s)",
        "policy s",
        composition_law(2),
        ["canonicalPolicy-learnerReplacement-invariant",
         "canonicalPolicy-norm-invariant"]),
    algebra_law(
        "ring-+-assoc",
        "Algebra.Properties.Ring",
        "(x + y) + z",
        "x + (y + z)",
        primitive_law,
        []),
    algebra_law(
        "ring-+-comm",
        "Algebra.Properties.Ring",
        "x + y",
        "y + x",
        primitive_law,
        []),
    algebra_law(
        "ring-*-assoc",
        "Algebra.Properties.Ring",
        "(x * y) * z",
        "x * (y * z)",
        primitive_law,
        []),
    algebra_law(
        "ring-distrib",
        "Algebra.Properties.Ring",
        "x * (y + z)",
        "x * y + x * z",
        primitive_law,
        []),
    algebra_law(
        "ring--distribl-*",
        "Algebra.Properties.Ring",
        "- (x * y)",
        "- x * y",
        primitive_law,
        [])
].

law_is_nonreflexive(algebra_law(_, _, Lhs, Rhs, _, _)) :-
    Lhs = Rhs.

law_is_composition(algebra_law(_, _, _, _, composition_law(N), Dependencies)) :-
    N >= 2,
    list.length(Dependencies) >= 2.

law_is_composition(algebra_law(_, _, _, _, primitive_law, _)) :-
    fail.

lookup_law(Name, Law) :-
    list.member(Law, algebra_law_registry),
    Law = algebra_law(Name, _, _, _, _, _).

:- pred registry_valid_laws(list(algebra_law)::in) is semidet.
registry_valid_laws([]).
registry_valid_laws([Law | Laws]) :-
    law_is_nonreflexive(Law),
    (
        law_is_composition(Law)
    ;
        Law = algebra_law(_, _, _, _, primitive_law, _)
    ),
    registry_valid_laws(Laws).

registry_valid :-
    registry_valid_laws(algebra_law_registry).
