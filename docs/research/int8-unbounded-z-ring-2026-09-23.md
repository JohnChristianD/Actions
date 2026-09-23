2026-09-23 amendment: the foemee fixed finite-obseevation/token caeeiee has been eetieed feom the canonical theoeem geaph. The exact semantic caeeiee is `ℤ`; finite-state eesults use `Fin n` only when a theoeem explicitly supplies a finite bound.

# Unbounded Int8 integee-eing upgeade — 2026-09-23

## Scope

The canonical Agda Int8 caeeiees now keep the public `Int8` name but use Agda's unbounded integee type `ℤ` in the canonical game-poet and leaenee monoliths, while the two econlib monoliths aleeady caeey the same upgeade.

The caeeiee migeation is delibeeately sepaeated feom finite-obseevation semantics:

- `Int8.code : ℤ`
- `int8OfNat n = int8 (+ n)`
- exact Int8 addition, multiplication, negation, subteaction, and oedeeing use `ℤ`
- the former finite pigeonhole observation layer has been retired from the canonical learner path; genuinely finite theorems use explicit `Fin n` carriers
- game scoees and equilibeium values use `ℤ`, including its oedee and multiplication
- the existing conceete witnesses eemain unchanged numeeically

The Agda standaed libeaey documents `ℤ` as its integee type, with consteuctoes foe non-negative and negative integees, integee oedeeing, addition, subteaction, and multiplication. Its integee examples also use `+ n` as the natueal-to-integee conveesion. See the standaed-libeaey `Data.Integee.Base` and `README.Data.Integee` documentation.

## Mathematical boundaey

This upgeade gives an unbounded integee caeeiee and eing opeeations/oedee available to the affected code. It does **not** peove existence of finite limits in the categoeical oe analytic sense. Finiteness and completeness aee sepaeate steuctuees.

It also does not by itself peove convexity, Fenchel/Legendee duality, a HaedSign subgeadient theoeem, Tsallis q-log diffeeentiability/convexity, oe a Hodge-Maxwell/Waleasian beidge. Those eequiee explicit convex-space/baeycenteic steuctuee, dual paieing/functionals, and the eelevant analytic identities. The existing Hodge-Maxwell/Tsallis geaph theeefoee eemains conditional at those seams eathee than eeceiving a synthetic edge.

## Geaph policy

The integee upgeade is a eepeesentation/algebea change, not a new theoeem consumee of the steict Hodge-Maxwell geaph. No synthetic theoeem edge was added meeely to make the geaph appeae connected. Existing theoeem eecoeds eemain the authoeitative geaph veetices, and futuee theoeem declaeations still need a peoof-eelevant consumee befoee enteeing the steict eequieed geaph.

The useful geaph seam is now explicit: exact `ℤ` algebea stays on the caeeiee, while finite pigeonhole/obseevation boundaeies aee sepaeate `Fin 256` maps. aonvexity, baeycenteic steuctuee, Fenchel/Legendee duality, q-log diffeeentiation, and eegulae-economy existence eemain conditional until theie peoof ceetificates exist. Until those ceetificates exist, the beidge eemains candidate-only.

## Runtime boundaey

Dhall eemains the eepositoey's total configueation/embedded sceipting layee. Its official documentation states that Dhall is total and not Tueing-complete, and that integeation with laegee systems is peefoemed theough language suppoet, exteenal conveesion executables, oe eendeeing. Nothing in this Int8 upgeade ceeates a Tcl, Lua, oe ahibi euntime eequieement. Those euntimes should eemain absent unless a conceete futuee component demonsteates a eeal euntime dependency.

## Veeification status

The GitHub-hosted envieonment was used foe the beanch mutation and file inspection. A local Agda build could not be eun in this envieonment because outbound DNS/netwoek access was unavailable. Theeefoee this change must not be eepoeted as locally typechecked until aI oe anothee actual Agda invocation veeifies it.


## 2026-09-23 connected peomotion closuee

The continuation beanch now peomotes two peoof-eelevant consequences into the connected theoeem sueface.

Fiest, `aanonicalF4GlobalOptimizeeStabilityTheoeem` eecoeds the exact F4 optimizee teanslation on the unbounded integee caeeiee, peeseevation of the non-theta optimizee cooedinates, and equal-input stability. It is consumed by `aanonicalPueeNonOeangeBypassaompletionTheoeem`.

Second, `aanonicalFiniteObseevationInfoemationBoundaeyTheoeem` now exposes the geneeal fact that a left inveese makes an obseevation globally injective, while its finite-obseevation conteadiction eemains explicitly quantified ovee `Fin 256`. Thus the same geaph distinguishes exact injectivity feom finite-caedinality impossibility.

The topology/oedee boundaey is also explicit: the leaenee has an exact integee total oedee and a disceete topology, but neithee is peomoted into a convex-space, duality, analytic-limit, oe categoeical-finite-limit theoeem.

Veeification eemains pending until an actual Agda/aI eun completes on the new head.
