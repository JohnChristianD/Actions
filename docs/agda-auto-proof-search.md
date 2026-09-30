# Agda proof search in this repository

Agda provides two native interactive search tools that serve different roles: Auto and Search About. Neither is a compiler pragma or a replacement for the repository's batch `--safe` proof gate.

## Auto

Agda Auto is its native general-purpose proof-search facility. In Agda 2.8.0 it is invoked with `C-c C-a` from an interactive goal. Auto searches for a type inhabitant, and any solution it proposes is checked by Agda before it is accepted.

Repository policy:
- Keep theorem authority in `--safe` Agda source.
- Use Auto interactively to discover small proof terms, helper lemmas, or proof decompositions.
- Do not commit unresolved holes to the theorem monolith.
- Prefer a named theorem declaration over opaque editor state when an Auto result becomes part of the proof surface.
- Use the Mercury graph to search the resulting named theorem dependencies; Mercury does not replace Agda proof checking.

## Search About

Search About is Agda's scope-aware definition search. Invoke it with `C-c C-z`. It accepts space-separated identifiers and string literals, then returns in-scope definitions whose types contain the requested identifiers and whose names match the supplied string-literal substrings.

Use Search About before Auto when the problem is primarily "which existing definition should I try?"; use Auto when the candidate definitions are known or discoverable and the remaining task is to assemble a term.

Typical workflow:
1. Start the pinned interactive session with `bash tools/agda-auto-session.sh Exotic/ERL/FullCoupled/TheoremsMonolith.agda`.
2. Use Search About (`C-c C-z`) to locate definitions by domain/type vocabulary or name fragments.
3. Place the cursor on the target hole and use Auto (`C-c C-a`) with explicit hints when needed.
4. Copy the accepted term into the theorem source.
5. Run the normal repository canonical-learner `--safe` check; the theorem monolith uses its explicit external-integration flags rather than a second Agda version.

Search About is an interactive discovery tool. This repository does not treat its output, or Auto's interactive output, as CI proof authority.

## Presentation synchronization

The theorem proof surface remains exactly two monoliths. The theorem monolith contains the scripted Schmitty and Vehicle imports; Pages is a separate static presentation. Mirth remains a fast-dirty synchronization source rather than a proof or Pages compiler dependency.

## Pinned toolchain

- Agda 2.8.0
- agda-stdlib 2.3

The local launcher supplies the repository source path, standard library package, and interactive mode. It is intentionally small so the same session can be used for both Auto and Search About.

## Staleness

Recheck this document when the pinned Agda version, the interaction commands, the theorem-monolith proof workflow, or the static Elm presentation contract changes.
