# Isolated Min / Forth / gbForth Lab

This folder is intentionally separate from the repository's canonical learner and proof surfaces.

The flake provisions Gforth and gbForth from Nixpkgs. Min is bootstrapped locally with Nimble the first time the shell is entered, because the current Nixpkgs package set does not provide the Min language as a maintained package.

Enter environment:

```sh
cd forth-lab
nix develop
```

Run Min example:

```sh
min examples/min/squares.min
```

Run Gforth example:

```sh
gforth examples/gforth/hello.fs
```

Compile gbForth example:

```sh
gbforth examples/gbforth/hello.fs examples/gbforth/hello.gb
```

Generated Min bootstrap state stays under `forth-lab/.min-runtime/` and is not part of the tracked source surface.

Min is a functional, concatenative language with postfix notation. Gforth provides a host Forth implementation. gbForth is a Forth-based Game Boy development kit.

This lab is an implementation playground only. It is not part of the repository's Agda proof authority, canonical learner semantics, or theorem extraction surface.
