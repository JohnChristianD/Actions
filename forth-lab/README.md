# Isolated Min / Forth / gbForth / Factor Lab

This folder is intentionally separate from the repository's canonical learner and proof surfaces.

The flake provisions Gforth and gbForth from Nixpkgs. Min is bootstrapped locally with Nimble the first time the shell is entered. Factor uses Nixpkgs' minimal Factor runtime on `x86_64-linux`; current Nixpkgs packages Factor for that host only.

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

Run Factor example:

```sh
factor examples/factor/hello.factor
```

Compile gbForth example:

```sh
gbforth examples/gbforth/hello.fs examples/gbforth/hello.gb
```

Run focused verification:

```sh
bash verify.sh
```

The verifier executes Min, Gforth, and Factor where supported. It also compiles the gbForth program and requires a non-empty ROM. The gbForth `main` initializes the font and terminal, positions the cursor, and renders `Hello World!`, so it is not an empty entry point.

Generated Min bootstrap state stays under `forth-lab/.min-runtime/` and generated gbForth ROM/symbol files stay ignored by this folder's `.gitignore`.

Min is a functional, concatenative language with postfix notation. Gforth provides a host Forth implementation. gbForth is a Forth-based Game Boy development kit. Factor is a concatenative, stack-based language with a compiled runtime.

This lab is an implementation playground only. It is not part of the repository's Agda proof authority, canonical learner semantics, or theorem extraction surface.

Upstream references:
- Min: https://min-lang.org/
- Factor: https://www.factorcode.org/
- gbForth hello world: https://gbforth.org/hello-world.html
