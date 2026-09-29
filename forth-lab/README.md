# Isolated Min / Forth / gbForth / Factor / Pony Lab

This folder is intentionally separate from the repository's canonical learner and proof surfaces.

The flake provisions Gforth, gbForth, and Pony from Nixpkgs 26.05. Min is bootstrapped locally with Nimble the first time the shell is entered. Factor uses Nixpkgs' minimal Factor runtime on `x86_64-linux`.

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

Compile and run Pony example:

```sh
cd examples/ponyc/hello
ponyc
./hello
cd ../../..
```

Run focused verification:

```sh
bash verify.sh
```

The verifier executes Min, Gforth, Factor where supported, compiles gbForth to a non-empty ROM, and compiles and runs Pony from an isolated temporary copy. Pony's `Main` constructor is the executable entry point.

Generated Min bootstrap state stays under `forth-lab/.min-runtime/`. Generated gbForth ROM/symbol files are ignored by this folder's `.gitignore`.

Min is a functional, concatenative language with postfix notation. Gforth provides a host Forth implementation. gbForth is a Forth-based Game Boy development kit. Factor is a concatenative, stack-based language. Pony is an ahead-of-time compiled actor-model language.

This lab is an implementation playground only. It is not part of the repository's Agda proof authority, canonical learner semantics, or theorem extraction surface.

Upstream references:
- Min: https://min-lang.org/
- Factor: https://www.factorcode.org/
- Pony hello world: https://tutorial.ponylang.io/getting-started/hello-world.html
- gbForth hello world: https://gbforth.org/hello-world.html
