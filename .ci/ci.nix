{ writeShellApplication
, mercury
, gnumake
, git
, coreutils
, findutils
, gnugrep
}:

writeShellApplication {
  name = "actions-ci";
  runtimeInputs = [
    mercury
    gnumake
    git
    coreutils
    findutils
    gnugrep
  ];
  text = builtins.readFile ./ci.sh;
}
