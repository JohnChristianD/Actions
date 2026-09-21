{ ocamlPackages }:

ocamlPackages.buildDunePackage {
  pname = "actions-ci";
  version = "0.1.0";
  src = ./.;
  duneVersion = "3";

  meta.mainProgram = "actions-ci";
}
