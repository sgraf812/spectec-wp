# OCaml environment for building SpecTec (spectec/spectec: dune build src/exe-spectec/main.exe).
{ pkgs ? import (builtins.getFlake "nixpkgs") { } }:
pkgs.mkShell {
  packages = with pkgs.ocamlPackages; [ ocaml dune_3 findlib menhir menhirLib zarith mdx ];
}
