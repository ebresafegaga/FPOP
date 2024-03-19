{
  description = "FPOP";

  inputs = {
    nixpkgs.url = "nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";    
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; overlays = [ ]; };
        ocamlDeps = with pkgs.ocaml-ng.ocamlPackages_4_13; [
          ocaml
          ocaml-lsp          
          dune_3
          utop
          merlin
          pkgs.coq_8_15
        ];
      in
        {
          devShell = pkgs.mkShell {
            buildInputs = ocamlDeps;
          };
        }
    );
}
