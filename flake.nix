{
  description = "my project description";

  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let pkgs = nixpkgs.legacyPackages.${system}; in
        let ec = pkgs.callPackage ./default.nix { nixpkgs = pkgs;};
        in {
          devShells.default = pkgs.mkShell {
            buildInputs = ec.buildInputs
              ++ ec.propagatedBuildInputs
              ++ (with pkgs.python3Packages; [
              pyyaml
            ]);
          };
        }

      );
}

