{
  description = "Opam setup for kot-proof";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
    newpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
  };

  outputs = { self, nixpkgs, newpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        npkgs = import newpkgs { inherit system; };
      
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.opam pkgs.pkg-config pkgs.gmp pkgs.cmake
          ];

          shellHook = ''
            # TODO: opam setup
            export OPAMSWITCH=rocq9
            eval $(opam env)
          '';
        };
      });
}
