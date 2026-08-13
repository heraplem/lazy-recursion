{
  description = "Description for the project";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-24.11;
    flake-parts.url = "github:hercules-ci/flake-parts";
    gitrees.url = "github:logsem/gitrees";
    gitrees.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = inputs@{ self, flake-parts, ... }: flake-parts.lib.mkFlake { inherit inputs; } {
    # NOTE Add systems as tested.
    systems = [ "x86_64-linux" ];
    perSystem = { system, inputs', pkgs, ... }: let
      coqPkgsName = "coqPackages_8_20";
      coqPkgs = pkgs.${coqPkgsName};
    in {
      _module.args.pkgs = import inputs.nixpkgs {
        inherit system;
        overlays = [
          (final: prev: {
            ${coqPkgsName} = prev.${coqPkgsName}.overrideScope (final: prev: {
              gitrees = inputs'.gitrees.packages.coq-artifact;
            });
          })
        ];
      };
      devShells.default = pkgs.mkShell {
        packages = [
          coqPkgs.coq
          coqPkgs.ExtLib
          coqPkgs.ITree
          coqPkgs.gitrees
        ];
      };
    };
  };
}
