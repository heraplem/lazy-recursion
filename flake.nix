{
  description = "Description for the project";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = inputs@{ flake-parts, ... }: flake-parts.lib.mkFlake { inherit inputs; } {
    systems = [ "x86_64-linux" ];
    perSystem = { pkgs, ... }: {
      devShells.default = pkgs.mkShell {
        packages = [
          (pkgs.coq.withPackages (coqPkgs: [
            coqPkgs.ITree
          ]))
        ];
      };
    };
  };
}
