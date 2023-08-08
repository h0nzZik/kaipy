{
  description = "An abstract interpreter based on the K framework";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.05";
    flake-utils.url = "github:numtide/flake-utils";
    pyk.url = "github:runtimeverification/pyk/v0.1.397";
    k-framework.url = "github:runtimeverification/k/v6.0.42";
    k-framework.inputs.nixpkgs.follows = "nixpkgs";
    pyk.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self,flake-utils, nixpkgs, pyk, k-framework, ...}:
    ({
      overlay = final: prev:
        let
          #python = prev.python311;
          python = prev.pyk-python311.python;
          k = k-framework.packages.${prev.system}.k;
          kaipy = python.pkgs.buildPythonApplication {
              name = "kaipy";
              src = ./kaipy;
              format = "pyproject";
              propagatedBuildInputs = [
                k
                prev.pyk-python311
                python.pkgs.setuptools
                python.pkgs.networkx
                python.pkgs.immutabledict
                python.pkgs.pytest
                python.pkgs.multiprocess
              ];
              postInstall = ''
                substituteInPlace $out/lib/*/site-packages/kaipy/kcommands.py \
                  --replace "\"kompile\"" "\"${k}/bin/kompile\""
                substituteInPlace $out/lib/*/site-packages/kaipy/kcommands.py \
                  --replace "\"kprove\"" "\"${k}/bin/kprove\""
                substituteInPlace $out/lib/*/site-packages/kaipy/kcommands.py \
                  --replace "\"krun\"" "\"${k}/bin/krun\""
                substituteInPlace $out/lib/*/site-packages/kaipy/kcommands.py \
                  --replace "\"kore-rpc\"" "\"${k}/bin/kore-rpc\""
              '';

          };
        in {
          kaipy = kaipy;
        };
    } // (
        flake-utils.lib.eachDefaultSystem (system:
          let
            pkgs = import nixpkgs {
              inherit system;
              overlays = [
                pyk.overlay
                self.overlay
              ];
            };
          in {
            packages = {
              inherit (pkgs) kaipy;
              default = pkgs.kaipy;
            };
            devShells = {
              kaipy = pkgs.mkShell {
                inputsFrom = [self.outputs.packages.${system}.kaipy];
                packages = [
                    pkgs.autoflake
                    pkgs.isort
                    pkgs.black
                    pkgs.python311.pkgs.mypy
                ];
              };
            };
          })  
      ));
}
