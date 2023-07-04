{
  description = "An abstract interpreter based on the K framework";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.05";
    pyk.url = "github:runtimeverification/pyk/v0.1.358";
    k-framework.url = "github:runtimeverification/k/v6.0.1";
    k-haskell-backend.follows = "k-framework/haskell-backend";
    #k-haskell-backend.url = "github:runtimeverification/haskell-backend/remove-rewrite-antileft";
    #k-llvm-backend.url = "github:runtimeverification/llvm-backend";
    #k-llvm-backend.inputs.nixpkgs.follows = "nixpkgs";
    k-framework.inputs.nixpkgs.follows = "nixpkgs";
    pyk.inputs.nixpkgs.follows = "nixpkgs";
    #k-framework.inputs.llvm-backend.follows = "k-llvm-backend";
    #k-framework.inputs.haskell-backend.follows = "k-haskell-backend";
  };

  outputs = { self, nixpkgs, pyk, k-framework, ...}:
    let
      forAllSystems = f: nixpkgs.lib.genAttrs nixpkgs.lib.systems.flakeExposed (system: f system);
      pkgs = forAllSystems (system: nixpkgs.legacyPackages.${system});
    in
    {
      packages = forAllSystems (system:
      let
        python = pkgs.${system}.python311;
        stdenv = pkgs.${system}.stdenv;
        pythonPackages = pkgs.${system}.python311Packages;
        k = k-framework.packages.${system}.k;
        python-pyk = pyk.packages.${system}.pyk-python311 ;
      in {
        kaipy = python.pkgs.buildPythonApplication {
            name = "kaipy";
            src = ./kaipy;
            format = "pyproject";
            propagatedBuildInputs = [
              python-pyk
              python.pkgs.setuptools
              python.pkgs.networkx
              python.pkgs.immutabledict
              python.pkgs.matplotlib
              #python.pkgs.pyqt5
              python.pkgs.tkinter
              python.pkgs.mypy
              python.pkgs.pytest
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

        test = stdenv.mkDerivation {
          name = "kaipy-test" ;
          src = ./test ;
          propagatedBuildInputs = [
            self.outputs.packages.${system}.kaipy
            k
            #kore-rpc
            python-pyk
          ];

          buildPhase = "make default";
          installPhase = "echo 'Empty install phase'";
        };

        default = self.outputs.packages.${system}.kaipy ;
      });
      devShells = forAllSystems(system: {
        kaipy = pkgs.${system}.mkShell {
          inputsFrom = [self.outputs.packages.${system}.kaipy];
          packages = [
              pkgs.${system}.autoflake
              pkgs.${system}.isort
              pkgs.${system}.black
          ];
        };
      });
    };
}
