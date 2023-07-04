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

  outputs = { self, nixpkgs, pyk, k-framework, k-haskell-backend, ...}:
    let
      supportedSystems = [ "x86_64-linux" "x86_64-darwin" "aarch64-linux" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
      pkgs = forAllSystems (system: nixpkgs.legacyPackages.${system});
    in
    {
      packages = forAllSystems (system:
      let
        python = pkgs.${system}.python311;
        stdenv = pkgs.${system}.stdenv;
        pythonPackages = pkgs.${system}.python311Packages;
        k = k-framework.packages.${system}.k;
        #kore-rpc = k-haskell-backend.project.${system}.hsPkgs.kore.components.exes.kore-rpc;
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
