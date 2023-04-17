{
  description = "An abstract interpreter based on the K framework";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    pyk.url = "github:runtimeverification/pyk/v0.1.239";
    k-framework.url = "github:runtimeverification/k/no-antileft";
    #k-haskell-backend.follows = "k-framework/haskell-backend";
    k-haskell-backend.url = "github:runtimeverification/haskell-backend/remove-rewrite-antileft";
    k-llvm-backend.url = "github:runtimeverification/llvm-backend";
    k-llvm-backend.inputs.nixpkgs.follows = "nixpkgs";
    k-framework.inputs.nixpkgs.follows = "nixpkgs";
    k-framework.inputs.llvm-backend.follows = "k-llvm-backend";
    k-framework.inputs.haskell-backend.follows = "k-haskell-backend";
  };

  outputs = { self, nixpkgs, pyk, k-framework, k-haskell-backend, k-llvm-backend }:
    let
      supportedSystems = [ "x86_64-linux" "x86_64-darwin" "aarch64-linux" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
      pkgs = forAllSystems (system: nixpkgs.legacyPackages.${system});
    in
    {
      packages = forAllSystems (system:
      let
        python = pkgs.${system}.python310;
        stdenv = pkgs.${system}.stdenv;
        pythonPackages = pkgs.${system}.python310Packages;
        k = k-framework.packages.${system}.k;
        kore-rpc = k-haskell-backend.project.${system}.hsPkgs.kore.components.exes.kore-rpc;
        python-pyk = pyk.packages.${system}.pyk-python310 ;
      in {
        kaipy = python.pkgs.buildPythonApplication {
            name = "kaipy";
            src = ./kaipy;
            format = "pyproject";
            propagatedBuildInputs = [
              python-pyk
              python.pkgs.setuptools
              python.pkgs.networkx
              python.pkgs.frozendict
            ];
            postInstall = ''
              substituteInPlace $out/lib/*/site-packages/kaipy/kcommands.py \
                --replace "\"kompile\"" "\"${k}/bin/kompile\""
              substituteInPlace $out/lib/*/site-packages/kaipy/kcommands.py \
                --replace "\"kprove\"" "\"${k}/bin/kprove\""
              substituteInPlace $out/lib/*/site-packages/kaipy/kcommands.py \
                --replace "\"krun\"" "\"${k}/bin/krun\""
              substituteInPlace $out/lib/*/site-packages/kaipy/kcommands.py \
                --replace "\"kore-rpc\"" "\"${kore-rpc}/bin/kore-rpc\""
            '';
        };

        test = stdenv.mkDerivation {
          name = "kaipy-test" ;
          src = ./test ;
          propagatedBuildInputs = [
            self.outputs.packages.${system}.kaipy
            k
            kore-rpc
            python-pyk
          ];

          buildPhase = "make default";
          installPhase = "echo 'Empty install phase'";
        };

        default = self.outputs.packages.${system}.kaipy ;
      });
    };
}