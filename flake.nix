{
  description = "Sam's agda blog";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    # systems.url = "github:nix-systems/default";
    flake-utils.url = "github:numtide/flake-utils";
    agda = {
      url = "github:agda/agda";
      # rev = "8ede3561ae32257eb7a102b8301c61fae1debb23";
      # sha256 = "0iwif4ix47974j5mnq24a2afhgc03y0gp977bn0vsb3ics8dg6bz";
      flake = false;
    };
    onelab = {
      url = "github:plt-amy/1lab";
      flake = false;
    };
  };

  outputs = inputs@{
      self,
      nixpkgs,
      flake-utils,
      agda,
      onelab,
      ...
    }: flake-utils.lib.eachDefaultSystem (system: 
        let
          pkgs = import nixpkgs { inherit system; overlays = [
            (pkgs: prev: {
              haskellPkgs = prev.haskell.packages.ghc946.override (old: {
                overrides = self: super: {
                  Agda = super.callCabal2nix "Agda" agda "-f optimise-heavily -f debug" {};
                };});
            })
            ]; };
          # pkgs = nixpkgs.legacyPackages."${system}";
          agda = pkgs.agdaPackages.override {
            Agda = pkgs.haskellPkgs.Agda;
          };
          proper-1lab = mkDerivation: mkDerivation {
                pname = "1lab";
                name = "1lab";
                src = onelab.outPath;

                postPatch = ''
                  # We don't need anything in support; avoid installing LICENSE.agda
                  # rm -rf support


                  echo "module Everything where" > src/Everything.agda

                  echo "import index" >> src/Everything.agda

                  find src/ -type f -name 'Solver.agda' | \
                    sort | \
                    sed -re 's@src/@@g;s@.agda@@g;s@/@.@g;s@^@import @g;s@$@@g' \
                    >> src/Everything.agda

                  # Remove verbosity options as they make Agda take longer and use more memory.
                  shopt -s globstar extglob
                  sed -Ei '/OPTIONS/s/ -v ?[^ #]+//g' src/**/*.@(agda|lagda.md)
                '';

                everythingFile = "src/Everything.agda";

                libraryName = "1lab";
                libraryFile = "1lab.agda-lib";

                GHCRTS = "-M5G";

                meta = {};
              };
          local-1lab = mkDerivation: mkDerivation {
                pname = "1lab";
                name = "1lab";
                src = /home/samt/Projects/1lab;

                libraryName = "1lab";
                libraryFile = "1lab.agda-lib";

                GHCRTS = "-M5G";
                everythingFile = "src/index.lagda.md";

                meta = {};
              };
        in with pkgs; {
          packages.agdaParts = agdaPackages.callPackage ({ lib, mkDerivation }: mkDerivation {
            name = "samsAgdaNotes";
            pname = "blog";

            buildInputs = [
              (proper-1lab mkDerivation)
            ];

            src = ./.;

            meta = {
              name = "agdaNotes";
            };
          }) {};

          devShells.default = mkShell {
              inputsFrom = [    
                self.packages."${system}".agdaParts
                self.packages."${system}".site 
              ];

              packages = [  ];
          };

          packages.site = stdenv.mkDerivation {
            name = "sam's-blog";
            src = ./.;

            buildCommand = ''
              touch $out
            '';
          };

          packages.default = self.packages."${system}".site;

        });
}  
    
    
    
    # flake-parts.lib.mkFlake { inherit inputs; } {
    #   systems = import systems;
    #   perSystem = { self', config, pkgs, system, ... }: 
    #   let 
    #     haskellPkgs = pkgs.haskell.packages.ghc946.extend (old: {
    #       overrides = self: super: {
    #         Agda = super.callCabal2nix "Agda" agda "-f optimise-heavily -f debug" {};
    #       };});
    #     ghc = interactive: haskellPkgs.ghcWithPackages (ps: with ps; ([
    #       Agda shake pandoc
    #     ] ++ (if interactive then [ haskell-language-server ] else [])));

    #   in {
    #     packages.blogShake = haskellPkgs.callCabal2nix "blog" ./site/blog.cabal {};

    #     packages.staticSite = pkgs.stdenv.mkDerivation {
    #       name = "blog";
    #       src = ./.;
    #       # nativeBuildInputs = [
    #       #   self'.packages.blogShake
    #       # ];

    #       LANG = "C.UTF-8";
    #       buildPhase = ''
    #         touch $out
    #       '';
    #     };

    #     packages.default = self'.packages.staticSite;
    #   };
    # };


    # let 
    #     pkgs = import nixpkgs { inherit system; };
    # in with pkgs; {
    #   packages.${system} = {
    #     default = stdenv.mkDerivation {
    #       name = "sam's-blog";
    #       src = ./.;

    #       buildCommand = ''
    #         touch $out
    #       '';
    #     };
    #   };

    #   devShells.${system} = {
    #     default = mkShell {
    #       inputsFrom = [ol];
    #       agda-libs = pkgs.writeTextDir "libraries" ''
    #         ${ol.src}/1lab.agda-lib
    #       '';

    #       shellHook = ''
    #         export AGDA_DIR=${self.devShells.${system}.default.agda-libs}
    #       '';
    #     };
    #   };
    # };
