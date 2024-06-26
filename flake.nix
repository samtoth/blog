{
  description = "Sam's agda blog";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/6cfbf89825dae72c64188bb218fd4ceca1b6a9e3";
    # systems.url = "github:nix-systems/default";
    flake-utils.url = "github:numtide/flake-utils";
    agda = {
      # url = "github:agda/agda";
      url = "github:agda/agda/403ee4263e0f14222956e398d2610ae1a4f05467";
      # sha256 = "09rbhysb06xbpw4hak69skxhdpcdxwj451rlgbk76dksa6rkk8wm";
      flake = false;
    };
    onelab = {
      url = "github:plt-amy/1lab/d2c0e8824797353b59eb25eaa9d14cd8981830df";
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
                  Agda = pkgs.haskell.lib.overrideCabal (super.callCabal2nixWithOptions "Agda" inputs.agda "-f optimise-heavily -f debug" {}) {
                      doCheck = false;
                      doHaddock = false;
                      testHaskellDepends = [];
                    };
                };});
            })
            ];};
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
          myGhc = pkgs.haskellPkgs.ghcWithPackages (ps: with ps; ([
              shake Agda haskell-language-server
            ]));
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

          devShells.site = mkShell {
            inputsFrom = [    
              self.packages."${system}".site 
            ];

            packages = [  ];
          };

          packages.site = stdenv.mkDerivation {
            name = "sam's-blog";
            src = ./.;

            buildInputs = [ myGhc ];

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
