{
  description = "my project description";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.nixpkgs-old.url = "github:nixos/nixpkgs/nixos-25.11";

  outputs = { self, nixpkgs, flake-utils, nixpkgs-old }:
    flake-utils.lib.eachDefaultSystem (system:
      let
         
	#oldPkg = import (builtins.fetchTarball {
        #   url = "https://nixos.org/channels/nixos-25.11";
        #   }) {};
        oldPkg = nixpkgs-old.legacyPackages.${system}; 

        pkgs = nixpkgs.legacyPackages.${system};

        hPkgs =
          pkgs.haskell.packages."ghc912"; # need to match Stackage LTS version
                                           # from stack.yaml snapshot
        # hPOld = pkgs.haskell.packages."ghc98";

        # hP10 = pkgs.haskell.packages."ghc910"; 

        myDevTools = [
          hPkgs.ghc # GHC compiler in the desired version (will be available on PATH)
	  hPkgs.ghc-internal
          hPkgs.ghcid # Continuous terminal Haskell compile checker
          hPkgs.ormolu # Haskell formatter
          hPkgs.hlint # Haskell codestyle checker
          hPkgs.hoogle # Lookup Haskell documentation
          hPkgs.haskell-language-server # LSP server for editor
	  #oldPkg.haskellPackages.haskell-debugger
          hPkgs.implicit-hie # auto generate LSP hie.yaml file from cabal
          # hPkgs.retrie # Haskell refactoring tool
          # hPkgs.cabal-install
	  hPkgs.implicit-hie
          hPkgs.stack
	  hPkgs.cabal-install
          pkgs.zlib # External C library needed by some Haskell packages
          hPkgs.OpenGL
          pkgs.freeglut
          hPkgs.gl
	  hPkgs.GLUT
	  hPkgs.GLUtil
          pkgs.libGL
          pkgs.libGLU
	  pkgs.freeglut
	  #pkgs.alex
	  #hPOld.c2hs
	  #hPOld.cpphs
	  #hPOld.doctest
	  #hPOld.ghcjs
	  #hPOld.ghcjs-pkgs
	  #hPOld.greencard
	  #hPOld.happy
	  #hPOld.hmake
	  #hPOld.jhs
	  #pkgs.pkg-config
	  #pkgs.uhc
        ];

        # Wrap Stack to work with our Nix integration. We don't want to modify
        # stack.yaml so non-Nix users don't notice anything.
        # - no-nix: We don't want Stack's way of integrating Nix.
        # --system-ghc    # Use the existing GHC on PATH (will come from this Nix file)
        # --no-install-ghc  # Don't try to install GHC if no matching GHC found on PATH
        
        
        stack-wrapped = pkgs.symlinkJoin {
          name = "stack"; # will be available as the usual `stack` in terminal
          paths = [ pkgs.stack ];
          buildInputs = [ pkgs.makeWrapper ];
          postBuild = ''
            wrapProgram $out/bin/stack \
              --add-flags "\
                --no-nix \
                --system-ghc \
                --no-install-ghc \
              "
          '';
        };
      in {
        devShells.default = pkgs.haskellPackages.shellFor {
	  packages = p: [ ];
          buildInputs = myDevTools;

          # Make external Nix c libraries like zlib known to GHC, like
          # pkgs.haskell.lib.buildStackProject does
          # https://github.com/NixOS/nixpkgs/blob/d64780ea0e22b5f61cd6012a456869c702a72f20/pkgs/development/haskell-modules/generic-stack-builder.nix#L38
          LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath myDevTools;
        };
      });
}
