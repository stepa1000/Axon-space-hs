
{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux"; # Adjust for your system
      pkgs = import nixpkgs { inherit system; };
    in {
      devShells.${system}.default = pkgs.mkShell {
        buildInputs = [
	  pkgs.cabal-install
          pkgs.stack
          pkgs.haskell.compiler.ghc910 # Match your Stack resolver's GHC
          pkgs.zlib # Example of a C library dependency
          pkgs.pkg-config
          #pkgs.OpenGL
          pkgs.freeglut
          #pkgs.gl
	  #pkgs.GLUT
	  #pkgs.GLUtil
          pkgs.libGL
          pkgs.libGLU

        ];
      };
    };
}

