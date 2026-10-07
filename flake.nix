{
  description = "Haskell development environment with local AI";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        hPkgs = pkgs.haskell.packages."ghc910"; 

        # Плагины для Neovim с GitHub
        plugin-neocodeium = pkgs.vimUtils.buildVimPlugin {
          pname = "neocodeium";
          version = "latest";
          src = pkgs.fetchFromGitHub {
            owner = "monkoose";
            repo = "neocodeium";
            rev = "main";
            sha256 = "sha256-rvlTa5nj9Aoelk7taqW5nBSqLZXrLt52jfWc+23toEs=";
          };
          doCheck = false;
        };

        plugin-haskell-tools = pkgs.vimUtils.buildVimPlugin {
          pname = "haskell-tools-nvim";
          version = "latest";
          src = pkgs.fetchFromGitHub {
            owner = "mrcjkb";
            repo = "haskell-tools.nvim";
            rev = "v4.2.0"; 
            sha256 = "sha256-W7m6AasEvh0853ItXd/fP9wysHnHvhJcJG5X1ZSX1v0=";
          };
          doCheck = false;
        };

        plugin-overseer = pkgs.vimUtils.buildVimPlugin {
          pname = "overseer-nvim";
          version = "latest";
          src = pkgs.fetchFromGitHub {
            owner = "stevearc";
            repo = "overseer.nvim";
            rev = "master";
            sha256 = "sha256-eNDOUIPVbdo3jt4q+1Rw1QkGj7l0DTZu393V1xSiXi0="; 
          };
          doCheck = false;
        };

        # Конфигурация изолированного Neovim
        myNeovim = pkgs.neovim.override {
          configure = {
            customRC = ''
              set number
              set relativenumber
              set shiftwidth=2
              set tabstop=2
              set expandtab

              lua << EOF
                -- Настройка встроенного LSP клиента Neovim для Haskell 0.11+
                if vim.lsp.config then
                  vim.lsp.config('hls', {})
                  vim.lsp.enable('hls')
                else
                  local status, lspconfig = pcall(require, 'lspconfig')
                  if status then
                    lspconfig.hls.setup{}
                  end
                end

                -- Локальный автокомплит Neocodeium (использует модель 1.5b)
                require('neocodeium').setup({
                  server = {
                    api_url = "http://127.0.0.1:11434",
                    provider = "ollama",
                    model = "qwen2.5-coder:1.5b",
                  }
                })

                -- Инициализация диспетчера задач
                local overseer = require('overseer')
                overseer.setup()

                -- Горячие клавиши
                vim.keymap.set('n', '<leader>t', '<cmd>OverseerToggle<cr>') -- \t для логов задач
                vim.keymap.set('i', '<A-f>', function()
                  require('neocodeium').accept()                            -- Alt+f принять ИИ код
                end)
              EOF
            '';
            packages.myVimPackages = {
              start = with pkgs.vimPlugins; [
                nvim-lspconfig
                nvim-treesitter.withAllGrammars
                plugin-neocodeium
                plugin-haskell-tools
                plugin-overseer
              ];
            };
          };
        };

        # Инструменты разработки среды devShell
        myDevTools = [
          myNeovim 
          pkgs.ollama                 # ИИ движок
          pkgs.aider-chat             # Умный, стабильный многофайловый ИИ-архитектор
          hPkgs.ghc
          hPkgs.ghcid
          hPkgs.ormolu
          hPkgs.hlint
          hPkgs.hoogle
          hPkgs.haskell-language-server
          hPkgs.implicit-hie
          stack-wrapped
          hPkgs.cabal-install
          hPkgs.zlib
          hPkgs.OpenGL
          pkgs.libGL
          pkgs.libGLU
          pkgs.freeglut
          pkgs.blas
          pkgs.cairo.dev
          pkgs.gcc
          pkgs.gmp
          pkgs.gnumake
          pkgs.iana-etc
          pkgs.liblapack
          pkgs.ncurses
          pkgs.zeromq
          pkgs.zlib.dev
          pkgs.libffi
        ];

        myCLibs = [
          pkgs.zlib pkgs.freeglut pkgs.libGL pkgs.libGLU pkgs.blas pkgs.cairo.dev
          pkgs.gcc pkgs.gmp pkgs.gnumake pkgs.iana-etc pkgs.liblapack pkgs.ncurses
          pkgs.zeromq pkgs.zlib.dev pkgs.libffi
        ];
        
        stack-wrapped = pkgs.symlinkJoin {
          name = "stack";
          paths = [ pkgs.stack ];
          buildInputs = [ pkgs.makeWrapper ];
          postBuild = ''
            wrapProgram $out/bin/stack \
              --add-flags "--no-nix --system-ghc --no-install-ghc"
          '';
        };
      in {
        apps.default = {
          type = "app";
          program = "${myNeovim}/bin/nvim";
        };

        profile = ''
          export C_INCLUDE_PATH=/usr/include:$C_INCLUDE_PATH
        '';
        devShells.default = pkgs.mkShell {
          buildInputs = myDevTools ++ myCLibs;
          LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath myCLibs;
        };
      });
}
