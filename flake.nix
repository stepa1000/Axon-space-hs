{
  description = "my project description";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        hPkgs = pkgs.haskell.packages."ghc910"; 

        # 1. Нативная 100% свободная FHS-песочница для подгрузки glibc к бинарнику
        prime-agent-fhs = pkgs.buildFHSEnv {
          name = "prime-agent-env"; # Переименовали среду, чтобы имя не конфликтовало с алиасом
          targetPkgs = pkgs: with pkgs; [
            glibc
            gcc.cc.lib
            zlib
            openssl
            curl
          ];
          runScript = "bash";
        };

        # Плагины для Neovim
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

        myNeovim = pkgs.neovim.override {
          configure = {
            customRC = ''
              set number
              set relativenumber
              set shiftwidth=2
              set tabstop=2
              set expandtab

              lua << EOF
                if vim.lsp.config then
                  vim.lsp.config('hls', {})
                  vim.lsp.enable('hls')
                end

                require('neocodeium').setup({
                  server = {
                    api_url = "http://127.0.0.1:11434",
                    provider = "ollama",
                    model = "qwen2.5-coder:1.5b",
                  }
                })

                local overseer = require('overseer')
                overseer.setup()

                vim.keymap.set('n', '<leader>t', '<cmd>OverseerToggle<cr>')
                vim.keymap.set('i', '<A-f>', function()
                  require('neocodeium').accept()
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

        myDevTools = [
          myNeovim 
          pkgs.ollama
          pkgs.python3                # Интерпретатор для ядра ИИ
          prime-agent-fhs             # Добавили песочницу как готовый пакет в buildInputs
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

          # ЧИСТЫЙ ВЫЗОВ ЧЕРЕЗ СИСТЕМНЫЙ PATH БЕЗ ОШИБОК ПРИВЕДЕНИЯ ТИПОВ
          shellHook = ''
            prime-agent() {
              if [ -f "./.prime-bin/prime-agent" ]; then
                # Нативно вызываем бинарник среды, который теперь находится в нашем PATH
                prime-agent-env -c "./.prime-bin/prime-agent \"\$@\""
              else
                echo "❌ Ошибка: Бинарник ./.prime-bin/prime-agent не найден!"
                echo "Убедитесь, что архив распакован в папку проекта в ./.prime-bin/"
              fi
            }
            export -f prime-agent
          '';
        };
      });
}
