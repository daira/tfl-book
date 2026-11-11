{
  description = "The Zcash Trailing Finality Layer Book";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/23.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages."${system}";

        tfl-book-pkg = pkgs.stdenv.mkDerivation rec {
          pname = "tfl-book";
          version = "0.1.0"; # BUG: This should be derived from the `git describe --dirty`

          buildInputs = with pkgs; [
            graphviz
            mdbook
            mdbook-admonish
            mdbook-graphviz
            mdbook-linkcheck
            mdbook-katex
          ];

          src = ./.;

          builder = pkgs.writeScript "${pname}-builder-${version}" ''
            source "$stdenv/setup"
            cp -a "$src" ./src
            cd ./src
            chmod -R u+w .
            mdbook build
            dest="$out/share/doc/${pname}/"
            mkdir -p "$(dirname "$dest")"
            cp -a ./build/html "$dest"
          '';
        };
      in
      {
        packages.default = tfl-book-pkg;
      }
    );
}
