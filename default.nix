{nixpkgs ? import <nixpkgs> {}, compiler ? "ghc865"}:
let
  dapptools = builtins.fetchGit {
    url = "https://github.com/dapphub/dapptools.git";
    rev = "c44db1f252b870c0913d0f83093347e9c05469c9";
    ref = "symbolic";
  };
  pkgs-for-dapp = import <nixpkgs> {
    overlays = [
      (import (dapptools + /overlay.nix))
    ];
  };
  haskellPackages = nixpkgs.pkgs.haskell.packages.${compiler}.override (old: {
    overrides = nixpkgs.pkgs.lib.composeExtensions (old.overrides or (_: _: {})) (
      import (dapptools + /haskell.nix) { lib = nixpkgs.pkgs.lib; pkgs = pkgs-for-dapp; }
    );
  });
in

haskellPackages.callPackage (import ./src/default.nix) {}
