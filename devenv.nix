{ pkgs, ... }:
{
  # https://devenv.sh/packages/
  packages = [
    pkgs.git
    pkgs.elan
    pkgs.uv
  ];

  languages.python = {
    enable = true;
    # Nix-provided Python; 3.12 is fine (package requires >=3.10)
    package = pkgs.python312;
    uv = {
      enable = true;
      # Run `uv sync` automatically when the shell loads and the lock/manifest changed
      sync.enable = false;
    };
  };


  # Environment variables for Lean (elan will manage toolchain)
  env = {
    LEAN_PATH = ".lake/packages";
    LEAN_SRC_PATH = ".";
  };

  # https://devenv.sh/scripts/
  scripts.build.exec = "lake build";
  scripts.check.exec = "lean Succinct.lean";

  enterShell = ''
    echo "✅ Lean 4 + Mathlib4 environment loaded (elan-managed)"
    echo "Installing toolchain from lean-toolchain..."
    elan install $(cat lean-toolchain | grep -oP 'v\d+\.\d+\.\d+.*')
    lean --version
    echo "Try: lake build"
  '';
}
