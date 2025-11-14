# lean-succinct

A Lean 4 formalization effort for the notes `2023-succinct-la.pdf`, tracking the linear-algebraic preliminaries that underpin succinct argument systems. At the moment everything lives in `Succinct.lean`, which mirrors Section 1.1 and the parts of Section 1.2.

## Project status

- ✅ Section 1.1 (vectors, matrices, subspaces) is formalized with idiomatic mathlib constructions.
- ⚙️ Section 1.2 is in progress; the file already contains Vandermonde and evaluation-map scaffolding that upcoming lemmas plug into.
- 📄 The original reference lives alongside the code as `2023-succinct-la.pdf` so you can diff Lean statements against the text easily.

## Getting started

We standardize on `devenv` so both Lean and Python tooling stay in sync.

### With Nix + devenv

1. Install [devenv.sh](https://devenv.sh/getting-started/).
2. Run `devenv shell` from the repo root. The shell hook installs the Lean toolchain (from `lean-toolchain`, currently `leanprover/lean4:v4.25.0-rc2`), configures elan, and exposes `lake`, `lean`, and `uv`.
3. Optional scripts:
   - `devenv task build` → `lake build`
   - `devenv task check` → `lean Succinct.lean`

### Without Nix

1. Install `elan` and select the toolchain listed in `lean-toolchain`.
2. Run `lake exe cache get` if you need mathlib artifacts, then `lake build`.
3. Install [uv](https://github.com/astral-sh/uv) (or `pip install uv`).
4. Inside the repo run `uv sync` to grab the Python dependencies.

## Everyday workflows

- **Lean development:** `lean Succinct.lean` is the fastest way to iterate; `lake build` gives you cross-file assurance. (House rule: never run `lake clean`.)
- **Python helpers:** The `pyproject.toml` declares the lightweight tooling we use to run `aristotle`. After a sync, `uv run aristotle <args>` works from anywhere in the repo.
- **Doc alignment:** Keep the Lean module headings in sync with the section numbers from the PDF so future diffing stays obvious.

## Repository layout

```
README.md            ← project overview (this file)
Succinct.lean        ← formalization of §§1.1–1.2
2023-succinct-la.pdf ← source notes we are mechanizing
lakefile.lean        ← Lean package definition
lake-manifest.json   ← mathlib + dependency lockfile
lean-toolchain       ← elan toolchain pin (Lean 4.25.0-rc2)
devenv.nix           ← reproducible dev shell (elan, uv)
pyproject.toml       ← Python deps (aristotlelib via uv)
uv.lock              ← locked Python dependency graph
```

## Contributing

1. Stay within `Succinct.lean` until we split modules (call out new sections at the top of the file).
2. Before opening a PR, run both `lake build` and `uv run aristotle --help` (ensures the CLI entry point resolves).
3. Reference `2023-succinct-la.pdf` section numbers in commit messages or docstrings so reviewers can map proof obligations back to the text.
