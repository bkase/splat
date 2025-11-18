# SPLAT — Succinct Proofs and Linear Algebra Theorem-proven

A Lean 4 formalization of the notes `2023-succinct-la.pdf`, capturing the linear-algebraic preliminaries that underpin succinct argument systems. The project now lives under the barrel module `Succinct.lean` with a small family of focused submodules.

## Project status

- ✅ Section 1.1 (vectors, matrices, subspaces) is formalized with idiomatic mathlib constructions.
- ⚙️ Section 1.2 in progress; Vandermonde/evaluation scaffolding, linear codes, weights, and distance are organized as modules.
- 📄 The source notes live beside the code as `2023-succinct-la.pdf` for easy cross-checking.

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
README.md                 ← project overview (this file)
Succinct.lean             ← barrel module
Succinct/LinearAlgebra.lean
Succinct/Vandermonde.lean
Succinct/Codes/Core.lean
Succinct/Codes/Hamming.lean
Succinct/Codes/Distance.lean
Succinct/Codes/EvalCode.lean
2023-succinct-la.pdf      ← source notes we are mechanizing
lakefile.lean             ← Lean package definition
lake-manifest.json        ← mathlib + dependency lockfile
lean-toolchain            ← elan toolchain pin (Lean 4.25.0-rc2)
devenv.nix                ← reproducible dev shell (elan, uv)
pyproject.toml            ← Python deps (aristotlelib via uv)
uv.lock                   ← locked Python dependency graph
```

## Module map

- `Succinct.LinearAlgebra` — `Vec`, `Mat`, range/nullspace, bases.
- `Succinct.Vandermonde` — evaluation points, Vandermonde matrices, polynomial evaluation as matrix–vector multiplies.
- `Succinct.Codes.Core` — `LinearCode`, `encode`, repeat code helper.
- `Succinct.Codes.Hamming` — ℓ₀/Hamming weight on vectors and sets.
- `Succinct.Prob.Implication` — probabilistic implication calculus (paper §1.4), chaining/contrapositive/independence rules.
- `Succinct.Prob.Examples` — tiny sanity checks for the `⟹[μ]_` notation.
- `Succinct` — umbrella re-export for downstream users.

### Probabilistic implication at a glance

```
open Succinct.Prob

section
  variable {Ω} [MeasurableSpace Ω]
  variable (μ : Measure Ω) [IsProbabilityMeasure μ]
  variable {A B C : Set Ω} {p q : ℝ≥0∞}

  example (h₁ : A ⟹[μ]_(p) B) (h₂ : B ⟹[μ]_(q) C) : A ⟹[μ]_(p+q) C :=
    chain (μ:=μ) h₁ h₂

  example (h : A ⟹[μ]_(p) B) : Bᶜ ⟹[μ]_(p) Aᶜ :=
    contrapositive (μ:=μ) h
end
```

## Contributing

1. Import the specific `Succinct.*` module you need (or `Succinct` for convenience); keep new definitions in the most specific file.
2. Before opening a PR, run `lake build` and `uv run aristotle --help` (ensures the CLI entry point resolves).
3. Reference `2023-succinct-la.pdf` section numbers in comments or commits so reviewers can map proof obligations back to the text.
