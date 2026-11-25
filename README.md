# SPLAT — Succinct Proofs and Linear Algebra Theorem-proven

A Lean 4 formalization of [*Succinct Proofs and Linear Algebra*](https://eprint.iacr.org/2023/1478) (Alex Evans and Guillermo Angeris, IACR eprint 2023/1478; the paper is kept locally as `2023-succinct-la.pdf`), capturing the linear-algebraic preliminaries that underpin succinct argument systems. The project now lives under the barrel module `Succinct.lean` with a small family of focused submodules.

## Project status

### Completed sections

- ✅ **Section 1.1**: Vectors, matrices, subspaces with idiomatic mathlib constructions
- ✅ **Section 1.2**: Vandermonde matrices, evaluation maps, linear codes, weights, distance
- ✅ **Section 1.3**: Coding theory foundations
  - Reed-Solomon codes with Lagrange interpolation and degree bounds
  - Hadamard codes with distance formula via inner product counting
  - Singleton bound and kernel characterization
  - Kronecker product codes with tensor distance analysis
- ✅ **Section 1.4**: Probabilistic implication calculus (`Succinct.Prob.Implication`)
- ✅ **Section 3**: Probabilistic checks
  - Sparsity checking with geometric decay bounds
  - Zero-testing for vectors and polynomials via random evaluation
  - Matrix zero-testing via row sampling
  - Product measure projection for multi-round protocols
- **Section 4**: FRI folding and fixed-witness checks
  - Subspace distance theory relating matrix proximity to linear subspaces
  - Unique decoding radius argument via contrapositive
  - FRI construction: folding operation, bad alpha set finiteness
  - Polynomial decomposition for completeness
  - Fixed-witness soundness for one challenge and independent repetitions

The repeated check uses the same fold and witness throughout. The complete
recursive FRI protocol and its end-to-end soundness theorem remain outside
the formalization.

## Getting started

We standardize on `devenv` so both Lean and Python tooling stay in sync.

### With Nix + devenv

1. Install [devenv.sh](https://devenv.sh/getting-started/).
2. Run `devenv shell` from the repo root. The shell hook installs the Lean toolchain (from `lean-toolchain`, currently `leanprover/lean4:v4.36.0`), configures elan, and exposes `lake`, `lean`, and `uv`.
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
Challenge.lean            ← Palomar Challenge module (self-contained statements)
Solution.lean             ← Palomar Solution module (proofs)
comparator.json           ← Palomar Comparator configuration
formalization.yaml        ← Palomar entry metadata
LICENSE                   ← MIT
2023-succinct-la.pdf      ← source notes we are mechanizing
lakefile.lean             ← Lean package definition
lake-manifest.json        ← mathlib + dependency lockfile
lean-toolchain            ← elan toolchain pin (Lean 4.36.0)
devenv.nix                ← reproducible dev shell (elan, uv)
pyproject.toml            ← Python deps (aristotlelib via uv)
uv.lock                   ← locked Python dependency graph
```

## Module map

| Module | Contents |
|---|---|
| `Succinct.LinearAlgebra` | `Vec`, `Mat`, range/nullspace, bases |
| `Succinct.Vandermonde` | Evaluation points, Vandermonde matrices, polynomial evaluation as matrix–vector multiplication |
| `Succinct.Codes.Core` | `LinearCode`, `encode`, repeat code helper |
| `Succinct.Codes.Hamming` | ℓ₀/Hamming weight on vectors and sets |
| `Succinct.Prob.Implication` | Probabilistic implication calculus (paper §1.4), chaining/contrapositive/independence rules |
| `Succinct.Prob.Examples` | Examples of the `⟹[μ]_` notation |
| `Succinct` | Umbrella re-export for downstream users |

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

## Palomar registry layout

This repository is prepared for submission to the [Palomar registry](https://palomar-registry.org).
[Challenge.lean](Challenge.lean) contains eleven self-contained statements using
Mathlib and local support definitions. [Solution.lean](Solution.lean) repeats
those definitions and proves each statement from the existing `Succinct`
development. Neither module imports the other.

[comparator.json](comparator.json) selects all eleven theorems and permits only
`propext`, `Quot.sound`, and `Classical.choice`. [formalization.yaml](formalization.yaml)
records their scope and correspondence to the paper using the v0.4 schema.
All names below belong to the `SPLAT` namespace.

| Theorem | Result |
|---|---|
| `fri_folding_preserves_proximity` | Folding preserves proximity to the folded subspace |
| `bad_alpha_set_bound` | At most `k/2` challenges make two distinct vectors' folds collide |
| `fri_completeness` | Reed-Solomon codewords fold to evaluations with coefficient bound `(n+1)/2` |
| `fri_single_round_soundness` | A fixed-witness fold check has error at most `(k/2)/|F|` |
| `fri_multi_round_soundness` | Independent repetitions of that check have error at most `(k/2)^l / |F|^l` |
| `unique_decoding_radius` | The nearby matrix is unique below half the finite subspace distance |
| `singleton_bound` | Code distance is at most `m-n+1` for a nonempty message space |
| `kronecker_product_distance` | Component distance bounds multiply under the Kronecker product |
| `hadamard_distance_formula` | Nonzero messages have weight `|F|^n - |F|^(n-1)` for `n > 0` |
| `polynomial_zero_check` | A random evaluation has false-zero probability at most `(n-1)/|F|` |
| `reduced_matrix_zero_check` | Independent matrix zero checks have error at most `(1-d/m)^t` |

The probability statements bound the measure of acceptance together with a
false conclusion. The theorem `fri_multi_round_soundness` concerns repetitions
of one fold against a fixed witness, without recursive FRI commitments.

A predictive mechanical preflight can be run via the reusable workflow in `.github/workflows/palomar-preflight.yml`, pinned to an exact `PalomarRegistry/PalomarSubmission` commit. The preflight is advisory; actual submissions go through [submit.palomar-registry.org](https://submit.palomar-registry.org).
