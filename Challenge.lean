module

public import Mathlib.Tactic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Data.Fintype.Card

set_option warningAsError false
-- The deliberate `sorry`s below are the holes this repository's `Solution.lean`
-- discharges; they are expected by the Palomar Comparator layout.

public section

/-!
# Advertised statement

This module states, independently of the rest of the repository, the two
headline results of the formalization of Evans and Angeris,
*Succinct Proofs and Linear Algebra* (eprint 2023/1478), Section 4.2:

1. `SPLAT.fri_folding_preserves_proximity` — the one-step proximity
   reduction of the FRI low-degree test: if a vector is `q`-close to a
   linear subspace whose nonzero elements are all heavy, then its FRI
   fold is again `q`-close to the folded subspace.
2. `SPLAT.bad_alpha_set_bound` — the bad-challenge bound: for distinct
   vectors, at most `k / 2` folding challenges `α` make their folds
   collide.

Both statements use only ordinary Mathlib notions (finite fields,
function spaces, submodules, and cardinalities of finite sets) plus the
two definitions repeated below (the fold's index proofs are in term
mode so the Solution's copies elaborate to identical constants), so a
reader can audit them without reading the rest of the development.
-/

namespace SPLAT

/-- The Hamming weight of a vector: the number of nonzero coordinates. -/
@[expose]
def weightVec {F : Type*} [Field F] [DecidableEq F] {k : ℕ} (x : Fin k → F) : ℕ :=
  Fintype.card { i : Fin k | x i ≠ 0 }

/-- The FRI fold of a vector `v` with challenge `α` and evaluation points
`eval_points`: coordinate `j` of the fold combines the pair
`(v_{2j}, v_{2j+1})` as

`(v_{2j} + v_{2j+1}) / 2 + α * (v_{2j} - v_{2j+1}) / (2 * eval_points_{2j})`,

the decomposition of the underlying polynomial into its even and odd
parts, as in §4 of the paper. -/
@[expose]
def friFold {F : Type*} [Field F] {k : ℕ} (v : Fin k → F) (α : F)
    (eval_points : Fin k → F) (hk : k > 0) : Fin (k / 2) → F :=
  fun j =>
    let i1 : Fin k := ⟨2 * j.val, Nat.lt_of_lt_of_le
      ((Nat.mul_lt_mul_left (a := 2) Nat.zero_lt_two).mpr j.isLt) (Nat.mul_div_le k 2)⟩
    let i2 : Fin k := ⟨2 * j.val + 1, Nat.lt_of_lt_of_le
      (Nat.succ_lt_succ (Nat.lt_succ_self (2 * j.val)))
      (Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt j.isLt))
        (Nat.mul_div_le k 2))⟩
    (v i1 + v i2) / 2 + α * (v i1 - v i2) / (2 * eval_points i1)

/-- **FRI one-step proximity reduction** (§4.2 of the paper).

Let `V ⊆ F^k` be a linear subspace all of whose nonzero elements have
Hamming weight at least `d`, and let `v` be `q`-close to `V`. For any
challenge `α`, the FRI fold of `v` is `q`-close to the set of folds of
elements of `V`: folding cannot increase the distance of `v` to the
code. -/
theorem fri_folding_preserves_proximity {F : Type*} [Field F] [DecidableEq F] {k : ℕ}
    (eval_points : Fin k → F)
    (h_distinct : ∀ i j : Fin k, i ≠ j → eval_points i ≠ eval_points j)
    (V : Submodule F (Fin k → F))
    (d : ℕ)
    (h_dist : ∀ v ∈ V, v ≠ 0 → weightVec v ≥ d)
    (v : Fin k → F)
    (q : ℕ)
    (h_close : ∃ w ∈ V, weightVec (v - w) ≤ q)
    (α : F)
    (hk : k > 0)
    (hk_even : k % 2 = 0) :
    ∃ w_next ∈ {w : Fin (k / 2) → F | ∃ v ∈ V, w = friFold v α eval_points hk},
      weightVec (friFold v α eval_points hk - w_next) ≤ q := by
  sorry

/-- **Bad-challenge bound** for the FRI fold (§4.2 of the paper).

For distinct vectors `v ≠ w` over an even-length domain with nonzero
evaluation points and `2 ≠ 0`, the set of challenges `α` for which the
folds of `v` and `w` agree has cardinality at most `k / 2`. -/
theorem bad_alpha_set_bound {F : Type*} [Field F] [DecidableEq F] [Fintype F] {k : ℕ}
    (v w : Fin k → F) (eval_points : Fin k → F)
    (hk : k > 0) (hk_even : k % 2 = 0)
    (hω : ∀ i : Fin k, eval_points i ≠ 0)
    (h2 : (2 : F) ≠ 0)
    (hvw : v ≠ w) :
    Fintype.card {α : F | friFold v α eval_points hk = friFold w α eval_points hk}
      ≤ k / 2 := by
  sorry

end SPLAT
