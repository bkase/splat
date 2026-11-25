module

public import Succinct

public section

/-!
# Proved solution

This module supplies the proofs of the two headline statements advertised
in `Challenge.lean`. The support definitions are repeated with bodies
identical to the Challenge's, and the theorems follow directly from the
corresponding results of the `Succinct` development: the one-step
proximity reduction of the FRI fold
(`SuccinctProofs.fri_folding_preserves_proximity`) and the
bad-challenge bound (`SuccinctProofs.bad_alpha_set_finite_of_ne`).
-/

namespace SPLAT

/-- The Hamming weight of a vector: the number of nonzero coordinates. -/
@[expose]
def weightVec {F : Type*} [Field F] [DecidableEq F] {k : ℕ} (x : Fin k → F) : ℕ :=
  Fintype.card { i : Fin k | x i ≠ 0 }

/-- The FRI fold of a vector `v` with challenge `α` and evaluation points
`eval_points`, as in `Challenge.lean`. -/
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

/-- **FRI one-step proximity reduction** (§4.2 of the paper). -/
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
      weightVec (friFold v α eval_points hk - w_next) ≤ q :=
  SuccinctProofs.fri_folding_preserves_proximity eval_points h_distinct V d h_dist v q
    h_close α hk hk_even

/-- **Bad-challenge bound** for the FRI fold (§4.2 of the paper). -/
theorem bad_alpha_set_bound {F : Type*} [Field F] [DecidableEq F] [Fintype F] {k : ℕ}
    (v w : Fin k → F) (eval_points : Fin k → F)
    (hk : k > 0) (hk_even : k % 2 = 0)
    (hω : ∀ i : Fin k, eval_points i ≠ 0)
    (h2 : (2 : F) ≠ 0)
    (hvw : v ≠ w) :
    Fintype.card {α : F | friFold v α eval_points hk = friFold w α eval_points hk}
      ≤ k / 2 :=
  SuccinctProofs.bad_alpha_set_finite_of_ne v w eval_points hk hk_even hω h2 hvw

end SPLAT
