/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 94232e82-1f80-4177-825c-55029b39cb79

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem linear_constraint_solutions {a b : F} :
    Fintype.card {x : F | a * x = b} ≤ 1 ∨ a = 0

- theorem bad_alpha_set_finite_gated
    (v w : Fin k → F)
    (ω : Fin k → F)
    (hk : k > 0)
    (hk_even : k % 2 = 0)
    (hω : ∀ i : Fin k, ω i ≠ 0)
    (h2 : (2 : F) ≠ 0)
    (hvw : v ≠ w) :
    Fintype.card {α : F | friFoldGated v α ω hk = friFoldGated w α ω hk} ≤ k / 2
-/

/-
Gated Submission for bad_alpha_set_finite (Batch 157)
Target: Prove that for v ≠ w, the set of α with friFold v α = friFold w α has cardinality ≤ k/2

This is a self-contained gated submission that uses only Mathlib.Tactic.

Key insight: The FRI fold at each position j is:
  friFold v α j = (v[2j] + v[2j+1])/2 + α * (v[2j] - v[2j+1])/(2*ω[2j])

So friFold v α = friFold w α means for each j:
  α * [(v[2j] - v[2j+1]) - (w[2j] - w[2j+1])] / (2*ω[2j]) = [(w[2j] + w[2j+1]) - (v[2j] + v[2j+1])] / 2

For v ≠ w, at least one j has a non-trivial constraint on α.
Each constraint is either:
- Impossible (0 solutions)
- Degree 0 (any α works, or constraint is satisfied for all α)
- Degree 1 (exactly 1 solution)

With k/2 positions, at most k/2 values of α satisfy all constraints.

Generated: 2026-03-05
-/

import Mathlib.Tactic


noncomputable section

open scoped BigOperators

section MainTheorem

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable {k : ℕ}

/-- FRI fold operation: combines pairs of evaluations.

    For j ∈ {0, ..., k/2 - 1}, the j-th output is:
    (v[2j] + v[2j+1])/2 + α * (v[2j] - v[2j+1])/(2*ω[2j])

    This is linear in α. -/
def friFoldGated (v : Fin k → F) (α : F) (ω : Fin k → F) (hk : k > 0) : Fin (k / 2) → F :=
  fun j =>
    let i1 : Fin k := ⟨2 * j.val, by omega⟩
    let i2 : Fin k := ⟨2 * j.val + 1, by omega⟩
    (v i1 + v i2) / 2 + α * (v i1 - v i2) / (2 * ω i1)

/-- **Helper 1**: Linear constraint analysis

    For a single position j, the equation friFold v α j = friFold w α j is linear in α.
    If the coefficient of α is nonzero, there is exactly one solution.
    If the coefficient is zero and the constant term is nonzero, there are no solutions.
    If both are zero, any α satisfies the constraint.

    PROVE THIS THEOREM.
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem linear_constraint_solutions {a b : F} :
    Fintype.card {x : F | a * x = b} ≤ 1 ∨ a = 0 := by
  exact Classical.or_iff_not_imp_right.2 fun ha => by rw [ Fintype.card_subtype ] ; exact Finset.card_le_one.2 fun x hx y hy => mul_left_cancel₀ ha <| by aesop;

/-- **Main Theorem**: Bad alpha set cardinality bound

    For v ≠ w, the set of α with friFold v α = friFold w α has cardinality at most k/2.

    Key insight: Each pair gives a linear constraint on α.
    For v ≠ w, at least one pair has a non-trivial constraint.
    A non-trivial linear constraint has at most 1 solution.
    But we have k/2 pairs, so at most k/2 "degrees of freedom".

    Actually, the tighter bound: if ANY pair has a non-trivial constraint,
    the intersection has at most 1 solution for α.
    So the cardinality is ≤ 1 ≤ k/2 when v ≠ w and k ≥ 2.

    PROVE THIS THEOREM.
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem bad_alpha_set_finite_gated
    (v w : Fin k → F)
    (ω : Fin k → F)
    (hk : k > 0)
    (hk_even : k % 2 = 0)
    (hω : ∀ i : Fin k, ω i ≠ 0)
    (h2 : (2 : F) ≠ 0)
    (hvw : v ≠ w) :
    Fintype.card {α : F | friFoldGated v α ω hk = friFoldGated w α ω hk} ≤ k / 2 := by
  by_contra! h_contra;
  -- Since $v \ne w$, there exists at least one index $j$ such that $v_{2j} \ne w_{2j}$ or $v_{2j+1} \ne w_{2j+1}$.
  obtain ⟨j, hj⟩ : ∃ j : Fin (k / 2), v ⟨2 * j.val, by omega⟩ ≠ w ⟨2 * j.val, by omega⟩ ∨ v ⟨2 * j.val + 1, by omega⟩ ≠ w ⟨2 * j.val + 1, by omega⟩ := by
    contrapose! hvw;
    ext ⟨ i, hi ⟩ ; induction' i using Nat.strong_induction_on with i ih ; rcases Nat.even_or_odd' i with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide [ Nat.add_mod, Nat.mul_mod ] ;
    · exact hvw ⟨ c, by linarith [ Nat.mod_add_div k 2 ] ⟩ |>.1;
    · exact hvw ⟨ c, by linarith [ Nat.mod_add_div k 2 ] ⟩ |>.2;
  -- Since $v_{2j} \ne w_{2j}$ or $v_{2j+1} \ne w_{2j+1}$, the linear constraint for $j$ is non-trivial.
  have h_nontrivial : ∃ α₁ α₂ : F, α₁ ≠ α₂ ∧ friFoldGated v α₁ ω hk j = friFoldGated w α₁ ω hk j ∧ friFoldGated v α₂ ω hk j = friFoldGated w α₂ ω hk j := by
    have h_card : Fintype.card {α : F | friFoldGated v α ω hk = friFoldGated w α ω hk} > 1 := by
      exact lt_of_le_of_lt ( Nat.div_pos ( Nat.le_of_dvd hk ( Nat.dvd_of_mod_eq_zero hk_even ) ) zero_lt_two ) h_contra;
    obtain ⟨ α₁, hα₁ ⟩ := Finset.one_lt_card.mp h_card;
    rcases hα₁ with ⟨ _, α₂, _, hα₂ ⟩ ; use α₁, α₂ ; aesop;
  unfold friFoldGated at *;
  grind

end MainTheorem
