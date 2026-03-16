/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 595cc288-07f4-41d0-86d4-d5a8bdd4d7a8

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem uniform_product_cylinder {m n : ℕ} [NeZero m] [NeZero n]
    (S₁ : Set (Fin m)) :
    uniformOn (Set.univ : Set (Fin m × Fin n)) { p | p.1 ∈ S₁ }
    = uniformOn (Set.univ : Set (Fin m)) S₁

- theorem uniform_product_first_coord_bound {m n : ℕ} [NeZero m] [NeZero n]
    (P : Fin m → Prop) (p : ℝ≥0∞)
    (h : uniformOn (Set.univ : Set (Fin m)) { i | P i } ≤ p) :
    uniformOn (Set.univ : Set (Fin m × Fin n)) { ω | P ω.1 } ≤ p
-/

/-
Target: Show that uniform on Fin m × Fin n applied to a set depending only on
        the first coordinate equals uniform on Fin m applied to that set.

Key insight: For a set S ⊆ Fin m × Fin n of the form S = S₁ × Fin n where
S₁ ⊆ Fin m, we have:
  uniformOn (Fin m × Fin n) S = uniformOn (Fin m) S₁

This is because the product measure factors and the second coordinate contributes
a factor of n/n = 1.

-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Notation
import Mathlib.Data.ENNReal.Basic


noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

section MainTheorem

/-- **Main Theorem**: Uniform measure on product applied to cylinder set.

    If S ⊆ Fin m × Fin n is a "cylinder" set S = {(i,j) | i ∈ S₁} for some S₁ ⊆ Fin m,
    then uniformOn (Fin m × Fin n) S = uniformOn (Fin m) S₁.

    PROVE THIS THEOREM.
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem uniform_product_cylinder {m n : ℕ} [NeZero m] [NeZero n]
    (S₁ : Set (Fin m)) :
    uniformOn (Set.univ : Set (Fin m × Fin n)) { p | p.1 ∈ S₁ }
    = uniformOn (Set.univ : Set (Fin m)) S₁ := by
  unfold ProbabilityTheory.uniformOn;
  simp +decide [ ProbabilityTheory.cond ];
  rw [ show { p : Fin m × Fin n | p.1 ∈ S₁ } = S₁ ×ˢ Set.univ from ?_, MeasureTheory.Measure.count_apply, MeasureTheory.Measure.count_apply ];
  · simp +decide [ ENat.card, mul_assoc, mul_comm, mul_left_comm ];
    rw [ ← mul_assoc, ENNReal.mul_inv ];
    · rw [ mul_left_comm, ENNReal.mul_inv_cancel ] <;> aesop;
    · exact Or.inl <| Nat.cast_ne_zero.mpr <| NeZero.ne m;
    · exact Or.inl <| ENNReal.natCast_ne_top _;
  · exact trivial
  · exact MeasurableSet.prod ( by measurability ) ( by measurability );
  · aesop

/-- **Corollary**: The bound from the first coordinate.

    If uniformOn (Fin m) {i | P i} ≤ p,
    then uniformOn (Fin m × Fin n) {(i,j) | P i} ≤ p.

    PROVE THIS THEOREM.
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem uniform_product_first_coord_bound {m n : ℕ} [NeZero m] [NeZero n]
    (P : Fin m → Prop) (p : ℝ≥0∞)
    (h : uniformOn (Set.univ : Set (Fin m)) { i | P i } ≤ p) :
    uniformOn (Set.univ : Set (Fin m × Fin n)) { ω | P ω.1 } ≤ p := by
  convert h using 1;
  convert uniform_product_cylinder { i : Fin m | P i } using 1;
  infer_instance

end MainTheorem
