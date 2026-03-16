/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 80a44abe-c973-4820-9547-e60182462766

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem reduced_matrix_zero_check_bound
    (t m d : ℕ) [NeZero m] (hd_pos : 0 < d) (hle : d ≤ m) :
    ∀ (check : Fin m → Prop),
      -- Suppose: for uniform r on Fin m, P[check r] ≤ (1 - d/m)
      (uniformOn (Set.univ : Set (Fin m))) { r | check r } ≤ (1 - d / m) →
      -- Then: for t independent samples, P[∀ i, check (ω i)] ≤ (1 - d/m)^t
      (uniformOn (Set.univ : Set (Fin t → Fin m))) { ω | ∀ i, check (ω i) } ≤ (1 - d / m) ^ t
-/

/-
Target: Prove t independent rounds give (1 - d/m)^t failure bound

This is a self-contained gated submission that uses only Mathlib.Tactic
and includes inline definitions for all dependencies.

Key insight: For t independent uniform samples from Fin m, if each sample
has probability (1 - d/m) of "failing" (checking passes when X ≠ 0),
then the probability all t samples fail is (1 - d/m)^t.

-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Set.Lattice


noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal BigOperators

section Definitions

/-- Event-level probabilistic implication: `μ (A ∩ Bᶜ) ≤ p` -/
def ProbImpEv {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Set Ω) (p : ℝ≥0∞) : Prop :=
  μ (A ∩ Bᶜ) ≤ p

/-- Helper: The uniform measure on a finite function space Fin t → Fin m. -/
def uniformOnFunctions (t m : ℕ) [NeZero m] : Measure (Fin t → Fin m) :=
  Measure.pi (fun _ => Measure.count)

end Definitions

section MainTheorem

/-- **Main Theorem**: For t independent uniform samples, probability all checks pass
    given a per-sample failure bound.

    Setup:
    - Sample space: Fin t → Fin m (t independent samples from Fin m)
    - Each coordinate i has marginal uniform on Fin m
    - Event A_i = {ω | check passes at ω(i)} has measure ≤ (1 - d/m) when condition fails
    - Event A = ∩ᵢ A_i (all checks pass) has measure ≤ (1 - d/m)^t

    PROVE THIS THEOREM.
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem reduced_matrix_zero_check_bound
    (t m d : ℕ) [NeZero m] (hd_pos : 0 < d) (hle : d ≤ m) :
    ∀ (check : Fin m → Prop),
      -- Suppose: for uniform r on Fin m, P[check r] ≤ (1 - d/m)
      (uniformOn (Set.univ : Set (Fin m))) { r | check r } ≤ (1 - d / m) →
      -- Then: for t independent samples, P[∀ i, check (ω i)] ≤ (1 - d/m)^t
      (uniformOn (Set.univ : Set (Fin t → Fin m))) { ω | ∀ i, check (ω i) } ≤ (1 - d / m) ^ t := by
  intro check hcheck; specialize hcheck; simp_all +decide [ ProbabilityTheory.uniformOn ] ;
  simp_all +decide [ Set.indicator_apply, ProbabilityTheory.cond ];
  refine' le_trans _ ( pow_le_pow_left' hcheck t );
  simp +decide [ mul_pow, ENNReal.mul_inv ];
  rw [ ENNReal.inv_pow ];
  erw [ MeasureTheory.Measure.count_apply, MeasureTheory.Measure.count_apply ];
  · rw [ Set.encard, Set.encard ];
    simp +decide [ ENat.card ];
    rw [ Cardinal.mk_congr ];
    rotate_right;
    exact ( Fin t → { r : Fin m // check r } );
    · simp +decide [ Cardinal.mk_pi ];
    · exact ⟨ fun x => fun i => ⟨ x.val i, x.prop i ⟩, fun x => ⟨ fun i => x i |>.1, fun i => x i |>.2 ⟩, fun x => rfl, fun x => rfl ⟩;
  · exact trivial
  · exact DiscreteMeasurableSpace.forall_measurableSet (s := {ω : Fin t → Fin m | ∀ (i : Fin t), check (ω i)})

end MainTheorem
