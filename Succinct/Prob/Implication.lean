import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Set.Lattice

/-!
# Probabilistic Implication (Section 1.4)

This module formalizes the tiny calculus of probabilistic implication used
throughout the paper.  It works at the level of events and provides a thin
wrapper for random variables so the definitions match the paper's notation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Succinct.Prob

/-- Event-level probabilistic implication: `A ⟹[μ]_(p) B` means
`μ (A ∩ Bᶜ) ≤ p`.  This is exactly the definition in §1.4 of the paper. -/
def ProbImpEv {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Set Ω) (p : ℝ≥0∞) : Prop :=
  μ (A ∩ Bᶜ) ≤ p

notation:50 A " ⟹[" μ "]_(" p ")" B => ProbImpEv μ A B p

/-- Random-variable-level wrapper: `P ⟹[μ; r ⇒ s]_(p) Q` expands to the
event version on `{ω | P (r ω)}` and `{ω | Q (s ω)}`. -/
def ProbImp {Ω α β : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (r : Ω → α) (s : Ω → β)
    (P : α → Prop) (Q : β → Prop) (p : ℝ≥0∞) : Prop :=
  ProbImpEv μ ({ω | P (r ω)}) ({ω | Q (s ω)}) p

notation:50 P " ⟹[" μ "; " r " ⇒ " s "]_(" p ")" Q =>
  ProbImp μ r s P Q p

/-- If `p = 0`, probabilistic implication is almost-sure implication. -/
lemma zero_iff {Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    {A B : Set Ω} :
    (A ⟹[μ]_((0 : ℝ≥0∞)) B) ↔ μ (A ∩ Bᶜ) = 0 := by
  constructor
  · intro h; exact le_antisymm h bot_le
  · intro h; exact le_of_eq h

/-- Chaining (union bound): if `A ⇒ₚ B` and `B ⇒_{p'} C` then `A ⇒_{p+p'} C`. -/
lemma chain {Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    {A B C : Set Ω} {p p' : ℝ≥0∞}
    (h₁ : A ⟹[μ]_(p) B) (h₂ : B ⟹[μ]_(p') C) :
    A ⟹[μ]_(p + p') C := by
  have hsubset : A ∩ Cᶜ ⊆ (A ∩ Bᶜ) ∪ (B ∩ Cᶜ) := by
    intro ω hω
    rcases hω with ⟨hA, hC⟩
    by_cases hB : ω ∈ B
    · exact Or.inr ⟨hB, hC⟩
    · have hB' : ω ∈ Bᶜ := by simpa using hB
      exact Or.inl ⟨hA, hB'⟩
  calc
    μ (A ∩ Cᶜ)
        ≤ μ ((A ∩ Bᶜ) ∪ (B ∩ Cᶜ)) := measure_mono hsubset
    _ ≤ μ (A ∩ Bᶜ) + μ (B ∩ Cᶜ)     := measure_union_le _ _
    _ ≤ p + p'                       := add_le_add h₁ h₂

/-- Contrapositive (same randomness): `A ⇒ₚ B` implies `Bᶜ ⇒ₚ Aᶜ`. -/
lemma contrapositive {Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    {A B : Set Ω} {p : ℝ≥0∞}
    (h : A ⟹[μ]_(p) B) :
    Bᶜ ⟹[μ]_(p) Aᶜ := by
  -- `Bᶜ ∩ A = A ∩ Bᶜ`, so the bound is identical.
  simpa [ProbImpEv, Set.inter_comm] using h

/-- Conjunction rule from §1.4 (deterministic `Q`) under independence:
If `A ⇒ₚ Q` and `B ⇒_{p'} Q`, with `A` independent of `B`, then
`(A ∩ B) ⇒_{p*p'} Q`. -/
lemma conj_of_indep_const {Ω} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Set Ω} {Q : Prop} [Decidable Q]
    {p p' : ℝ≥0∞}
    (hA : A ⟹[μ]_(p) {_ω | Q})
    (hB : B ⟹[μ]_(p') {_ω | Q})
    (h_ind : IndepSet A B μ) :
    (A ∩ B) ⟹[μ]_((p * p')) {_ω | Q} := by
  classical
  by_cases hQ : Q
  · -- If `Q` is true, the failure event is empty.
    have hQtrue : ({ω | Q} : Set Ω) = Set.univ := by
      ext ω; simp [hQ]
    simp [ProbImpEv, hQtrue, Set.compl_univ, measure_empty]
  · -- If `Q` is false, the failure event is `A ∩ B`.
    have hQfalse : ({ω | Q} : Set Ω) = (∅ : Set Ω) := by
      ext ω; simp [hQ]
    have hA' : μ A ≤ p := by
      simpa [ProbImpEv, hQfalse, Set.compl_empty, Set.inter_univ] using hA
    have hB' : μ B ≤ p' := by
      simpa [ProbImpEv, hQfalse, Set.compl_empty, Set.inter_univ] using hB
    have hAB : μ (A ∩ B) = μ A * μ B := by
      simpa using (h_ind.measure_inter_eq_mul)
    calc
      μ ((A ∩ B) ∩ {ω | Q}ᶜ)
          = μ (A ∩ B) := by simp [hQfalse]
      _ = μ A * μ B := hAB
      _ ≤ p * p' := by
        refine mul_le_mul hA' hB' ?_ ?_
        · exact bot_le
        · exact bot_le

end Succinct.Prob
