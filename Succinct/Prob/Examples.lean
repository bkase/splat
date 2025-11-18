import Succinct.Prob.Implication

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Succinct.Prob

/-!
Small sanity-check examples for the probabilistic implication notation.
-/

section
  variable {Ω : Type*} [MeasurableSpace Ω]
  variable (μ : Measure Ω) [IsProbabilityMeasure μ]
  variable {A B C : Set Ω} {p q : ℝ≥0∞}

  example (h1 : A ⟹[μ]_(p) B) (h2 : B ⟹[μ]_(q) C) :
      A ⟹[μ]_(p + q) C :=
    chain h1 h2

  example (h : A ⟹[μ]_(p) B) :
      Bᶜ ⟹[μ]_(p) Aᶜ :=
    contrapositive h
end
