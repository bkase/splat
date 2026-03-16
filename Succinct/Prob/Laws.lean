import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Set.Lattice
import Succinct.Prob.Implication

/-!
# Additional Probabilistic Laws (Section 1.4)

Extensions to the probabilistic implication calculus.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Succinct.Prob

/-- **Monotonicity**: If A ⇒ₚ B and p ≤ p', then A ⇒₍p'₎ B (weaker bound) -/
lemma monotone {Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    {A B : Set Ω} {p p' : ℝ≥0∞}
    (h : A ⟹[μ]_(p) B) (hle : p ≤ p') :
    A ⟹[μ]_(p') B := by
  calc
    μ (A ∩ Bᶜ) ≤ p := h
    _         ≤ p' := hle

end Succinct.Prob
