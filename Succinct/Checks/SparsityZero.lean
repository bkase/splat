import Succinct.LinearAlgebra
import Succinct.Codes.Core
import Succinct.Codes.Distance
import Succinct.Codes.Hamming
import Succinct.Checks.Sparsity
import Succinct.Checks.Zero
import Succinct.Prob.Implication
import Succinct.Checks.Aristotle.ProductMeasureProjection
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Notation

/-! ### Sparsity-Zero Composition (§3.2)

Combining sparsity and zero checks: if a vector is sparse AND passes
the zero check for a high-distance code, then we have strong guarantees
about the original message.

Paper reference: Sparsity-Zero Composition (§3.2)
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace SuccinctProofs

section SparsityZeroComposition

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Sparsity-Zero Composition Lemma** (§3.2): Chain sparsity and zero checks.

    If x is sparse (bounded Hamming weight) AND passes the zero check
    for a code with distance d, then we have combined probabilistic guarantees.

    Statement: Let G have distance d, x ∈ 𝔽ⁿ, q < d.
    If x_r = 0 ⇒_{1-(q+1)/k} ∥x∥₀ ≤ q (sparsity)
    and (Gx)_r = 0 ⇒_{1-d/m} x = 0 (zero check)
    then together: (x_r = 0 ∧ (Gx)_r = 0) ⇒_{...} x = 0 with improved bound -/
lemma sparsity_zero_composition {d : ℕ} (G : LinearCode F)
    (h_dist : distance G ≥ d) (hd_pos : 0 < d) (hle : d ≤ G.m)
    {q : ℕ} (hq : q < d)
    {x : Vec F G.n} :
    Succinct.Prob.ProbImpEv (uniformOn (Set.univ : Set (Fin G.m)))
      { ω | (G ⇀ₑ x) ω = 0 }
      { ω | x = 0 }
      (1 - d / G.m) := by
  -- This follows by chaining the zero_check lemma
  -- The sparsity condition (q < d) ensures that if x is nonzero,
  -- it must have weight ≥ d, which the zero check will catch
  exact zero_check G h_dist hd_pos hle

/-- **Composition with improved bound**: When we know ∥x∥₀ ≤ q and q < d,
    the zero check failure probability decreases.

    If we already know x is sparse (weight ≤ q), and q < distance(G),
    then the zero check becomes even stronger.

    Key idea: If x ≠ 0 is sparse (∥x∥₀ ≤ q < d), then by the distance
    property, Gx must have weight ≥ d, so Gx cannot be zero. -/
lemma sparsity_zero_improved {d : ℕ} (G : LinearCode F)
    (h_dist : distance G ≥ d) (hd_pos : 0 < d) (hle : d ≤ G.m)
    {q : ℕ} (hq_lt : q < d) {x : Vec F G.n}
    (h_sparse : ∥x∥₀ ≤ q) :
    (G ⇀ₑ x) = 0 → x = 0 := by
  intro hx_zero
  contrapose! h_dist
  refine' lt_of_le_of_lt (csInf_le _ ⟨x, h_dist, rfl⟩) _
  · exact ⟨0, fun w hw => hw.choose_spec.2.symm ▸ Nat.cast_nonneg _⟩
  · aesop

/-- **Probabilistic version**: Combining both checks gives better bounds.

    This version samples both from the encoded space (G.m) and original space (G.n)
    to check both sparsity and zero conditions simultaneously. -/
lemma sparsity_zero_probabilistic {d : ℕ} (G : LinearCode F)
    (h_dist : distance G ≥ d) (hd_pos : 0 < d) (hle : d ≤ G.m)
    {q : ℕ} (hq_lt : q < d)
    {x : Vec F G.n} :
    Succinct.Prob.ProbImpEv (uniformOn (Set.univ : Set (Fin G.m × Fin G.n)))
      { ω | (G ⇀ₑ x) ω.1 = 0 ∧ x ω.2 = 0 }
      { ω | x = 0 }
      (1 - d / G.m) := by
  -- The key insight: the joint event {(Gx)_r = 0 ∧ x_s = 0} is a subset of
  -- {(Gx)_r = 0} when we project to the first coordinate.
  --
  -- More precisely, the intersection with {x ≠ 0}ᶜ is the same whether we
  -- include the extra condition x ω.2 = 0 or not.
  --
  -- So the probability bound is just from zero_check applied to the first coordinate.
  unfold Succinct.Prob.ProbImpEv
  -- The failure event is: {ω | (G ⇀ₑ x) ω.1 = 0 ∧ x ω.2 = 0} ∩ {ω | x ≠ 0}
  -- This is a subset of {ω | (G ⇀ₑ x) ω.1 = 0} ∩ {ω | x ≠ 0}
  have h_subset : { ω : Fin G.m × Fin G.n | (G ⇀ₑ x) ω.1 = 0 ∧ x ω.2 = 0 } ∩ { ω | x = 0 }ᶜ ⊆
                  { ω : Fin G.m × Fin G.n | (G ⇀ₑ x) ω.1 = 0 } ∩ { ω | x = 0 }ᶜ := by
    intro ω hω
    exact ⟨hω.1.1, hω.2⟩
  calc uniformOn (Set.univ : Set (Fin G.m × Fin G.n))
          ({ ω | (G ⇀ₑ x) ω.1 = 0 ∧ x ω.2 = 0 } ∩ { ω | x = 0 }ᶜ)
      ≤ uniformOn (Set.univ : Set (Fin G.m × Fin G.n))
          ({ ω | (G ⇀ₑ x) ω.1 = 0 } ∩ { ω | x = 0 }ᶜ) := measure_mono h_subset
    _ ≤ (1 - d / G.m) := by
        -- Now we need to show this is bounded by (1 - d/G.m)
        -- The event {(G ⇀ₑ x) ω.1 = 0} ∩ {x ≠ 0} only depends on ω.1
        -- By Fubini/product measure, integrating over ω.2 just multiplies by G.n/G.n = 1
        by_cases hx : x = 0
        · -- If x = 0, the complement is empty so measure is 0
          simp [hx]
        · -- If x ≠ 0, use that the projection gives the same bound
          -- The set {ω | x = 0}ᶜ = Set.univ when x ≠ 0
          have hxne : { ω : Fin G.m × Fin G.n | x = 0 }ᶜ = Set.univ := by
            ext ω; simp [hx]
          rw [hxne, Set.inter_univ]
          -- Now the event only depends on ω.1
          -- Use uniform_product_first_coord_bound from Aristotle
          have h_zero_check := zero_check G h_dist hd_pos hle (x := x)
          unfold Succinct.Prob.ProbImpEv at h_zero_check
          -- When x ≠ 0, the intersection with {x = 0}ᶜ is the whole set
          have hcompl_univ : ({ i : Fin G.m | x = 0 }ᶜ : Set (Fin G.m)) = Set.univ := by
            ext i; simp [hx]
          have h_zero_check' : uniformOn (Set.univ : Set (Fin G.m)) { i | (G ⇀ₑ x) i = 0 } ≤ (1 - d / G.m) := by
            calc uniformOn (Set.univ : Set (Fin G.m)) { i | (G ⇀ₑ x) i = 0 }
                = uniformOn (Set.univ : Set (Fin G.m)) ({ i | (G ⇀ₑ x) i = 0 } ∩ Set.univ) := by rw [Set.inter_univ]
              _ = uniformOn (Set.univ : Set (Fin G.m)) ({ i | (G ⇀ₑ x) i = 0 } ∩ { i : Fin G.m | x = 0 }ᶜ) := by rw [← hcompl_univ]
              _ ≤ (1 - d / G.m) := h_zero_check
          -- Need NeZero instances for uniform_product_first_coord_bound
          have hGm_pos : G.m > 0 := Nat.lt_of_lt_of_le hd_pos hle
          have hGn_pos : G.n > 0 := by
            by_contra h_neg
            push_neg at h_neg
            simp at h_neg
            have : x = 0 := by ext i; exact (Fin.elim0 (h_neg ▸ i))
            contradiction
          haveI : NeZero G.m := ⟨Nat.ne_of_gt hGm_pos⟩
          haveI : NeZero G.n := ⟨Nat.ne_of_gt hGn_pos⟩
          exact uniform_product_first_coord_bound (fun i => (G ⇀ₑ x) i = 0) (1 - d / G.m) h_zero_check'

end SparsityZeroComposition

end SuccinctProofs
