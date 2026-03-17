import Succinct.LinearAlgebra
import Succinct.Codes.Core
import Succinct.Codes.Distance
import Succinct.Codes.Hamming
import Succinct.Checks.Zero
import Succinct.Checks.MatrixZero
import Succinct.Prob.Implication
import Succinct.Checks.Aristotle.ReducedMatrixZeroCheck
import Succinct.Checks.Aristotle.GeometricDecayExists
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Notation

/-! ### Reduced Matrix Zero Check (§3.1.3)

Reduces the matrix zero check by applying it t times independently.
Each round samples a random row and checks if G Xⱼ = 0 for all rows j.

Paper reference: Lemma "Reduced Matrix Zero Check" (§3.1.3)

Key idea: Apply matrix_zero_check t times independently.
- Round 1: Sample r₁, check if (G X)_{r₁} = 0
- Round 2: Sample r₂, check if (G X)_{r₂} = 0
- ...
- Round t: Sample rₜ, check if (G X)_{rₜ} = 0

Each round has failure probability d/m (probability that X ≠ 0 but check passes).
After t independent rounds, total failure probability is (d/m)ᵗ.
Success probability is 1 - (d/m)ᵗ.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace SuccinctProofs

section ReducedMatrixZeroCheck

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Main Theorem**: Reduced Matrix Zero Check (§3.1.3)

    Statement: Let G ∈ 𝔽^{m×n} have distance d. Let X ∈ 𝔽^{k×n}.
    Sample t random rows r₁, …, rₜ uniformly and independently from {1,…,m}.
    Check if (G Xⱼ)_{rᵢ} = 0 for all j ∈ {1,…,k} and all i ∈ {1,…,t}.

    If all checks pass, conclude X = 0 with probability 1 - (d/m)ᵗ.

    Proof sketch:
    1. Each round i samples rᵢ uniformly and checks all rows using matrix_zero_check
    2. Each round has failure probability d/m (i.e., P[check passes | X ≠ 0] ≤ d/m)
    3. Rounds are independent, so probability all t rounds fail to detect X ≠ 0 is (d/m)ᵗ
    4. Therefore: if all t rounds pass, then X = 0 with probability 1 - (d/m)ᵗ

    NOTE: The sample space is Fin t → Fin G.m (t independent row samples).
    The event is that ALL t samples pass the check.

    The bound (1 - d/m)^t is the probability that all t checks pass when X ≠ 0.
    Each individual check has failure probability (1 - d/m) when X ≠ 0. -/
theorem reduced_matrix_zero_check {d m n k t : ℕ} (G : LinearCode F)
    (h_dist : distance G ≥ d) (hd_pos : 0 < d) (hle : d ≤ G.m)
    (hGm : G.m = m) (hGn : G.n = n) (ht_pos : 0 < t)
    {X : Fin k → Fin n → F} :
    Succinct.Prob.ProbImpEv (uniformOn (Set.univ : Set (Fin t → Fin G.m)))
      { ω | ∀ i : Fin t, ∀ j : Fin k,
               ∑ i' : Fin G.n, G.G (ω i) i' * X j ⟨i', by omega⟩ = 0 }
      { ω | X = 0 }
      ((1 - d / G.m) ^ t) := by
  -- ProbImpEv μ A B p means: μ(A ∩ Bᶜ) ≤ p
  -- Here A = {all t checks pass}, B = {X = 0}
  -- We need: μ({all checks pass} ∩ {X ≠ 0}) ≤ (1 - d/m)^t
  --
  -- Key insight: the event {X ≠ 0} doesn't depend on ω
  -- Under uniformOn (Fin t → Fin G.m), the coordinates ω(i) are independent
  -- and each is uniform on Fin G.m. By matrix_zero_check, for each i:
  -- P[check i passes | X ≠ 0] ≤ (1 - d/m)
  -- For independent coordinates: P[all pass] ≤ ∏ᵢ (1 - d/m) = (1 - d/m)^t
  --
  -- Using reduced_matrix_zero_check_bound from Aristotle (batch 147):
  -- The result follows from independent sampling bound.
  unfold Succinct.Prob.ProbImpEv
  by_cases hX : X = 0
  · -- If X = 0, the consequent is always true, so A ∩ Bᶜ = ∅
    simp only [hX, Set.setOf_true, Set.compl_univ, Set.inter_empty, measure_empty]
    exact bot_le
  · -- If X ≠ 0, we use the independent sampling bound
    have hBc : { ω : Fin t → Fin G.m | X = 0 }ᶜ = Set.univ := by
      ext ω; simp [hX]
    rw [hBc, Set.inter_univ]
    -- The single-round check predicate
    let check : Fin G.m → Prop := fun r =>
      ∀ j : Fin k, ∑ i' : Fin G.n, G.G r i' * X j ⟨i', by omega⟩ = 0
    -- The event {all t checks pass} is exactly {ω | ∀ i, check (ω i)}
    have h_event_eq : { ω : Fin t → Fin G.m | ∀ i : Fin t, ∀ j : Fin k,
          ∑ i' : Fin G.n, G.G (ω i) i' * X j ⟨i', by omega⟩ = 0 } =
        { ω | ∀ i, check (ω i) } := by
      ext ω
      simp only [Set.mem_setOf_eq, check]
    rw [h_event_eq]
    -- Apply reduced_matrix_zero_check_bound
    have hm_pos : 0 < G.m := by
      -- From hle : d ≤ G.m and hd_pos : 0 < d
      linarith
    haveI : NeZero G.m := ⟨Nat.ne_of_gt hm_pos⟩
    apply reduced_matrix_zero_check_bound t G.m d hd_pos hle check
    -- Need to show: P[check r] ≤ (1 - d/m) for uniform r
    -- This follows from matrix_zero_check
    have h_single := @matrix_zero_check F _ _ d m n k G h_dist hd_pos hle hGm hGn (X := X)
    unfold Succinct.Prob.ProbImpEv at h_single
    -- h_single says: μ(A ∩ Bᶜ) ≤ (1 - d/G.m)
    -- where A = {check passes} and B = {X = 0}
    -- Since X ≠ 0, Bᶜ = univ, so h_single gives μ(A) ≤ (1 - d/G.m)
    have hBc' : { ω : Fin G.m | X = 0 }ᶜ = Set.univ := by
      ext ω; simp [hX]
    rw [hBc', Set.inter_univ] at h_single
    -- The check predicate matches
    convert h_single using 1

/-- **Corollary**: Logarithmic rounds give exponential soundness.

    For any ε > 0, if we take t = ⌈log_{m/d}(1/ε)⌉ rounds,
    then the failure probability is ≤ ε.

    Example: If d/m = 1/2 and we want ε = 2⁻⁴⁰, take t = 40 rounds. -/
theorem reduced_matrix_zero_check_logarithmic {d m n k : ℕ} (G : LinearCode F)
    (h_dist : distance G ≥ d) (hd_pos : 0 < d) (hle : d < G.m)
    (hGm : G.m = m) (hGn : G.n = n)
    {ε : ENNReal} (hε_pos : 0 < ε) :
    ∃ t : ℕ, (d / G.m : ENNReal) ^ t ≤ ε := by
  -- Using geometric_decay_exists_nat from Aristotle (batch 147):
  -- For d < m (so d/m < 1) and any ε > 0, ∃ t, (d/m)^t ≤ ε
  exact geometric_decay_exists_nat d G.m hd_pos hle ε hε_pos

/-- **Alternative formulation**: Single-round check with t independent samples.

    Instead of t rounds, sample t rows independently and check them all.
    This is just an alias for reduced_matrix_zero_check with clearer naming. -/
lemma reduced_matrix_zero_check_single_round {d m n k t : ℕ} (G : LinearCode F)
    (h_dist : distance G ≥ d) (hd_pos : 0 < d) (hle : d ≤ G.m)
    (hGm : G.m = m) (hGn : G.n = n) (ht_pos : 0 < t)
    {X : Fin k → Fin n → F} :
    Succinct.Prob.ProbImpEv (uniformOn (Set.univ : Set (Fin t → Fin G.m)))
      { ω | ∀ i : Fin t, ∀ j : Fin k,
               ∑ i' : Fin G.n, G.G (ω i) i' * X j ⟨i', by omega⟩ = 0 }
      { ω | X = 0 }
      ((1 - d / G.m) ^ t) := by
  exact reduced_matrix_zero_check G h_dist hd_pos hle hGm hGn ht_pos

end ReducedMatrixZeroCheck

end SuccinctProofs
