import Succinct.LinearAlgebra
import Succinct.Codes.Core
import Succinct.Codes.Distance
import Succinct.Codes.Hamming
import Succinct.Prob.Implication
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Notation

/-! ### Zero Check (§3.1.1)

Zero check using high-distance linear codes: if a random coordinate
of the encoded message is zero, then with high probability the original
message is zero.

Paper reference: Lemma "Zero Check" (§3.1.1)
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace SuccinctProofs

section ZeroCheck

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Zero Check Lemma** (§3.1.1): For a code G with distance d,
    if a random coordinate of Gx is zero, then x = 0 with high probability.

    Statement: Let G ∈ 𝔽^{m×n} have distance d. Let x ∈ 𝔽^n.
    Let r be uniform on {1,…,m}.
    Then: (Gx)_r = 0 ⇒_{1-d/m} x = 0

    Proof sketch: If x ≠ 0, then Gx ≠ 0 (by injectivity from distance > 0).
    By definition of distance, ∥Gx∥₀ ≥ d, meaning at least d coordinates are nonzero.
    The probability a random r hits one of these is d/m.
    Thus: ℙ[(Gx)_r = 0 | x ≠ 0] ≤ 1 - d/m. -/
lemma zero_check {d : ℕ} (G : LinearCode F)
    (h_dist : distance G ≥ d)
    (hd_pos : 0 < d) (hle : d ≤ G.m)
    {x : Vec F G.n} :
    Succinct.Prob.ProbImpEv (uniformOn (Set.univ : Set (Fin G.m)))
      { ω | (G ⇀ₑ x) ω = 0 }
      { ω | x = 0 }
      (1 - d / G.m) := by
  -- Key steps:
  -- 1. If x ≠ 0, then by distance definition, ∥G ⇀ₑ x∥₀ ≥ d
  -- 2. This means |{i | (G ⇀ₑ x) i ≠ 0}| ≥ d
  -- 3. For random r, ℙ[(G ⇀ₑ x) r = 0] = |{i | (G ⇀ₑ x) i = 0}| / m ≤ (m-d)/m
  -- 4. So failure probability (x ≠ 0 but check passes) ≤ 1 - d/m
  by_cases hx : x = 0 <;> simp_all +decide [ Finset.filter_ne', ProbabilityTheory.uniformOn, ProbabilityTheory.cond, MeasureTheory.Measure.restrict_apply, Set.indicator_apply ];
  · exact le_trans ( by aesop ) ( zero_le _ );
  · -- Since the distance is at least d, the number of non-zero coordinates in Gx is at least d.
    have h_nonzero_coords : ∑ i : Fin G.m, (if (G ⇀ₑ x) i = 0 then 0 else 1) ≥ d := by
      have h_nonzero_coords : ∑ i : Fin G.m, (if (G ⇀ₑ x) i = 0 then 0 else 1) = ∥G ⇀ₑ x∥₀ := by
        unfold weightVec;
        simp +decide [ Finset.sum_ite, Fintype.card_subtype ];
      exact h_nonzero_coords.symm ▸ Nat.cast_le.mp ( h_dist.trans ( SuccinctProofs.distance_le_weight_encode_nonzero G x hx ) );
    simp_all +decide [ Finset.sum_ite ];
    simp_all +decide [ Finset.filter_not, Finset.card_sdiff ];
    rw [ Nat.le_sub_iff_add_le ] at h_nonzero_coords;
    · refine' le_trans _ ( ENNReal.div_le_of_le_mul _ );
      rotate_left;
      exact ( Finset.card ( Finset.filter ( fun a => ( G ⇀ₑ x ) a = 0 ) Finset.univ ) : ENNReal );
      exact ↑G.m;
      · rw [ ENNReal.sub_mul ];
        · rw [ ENNReal.div_mul_cancel ] <;> norm_cast;
          · exact le_tsub_of_add_le_left ( by linarith );
          · linarith;
          · exact ENNReal.natCast_ne_top _;
        · exact fun a a => ENNReal.natCast_ne_top G.m;
      · simp +decide [ div_eq_inv_mul, MeasureTheory.Measure.count_apply ];
        rw [ ENNReal.div_eq_inv_mul, Set.encard_eq_coe_toFinset_card ] ; aesop;
    · exact le_trans ( Finset.card_le_univ _ ) ( by simp +decide )

end ZeroCheck

end SuccinctProofs
