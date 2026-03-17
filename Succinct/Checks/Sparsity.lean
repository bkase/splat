import Succinct.LinearAlgebra
import Succinct.Codes.Hamming
import Succinct.Prob.Implication
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Notation

/-! ### Sparsity Check (§3.2)

Sparsity testing via random sampling: if a randomly chosen coordinate
is zero, then with high probability the entire vector has bounded weight.

Paper reference: Lemma "Sparsity Check" (§3.2)
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace SuccinctProofs

section SparsityCheck

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Sparsity Check Lemma** (§3.2): If a random coordinate of x is zero,
    then with high probability the Hamming weight of x is bounded by q.

    Statement: For x ∈ 𝔽^k, q ∈ {0,…,k}, and r uniform on {1,…,k}:
    x_r = 0 ⇒_{1-(q+1)/k} ∥x∥₀ ≤ q

    Proof sketch: If ∥x∥₀ > q+1, then at least q+1 coordinates are nonzero.
    The probability a random r misses all of them is (1 - (q+1)/k)^1 ≤ 1 - (q+1)/k. -/
lemma sparsity_check {k : ℕ} {x : Vec F k} {q : ℕ}
    (hq : q ≤ k) :
    Succinct.Prob.ProbImpEv (uniformOn (Set.univ : Set (Fin k)))
      { ω | x ω = 0 }
      { ω | ∥x∥₀ ≤ q }
      (1 - (q + 1) / k) := by
  -- If ∥x∥₀ > q, then |{i | x i ≠ 0}| ≥ q+1
  -- The probability that a random r satisfies x r = 0 is:
  --   |{i | x i = 0}| / k = (k - |{i | x i ≠ 0}|) / k ≤ (k - (q+1)) / k
  -- Therefore: ℙ[r | x r = 0 ∧ ∥x∥₀ > q] ≤ 1 - (q+1)/k
  by_contra h;
  -- If $x$ is not sparse, then $\|x\|_0 > q$.
  have h_not_sparse : ∥x∥₀ > q := by
    exact lt_of_not_ge fun h' => h ( by simp_all +decide [ Succinct.Prob.ProbImpEv ] );
  -- If $x$ is not sparse, then there are at least $q+1$ nonzero coordinates.
  have h_nonzero_coords : ∃ s : Finset (Fin k), s.card ≥ q + 1 ∧ ∀ i ∈ s, x i ≠ 0 := by
    have h_nonzero_coords : Finset.card (Finset.filter (fun i => x i ≠ 0) Finset.univ) > q := by
      convert h_not_sparse using 1;
      simp +decide [ weightVec ];
      rw [ Fintype.card_subtype ];
      rw [ Finset.filter_not, Finset.card_sdiff ] ; aesop;
    exact ⟨ _, h_nonzero_coords, fun i hi => Finset.mem_filter.mp hi |>.2 ⟩;
  obtain ⟨ s, hs₁, hs₂ ⟩ := h_nonzero_coords;
  -- The probability that a random coordinate is zero is at most $(k - (q + 1)) / k = 1 - (q + 1) / k$.
  have h_prob_zero : (ProbabilityTheory.uniformOn (Set.univ : Set (Fin k)) {ω : Fin k | x ω = 0}) ≤ ENNReal.ofReal (1 - (q + 1) / k : ℝ) := by
    by_cases hk : k = 0 <;> simp_all +decide [ ProbabilityTheory.uniformOn ];
    · exact prob_le_one;
    · -- The probability that a random coordinate is zero is at most $(k - (q + 1)) / k$.
      have h_prob_zero : (Finset.card (Finset.filter (fun i => x i = 0) Finset.univ) : ℝ) / k ≤ 1 - (q + 1) / k := by
        have h_prob_zero : (Finset.card (Finset.filter (fun i => x i = 0) Finset.univ) : ℝ) ≤ k - (q + 1) := by
          exact le_tsub_of_add_le_right ( mod_cast by linarith [ show Finset.card ( Finset.filter ( fun i => x i = 0 ) Finset.univ ) + Finset.card ( Finset.filter ( fun i => ¬x i = 0 ) Finset.univ ) = k from by rw [ Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_fin ], show Finset.card ( Finset.filter ( fun i => ¬x i = 0 ) Finset.univ ) ≥ q + 1 from by exact le_trans hs₁ ( Finset.card_le_card fun i hi => by aesop ) ] );
        rw [ one_sub_div ( by positivity ) ] ; gcongr;
      convert ENNReal.ofReal_le_ofReal h_prob_zero using 1;
      rw [ ProbabilityTheory.cond_apply ] <;> norm_num [ hk ];
      rw [ ENNReal.ofReal_div_of_pos ( by positivity ) ] ; norm_num [ mul_comm, MeasureTheory.Measure.count_apply ];
      rw [ Set.encard_eq_coe_toFinset_card ] ; simp +decide [ div_eq_inv_mul ];
      rw [ div_eq_mul_inv, mul_comm ];
  refine' h _;
  refine' le_trans _ ( h_prob_zero.trans _ );
  · apply_rules [ MeasureTheory.measure_mono ];
    exact Set.inter_subset_left;
  · rw [ ENNReal.ofReal_sub ] <;> norm_num;
    · rw [ ENNReal.ofReal_div_of_pos ] <;> norm_num;
      · rw [ ENNReal.ofReal_add ] <;> norm_num;
        rw [ tsub_add_cancel_of_le ];
        rw [ ENNReal.div_le_iff_le_mul ] <;> norm_cast <;> norm_num;
        exact hs₁.trans ( le_trans ( Finset.card_le_univ _ ) ( by simpa ) );
      · cases k <;> norm_num at *;
        exact absurd hs₁ ( by rw [ Finset.card_eq_zero.mpr ( Finset.eq_empty_of_forall_notMem fun i hi => by fin_cases i ) ] ; linarith );
    · positivity

/-- **Alternative formulation**: Using the probability notation directly.
    The complement form: ℙ[x_r ≠ 0] ≥ (q+1)/k when ∥x∥₀ > q. -/
lemma sparsity_check_complement {k : ℕ} {x : Vec F k} {q : ℕ}
    (hq : q ≤ k) (h_heavy : ∥x∥₀ > q) :
    (uniformOn (Set.univ : Set (Fin k))) { ω | x ω ≠ 0 } ≥ (q + 1) / k := by
  -- Direct counting: there are at least q+1 nonzero coordinates
  -- The probability a random r hits one of them is (q+1)/k
  have := @sparsity_check F _ _ k x q hq;
  unfold Succinct.Prob.ProbImpEv at this;
  simp_all +decide [ Set.compl_def ];
  -- Since these two sets are complementary within the uniform distribution, we have:
  have h_compl : (ProbabilityTheory.uniformOn (Set.univ : Set (Fin k))) {ω | x ω = 0} + (ProbabilityTheory.uniformOn (Set.univ : Set (Fin k))) {ω | ¬x ω = 0} = 1 := by
    rw [ ← MeasureTheory.measure_union ] <;> norm_num;
    · rw [ show { ω : Fin k | x ω = 0 } ∪ { ω : Fin k | ¬x ω = 0 } = Set.univ from Set.eq_univ_of_forall fun ω => by by_cases h : x ω = 0 <;> simp +decide [ h ] ] ; simp +decide [ ProbabilityTheory.uniformOn ];
      simp +decide [ ProbabilityTheory.cond, MeasureTheory.Measure.dirac_apply ];
      rw [ ENNReal.inv_mul_cancel ] <;> norm_num ; contrapose! h_heavy ; aesop;
    · exact disjoint_compl_right;
  convert tsub_le_tsub_left this 1 using 1;
  · rw [ ENNReal.sub_sub_cancel ] <;> norm_num;
    rw [ ENNReal.div_le_iff_le_mul ] <;> norm_cast <;> norm_num;
    exact Nat.succ_le_of_lt ( lt_of_lt_of_le h_heavy ( show ∥x∥₀ ≤ k from le_trans ( Fintype.card_subtype_le _ ) ( by simp +decide ) ) );
  · rw [ ← h_compl, ENNReal.add_sub_cancel_left ( by aesop ) ]

/-- **Consequence**: For sparse vectors (small ∥x∥₀), the probability
    that a random sample catches a nonzero entry is small. -/
lemma sparse_vectors_rarely_detected {k : ℕ} {x : Vec F k} {q : ℕ}
    (h_sparse : ∥x∥₀ ≤ q) :
    (uniformOn (Set.univ : Set (Fin k))) { ω | x ω ≠ 0 } ≤ q / k := by
  -- At most q coordinates are nonzero, out of k total
  rcases k with ( _ | k ) <;> simp_all +decide [ uniformOn, Nat.cast_add_one_ne_zero, ProbabilityTheory.cond_apply ];
  · simp +decide [ MeasureTheory.Measure.count ];
  · rw [ ENNReal.div_eq_inv_mul ];
    gcongr;
    convert ENat.coe_le_coe.mpr h_sparse using 1;
    rw [ MeasureTheory.Measure.count_apply ];
    · simp +decide [ Set.encard, weightVec ];
      norm_cast;
    · exact trivial

end SparsityCheck

end SuccinctProofs
