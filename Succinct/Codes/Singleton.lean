module

public import Succinct.Codes.Core
public import Succinct.Codes.Distance
public import Succinct.Codes.SingletonLemmas
public import Mathlib.Data.Nat.Basic

public section

noncomputable section

namespace SuccinctProofs

/-! ### Singleton Bound

The Singleton bound is a fundamental limit on linear codes:
    d ≤ n - k + 1
where d is the minimum distance, n is the block length, and k is the message dimension.
The generator must be injective, so the image code also has dimension k.
-/

section SingletonBound

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **Singleton Bound**: For an injective generator over a finite field F with
    positive message length, the minimum distance satisfies d ≤ m - n + 1.

    PROVED by Aristotle (Batch 19, c4d4f45f-3516-4181-98c0-6ad72281d542).
    The distance equals the minimum weight of a nonzero image codeword.

    The proof uses the kernel dimension argument via helper lemmas in SingletonLemmas:
    - exists_nonzero_mem_kernel_of_rows: finds nonzero x with Gx = 0 on selected rows
    - weight_le_of_subset_zeros: bounds weight by positions where v = 0
    - distance_eq_weightSet_range_diff_zero: identifies nonzero image codewords

    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem singleton_bound (C : LinearCode F) (hn : 0 < C.n)
    (hG : Function.Injective (encode C)) :
    (distance C : WithTop ℕ) ≤ (C.m - C.n + 1 : ℕ) := by
  classical
  rw [distance_eq_weightSet_range_diff_zero C hG]
  -- Proof adapted from Aristotle's portable Singleton bound (Batch 57)
  -- We require n > 0 as a precondition since the bound doesn't make sense for n = 0
  -- (when n = 0, distance = ⊤ and the inequality ⊤ ≤ m + 1 is false)
  -- Let k_val = min(m, n-1). Since k_val ≤ n - 1 < n, we have |S| < n.
  set k_val := min C.m (C.n - 1) with hk_val_def_val
  have h_subset : ∃ S : Finset (Fin C.m), S.card = k_val := by
    have hS : k_val ≤ C.m := by exact min_le_left _ _
    have hS : k_val ≤ Fintype.card (Fin C.m) := by
      rwa [Fintype.card_fin]
    exact Exists.imp (by aesop) (Finset.exists_subset_card_eq hS)
  obtain ⟨S, hS_card, hS⟩ : ∃ S : Finset (Fin C.m), S.card = k_val ∧
      ∃ x : Fin C.n → F, x ≠ 0 ∧ ∀ i ∈ S, Matrix.mulVec C.G x i = 0 := by
    obtain ⟨S, hS_card⟩ := h_subset
    have h_card_lt : S.card < C.n := by
      have hn_ne : C.n ≠ 0 := by omega
      linarith [hS_card, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn_ne),
        min_le_right C.m (C.n - 1)]
    obtain ⟨x, hx⟩ := exists_ne_zero_mulVec_restrict_eq_zero C.G S h_card_lt
    exact ⟨S, hS_card, x, hx⟩
  -- Injectivity makes the encoding of the nonzero message a nonzero codeword.
  obtain ⟨x, hx_ne_zero, hx_zero⟩ := hS
  have hx_encode_ne_zero : encode C x ≠ 0 := by
    intro hx
    apply hx_ne_zero
    apply hG
    simpa [encode] using hx
  have h_dist_le : weightSet (Set.range (encode C) \ {0}) ≤
      weightVec (Matrix.mulVec C.G x) := by
    exact sInf_le ⟨encode C x, ⟨⟨x, rfl⟩, hx_encode_ne_zero⟩, rfl⟩
  -- By weight_le_of_subset_zeros, we know that ‖Gx‖₀ ≤ m - S.card
  have h_weight_le : weightVec (Matrix.mulVec C.G x) ≤ C.m - S.card := by
    exact weight_le_of_subset_zeros (Matrix.mulVec C.G x) S hx_zero
  -- Combine the inequalities (need to cast weight to WithTop ℕ)
  have h_combined : weightSet (Set.range (encode C) \ {0}) ≤
      (C.m - S.card : ℕ) := by
    exact le_trans h_dist_le (Nat.cast_le.mpr h_weight_le)
  -- Show that m - S.card ≤ m - n + 1
  have h_final : (C.m - S.card : ℕ) ≤ (C.m - C.n + 1 : ℕ) := by
    have h1 : S.card = k_val := hS_card
    have h2 : k_val ≤ C.n - 1 := by exact min_le_right _ _
    have h3 : S.card ≤ C.n - 1 := by linarith [h1, h2]
    have h4 : C.n - 1 < C.n := by
      have hn_ne : C.n ≠ 0 := by omega
      exact Nat.sub_lt (Nat.one_le_iff_ne_zero.mpr hn_ne) (by norm_num)
    have h5 : S.card < C.n := by linarith [h3, h4]
    -- Use omega to solve the arithmetic
    omega
  -- Combine to get the final result
  exact le_trans h_combined (Nat.cast_le.mpr h_final)

end SingletonBound

end SuccinctProofs
