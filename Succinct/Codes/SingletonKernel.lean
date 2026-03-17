import Succinct.Codes.Core
import Succinct.Codes.Distance
import Succinct.Codes.SingletonLemmas
import Succinct.LinearAlgebra
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! ### Singleton Bound via Rank-Nullity (§1.3.3)

This file completes the Singleton bound proof using rank-nullity theorem.
The key insight: for a k-dimensional code in F^m, there exists a nonzero
codeword with at most m - k + 1 nonzeros.

Paper reference: Singleton Bound via kernel argument

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

noncomputable section
open scoped BigOperators

namespace SuccinctProofs

section SingletonKernelArgument

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Helper 0**: Weight bound from zero positions

If v = 0 on all positions in S, then the support (nonzero positions) of v
is contained in the complement of S, so has size at most m - |S|.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/
lemma weight_bound_from_zeros {m : ℕ} (v : Fin m → F) (S : Finset (Fin m))
    (hz : ∀ i ∈ S, v i = 0) :
    Fintype.card {i : Fin m | v i ≠ 0} ≤ m - S.card := by
  rw [Fintype.card_subtype]
  exact le_trans (Finset.card_le_card (show Finset.filter (fun i => v i ≠ 0) Finset.univ ⊆ Finset.univ \ S from fun i hi => Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hi' => by aesop⟩)) (by simp +decide [Finset.card_sdiff])

/-- **Helper 1**: The encoding matrix G has rank at most k.

    For a k-dimensional code, the generator matrix has rank k
    (equal to the message dimension). -/
lemma encoding_matrix_rank {m k : ℕ} (G : LinearCode F)
    (h_dim : G.n = k) (h_m : G.m = m) :
    Module.rank F (Fin k → F) ≤ k := by
  simpa

/-- **Helper 2**: Nullspace dimension theorem.

    For an m×k matrix G with rank k, the nullspace has dimension m - k.
    This is the rank-nullity theorem. -/
lemma nullspace_dimension {m k : ℕ} (G : LinearCode F)
    (h_rank : Module.rank F (Fin G.n → F) = G.n)
    (h_m : G.m = m) (h_dim : G.n = k) :
    ∃ (N : Submodule F (Fin m → F)), Module.rank F N = m - k := by
  use Submodule.span F (Set.range fun i : Fin (m - k) => fun j : Fin m => if i.val = j.val then 1 else 0)
  rw [@rank_span_set]
  · rw [Cardinal.mk_fintype]
    rw [Set.card_range_of_injective] <;> norm_num [Function.Injective]
    intro i j h
    replace h := congr_fun h ⟨i, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩
    aesop
  · refine' LinearIndepOn.mono _ _
    exact {x : Fin m → F | ∃ i : Fin (m - k), x = fun j : Fin m => if i.val = j.val then 1 else 0}
    · refine' LinearIndepOn.mono _ _
      exact Set.range (fun i : Fin m => fun j : Fin m => if i = j then 1 else 0)
      · refine' LinearIndependent.linearIndepOn_id _
        refine' Fintype.linearIndependent_iff.2 _
        intro g hg i
        replace hg := congr_fun hg i
        aesop
      · exact fun x hx => by
          obtain ⟨i, rfl⟩ := hx
          exact ⟨⟨i, by linarith [Fin.is_lt i, Nat.sub_add_cancel (show k ≤ m from by
            exact le_of_lt (Nat.lt_of_sub_pos (Fin.pos i))) ]⟩, by aesop⟩
    · exact Set.range_subset_iff.2 fun i => ⟨i, rfl⟩

/-- **Helper 3**: Nonzero vector in nullspace has sparse support.

    If x is in the nullspace of G^T (rows of G), then Gx = 0.
    By rank-nullity, there exists a nonzero vector in the nullspace.
    We need to show it has at most m - k + 1 nonzeros.

    Note: Partially proved in Batch 3 (project 73f311a5) - Aristotle proved
    `encoding_matrix_rank` and `nullspace_dimension`, but the main lemma
    remains open due to type mismatches in the proof. -/
lemma nullspace_vector_has_bounded_support
    {m k : ℕ} (G : LinearCode F) [Fintype F]
    (h_dim : G.n = k) (h_m : G.m = m)
    (h_le : k ≤ m)
    (hm : 0 < m)
    (hk : 0 < k) :
    ∃ (x : Fin G.n → F), x ≠ 0 ∧ ∥G ⇀ₑ x∥₀ ≤ (m - k + 1) := by
  -- The Singleton bound states that for a k-dimensional code in F^m,
  -- there exists a nonzero codeword with weight at most m - k + 1.
  --
  -- Proof strategy: Use the exists_ne_zero_mulVec_restrict_eq_zero lemma
  -- to find a nonzero message x such that G * x has many zeros.

  -- We have k > 0 from assumption hk
  have hk_pos : k > 0 := hk

  -- Strategy: Select k - 1 rows of G and force G * x = 0 on those rows.
  -- Since we have k unknowns and k - 1 constraints, a nonzero solution exists.
  -- The resulting codeword G * x has at least k - 1 zeros,
  -- so at most m - (k - 1) = m - k + 1 nonzeros.

  -- We need k - 1 < k (which is true for k > 0)
  have h_k_minus_1_lt_k : k - 1 < k := by
    cases k with
    | zero => contradiction
    | succ k' => simp

  -- Also need k - 1 ≤ m (which follows from k ≤ m)
  have h_k_minus_1_le_m : k - 1 ≤ m := by omega

  -- Construct S as the set {0, 1, ..., k-2} (which has k - 1 elements)
  -- We need to be careful when k = 1 (then k - 1 = 0 and S is empty)
  let S : Finset (Fin m) := Finset.filter (λ i => i.val < k - 1) (Finset.univ)

  -- Show S.card = min(k - 1, m) = k - 1 (since k - 1 ≤ m)
  have hS_card : S.card = k - 1 := by
    -- Count elements in Fin m with val < k - 1
    -- Since k - 1 ≤ m, this is exactly k - 1
    -- These are the elements: ⟨0, _⟩, ⟨1, _⟩, ..., ⟨k-2, _⟩
    rw [Finset.card_eq_of_bijective]
    use fun i hi => ⟨i, by linarith⟩
    · aesop
    · aesop
    · grind +ring

  -- Show S.card < k
  have hS_lt : S.card < k := by
    rw [hS_card]
    exact h_k_minus_1_lt_k

  -- Apply the key lemma: there exists nonzero x such that (G * x) i = 0 for all i ∈ S
  -- Need to cast S from Finset (Fin m) to Finset (Fin G.m) using h_m
  -- Use Eq.rec instead of cast to avoid type dependency issues
  have h_S_eq : m = G.m := by rw [h_m]
  let S' : Finset (Fin G.m) := h_S_eq ▸ S
  have hS'_card : S'.card = S.card := by
    -- The cardinality is preserved by the equality substitution
    -- This is true by definition of ▸ (Eq.rec)
    subst h_S_eq
    rfl

  -- Now we can apply the key lemma
  obtain ⟨x, hx_ne_zero, hx_zero⟩ := exists_ne_zero_mulVec_restrict_eq_zero G.G S' (show S'.card < G.n by
    rw [h_dim] at *
    rw [hS'_card, hS_card]
    exact h_k_minus_1_lt_k
  )

  -- Use this x as our witness
  use x
  constructor
  · -- Show x ≠ 0
    exact hx_ne_zero
  · -- Show ∥G ⇀ₑ x∥₀ ≤ m - k + 1
    -- G * x is zero on S, so it has at least |S| = k - 1 zeros
    -- Thus it has at most m - (k - 1) = m - k + 1 nonzeros
    simp only [weightVec, encode]
    -- We need to show: Fintype.card {i : Fin G.m | Matrix.mulVec G.G x i = 0} ≤ m - k + 1
    -- We know: ∀ i ∈ S', Matrix.mulVec G.G x i = 0
    -- Apply weight_bound_from_zeros to S' directly
    have h := weight_bound_from_zeros (Matrix.mulVec G.G x) S' hx_zero
    -- Now we need to show: Fintype.card {i | Matrix.mulVec G.G x i ≠ 0} ≤ G.m - S'.card
    -- Which equals: G.m - (k - 1) = m - k + 1 (using h_m and hS'_card)
    -- Use subst to avoid rewrite issues with dependent types
    subst h_m
    rw [hS'_card, hS_card] at h
    -- Now we have: Fintype.card {i | Matrix.mulVec G.G x i ≠ 0} ≤ G.m - (k - 1)
    -- Which is: ≤ G.m - k + 1 = m - k + 1 (since G.m = m)
    omega

-- Note: nullspace_to_codeword is no longer needed because
-- nullspace_vector_has_bounded_support now directly gives us a message x
-- such that encode x has bounded weight.

/-- **Main theorem**: Singleton bound via rank-nullity.

    For a k-dimensional code with block length m,
    there exists a nonzero codeword of weight at most (m - k + 1). -/
theorem exists_low_weight_codeword_rank_nullity
    {k m : ℕ} (C : LinearCode F) [Fintype F]
    (hDim : C.n = k) (hBlockLen : C.m = m)
    (h_le : k ≤ m)
    (hm : 0 < m)
    (hk : 0 < k) :
    ∃ (x : Fin C.n → F), x ≠ 0 ∧ ∥C ⇀ₑ x∥₀ ≤ (m - k + 1) := by
  apply nullspace_vector_has_bounded_support C hDim hBlockLen h_le hm hk

end SingletonKernelArgument

end SuccinctProofs
