import Succinct.Codes.Core
import Succinct.Codes.Distance
import Mathlib.Data.Nat.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct

noncomputable section

namespace SuccinctProofs

/-! ### Breaking Down the Singleton Bound

The Singleton bound d ≤ n - k + 1 is proved by:
1. A k-dimensional code has a basis of k message vectors
2. The encoding of the basis spans the code's range
3. By linear algebra: ∃ nonzero codeword with ≤ (m - k + 1) nonzeros

This file breaks down the proof into smaller lemmas.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

section SingletonLemmas

variable {F : Type*} [Field F] [DecidableEq F]

open scoped BigOperators

/-- **Helper**: Any vector in F^n can be expressed as a linear combination
    of the standard basis vectors with its coordinates as coefficients.

    For any x, we have x[j] = ∑ᵢ x[i] · eᵢ[j] where eᵢ[j] = 1 if i=j else 0.
    PROVED by Aristotle (Batch 13+, f0fc48d6-0033-4dd7-a4e9-a6be2137a167). -/
lemma any_vector_is_linear_combination_of_basis {n : ℕ} (x : Vec F n) :
    x = fun j => ∑ i : Fin n, x i * (if i = j then 1 else 0) := by
  exact funext fun j => by simp +decide [Finset.sum_ite, Finset.filter_eq']

/-- A linear code with dimension k has a basis of exactly k message vectors.
    This is the standard result that any subspace of dimension k has a basis of size k.

    This is already available as `Module.finBasis` in mathlib for the message space. -/
lemma code_has_message_basis (C : LinearCode F) :
    ∃ (b : Fin C.n → Vec F C.n),
      LinearIndependent F b ∧
      Submodule.span F (Set.range b) = ⊤ := by
  -- The message space F^n has a standard basis
  -- Use Module.finBasis for the vector space F^n
  use fun i => fun j => if j = i then 1 else 0;
  refine' ⟨ Fintype.linearIndependent_iff.2 _, _ ⟩;
  · intro g hg i; replace hg := congr_fun hg i; aesop;
  · refine' eq_top_iff.2 fun x hx => _;
    rw [ Submodule.mem_span_range_iff_exists_fun ];
    exact ⟨ fun i => x i, by ext i; simp +decide ⟩

/-- If a vector x is a linear combination of k basis vectors with coefficients c_j,
    and x is nonzero, then at least one coefficient c_j is nonzero.

    PROVED by Aristotle (Batch 17, d3ccb224-ed38-418d-9805-89ddd194f60c). -/
lemma exists_nonzero_coeff_of_nonzero_combination
    {k m : ℕ} {b : Fin k → Vec F m} {coeffs : Fin k → F}
    (hNonzero : (∑ j : Fin k, coeffs j • b j) ≠ 0) :
    ∃ j : Fin k, coeffs j ≠ 0 := by
  -- If all coeffs were zero, the combination would be zero
  contrapose! hNonzero; simp_all +decide [ Finset.sum_eq_zero ]

/-! ### Helper Lemmas from Aristotle (Batch 19, c4d4f45f-3516-4181-98c0-6ad72281d542)

These lemmas support the portable Singleton bound proof.
-/

variable [Fintype F] in
/-- If we select a set of rows S from a matrix G such that |S| < n,
    then there exists a non-zero vector x such that Gx is zero at all indices in S.

    PROVED by Aristotle (Batch 19, c4d4f45f-3516-4181-98c0-6ad72281d542).
    This is the core lemma for the Singleton bound proof.

    Intuition: A matrix G : F^{m×n} defines n columns in F^m.
    Selecting |S| < n rows gives a linear map L : F^n → F^{|S|}.
    Since domain dimension > codomain dimension, L is not injective.
    Hence ∃ x ≠ y with Lx = Ly, so (x-y) is nonzero and G(x-y) = 0 on S.

    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma exists_nonzero_mem_kernel_of_rows
    {m n : ℕ} (G : Mat F m n) (S : Finset (Fin m)) (hS : S.card < n) :
    ∃ x : Vec F n, x ≠ 0 ∧ ∀ i ∈ S, (Matrix.mulVec G x) i = 0 := by
  classical
  -- Consider the linear map L : F^n → F^S by restricting to rows in S
  let L : (Vec F n) → (S → F) := fun x i => (G.mulVec x) i.val
  -- Since |S| < n, L is not injective (domain larger than codomain)
  have h_not_injective : ¬ Function.Injective L := by
    intro hL_injective
    have := Fintype.card_le_of_injective L hL_injective
    simp +zetaDelta at *
    exact this.not_lt (pow_lt_pow_right₀ (Fintype.one_lt_card) hS)
  simp_all +decide [Function.Injective]
  obtain ⟨x, y, hxy, hne⟩ := h_not_injective
  use x - y
  constructor
  · -- Show x - y ≠ 0
    intro h_eq
    apply hne
    ext i
    simp_all +decide [sub_eq_zero]
  · -- Show (x - y) is in kernel on all positions in S
    intro i hi
    -- From hxy: L x = L y on S, so (Gx)_i = (Gy)_i for all i ∈ S
    -- By linearity, G(x - y) = Gx - Gy = 0 on S
    have h_Gx_eq_Gy : (G.mulVec x) i = (G.mulVec y) i := by
      have h_L_eq : L x ⟨i, hi⟩ = L y ⟨i, hi⟩ := by
        -- From hxy: L x = L y as functions, they agree at every point
        -- In particular, at point ⟨i, hi⟩ which represents i ∈ S
        -- This is exactly congrFun applying function equality pointwise
        apply congrFun hxy ⟨i, hi⟩
      exact h_L_eq
    -- Use linearity of matrix multiplication
    show (G.mulVec (x - y)) i = 0
    -- G(x - y) = Gx - Gy (by linearity)
    have : (G.mulVec (x - y)) i = (G.mulVec x) i - (G.mulVec y) i := by
      -- By definition of matrix-vector multiplication
      unfold Matrix.mulVec
      -- Show: Σ_j G_ij * (x_j - y_j) = Σ_j G_ij * x_j - Σ_j G_ij * y_j
      -- This follows from field distributivity
      simp +decide only [dotProduct];
      exact Eq.symm ( by rw [ ← Finset.sum_sub_distrib ] ; exact Finset.sum_congr rfl fun _ _ => by simp +decide [ mul_sub ] )
    rw [this, h_Gx_eq_Gy]
    simp only [sub_self]

variable [Fintype F] in
/-- If a vector v is zero on a subset of indices S,
    then its Hamming weight is at most m - |S|.

    PROVED by Aristotle (Batch 19, c4d4f45f-3516-4181-98c0-6ad72281d542).

    Intuition: The weight counts positions where v is nonzero.
    If v is zero on all positions in S, then nonzero positions are in Sᶜ.
    So ∥v∥₀ ≤ |Sᶜ| = m - |S|.

    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma weight_le_of_subset_zeros
    {m : ℕ} (v : Vec F m) (S : Finset (Fin m))
    (h : ∀ i ∈ S, v i = 0) :
    weightVec v ≤ m - S.card := by
  classical
  convert Set.ncard_le_ncard (show {i | v i ≠ 0} ⊆ Sᶜ from fun x hx ↦ by aesop) using 1
  · simp +decide [Set.ncard_eq_toFinset_card']
    convert rfl
    convert Set.toFinset_card _
    aesop
  · simp +decide [Set.ncard_eq_toFinset_card', Finset.card_compl]

variable [Fintype F] in
/-- If we select a subset of rows `S` from a matrix `G` such that `|S| < n`
    (where `n` is the number of columns), there exists a non-zero vector `x`
    that is orthogonal to all rows in `S`.

    This is the key lemma for the kernel argument in the Singleton bound proof.
    It uses the rank-nullity theorem to show the kernel is nontrivial.

    PROVED by Aristotle (Batch 57, 01cefa09-29dc-48c9-acb6-b1b8248dd4fe). -/
lemma exists_ne_zero_mulVec_restrict_eq_zero
    {m n : ℕ} (G : Fin m → Fin n → F) (S : Finset (Fin m)) (h : S.card < n) :
    ∃ x : Fin n → F, x ≠ 0 ∧ ∀ i ∈ S, Matrix.mulVec G x i = 0 := by
  exact exists_nonzero_mem_kernel_of_rows G S h

variable [Fintype F] in
/-- When no nonzero vectors exist in F^n, the distance is ⊤ (infinity/undefined).

    PROVED by Aristotle (Batch 19, 03149310-9a51-4ef9-aff5-3d9b34e8a22b).

    This handles the edge case for the Singleton bound when n = 0.
    The distance set is empty, so sInf ∅ = ⊤.

    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem distance_when_no_nonzero_vectors (C : LinearCode F) :
    (¬∃ x : Vec F C.n, x ≠ 0) →
    distance C = ⊤ := by
  intro h_no_nonzero
  -- When there are no nonzero vectors, n must be 0
  -- (Vec F 0 has only the zero vector)
  -- The distance set is empty, so distance C = sInf ∅ = ⊤
  unfold distance
  have h_empty : { w : WithTop ℕ | ∃ x : Vec F C.n, x ≠ 0 ∧ w = ∥C ⇀ₑ x∥₀ } = ∅ := by
    apply Set.ext
    intro w
    constructor
    · rintro ⟨x, hx⟩
      exact h_no_nonzero ⟨x, hx.1⟩
    · intro h_absurd
      cases h_absurd
  rw [h_empty]
  -- sInf ∅ = ⊤ for WithTop ℕ (standard definition in order theory)
  exact WithTop.sInf_empty

end SingletonLemmas

end SuccinctProofs
