/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3af9550e-d68e-4fcf-a03b-7ca874aa19e9

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem zero_inner_product_card
- theorem nonzero_inner_product_card
- theorem hadamard_distance_formula
- theorem hadamard_weight_lower_bound
-/

import Mathlib.Tactic

/-! ### Hadamard Distance Bridge (Batch 160)

This file contains self-contained proofs relating to Hadamard code distance.

A Hadamard code has rows indexed by all possible tuples (Fin n → F).
For a nonzero message x, the codeword is ⟨r, x⟩ for each tuple r.

Key result: The number of nonzero entries in the codeword is:
  |F|^n - |F|^(n-1)

This follows from counting:
- Total tuples: |F|^n
- Tuples r with ⟨r, x⟩ = 0 form a hyperplane of dimension n-1, so |F|^(n-1)
- Nonzero: |F|^n - |F|^(n-1)
-/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

/-- Inner product of two vectors -/
def innerProductGated (x y : Fin n → F) : F := ∑ i, x i * y i

/-- For nonzero x, the set of r with ⟨r, x⟩ = 0 is a proper subspace.
    Its cardinality is |F|^(n-1). -/
theorem zero_inner_product_card_gated (x : Fin n → F) (hx : x ≠ 0) (hn : n > 0) :
    Fintype.card {r : Fin n → F | innerProductGated r x = 0} = (Fintype.card F) ^ (n - 1) := by
  have h_subspace : ∃ (W : Submodule F (Fin n → F)), W = {r : Fin n → F | innerProductGated r x = 0} ∧ Module.finrank F W = n - 1 := by
    refine' ⟨LinearMap.ker (∑ i, x i • LinearMap.proj i), _, _⟩ <;> simp_all +decide [Set.ext_iff, innerProductGated]
    · simp +decide [mul_comm]
    · have h_surjective : Function.Surjective (∑ i : Fin n, x i • LinearMap.proj i : (Fin n → F) →ₗ[F] F) := by
        intro y
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
          exact Function.ne_iff.mp hx
        use fun j => if j = i then y / x i else 0
        simp [hi]
        rw [mul_div_cancel₀ _ hi]
      have := LinearMap.finrank_range_add_finrank_ker (∑ i : Fin n, x i • LinearMap.proj i : (Fin n → F) →ₗ[F] F)
      simp_all +decide [LinearMap.range_eq_top]
      rw [show LinearMap.range (∑ i : Fin n, x i • LinearMap.proj i : (Fin n → F) →ₗ[F] F) = ⊤ from LinearMap.range_eq_top.mpr <| by simpa [LinearMap.ext_iff] using h_surjective] at this
      simp_all +decide [Module.finrank_self]
      omega
  obtain ⟨W, hW₁, hW₂⟩ := h_subspace
  have := @Module.card_eq_pow_finrank F W
  simp_all +decide [Set.ext_iff]

/-- The complement: tuples with ⟨r, x⟩ ≠ 0 has cardinality |F|^n - |F|^(n-1). -/
theorem nonzero_inner_product_card_gated (x : Fin n → F) (hx : x ≠ 0) (hn : n > 0) :
    Fintype.card {r : Fin n → F | innerProductGated r x ≠ 0} =
      (Fintype.card F) ^ n - (Fintype.card F) ^ (n - 1) := by
  convert congr_arg _ (zero_inner_product_card_gated x hx hn) using 1
  simp +decide [Fintype.card_subtype]
  rw [Finset.filter_not, Finset.card_sdiff]
  aesop

/-- The Hadamard distance is exactly |F|^n - |F|^(n-1) for n > 0.

    Every nonzero message x produces a codeword with exactly this many nonzero entries.
    This is the minimum distance of the Hadamard code. -/
theorem hadamard_distance_formula_gated (hn : n > 0) :
    ∀ x : Fin n → F, x ≠ 0 →
      Fintype.card {r : Fin n → F | innerProductGated r x ≠ 0} =
        (Fintype.card F) ^ n - (Fintype.card F) ^ (n - 1) :=
  fun x hx => nonzero_inner_product_card_gated x hx hn

/-- Alternative formulation: The weight bound for Hadamard encoding.

    For any nonzero x, the number of r with ⟨r, x⟩ ≠ 0 is at least |F|^n - |F|^(n-1). -/
theorem hadamard_weight_lower_bound_gated (x : Fin n → F) (hx : x ≠ 0) (hn : n > 0) :
    Fintype.card {r : Fin n → F | innerProductGated r x ≠ 0} ≥
      (Fintype.card F) ^ n - (Fintype.card F) ^ (n - 1) := by
  rw [← nonzero_inner_product_card_gated x hx hn]
