/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a515167e-a591-4d9e-aa00-6c350c877b5f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem hyperplane_card {n : ℕ} (x : Fin n → F) (hx : x ≠ 0) :
    Fintype.card {r : Fin n → F | ∑ i, r i * x i = 0} =
    (Fintype.card F) ^ (n - 1)

- theorem hadamard_zero_inner_product_count {n : ℕ} (hn : n > 0) (x : Fin n → F) (hx : x ≠ 0) :
    Fintype.card {r : Fin n → F | ∑ i, r i * x i = 0} =
    (Fintype.card F) ^ (n - 1)

- theorem hadamard_nonzero_count {n : ℕ} (hn : n > 0) (x : Fin n → F) (hx : x ≠ 0) :
    Fintype.card {r : Fin n → F | ∑ i, r i * x i ≠ 0} =
    (Fintype.card F) ^ n - (Fintype.card F) ^ (n - 1)

- theorem hadamard_distance_fraction {n : ℕ} (hn : n > 0) (hF : Fintype.card F ≥ 2) :
    ∀ x : Fin n → F, x ≠ 0 →
      Fintype.card {r : Fin n → F | ∑ i, r i * x i ≠ 0} ≥
      (Fintype.card F)^n * (Fintype.card F - 1) / Fintype.card F
-/

/-
Target: Prove that Hadamard code has distance m/2 (approximately)


Key insight: For a nonzero vector x ∈ F^n, the number of vectors r ∈ F^n such that
⟨r, x⟩ = 0 (inner product equals zero) is |F|^{n-1}.

This is because the hyperplane {r | ⟨r,x⟩ = 0} has dimension n-1 over F.
So the Hadamard code has distance |F|^n - |F|^{n-1} = |F|^{n-1} * (|F| - 1).

-/

import Mathlib.Tactic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank


noncomputable section

open scoped BigOperators

section MainTheorem

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Helper 1**: Hyperplane has codimension 1

    For a nonzero x ∈ F^n, the set {r | ⟨r,x⟩ = 0} is a hyperplane of dimension n-1.

    PROVE THIS THEOREM.
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem hyperplane_card {n : ℕ} (x : Fin n → F) (hx : x ≠ 0) :
    Fintype.card {r : Fin n → F | ∑ i, r i * x i = 0} =
    (Fintype.card F) ^ (n - 1) := by
  rcases n with ( _ | n ) <;> simp_all +decide [ pow_succ, Finset.card_univ ];
  -- Consider the linear map $T : F^{n+1} \to F$ defined by $T(r) = \langle r, x \rangle$.
  set T : (Fin (n + 1) → F) →ₗ[F] F := ∑ i, (LinearMap.proj i).smulRight (x i);
  have h_kernel : (Fintype.card {r : Fin (n + 1) → F | T r = 0}) = (Fintype.card F) ^ (n + 1 - 1) := by
    have h_kernel : LinearMap.ker T ≃ₗ[F] (Fin (n) → F) := by
      -- Since $T$ is surjective, the kernel of $T$ has dimension $n$.
      have h_kernel_dim : Module.finrank F (LinearMap.ker T) = n := by
        have h_surjective : Function.Surjective T := by
          intro y; exact (by
          obtain ⟨ i, hi ⟩ := Function.ne_iff.mp hx; use fun j => if j = i then y / x i else 0; aesop;);
        have := LinearMap.finrank_range_add_finrank_ker T;
        rw [ LinearMap.range_eq_top.mpr h_surjective ] at this ; norm_num at this ; linarith;
      exact ( LinearEquiv.ofFinrankEq _ _ <| by simp +decide [ h_kernel_dim ] );
    convert Fintype.card_congr h_kernel.toEquiv using 1 ; simp +decide [ Fintype.card_pi ];
  aesop

/-- **Main Theorem 1**: Count of zero inner products for nonzero x

    For nonzero x ∈ F^n, the number of r such that ⟨r,x⟩ = 0 is |F|^{n-1}.

    PROVE THIS THEOREM.
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem hadamard_zero_inner_product_count {n : ℕ} (hn : n > 0) (x : Fin n → F) (hx : x ≠ 0) :
    Fintype.card {r : Fin n → F | ∑ i, r i * x i = 0} =
    (Fintype.card F) ^ (n - 1) := by
  convert hyperplane_card x hx using 1

/-- **Main Theorem 2**: Hadamard distance bound

    For the Hadamard code (encoding x as all inner products),
    any nonzero codeword has at least |F|^n - |F|^{n-1} nonzero entries.

    PROVE THIS THEOREM.
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem hadamard_nonzero_count {n : ℕ} (hn : n > 0) (x : Fin n → F) (hx : x ≠ 0) :
    Fintype.card {r : Fin n → F | ∑ i, r i * x i ≠ 0} =
    (Fintype.card F) ^ n - (Fintype.card F) ^ (n - 1) := by
  convert congr_arg _ ( hyperplane_card x hx ) using 1;
  simp +decide [ Fintype.card_subtype ];
  rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num [ Finset.card_univ ]

/-- **Corollary**: Hadamard distance as a fraction

    The Hadamard code has distance (1 - 1/|F|) fraction of the block length.
    When |F| = 2, this is 1/2 of the block length.

    PROVE THIS THEOREM.
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem hadamard_distance_fraction {n : ℕ} (hn : n > 0) (hF : Fintype.card F ≥ 2) :
    ∀ x : Fin n → F, x ≠ 0 →
      Fintype.card {r : Fin n → F | ∑ i, r i * x i ≠ 0} ≥
      (Fintype.card F)^n * (Fintype.card F - 1) / Fintype.card F := by
  intro x hx
  have h_nonzero_count : (Fintype.card {r : Fin n → F | ∑ i, r i * x i ≠ 0}) = (Fintype.card F)^n - (Fintype.card F)^(n-1) := by
    convert hadamard_nonzero_count hn x hx using 1;
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ, mul_tsub ];
  · exact Nat.div_le_of_le_mul <| by rw [ tsub_le_iff_right ] ; nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ Fintype.card F ) ] ;
  · exact Nat.div_le_of_le_mul <| by rw [ tsub_le_iff_right ] ; nlinarith [ Nat.sub_add_cancel ( show Fintype.card F ^ n * Fintype.card F * Fintype.card F ≥ Fintype.card F ^ n * Fintype.card F from Nat.le_mul_of_pos_right _ <| by positivity ) ] ;

end MainTheorem
