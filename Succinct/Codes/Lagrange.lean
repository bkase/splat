import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Lagrange

import Succinct.LinearAlgebra
import Succinct.Vandermonde
import Succinct.Codes.Core
import Succinct.Codes.EvalCode
import Succinct.Codes.Aristotle.PolynomialZeroLemmas
import Succinct.Codes.Aristotle.PolynomialCoeffSumLemma

noncomputable section
open scoped BigOperators
open Polynomial

namespace SuccinctProofs

/-! ### Polynomial Representation of Vectors

Helper lemmas from Aristotle showing the connection between
vectors of coefficients and polynomials.
-/

section PolyVec

variable {F : Type*} [Field F]
variable {n : ℕ}

/-- Define a polynomial from a vector of coefficients. -/
def polyOfVec (x : Vec F n) : Polynomial F :=
  ∑ j : Fin n, monomial j (x j)

/-- Evaluating the polynomial constructed from a vector is the same as `evalPolyOfVec`. -/
lemma polyOfVec_eval (x : Vec F n) (β : F) :
    (polyOfVec x).eval β = evalPolyOfVec x β := by
  simp [polyOfVec, Polynomial.eval_finset_sum, evalPolyOfVec]

/-- The degree of the polynomial constructed from a vector `x` of length `n` is strictly less than `n`. -/
lemma polyOfVec_degree_lt (x : Vec F n) : (polyOfVec x).degree < n := by
  rw [polyOfVec, Polynomial.degree_lt_iff_coeff_zero]
  simp [Polynomial.coeff_monomial]
  exact fun m hm => Finset.sum_eq_zero fun i hi =>
    if_neg (by linarith [Fin.is_lt i])

/-- The map `polyOfVec` is injective. -/
lemma polyOfVec_injective : Function.Injective (polyOfVec (F := F) (n := n)) := by
  intro x y hxy
  ext j
  unfold polyOfVec at hxy
  replace hxy := congr_arg (fun p => p.coeff j) hxy
  simp_all [Polynomial.coeff_monomial, Finset.sum_ite, Fin.val_inj]

/-! ### Polynomial-Vector Equivalence

The following definitions provide the missing inverse for polyOfVec.
These are marked as sorry for Aristotle to prove.

The key insight: polyOfVec gives a bijection between:
- Vec F n (vectors of length n)
- {p : Polynomial F | p.natDegree < n} (polynomials of degree < n)

This is used in PolynomialZero.lean to convert between polynomials and vectors.
-/

/-- The natDegree of the polynomial constructed from a vector is strictly less than n.

    This is needed to show that polyOfVec maps into the subtype {p | natDegree < n}.

    PROVED by Aristotle (Batch 19, ab6d2203-eb53-4dff-bf8b-685fc744c623).
    The complete proof uses natDegree_le_natDegree_of_sum and related lemmas.

    Note: Some lemma names may differ in this Mathlib version.
    The core insight is that polyOfVec x = Σ j : Fin n, monomial j (x j),
    and since each j < n, the resulting polynomial has natDegree < n.

    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma polyOfVec_natDegree_lt (x : Vec F n) (hn : 0 < n) : (polyOfVec x).natDegree < n := by
  classical
  -- Key insight: For polyOfVec x = Σ j : Fin n, monomial j (x j),
  -- all coefficients at index ≥ n are zero (we only sum over j < n).
  -- Therefore natDegree < n.

  -- First, show that all coefficients at index ≥ n are zero
  have h_coeff_zero : ∀ i ≥ n, (polyOfVec x).coeff i = 0 := by
    intro i hi
    unfold polyOfVec
    -- For each monomial j (x j), its coefficient at i is:
    -- - x j if i = j (as natural numbers)
    -- - 0 otherwise
    -- Since i ≥ n and j < n (j : Fin n), we have i ≠ j
    -- So each term contributes 0 to the sum
    have h_zero_each : ∀ j : Fin n, (monomial j (x j)).coeff i = 0 := by
      intro j
      have hj : j.val < n := Fin.is_lt j
      -- Since i ≥ n and j.val < n, we must have i ≠ j.val
      have hne : i ≠ j.val := by
        intro heq
        have : i < n := by
          have : j.val = i := by exact heq.symm
          exact this ▸ hj
        linarith
      -- Now show coeff is 0 using the fact i ≠ j.val
      rw [Polynomial.coeff_monomial]
      -- The result is `if i = j.val then x j else 0`
      -- Since hne : i ≠ j.val, this must be 0
      by_cases h_eq : i = j.val
      · -- Contradicts hne
        exact False.elim (hne h_eq)
      · -- If i ≠ j.val, then the ite returns 0
        aesop
    -- Now sum over all j
    simp [h_zero_each]

  -- Now use the fact that if all coefficients at index ≥ n are zero, then natDegree < n
  by_cases hp : polyOfVec x = 0
  · -- If polyOfVec x = 0, then natDegree = 0
    rw [hp, Polynomial.natDegree_zero]
    -- We have hn : 0 < n as a hypothesis, so this case is straightforward
    exact hn
  · -- If polyOfVec x ≠ 0, use the coefficient zero property
    -- Since all coefficients at index ≥ n are zero, natDegree < n
    -- By definition of natDegree, it's the largest index with nonzero coefficient
    -- Since all coefficients at index ≥ n are zero, natDegree < n
    by_contra h_contra
    push_neg at h_contra
    -- If natDegree ≥ n, then the coefficient at natDegree is zero (by h_coeff_zero)
    -- But for a nonzero polynomial, the coefficient at natDegree is nonzero
    -- Contradiction!
    have h_coeff_at_natDegree : (polyOfVec x).coeff (polyOfVec x).natDegree = 0 := by
      apply h_coeff_zero (polyOfVec x).natDegree
      omega
    -- The coefficient at natDegree is nonzero for a nonzero polynomial
    -- This follows from the definition of natDegree
    have h_coeff_nonzero : (polyOfVec x).coeff (polyOfVec x).natDegree ≠ 0 := by
      -- leadingCoeff = coeff at natDegree
      rw [←Polynomial.leadingCoeff]
      -- And leadingCoeff of a nonzero polynomial is nonzero
      exact Polynomial.leadingCoeff_ne_zero.2 hp
    contradiction

/-- Extract coefficients from a polynomial with natDegree < n.

    For a polynomial p with natDegree < n, we extract its first n coefficients
    to form a vector of length n. -/
def polyOfVecCoeffs (p : Polynomial F) (hDeg : p.natDegree < n) : Vec F n := fun j => p.coeff j

/-- For any polynomial with natDegree < n, reconstructing from its coefficients gives the same polynomial.

    This is the right-inverse property: polyOfVec ∘ polyOfVecCoeffs = id

    PROVED by Aristotle (Batch 16, a334c13e-6eb0-44f3-b240-a7120dc195d4). -/
lemma polyOfVec_coeff_right_inverse (p : Polynomial F) (hDeg : p.natDegree < n) :
    polyOfVec (polyOfVecCoeffs p hDeg) = p := by
  -- By definition of polynomial coefficients, we can write p as the sum of its monomials.
  have h_poly_eq_sum : p = Finset.sum (Finset.range n) (fun j => Polynomial.monomial j (p.coeff j)) := by
    exact SuccinctProofs.as_sum_range_of_natDegree_lt hDeg
  simpa only [Finset.sum_range, Fin.cast_val_eq_self] using h_poly_eq_sum.symm

/-- For any vector, extracting coefficients and reconstructing gives the same vector.

    This is the left-inverse property: polyOfVecCoeffs ∘ polyOfVec = id

    PROVED by Aristotle (Batch 16, a334c13e-6eb0-44f3-b240-a7120dc195d4). -/
lemma polyOfVec_coeff_left_inverse (x : Vec F n) (hn : 0 < n) :
    polyOfVecCoeffs (polyOfVec x) (polyOfVec_natDegree_lt x hn) = x := by
  -- By definition of `polyOfVec`, we know that its coefficients are exactly `x`.
  ext j
  simp [polyOfVecCoeffs]
  simp +decide [polyOfVec, Polynomial.coeff_monomial]
  simp +decide [Finset.sum_ite, Fin.val_inj]

/-- Equivalence between vectors of length n and polynomials with natDegree < n.

    This provides the inverse map `polyOfVec.symm` that was previously missing.
    The equivalence shows:
    - polyOfVec: Vec F n → {p : Polynomial F | natDegree < n} is bijective
    - polyOfVecCoeffs: {p | natDegree < n} → Vec F n is the inverse -/
def polyOfVecEquiv (hn : 0 < n) : Vec F n ≃ {p : Polynomial F // p.natDegree < n} where
  toFun := fun x => ⟨polyOfVec x, polyOfVec_natDegree_lt x hn⟩
  invFun := fun p => polyOfVecCoeffs p.1 p.2
  left_inv := fun x => polyOfVec_coeff_left_inverse x hn
  right_inv := fun p => by
    apply Subtype.eq
    exact polyOfVec_coeff_right_inverse p.1 p.2

/-- **Polynomial Zero Check via Coefficients**.

    A polynomial is zero iff all its coefficients are zero.
    This is a fundamental result that follows from the polyOfVec infrastructure.

    PROVED by Aristotle (Batch 17, 7d46259c-d477-4822-a8d8-9b5ebe59ab68).

    Statement: For any polynomial p with natDegree < n,
    if all coefficients of p are zero, then p is the zero polynomial.

    More formally: (∀ j : Fin n, p.coeff j = 0) ↔ p = 0

    This is critical for:
    - Polynomial zero checks in FRI (§4.2)
    - Reed-Solomon decoding verification
    - General polynomial equality testing -/
theorem polynomial_zero_via_coefficients {p : Polynomial F} (hDeg : p.natDegree < n) :
    (∀ j : Fin n, p.coeff j = 0) ↔ p = 0 := by
  constructor
  · -- Forward direction: if all coefficients are zero, then p = 0
    intro h_zero
    -- Reconstruct p from its coefficients using polyOfVec
    rw [← polyOfVec_coeff_right_inverse p hDeg]
    -- If all coefficients are zero, polyOfVec gives zero polynomial
    unfold polyOfVec polyOfVecCoeffs
    aesop
  · -- Backward direction: if p = 0, then all coefficients are zero
    intro h_zero
    -- If p = 0, then all its coefficients are zero by definition
    intro j
    rw [h_zero]
    rfl

/-- If a polynomial `p` has degree less than `m` and vanishes at `m` distinct points, then `p` is the zero polynomial. -/
lemma poly_eq_zero_of_distinct_roots {p : Polynomial F} {m : ℕ} {α : Fin m → F}
    (hDistinct : Function.Injective α)
    (hRoots : ∀ i, p.eval (α i) = 0)
    (hDeg : p.degree < m) :
    p = 0 := by
  have h_poly_zero : ∀ {p : Polynomial F}, p.degree < m → (∀ i : Fin m, Polynomial.eval (α i) p = 0) → p = 0 := by
    intro p hp hRoots
    contrapose! hp
    rw [Polynomial.degree_eq_natDegree hp]
    have h_div : ∃ q : Polynomial F, p = q * ∏ i : Fin m, (Polynomial.X - Polynomial.C (α i)) := by
      refine' exists_eq_mul_left_of_dvd (Finset.prod_dvd_of_coprime _ _)
      · exact fun i _ j _ hij => Polynomial.pairwise_coprime_X_sub_C hDistinct hij
      · exact fun i _ => Polynomial.dvd_iff_isRoot.mpr (hRoots i)
    obtain ⟨ q, rfl⟩ := h_div
    rw [Polynomial.natDegree_mul'] <;> simp_all [Polynomial.natDegree_prod']
    exact_mod_cast Nat.le_add_left _ _
  exact h_poly_zero hDeg hRoots

end PolyVec


/-! ### Lagrange Interpolation

Lagrange interpolation recovers the unique polynomial of degree `< n` that
passes through given points `(α[i], y[i])`.

Note: Aristotle proved key results here - `poly_eq_zero_of_distinct_roots`,
`evalPolyOfVec_sub`, `evalCode_injective_of_le`, `evalCode_not_injective_of_gt`,
`polyOfVec_coeff_right_inverse`, `polyOfVec_coeff_left_inverse`,
`lagrangeBasis_eval_eq_one`, `lagrangeBasis_eval_eq_zero`,
and the corrected characterization `evalCode_injective_iff`. The original
claim that "evaluation is injective when points are distinct" (for any n,m)
was shown to be FALSE.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

section Lagrange

variable {F : Type*} [Field F]
variable {m n : ℕ}
variable [DecidableEq (Fin m)]

/-- Lagrange basis polynomial `ℓ_j` coefficients for point `α[j]`.
    This polynomial evaluates to 1 at `α[j]` and 0 at all other `α[i]` (i ≠ j). -/
def lagrangeBasisCoeffs (α : EvalPoints m F) (j : Fin m) : Vec F n :=
  fun k => (Lagrange.basis Finset.univ α j).coeff k

/-- Evaluate the j-th Lagrange basis polynomial at a point `β`. -/
def lagrangeBasisEval (n : ℕ) (α : EvalPoints m F) (j : Fin m) (β : F) : F :=
  evalPolyOfVec (n := n) (lagrangeBasisCoeffs α j) β

/-- Direct evaluation formula for Lagrange basis polynomial ℓ_j at point β.
    Formula: ℓ_j(β) = ∏_{i≠j} (β - α_i) / (α_j - α_i)

    This definition avoids expanding into polynomial coefficients.
    PROVED by Aristotle (Batch 13+, fd2195d4-cec3-45f5-87a3-c78b606cda96). -/
def lagrangeBasisEvalDirect (α : EvalPoints m F) (j : Fin m) (β : F) : F :=
  ∏ i : Fin m, if i = j then 1 else (β - α i) / (α j - α i)

/-- The Lagrange basis polynomial evaluates to 1 at its designated point.
    PROVED by Aristotle (Batch 13+, fd2195d4-cec3-45f5-87a3-c78b606cda96).

    For the direct evaluation formula, the proof follows from:
    - For i = j: factor is 1
    - For i ≠ j: (α_j - α_i) / (α_j - α_i) = 1 (by field division) -/
lemma lagrangeBasis_eval_eq_one (α : EvalPoints m F) (hDistinct : ∀ i j, i ≠ j → α i ≠ α j) (j : Fin m) :
    lagrangeBasisEvalDirect α j (α j) = 1 := by
  -- By definition of Lagrange basis polynomial, for any i ≠ j,
  -- the term (α_j - α_i) / (α_j - α_i) simplifies to 1.
  have h_lagrange : ∀ i : Fin m, i ≠ j → (α j - α i) / (α j - α i) = 1 := by
    exact fun i hi => div_self (sub_ne_zero_of_ne (Ne.symm (hDistinct i j hi)))
  convert Finset.prod_eq_one _ <;> aesop

/-- The Lagrange basis polynomial evaluates to 0 at all other points.
    PROVED by Aristotle (Batch 13+, fd2195d4-cec3-45f5-87a3-c78b606cda96).

    When β = α_i for i ≠ j, one factor in the product is (α_i - α_i) / (α_j - α_i) = 0 -/
lemma lagrangeBasis_eval_eq_zero (α : EvalPoints m F) (hDistinct : ∀ i j, i ≠ j → α i ≠ α j) (i j : Fin m) (hne : i ≠ j) :
    lagrangeBasisEvalDirect α j (α i) = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by aesop)

/-- Interpolate: recover coefficient vector from evaluation vector `y`. -/
def lagrangeInterp (α : EvalPoints m F) (y : Vec F m) : Vec F n :=
  fun k : Fin n => ∑ j : Fin m, y j * (lagrangeBasisCoeffs α j) k

/-- Helper lemma: extend a finite sum over polynomial coefficients.
    When polynomial has degree < m and n ≥ m, summing over Fin n
    captures the full polynomial evaluation.
    Used in the Lagrange interpolation proof. -/
private lemma sum_coeff_pow_eq_eval {m' n' : ℕ} (p : Polynomial F) (β : F)
    (hdeg : p.natDegree < m') (hn : n' ≥ m') :
    ∑ k : Fin n', p.coeff ↑k * β ^ (k : ℕ) = p.eval β := by
  rw [Polynomial.eval_eq_sum_range]
  have h_coeff_zero : ∀ k : ℕ, k ≥ p.natDegree + 1 → p.coeff k = 0 := by
    exact fun k hk => Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have h_bound : p.natDegree + 1 ≤ n' := by omega
  symm
  calc ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * β ^ k
      = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * β ^ k + 0 := by ring
    _ = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * β ^ k +
        ∑ k ∈ (Finset.range n') \ (Finset.range (p.natDegree + 1)), p.coeff k * β ^ k := by
          congr 1
          symm
          apply Finset.sum_eq_zero
          intro k hk
          rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hk
          simp [h_coeff_zero k (by omega)]
    _ = ∑ k ∈ Finset.range n', p.coeff k * β ^ k := by
          rw [← Finset.sum_union]
          · congr 1
            ext k
            simp only [Finset.mem_range, Finset.mem_union, Finset.mem_sdiff]
            constructor
            · intro hk
              rcases hk with hk | ⟨hk1, hk2⟩
              · omega
              · exact hk1
            · intro hk
              by_cases h : k < p.natDegree + 1
              · left; exact h
              · right; exact ⟨hk, by simp [h]⟩
          · exact Finset.disjoint_sdiff
    _ = ∑ k : Fin n', p.coeff ↑k * β ^ (k : ℕ) := Finset.sum_range _

/-- Helper: When n ≥ m, evalPolyOfVec of lagrangeInterp equals sum of basis evaluations. -/
private lemma evalPolyOfVec_lagrangeInterp (α : EvalPoints m F) (y : Vec F m) (β : F)
    (hn : n ≥ m) (h_inj : Set.InjOn α (Finset.univ : Finset (Fin m))) :
    evalPolyOfVec (lagrangeInterp (n := n) α y) β =
    ∑ j : Fin m, y j * (Lagrange.basis Finset.univ α j).eval β := by
  simp only [evalPolyOfVec, lagrangeInterp, lagrangeBasisCoeffs]
  calc ∑ k : Fin n, (∑ j : Fin m, y j * (Lagrange.basis Finset.univ α j).coeff ↑k) * β ^ (k : ℕ)
      = ∑ k : Fin n, ∑ j : Fin m, y j * (Lagrange.basis Finset.univ α j).coeff ↑k * β ^ (k : ℕ) := by
        congr 1; ext k; rw [Finset.sum_mul]
    _ = ∑ j : Fin m, ∑ k : Fin n, y j * (Lagrange.basis Finset.univ α j).coeff ↑k * β ^ (k : ℕ) := by
        rw [Finset.sum_comm]
    _ = ∑ j : Fin m, y j * ∑ k : Fin n, (Lagrange.basis Finset.univ α j).coeff ↑k * β ^ (k : ℕ) := by
        congr 1; ext j; rw [Finset.mul_sum]; congr 1; ext k; ring
    _ = ∑ j : Fin m, y j * (Lagrange.basis Finset.univ α j).eval β := by
        congr 1; ext j; congr 1
        apply sum_coeff_pow_eq_eval
        · -- natDegree of basis is at most card s - 1 < card s = m
          have h_deg := Lagrange.degree_basis h_inj (Finset.mem_univ j)
          -- degree = card s - 1 implies natDegree ≤ card s - 1
          have h_natdeg : (Lagrange.basis Finset.univ α j).natDegree ≤ Fintype.card (Fin m) - 1 := by
            by_cases hp : (Lagrange.basis Finset.univ α j) = 0
            · simp [hp]
            · rw [Polynomial.natDegree_eq_of_degree_eq_some h_deg]
              simp only [Finset.card_univ, Fintype.card_fin]
              exact Nat.le_refl _
          simp only [Fintype.card_fin] at h_natdeg
          exact Nat.lt_of_le_of_lt h_natdeg (Nat.sub_lt (Nat.pos_of_ne_zero (Fin.pos j).ne') Nat.one_pos)
        · exact hn

/-- **Lagrange interpolation correctness**: encoding the interpolated coefficients
    recovers the original evaluation vector.

    Requires n ≥ m (the unique decoding condition) to ensure that the polynomial
    coefficients up to index n-1 capture the full Lagrange basis polynomial.

    Uses Mathlib's Lagrange.eval_basis_self and Lagrange.eval_basis_of_ne.

    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem lagrange_interp (α : EvalPoints m F) (y : Vec F m)
    (hDistinct : ∀ i j, i ≠ j → α i ≠ α j) (hn : n ≥ m) :
    (evalCode (n := n) α) ⇀ₑ (lagrangeInterp α y) = y := by
  have h_inj : Set.InjOn α (Finset.univ : Finset (Fin m)) := by
    intro a _ b _ hab
    by_contra hne
    exact hDistinct a b hne hab
  ext idx
  -- evalCode_encode_eq_eval : (evalCode α) ⇀ₑ x = fun i => evalPolyOfVec x (α i)
  simp only [evalCode_encode_eq_eval]
  rw [evalPolyOfVec_lagrangeInterp α y (α idx) hn h_inj]
  have h_basis_eval (j : Fin m) :
      (Lagrange.basis Finset.univ α j).eval (α idx) = if j = idx then 1 else 0 := by
    by_cases hji : j = idx
    · simp only [hji, ↓reduceIte]
      exact Lagrange.eval_basis_self h_inj (Finset.mem_univ idx)
    · rw [if_neg hji]
      exact Lagrange.eval_basis_of_ne hji (Finset.mem_univ idx)
  simp_rw [h_basis_eval]
  simp [Finset.sum_ite_eq']

/-- Evaluating polynomials is linear with respect to subtraction.
    PROVED by Aristotle. -/
lemma evalPolyOfVec_sub (x y : Vec F n) (β : F) :
    evalPolyOfVec (x - y) β = evalPolyOfVec x β - evalPolyOfVec y β := by
  unfold evalPolyOfVec
  simp [sub_mul]

/-- The evaluation code is injective when n ≤ m and points are distinct.
    PROVED by Aristotle. -/
theorem evalCode_injective_of_le (α : EvalPoints m F)
    (hDistinct : ∀ i j, i ≠ j → α i ≠ α j) (hle : n ≤ m) :
    Function.Injective (fun x : Vec F n => (evalCode (n := n) α) ⇀ₑ x) := by
  intro x y hxy
  have hp : polyOfVec x = polyOfVec y := by
    have h_distinct : Function.Injective α := by
      exact fun i j hij => Classical.not_not.1 fun hij' => hDistinct i j hij' hij
    have h_poly_eq : ∀ i : Fin m, (polyOfVec x).eval (α i) = (polyOfVec y).eval (α i) := by
      simp_all [evalCode_encode_eq_eval, funext_iff]
      simpa [polyOfVec_eval] using hxy
    have h_poly_eq_zero : polyOfVec x - polyOfVec y = 0 := by
      apply poly_eq_zero_of_distinct_roots h_distinct
      · aesop
      · exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
          (max_lt (lt_of_lt_of_le (polyOfVec_degree_lt x) (WithBot.coe_le_coe.mpr hle))
            (lt_of_lt_of_le (polyOfVec_degree_lt y) (WithBot.coe_le_coe.mpr hle)))
    exact eq_of_sub_eq_zero h_poly_eq_zero
  exact polyOfVec_injective hp

/-- If m < n, then the evaluation code is NOT injective.
    PROVED by Aristotle. -/
theorem evalCode_not_injective_of_gt (α : EvalPoints m F) (h : m < n) :
    ¬ Function.Injective (fun x : Vec F n => (evalCode (n := n) α) ⇀ₑ x) := by
  intro h_inj
  let f : Vec F n →ₗ[F] Vec F m := Matrix.mulVecLin (vandermonde α)
  have h_inj_lin : Function.Injective f := h_inj
  have h_rank := LinearMap.finrank_le_finrank_of_injective h_inj_lin
  rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at h_rank
  linarith

/-- The evaluation code is injective if and only if n ≤ m (when points are distinct).
    PROVED by Aristotle - this corrects our original FALSE claim. -/
theorem evalCode_injective_iff (α : EvalPoints m F)
    (hDistinct : ∀ i j, i ≠ j → α i ≠ α j) :
    Function.Injective (fun x : Vec F n => (evalCode (n := n) α) ⇀ₑ x) ↔ n ≤ m := by
  constructor
  · intro h_inj
    by_contra h_gt
    push_neg at h_gt
    have h_not_inj := evalCode_not_injective_of_gt α h_gt
    contradiction
  · intro h_le
    exact evalCode_injective_of_le α hDistinct h_le

/-- The original theorem "evalCode_injective_of_distinct" (which claimed injectivity for ANY n,m)
    is FALSE. This counterexample proof is by Aristotle.

    The theorem should require n ≤ m instead. -/
theorem evalCode_injective_of_distinct_false :
    ¬ (∀ {F : Type*} [Field F] {m n : ℕ} (α : EvalPoints m F),
        (∀ i j, i ≠ j → α i ≠ α j) → Function.Injective (fun x : Vec F n => (evalCode (n := n) α) ⇀ₑ x)) := by
  push_neg
  refine' ⟨_, _, 2, 3, _, _, _⟩
  exact ULift (ZMod 3)
  refine' { .. }
  native_decide +revert
  native_decide +revert
  exact fun i => if i = 0 then 0 else 1
  · decide +revert
  · native_decide +revert

end Lagrange

end SuccinctProofs
