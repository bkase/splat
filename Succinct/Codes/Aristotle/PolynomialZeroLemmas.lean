import Mathlib.Tactic

/-! ### Polynomial Zero Lemmas

Paper reference: Polynomial algebra basics

Target lemmas: monomial_zero and related polynomial lemmas
These are fundamental lemmas blocking polyOfVec_natDegree_lt in Lagrange.lean.

Strategy: Use import Mathlib for auto-imports. Self-contained proofs.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

noncomputable section

namespace SuccinctProofs

section PolynomialZeroLemmas

variable {R : Type*} [Semiring R]

/-! ### Target Theorems for Aristotle -/

/-- **LEMMA 1**: monomial n 0 = 0.
    The monomial with coefficient zero is the zero polynomial. -/
theorem monomial_zero (n : ℕ) :
    Polynomial.monomial n (0 : R) = 0 := by
  classical
  -- By definition, monomial n 0 = 0
  exact Polynomial.monomial_zero_right n

/-- **LEMMA 2**: monomial n x = 0 iff x = 0.
    A monomial is zero iff its coefficient is zero. -/
theorem monomial_zero' (n : ℕ) (x : R) :
    Polynomial.monomial n x = 0 ↔ x = 0 := by
  classical
  constructor
  · -- If monomial n x = 0, then x = 0
    intro h_mono
    -- Take coefficient at position n
    have h_coeff : (Polynomial.monomial n x).coeff n = 0 := by
      rw [h_mono]
      exact Polynomial.coeff_zero (R := R) n
    -- But by coeff_monomial, this coefficient equals x
    rw [Polynomial.coeff_monomial] at h_coeff
    simp at h_coeff
    exact h_coeff
  · -- If x = 0, then monomial n x = 0
    intro h_x
    rw [h_x]
    exact monomial_zero n

/-- **LEMMA 3**: Coefficient of monomial n 0.
    All coefficients of monomial n 0 are zero. -/
theorem coeff_monomial_zero (n i : ℕ) :
    (Polynomial.monomial n (0 : R)).coeff i = 0 := by
  classical
  rw [monomial_zero n]
  exact Polynomial.coeff_zero (R := R) i

/-- **LEMMA 4**: Coefficient of monomial n x at position n.
    The n-th coefficient of monomial n x is x. -/
theorem coeff_monomial_of_ne {n : ℕ} {x : R} :
    (Polynomial.monomial n x).coeff n = x := by
  classical
  rw [Polynomial.coeff_monomial]
  simp

/-- **LEMMA 5**: natDegree of monomial n 0.
    The zero monomial has natDegree 0. -/
theorem natDegree_monomial_zero (n : ℕ) :
    (Polynomial.monomial n (0 : R)).natDegree = 0 := by
  classical
  rw [monomial_zero n]
  exact Polynomial.natDegree_zero

/-- **LEMMA 6**: natDegree of monomial n x when x ≠ 0.
    If x ≠ 0, then natDegree (monomial n x) = n. -/
theorem natDegree_monomial_of_ne {n : ℕ} {x : R} (hx : x ≠ 0) :
    (Polynomial.monomial n x).natDegree = n :=
  Polynomial.natDegree_monomial_eq n hx

end PolynomialZeroLemmas

end SuccinctProofs
