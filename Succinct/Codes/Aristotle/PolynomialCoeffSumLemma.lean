import Mathlib.Tactic

/-! ### Polynomial Coefficient Sum Lemma

Paper reference: Lagrange interpolation - polyOfVec reconstruction

Target lemmas: p = ∑ monomial i (coeff i) for natDegree < n
This is THE critical lemma blocking polyOfVec reconstruction in Lagrange.lean.

Strategy: Use import Mathlib for auto-imports. Self-contained proofs.
Gating: Uses only Mathlib Polynomial lemmas.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

noncomputable section

namespace SuccinctProofs

section PolynomialCoeffSumLemma

variable {R : Type*} [Semiring R]
open Polynomial

/-! ### Target Theorem for Aristotle -/

/-- **MAIN LEMMA**: Polynomial equals sum of monomials when natDegree < n.
    If p.natDegree < n, then p = ∑ i in range n, monomial i (coeff i)

    This is the KEY lemma needed for polyOfVec reconstruction in Lagrange.lean.
    It shows that any polynomial with degree less than n can be represented
    as the sum of monomials up to n.

    PROVED by Aristotle (Batch 27, 0e0c23e4-d54c-4da2-9107-7030c00a8814). -/
theorem as_sum_range_of_natDegree_lt {p : Polynomial R} {n : ℕ}
    (hDeg : p.natDegree < n) :
    p = Finset.sum (Finset.range n) fun i => Polynomial.monomial i (p.coeff i) := by
  classical
  -- This is a fundamental representation theorem for polynomials
  -- Every polynomial is the sum of its monomials
  -- The constraint natDegree < n ensures we only need to sum up to n
  conv_lhs => rw [Polynomial.as_sum_range' p n hDeg]

end PolynomialCoeffSumLemma

end SuccinctProofs
