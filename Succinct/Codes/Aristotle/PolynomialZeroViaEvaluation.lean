import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-! ### Polynomial Zero Via Evaluation Library

This file contains the key lemma for polynomial zero checking:
A polynomial of degree < n that vanishes at n distinct points must be zero.

Paper reference: Section 3.1.4 - Polynomial Zero Check

Strategy: Minimal submission - just the target lemma with all
necessary context inline.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

noncomputable section

open scoped BigOperators

open Polynomial

namespace SuccinctProofs

section PolynomialZeroViaEvaluation

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-! ### Target Lemma for Aristotle -/

/-- **Main Lemma**: A polynomial of degree < n that vanishes at n distinct points is zero.

    This is the FUNDAMENTAL fact for polynomial zero checking.
    If a degree < n polynomial evaluates to zero at n distinct points,
    then the polynomial must be identically zero.

    Key facts to use:
    1. Mathlib.Polynomial.card_roots' gives: |p.roots| = p.natDegree for p ≠ 0
    2. Each evaluation point α i where p.eval (α i) = 0 is a root of p
    3. So {α i | p.eval (α i) = 0} ⊆ p.roots
    4. If p ≠ 0, then |{α i | p.eval (α i) = 0}| ≤ |p.roots| = p.natDegree < n
    5. But we have n distinct such points, contradiction
    6. Therefore p = 0

    Proved by Aristotle (Batch 11, ab486136-d7e8-4fbd-97b1-8681daf93e5f).

    The proof uses contradiction: if p ≠ 0, then p has at most p.natDegree roots,
    but we have n distinct roots (the evaluation points), and n > p.natDegree. -/
lemma polynomial_zero_via_evaluations {n : ℕ} {α : Fin n → F}
    (h_distinct : Pairwise (fun i j => α i ≠ α j))
    (p : Polynomial F) (hDeg : p.natDegree < n)
    (h_zero : ∀ i : Fin n, p.eval (α i) = 0) :
    p = 0 := by
  -- Since p has n distinct roots and its degree is less than n, it must be the zero polynomial.
  by_contra h_nonzero
  have h_card_roots : (Finset.image α Finset.univ).card ≤ p.natDegree := by
    exact le_trans ( Finset.card_le_card ( show Finset.image α Finset.univ ⊆ p.roots.toFinset by intros x hx; aesop ) ) ( by exact le_trans ( Multiset.toFinset_card_le _ ) ( Polynomial.card_roots' _ ) );
  rw [ Finset.card_image_of_injective _ fun i j hij => by contrapose hij; exact h_distinct hij ] at h_card_roots ; simp_all +decide;
  exact not_lt_of_ge h_card_roots hDeg

end PolynomialZeroViaEvaluation

end SuccinctProofs
