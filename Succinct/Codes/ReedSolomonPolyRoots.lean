import Succinct.LinearAlgebra
import Mathlib.Algebra.Polynomial.Roots

/-! ### Polynomial Roots Bound (Helper for Reed-Solomon Distance)

This file provides helper lemmas for bounding the number of roots
of a polynomial, used to prove the Reed-Solomon distance bound.

Key mathlib lemmas:
- Polynomial.card_roots_toFinset_le_natDegree
- Polynomial.natDegree_le_of_card_roots
-/

noncomputable section
open scoped BigOperators

namespace SuccinctProofs

section PolynomialRoots

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Helper 1**: A root of p in F is also in p.roots multiset.

    If p.eval β = 0 for some β : F and p ≠ 0, then β is in p.roots.toFinset.

    PROVED by Aristotle (Batch 18, 514685c5-ce40-4746-8869-c3595d4cabcd). -/
lemma root_in_roots_finset {p : Polynomial F} {β : F} (hp : p ≠ 0) (h_root : p.eval β = 0) :
    β ∈ p.roots.toFinset := by
  exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots hp).2 h_root)

/-- **Helper 2**: Cardinality of a subset is at most cardinality of the superset.

    If A ⊆ B (as Finsets), then |A| ≤ |B|. -/
lemma card_subset_le_finset {α : Type*} [DecidableEq α] {A B : Finset α} (h : A ⊆ B) :
    A.card ≤ B.card := by
  exact Finset.card_le_card h

/-- **Helper 3**: Convert polynomial degree bound to root bound.

    If natDegree p < n, then the polynomial has at most n-1 distinct roots.
    This uses mathlib's Polynomial.card_roots_toFinset_le_natDegree. -/
lemma poly_roots_bound_mathlib {p : Polynomial F} (hDeg : p.natDegree < n) :
    p.roots.toFinset.card ≤ n - 1 := by
  exact le_trans (Multiset.toFinset_card_le _)
    (Nat.le_pred_of_lt (lt_of_le_of_lt (Polynomial.card_roots' _) hDeg))

/-- **Main theorem**: A degree < n polynomial has at most n-1 roots in F.

    This is the key lemma for Reed-Solomon distance.
    Combines the subset relation with mathlib's root bound. -/
theorem poly_roots_bound {p : Polynomial F} (hDeg : p.natDegree < n) :
    {β : F | p.eval β = 0}.ncard ≤ n - 1 := by
  by_cases hp : p = 0
  · simp only [hp, Polynomial.eval_zero, Set.setOf_true, Set.ncard_univ]
    by_cases hF : Finite F
    · exact le_trans (Nat.card_le_one_iff_subsingleton.mpr (by
        haveI := hF
        simp only [Polynomial.natDegree_zero] at hDeg
        omega)).le (Nat.sub_le n 1)
    · simp only [not_finite_iff_infinite] at hF
      haveI := hF
      simp only [Nat.card_eq_zero_of_infinite, Nat.zero_le]
  · have h_card_subset_le_p_roots_bound : {β : F | p.eval β = 0}.ncard ≤ (p.roots.toFinset).card := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard fun x hx => root_in_roots_finset hp hx
    exact h_card_subset_le_p_roots_bound.trans (poly_roots_bound_mathlib hDeg)

end PolynomialRoots

end SuccinctProofs
