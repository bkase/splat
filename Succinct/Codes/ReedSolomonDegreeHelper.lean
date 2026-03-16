import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Card

/-! ### Reed-Solomon Degree Helper

This file contains helper lemmas for polynomial root bounds
needed to complete the Reed-Solomon distance proof in ReedSolomon.lean

The key issue is connecting the evaluation-based root counting with
degree-based arguments. We use Mathlib's polynomial root lemmas.

Paper reference: Section 1.3.2 - Reed-Solomon Distance
-/

noncomputable section

open scoped BigOperators

namespace SuccinctProofs

section ReedSolomonDegreeHelper

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### Target Lemma for Aristotle

**Helper**: Application of root counting lemma.

    For a non-zero polynomial of degree at most n-1, evaluating at m distinct points
    yields at most n-1 zero values (equivalently, at least m-n+1 non-zero values).

    This uses Mathlib's `Polynomial.card_roots_toFinset_le_natDegree'` lemma.

This follows the pattern Aristotle succeeded with in ReedSolomonPolyRoots.lean.
-/

/-- For a non-zero polynomial of degree at most n-1, the evaluation vector
    at m distinct points has Hamming weight at least m-n+1.

    This is the core bound for Reed-Solomon distance: if p ≠ 0 has degree ≤ n-1,
    then for distinct points α₁,...,αₘ, at most n-1 of the values p(αᵢ) can be zero.

    Equivalently: |{i : p(αᵢ) = 0}| ≤ n-1, so |{i : p(αᵢ) ≠ 0}| ≥ m-n+1. -/
lemma eval_poly_weight_of_degree_le {m n : ℕ} (p : Polynomial F)
    (hp : p ≠ 0) (hdeg : p.natDegree ≤ n - 1) (hle : n ≤ m)
    {α : Fin m → F} (h_distinct : Pairwise (fun i j => α i ≠ α j)) :
    weightVec (fun i : Fin m => p.eval (α i)) ≥ m - n + 1 := by
  -- Step 1: The weight equals m minus the number of roots among evaluation points
  have h_weight_eq_m_minus_roots : weightVec (fun i : Fin m => p.eval (α i)) =
      m - Fintype.card {i : Fin m | p.eval (α i) = 0} := by
    rw [eval_weight_eq_m_minus_roots]
    exact h_distinct
  rw [h_weight_eq_m_minus_roots]

  -- Step 2: The number of roots among distinct points is at most natDegree
  have h_roots_le_deg : Fintype.card {i : Fin m | p.eval (α i) = 0} ≤ p.natDegree := by
    -- Convert to Finset and use Polynomial.card_roots'
    have h1 : {i : Fin m | p.eval (α i) = 0}.toFinset.card = Fintype.card {i : Fin m | p.eval (α i) = 0} := by
      simp
    have h2 : {i : Fin m | p.eval (α i) = 0}.toFinset.card ≤ p.natDegree := by
      have h_subset : {i : Fin m | p.eval (α i) = 0}.toFinset ⊆ p.roots.toFinset := by
        intro x hx
        simp at hx ⊢
        exact hx
      have h_card_le : {i : Fin m | p.eval (α i) = 0}.toFinset.card ≤ p.roots.toFinset.card := by
        exact Finset.card_le_card h_subset
      have h_roots_card : p.roots.toFinset.card ≤ p.natDegree := by
        exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' p)
      exact le_trans h_card_le h_roots_card
    linarith [h1, h2]

  -- Step 3: Combine to get the bound
  have h3 : Fintype.card {i : Fin m | p.eval (α i) = 0} ≤ n - 1 := by
    exact le_trans h_roots_le_deg hdeg

  -- Step 4: m - roots ≥ m - (n - 1) = m - n + 1
  have h4 : m - Fintype.card {i : Fin m | p.eval (α i) = 0} ≥ m - (n - 1) := by
    apply Nat.sub_le_sub_left
    exact h3

  -- Step 5: Simplify m - (n - 1) to m - n + 1
  have h5 : m - (n - 1) = m - n + 1 := by
    cases n with
    | zero =>
      -- n = 0, but then p.natDegree ≤ -1 which is impossible
      simp at hdeg
      have : p.natDegree ≥ 0 := Polynomial.natDegree_nonneg
      linarith
    | succ n =>
      cases n with
      | zero =>
        -- n = 1, so m - 0 = m - 1 + 1 = m
        simp
      | succ n =>
        -- n ≥ 2
        simp [Nat.sub_sub, Nat.add_comm]

  linarith [h4, h5]

/-! ### Alternative Formulation Using Card Roots

This version directly uses Mathlib's root counting lemma,
which may be easier for Aristotle to prove.
-/

/-- A non-zero polynomial of degree at most n-1 has at most n roots in F.

    This is a direct application of Mathlib's root counting lemma.
    The evaluation version follows by restricting to the distinct points α₁,...,αₘ. -/
lemma card_roots_le_natDegree {p : Polynomial F} {n : ℕ}
    (hp : p ≠ 0) (hdeg : p.natDegree ≤ n - 1) :
    Fintype.card {β : F | p.eval β = 0} ≤ n := by
  have := Polynomial.card_roots_toFinset_le_natDegree' hp
  exact this

/-- The Hamming weight of the evaluation vector equals m minus the number of roots.

    For distinct points α₁,...,αₘ and polynomial p:
    ∥eval(p, α)∥₀ = m - |{i : p(αᵢ) = 0}|

    This gives an alternative formulation of the weight bound.

    Proved by Aristotle (Batch 9, ae985686-e675-46e5-97a7-3570e01a607b). -/
lemma eval_weight_eq_m_minus_roots {m : ℕ} {p : Polynomial F}
    {α : Fin m → F} (h_distinct : Pairwise (fun i j => α i ≠ α j)) :
    ∥fun i : Fin m => p.eval (α i)∥₀ = m - Fintype.card {i : Fin m | p.eval (α i) = 0} := by
  unfold weightVec
  simp +decide [Fintype.card_subtype]
  rw [Finset.filter_not, Finset.card_sdiff]
  aesop

end ReedSolomonDegreeHelper

end SuccinctProofs
