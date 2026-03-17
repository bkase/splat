/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 810309e0-cc28-4ec0-aa36-ae4311fa5790

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem poly_roots_card_bound [DecidableEq F] (p : Polynomial F) (hp : p ≠ 0) :
    (p.roots.toFinset.card : ℕ) ≤ p.natDegree

- theorem poly_roots_fintype_card_bound [Fintype F] [DecidableEq F] (p : Polynomial F) (hp : p ≠ 0) :
    Fintype.card {x : F | p.eval x = 0} ≤ p.natDegree

- theorem poly_root_probability_bound [Fintype F] [DecidableEq F] (p : Polynomial F) (hp : p ≠ 0)
    (hF : Fintype.card F > 0) :
    (Fintype.card {x : F | p.eval x = 0} : ℝ) / Fintype.card F ≤
    (p.natDegree : ℝ) / Fintype.card F
-/

/-
Target: Prove that polynomial roots count is bounded by degree

Key insight: A nonzero polynomial of degree n has at most n roots in any field.
This is a fundamental result from algebra (polynomial factor theorem).

-/

import Mathlib.Tactic


noncomputable section

open Polynomial

section MainTheorem

variable {F : Type*} [Field F]

/-- **Main Theorem 1**: Polynomial roots count bound

    A nonzero polynomial of degree n has at most n roots.

    PROVE THIS THEOREM.
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem poly_roots_card_bound [DecidableEq F] (p : Polynomial F) (hp : p ≠ 0) :
    (p.roots.toFinset.card : ℕ) ≤ p.natDegree := by
  exact le_trans ( Multiset.toFinset_card_le _ ) ( Polynomial.card_roots' _ )

/-- **Main Theorem 2**: Fintype version of roots bound

    When F is finite, the set {x : F | p.eval x = 0} has cardinality at most p.natDegree.

    PROVE THIS THEOREM.
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem poly_roots_fintype_card_bound [Fintype F] [DecidableEq F] (p : Polynomial F) (hp : p ≠ 0) :
    Fintype.card {x : F | p.eval x = 0} ≤ p.natDegree := by
  convert poly_roots_card_bound p hp using 1;
  rw [ Fintype.card_of_subtype ] ; aesop_cat;

/-- **Corollary**: Probability of hitting a root

    For a nonzero polynomial p over a finite field F,
    the probability that a random element of F is a root is at most natDegree(p) / |F|.

    PROVE THIS THEOREM.
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem poly_root_probability_bound [Fintype F] [DecidableEq F] (p : Polynomial F) (hp : p ≠ 0)
    (hF : Fintype.card F > 0) :
    (Fintype.card {x : F | p.eval x = 0} : ℝ) / Fintype.card F ≤
    (p.natDegree : ℝ) / Fintype.card F := by
  exact div_le_div_of_nonneg_right ( mod_cast by simpa using poly_roots_fintype_card_bound p hp |> le_trans <| le_refl _ ) ( Nat.cast_nonneg _ )

end MainTheorem
