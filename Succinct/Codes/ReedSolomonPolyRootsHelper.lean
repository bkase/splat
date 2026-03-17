import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Card

/-! ### Reed-Solomon Polynomial Roots Lemma

This file contains a simple lemma about polynomial roots:
A root of p in F is also in p.roots multiset.

This is an independent, self-contained fact that Aristotle should be able to prove.
-/

noncomputable section

open scoped BigOperators

namespace SuccinctProofs

section ReedSolomonPolyRootsHelper

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### Target Lemma for Aristotle

**Helper 1**: A root of p in F is also in p.roots multiset.

    If p.eval β = 0 for some β : F, then β is in p.roots.toFinset.

This is a fundamental fact about polynomial roots that should be in Mathlib.
Aristotle should be able to prove this using basic polynomial properties.
-/

lemma root_in_roots_finset {p : Polynomial F} {β : F} (h_root : p.eval β = 0) (hp : p ≠ 0) :
    β ∈ p.roots.toFinset := by
  simp [Multiset.mem_toFinset, h_root, hp]

end ReedSolomonPolyRootsHelper

end SuccinctProofs
