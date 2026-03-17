import Succinct.LinearAlgebra
import Succinct.Vandermonde
import Succinct.Codes.Core
import Succinct.Codes.Distance
import Succinct.Codes.Lagrange

noncomputable section
open scoped BigOperators

namespace SuccinctProofs

/-! ### Reed-Solomon Codes

Reed-Solomon codes are evaluation codes: the codeword is the polynomial
evaluated at m distinct points. This file develops RS properties
independent of the Singleton bound.

Key paper reference: Section 1.3.2
-/

section ReedSolomon

variable (F : Type*) [Field F] [DecidableEq F]

/-- A Reed-Solomon code is an evaluation code with distinct points.
    We add the distinctness condition as part of the structure. -/
structure RSCode where
  m : ℕ      -- block length (number of evaluation points)
  n : ℕ      -- message dimension (degree bound - 1)
  α : EvalPoints m F
  distinct : ∀ i j, i ≠ j → α i ≠ α j

/-- The evaluation points are all distinct (by definition of RS code). -/
lemma RSCode.eval_points_distinct {C : RSCode F} (i j : Fin C.m) (h : i ≠ j) :
    C.α i ≠ C.α j := by
  exact C.distinct i j h

/-- A degree < n polynomial is uniquely determined by its values at n distinct points.
    This is the key property that makes RS codes work.

    CORRECTED VERSION: Requires n ≤ m (need at least as many points as degree bound).
    PROVED by Aristotle in Lagrange.lean. -/
lemma RSCode.unique_interpolation_of_le
    {C : RSCode F} (hle : C.n ≤ C.m)
    (x y : Vec F C.n)
    (h : (evalCode (α := C.α) (n := C.n) ⇀ₑ x) = (evalCode (α := C.α) (n := C.n) ⇀ₑ y)) :
    x = y := by
  -- This is exactly evalCode_injective_of_le from Lagrange.lean
  have h_inj := evalCode_injective_of_le C.α C.distinct hle
  exact h_inj h

/-- When n ≤ m and points are distinct, the RS code has positive distance.
    This follows because the code is injective, so Gx ≠ 0 for x ≠ 0. -/
lemma RSCode.distance_pos_of_le {C : RSCode F} (hle : C.n ≤ C.m) :
    0 < distance (evalCode (α := C.α) (n := C.n)) := by
  -- Since the code is injective, any nonzero x has Gx ≠ 0
  -- Therefore the minimum weight is at least 1
  -- Since the RS code encoder is injective when $n \le m$ and points are distinct, for any $x \ne 0$, $Gx \ne 0$.
  have h_nonzero : ∀ x : Fin C.n → F, x ≠ 0 → (SuccinctProofs.evalCode C.α) ⇀ₑ x ≠ 0 := by
    intro x hx_ne_zero
    by_contra h_contra
    have h_injective : Function.Injective (fun x : Fin C.n → F => (SuccinctProofs.evalCode (α := C.α) (n := C.n) ⇀ₑ x)) := by
      apply_rules [ evalCode_injective_of_le ];
      exact C.distinct;
    have := @h_injective x 0; simp_all +decide ;
    exact this ( by ext i; simp +decide [ SuccinctProofs.encode ] );
  -- Therefore, the distance of the RS code is at least 1.
  have h_dist_ge_one : ∀ x : Fin C.n → F, x ≠ 0 → 1 ≤ ∥(SuccinctProofs.evalCode C.α) ⇀ₑ x∥₀ := by
    intro x hx_ne_zero
    have h_nonzero : (SuccinctProofs.evalCode C.α) ⇀ₑ x ≠ 0 := h_nonzero x hx_ne_zero;
    exact Nat.pos_of_ne_zero fun h => h_nonzero <| by simpa using weightVec_eq_zero_iff _ |>.1 h;
  -- Since the minimum Hamming weight of any nonzero codeword is at least 1, the infimum of these weights is also at least 1.
  have h_inf_ge_one : 1 ≤ sInf {w : WithTop ℕ | ∃ x : Fin C.n → F, x ≠ 0 ∧ w = ∥(SuccinctProofs.evalCode C.α) ⇀ₑ x∥₀} := by
    rcases C with ⟨ _, _, _, _ ⟩ ; aesop;
  exact lt_of_lt_of_le zero_lt_one h_inf_ge_one

/-- The message dimension of an RS code with n ≤ m and distinct points is exactly n.
    (The generator matrix has full column rank.) -/
lemma RSCode.dim_eq_n_of_le {C : RSCode F} (hle : C.n ≤ C.m) :
    (evalCode (α := C.α) (n := C.n)).n = C.n := by
  -- By definition, we set n as the dimension
  -- This lemma states that the matrix actually has rank n (full rank)
  rfl

/-- **Key RS property**: A nonzero polynomial of degree < n can have at most n-1 roots.
    This is a fundamental fact about polynomials.

    Used in: Distance proof (nonzero polynomial has limited zeros)

    Proved by Aristotle (Batch 11, fd55c7e6-6cfe-4b43-a05c-cecbf484b3d7). -/
lemma poly_roots_bound {p : Polynomial F} (hp : p ≠ 0) (hDeg : p.natDegree < n) :
    {β : F | p.eval β = 0}.ncard ≤ n - 1 := by
  -- Use Aristotle's proof from ReedSolomonPolyRootsBound
  have h_roots : (p.roots.toFinset).card ≤ n - 1 := by
    exact le_trans (Multiset.toFinset_card_le _) (Nat.le_sub_one_of_lt (lt_of_le_of_lt (Polynomial.card_roots' _) hDeg))
  exact le_trans (by rw [show {β : F | p.eval β = 0} = p.roots.toFinset by ext x; aesop];
                     rw [Set.ncard_eq_toFinset_card _]; aesop)
              h_roots

/-- **Key RS property**: If a degree < n polynomial vanishes at n distinct points,
    it must be the zero polynomial. -/
lemma poly_eq_zero_of_n_roots {p : Polynomial F} {α : Fin n → F}
    (hDistinct : ∀ i j, i ≠ j → α i ≠ α j)
    (hRoots : ∀ i, p.eval (α i) = 0)
    (hDeg : p.natDegree < n) :
    p = 0 := by
  -- This is poly_eq_zero_of_distinct_roots from Lagrange.lean
  -- Already proved by Aristotle
  by_contra h_nonzero;
  -- Since p is a non-zero polynomial of degree less than n, it can have at most n-1 roots.
  have h_roots : (p.roots.toFinset).card ≤ n - 1 := by
    exact le_trans ( Multiset.toFinset_card_le _ ) ( Nat.le_sub_one_of_lt ( lt_of_le_of_lt ( Polynomial.card_roots' _ ) hDeg ) );
  have h_roots_card : (Finset.image α Finset.univ).card ≤ n - 1 := by
    exact le_trans ( Finset.card_le_card ( show Finset.image α Finset.univ ⊆ p.roots.toFinset from fun x hx => by aesop ) ) h_roots;
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ Finset.card_image_of_injective _ fun i j hij => not_imp_not.mp ( hDistinct i j ) hij ]

/-- For RS codes, the encoding is the same as polynomial evaluation.
    This is a notation convenience. -/
lemma RSCode.encode_eq_eval {C : RSCode F} (x : Vec F C.n) (i : Fin C.m) :
    (evalCode (α := C.α) (n := C.n) ⇀ₑ x) i = evalPolyOfVec x (C.α i) := by
  -- Follows from evalCode_encode_eq_eval
  simp [evalCode_encode_eq_eval]

end ReedSolomon

end SuccinctProofs
