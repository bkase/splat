/-
# Preliminaries for Linear Codes and Evaluation Maps (Lean + mathlib)

This file sets up:
* Finite-length vectors and matrices over a field
* Matrix–vector multiplication and column/row views
* Subspaces as `Submodule`s; range & nullspace of a matrix
* Vandermonde matrices and "evaluate polynomial by coefficients" view
* Linear codes as matrices; encoding; Hamming weight & code distance (as an `Inf`)

It stays close to standard mathlib idioms, while mirroring the common crypto/coding
theory notation from paper preliminaries.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Logic.Equiv.Set
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Topology.Algebra.Polynomial -- only for some polynomial conveniences; safe to keep

noncomputable section
open scoped BigOperators
open Matrix

namespace SuccinctProofs

/-! ## 1 Linear algebra on `F^n` and `F^{m×n}` -/

section LinearAlgebra

variable {F : Type*} [Field F]

/-- Column vectors of length `n` over `F`. We use functions `Fin n → F`. -/
abbrev Vec (F : Type*) (n : ℕ) := Fin n → F

/-- `m × n` matrices over `F` with row indices `Fin m` and column indices `Fin n`. -/
abbrev Mat (F : Type*) (m n : ℕ) := Matrix (Fin m) (Fin n) F

namespace Mat

variable {m n : ℕ}

/-- j-th column of a matrix as a vector. -/
def col (A : Mat F m n) (j : Fin n) : Vec F m := fun i => A i j

/-- i-th row of a matrix as a vector. -/
def row (A : Mat F m n) (i : Fin m) : Vec F n := fun j => A i j

/-- Standard expansion for the `i`-th entry of `A x`. -/
@[simp] lemma mulVec_apply (A : Mat F m n) (x : Vec F n) (i : Fin m) :
    (mulVec A x) i = ∑ j : Fin n, A i j * x j := by
  simp [Matrix.mulVec, dotProduct]

end Mat

/-- Subspaces of `F^n` are Lean's `Submodule F (Fin n → F)`. -/
abbrev SubspaceVec (F : Type*) [Field F] (n : ℕ) := Submodule F (Vec F n)

namespace Mat

variable {m n : ℕ}

/-- Range (image) of a matrix as a subspace of `F^m`. -/
def range (A : Mat F m n) : SubspaceVec F m :=
  LinearMap.range (Matrix.mulVecLin A)

/-- Nullspace (kernel) of a matrix as a subspace of `F^n`. -/
def nullspace (A : Mat F m n) : SubspaceVec F n :=
  LinearMap.ker (Matrix.mulVecLin A)

lemma matrix_injective_iff_nullspace_eq_bot
    {m n : ℕ} (A : Mat F m n) :
    Function.Injective (Matrix.mulVec A) ↔
    Mat.nullspace (F := F) A = ⊥ := by
  constructor
  · intro h
    have hLin : Function.Injective (Matrix.mulVecLin A) := by
      intro v w hvw
      apply h
      simpa [Matrix.mulVec, Matrix.mulVecLin_apply] using hvw
    simpa [Mat.nullspace] using (LinearMap.ker_eq_bot).2 hLin
  · intro h
    have hLin : Function.Injective (Matrix.mulVecLin A) := by
      refine (LinearMap.ker_eq_bot).1 ?_
      simpa [Mat.nullspace] using h
    intro v w hvw
    apply hLin
    simpa [Matrix.mulVec, Matrix.mulVecLin_apply] using hvw

end Mat

namespace SubspaceVec

variable {m : ℕ}

/-- Given a finite-dimensional subspace, we can represent it as the range
    of a matrix `A`. -/
def basisMatrix (V : SubspaceVec (F := F) m) :
    Mat F m (Module.finrank F V) := by
  classical
  -- Use an explicit finite basis of `V`, indexed by `Fin (finrank F V)`.
  let b : Module.Basis (Fin (Module.finrank F V)) F V := Module.finBasis F V
  exact fun i j => (b j : Vec F m) i

/-- Every subspace `V ⊆ F^m` can be written as the range of some matrix `A`. -/
lemma range_basisMatrix (V : SubspaceVec (F := F) m) :
    have A := basisMatrix (F := F) V
    V = Mat.range A := by
  let b : Module.Basis (Fin (Module.finrank F V)) F V := Module.finBasis F V
  -- 1) The range of `mulVecLin` is the span of the columns.
  have hrange :
      Mat.range (basisMatrix (F := F) V)
        = Submodule.span F
            (Set.range fun j : Fin (Module.finrank F V) =>
              (basisMatrix (F := F) V).col j) := by
    simpa [Mat.range] using
      Matrix.range_mulVecLin (basisMatrix (F := F) V)
  -- 2) Those columns are exactly the coerced basis vectors of `V`.
  have hcols :
      (fun j : Fin (Module.finrank F V) =>
        (basisMatrix (F := F) V).col j)
        = fun j => (b j : Vec F m) := by
    funext j i
    simp [Mat.col, basisMatrix, b]
  -- 3) The span of those vectors equals `V`.
  have himage :
      ((fun v : V => (v : Vec F m)) '' Set.range
          (fun j : Fin (Module.finrank F V) => b j))
        = Set.range (fun j : Fin (Module.finrank F V) => (b j : Vec F m)) := by
    ext x; constructor
    · rintro ⟨v, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨_, ⟨j, rfl⟩, rfl⟩
  have hspan_coe :
      Submodule.span F
          (Set.range fun j : Fin (Module.finrank F V) =>
              (b j : Vec F m)) = V := by
    have hmap :=
      (Submodule.map_span (V.subtype)
        (Set.range fun j : Fin (Module.finrank F V) => b j))
    have hmap' :
        Submodule.map V.subtype (⊤ : Submodule F V)
          = Submodule.span F
              ((fun v : V => (v : Vec F m)) '' Set.range
                (fun j : Fin (Module.finrank F V) => b j)) := by
      simpa [b.span_eq] using hmap
    have hspan_image :
        V =
          Submodule.span F
            ((fun v : V => (v : Vec F m)) '' Set.range
              (fun j : Fin (Module.finrank F V) => b j)) := by
      simpa [Submodule.map_subtype_top] using hmap'
    simpa [himage] using hspan_image.symm
  -- 4) Combine the equalities.
  have hspan :
      Submodule.span F
          (Set.range fun j : Fin (Module.finrank F V) =>
              (basisMatrix (F := F) V).col j) = V := by
    simpa [hcols] using hspan_coe
  have h :
      Mat.range (basisMatrix (F := F) V) = V := by
    simp [hrange, hspan]
  simpa using h.symm

-- x ∈ N(C) iff Cx = 0
lemma mem_nullspace_iff {m k : ℕ} (C : Mat F k m) (x : Vec F m) :
    x ∈ Mat.nullspace (F := F) C ↔
    Matrix.mulVec C x = 0 :=
by
  rfl

end SubspaceVec


/-! ### Vandermonde matrices and polynomial evaluation view -/

def EvalPoints (m : ℕ) (F : Type*) [Field F] := Fin m → F

/-- The Vandermonde matrix with rows indexed by `Fin m` and columns `0..n-1`,
    using evaluation points `α : Fin m → F`. Entry is `(α i)^(j)`. -/
def vandermonde {m n : ℕ} (α : EvalPoints m F) : Mat F m n :=
  fun i j => (α i) ^ (j : ℕ)

/- Interpret coefficient vector `x : F^n` as a degree `< n` polynomial and evaluate. -/
def evalPolyOfVec {n : ℕ} (x : Vec F n) (β : F) : F :=
  ∑ j : Fin n, x j * β^(j : ℕ)

lemma evalPolyOfVec_comm {n : ℕ} (x : Vec F n) (β : F) :
    evalPolyOfVec (F := F) x β = ∑ j : Fin n, β^(j : ℕ) * x j := by
  -- swap factors inside the sum
  simp [evalPolyOfVec, mul_comm]

/-- Evaluating the polynomial with coefficients `x` at points `α i` equals `V.mulVec x`. -/
lemma eval_vec_eq_vandermonde_mul {m n : ℕ}
    (α : EvalPoints m F) (x : Vec F n) :
    (fun i : Fin m => evalPolyOfVec (F := F) x (α i))
      = (vandermonde (F := F) α).mulVec x := by
  funext i
  have :=
    evalPolyOfVec_comm (F := F) (x := x) (β := α i)
  -- rewrite the evaluation as a sum with the scalar on the left
  -- so that it matches the `mulVec` expansion.
  calc
    evalPolyOfVec (F := F) x (α i)
        = ∑ j : Fin n, (α i)^(j : ℕ) * x j := by
            simpa [evalPolyOfVec] using this
    _ = ((vandermonde (F := F) α).mulVec x) i := by
            simp [Mat.mulVec_apply, vandermonde]


/-- The subspace of evaluation vectors of low-degree polynomials is the
    range of the Vandermonde matrix. -/
def evalSubspace {m n : ℕ} (α : EvalPoints m F) : SubspaceVec (F := F) m :=
  Mat.range (n:=n) (vandermonde (F := F) α)

/- Direct sums -/
structure IsDirectSum
    {F : Type*} [Field F] {n : ℕ}
    (V T U : Submodule F (Fin n → F)) : Prop
where
  (sup_eq : T ⊔ U = V)
  (disjoint : T ⊓ U = ⊥ )

end LinearAlgebra

/-! ## 2. Linear codes (generator matrix), Hamming weight, distance -/

section Codes

variable {F : Type*} [Field F]

/-- A linear code represented by a generator matrix `G : F^{m×n}`. -/
structure LinearCode (F : Type*) [Field F] where
  (m n : ℕ)
  (G   : Mat F m n)

/-- Encode a message vector `x : F^n` to the codeword `G x : F^m`. -/
def encode (C : LinearCode F) (x : Vec F C.n) : Vec F C.m :=
  C.G *ᵥ x

scoped infixl:70 " ⇀ₑ " => encode

section Hamming
variable {F : Type*} [Field F]
variable [DecidableEq F]  -- needed so `x i ≠ 0` is a decidable predicate
variable {n : ℕ}

/-- Hamming weight (ℓ₀ "norm") of a vector `x : F^n`. -/
def weightVec (x : Vec F n) : ℕ :=
  Fintype.card { i : Fin n | x i ≠ 0 }

scoped notation "∥" x "∥₀" => weightVec x

/-- **Definiteness** -/
lemma weightVec_eq_zero_iff (x : Fin n → F) :
    ∥x∥₀ = 0 ↔ x = 0 := by
  classical
  -- helper facts about the subtype `{ i // x i ≠ 0 }`
  have h0 :
      ∥x∥₀ = 0 ↔ IsEmpty { i : Fin n // x i ≠ 0 } := by
    simpa [weightVec] using
      (Fintype.card_eq_zero_iff :
        Fintype.card { i : Fin n // x i ≠ 0 } = 0 ↔ _)
  have h1 :
      IsEmpty { i : Fin n // x i ≠ 0 } ↔ ∀ i : Fin n, x i = 0 := by
    constructor
    · intro h i
      by_contra hxi
      exact h.elim ⟨i, hxi⟩
    · intro hx
      refine ⟨?_⟩
      rintro ⟨i, hi⟩
      exact hi (hx i)
  -- wrap up
  constructor
  · intro hx
    have hxzero : ∀ i : Fin n, x i = 0 := (h1.mp ((h0.mp hx)))
    funext i; simpa using hxzero i
  · intro hx
    subst hx
    simp [weightVec]

/-- **0-homogeneity (invariance under nonzero scaling)**:
    for `a ≠ 0`, `weightVec (a • x) = weightVec x`. -/
lemma weightVec_smul_of_ne_zero (a : F) (x : Vec F n) (ha : a ≠ 0) :
    ∥a • x∥₀ = ∥x∥₀ := by
  classical
  -- Equivalence between the two index subtypes
  refine Fintype.card_congr
    { toFun := ?_
      invFun := ?invFun 
      left_inv := ?left
      right_inv := ?right }
  · -- forward: {(i | (a•x)i ≠ 0)} → {(i | x i ≠ 0)}
    intro ⟨i, hi⟩
    -- hi : (a•x) i ≠ 0; rewrite and use ha to conclude x i ≠ 0
    have h' : a * x i ≠ 0 := by simpa [Pi.smul_apply] using hi
    refine ⟨i, ?_⟩
    -- If x i = 0, then a * x i = 0, contradicting h'
    intro hx
    exact h' (by simp [hx])
  · -- backward: {(i | x i ≠ 0)} → {(i | (a•x)i ≠ 0)}
    intro ⟨i, hi⟩
    -- From ha and hi we get a * x i ≠ 0
    refine ⟨i, ?_⟩
    simpa [Pi.smul_apply] using mul_ne_zero ha hi
  · -- left inverse/right inverse are trivial because we keep the same index
    intro ⟨i, _⟩; rfl
  · intro ⟨i, _⟩; rfl

@[simp] lemma weightVec_zero {n : ℕ} :
    ∥(0 : Vec F n)∥₀ = 0 := by
  classical
  simp [weightVec]

/-- **Triangle inequality** for the Hamming weight pseudonorm. -/
lemma weightVec_triangle (x y : Vec F n) :
    ∥x + y∥₀ ≤ ∥x∥₀ + ∥y∥₀ := by
  classical
  -- encode supports as finite subtypes and embed into a disjoint union
  let Sxy := { i : Fin n // (x + y) i ≠ 0 }
  let Sx  := { i : Fin n // x i ≠ 0 }
  let Sy  := { i : Fin n // y i ≠ 0 }
  -- build an injection from `Sxy` into the disjoint union `Sx ⊕ Sy`
  have hcard :
      Fintype.card Sxy ≤ Fintype.card Sx + Fintype.card Sy := by
    classical
    let f : Sxy → Sum Sx Sy := fun h =>
      if hx : x h.1 = 0 then
        Sum.inr
          ⟨h.1, by
            have : y h.1 ≠ 0 := by
              simpa [Pi.add_apply, hx] using h.2
            simpa using this⟩
      else
        Sum.inl ⟨h.1, by simpa using hx⟩
    have hf : Function.Injective f := by
      intro a b h
      rcases a with ⟨i, hi⟩
      rcases b with ⟨j, hj⟩
      dsimp [f] at h
      by_cases hxi : x i = 0
      · have hxj : x j = 0 := by
          by_contra hxj
          have hxj' : x j ≠ 0 := by simpa using hxj
          simpa [f, hxi, hxj'] using h
        have hLeft :
            f ⟨i, hi⟩
              =
            Sum.inr (α := Sx)
              (⟨i, by
                  have : y i ≠ 0 := by
                    simpa [Pi.add_apply, hxi] using hi
                  simpa using this⟩ : Sy) := by
          simp [f, hxi]
        have hRight :
            f ⟨j, hj⟩
              =
            Sum.inr (α := Sx)
              (⟨j, by
                  have : y j ≠ 0 := by
                    simpa [Pi.add_apply, hxj] using hj
                  simpa using this⟩ : Sy) := by
          simp [f, hxj]
        have h' :=
          (Eq.trans hLeft.symm (Eq.trans h hRight))
        have : i = j := congrArg Subtype.val (Sum.inr.inj h')
        subst this
        simp
      · have hxj : x j ≠ 0 := by
          by_contra hxj
          have hxj' : x j = 0 := by simpa using hxj
          simpa [f, hxi, hxj'] using h
        have hLeft :
            f ⟨i, hi⟩
              =
            Sum.inl (β := Sy)
              (⟨i, by
                  have : x i ≠ 0 := by simpa using hxi
                  simpa using this⟩ : Sx) := by
          simp [f, hxi]
        have hRight :
            f ⟨j, hj⟩
              =
            Sum.inl (β := Sy)
              (⟨j, by
                  have : x j ≠ 0 := by simpa using hxj
                  simpa using this⟩ : Sx) := by
          simp [f, hxj]
        have h' :=
          (Eq.trans hLeft.symm (Eq.trans h hRight))
        have : i = j := congrArg Subtype.val (Sum.inl.inj h')
        subst this
        simp
    have hle :
        Fintype.card Sxy ≤ Fintype.card (Sum Sx Sy) :=
      Fintype.card_le_of_injective f hf
    simpa [Fintype.card_sum] using hle
  simpa [Sxy, Sx, Sy, weightVec] using hcard

/-- Weight (ℓ₀ "norm") of a set of vectors:
the minimum Hamming weight of any element, in `WithTop ℕ`
so that empty sets give `⊤`. -/
def weightSet (S : Set (Vec F n)) : WithTop ℕ :=
  sInf { w : WithTop ℕ | ∃ x ∈ S, w = ∥x∥₀ }

scoped notation "∥" S "∥ₛ" => weightSet S

-- point-set difference: { x - y | y ∈ S }
def vecDiff (x : Vec F n) (S : Set (Vec F n)) : Set (Vec F n) :=
  { z | ∃ y ∈ S, z = fun i => x i - y i }

scoped infixl:70 " -ₛ " => vecDiff

-- The main identity:
lemma weightSet_vecDiff_eq_sInf
    (x : Vec F n) (S : Set (Vec F n)) :
    ∥x -ₛ S∥ₛ
      =
    sInf { w : WithTop ℕ | ∃ y ∈ S, w = ∥x - y∥₀ } := by
  classical
  -- identify the sets under the `sInf`
  have hSet :
      { w : WithTop ℕ | ∃ z ∈ x -ₛ S, w = ∥z∥₀ }
        = { w : WithTop ℕ | ∃ y ∈ S, w = ∥x - y∥₀ } := by
    ext w
    constructor
    · intro hw
      rcases hw with ⟨z, hz, rfl⟩
      rcases hz with ⟨y, hyS, hz⟩
      have hxsub : x - y = fun i => x i - y i := by
        ext i; rfl
      refine ⟨y, hyS, ?_⟩
      simp [hz, hxsub]
    · intro hw
      rcases hw with ⟨y, hyS, rfl⟩
      have hxsub : x - y = fun i => x i - y i := by
        ext i; rfl
      refine ⟨x - y, ?_, by simp [hxsub]⟩
      exact ⟨y, hyS, hxsub⟩
  unfold weightSet
  simp [hSet]

end Hamming

section Distance

variable {F : Type*} [Field F] [DecidableEq F]

/-- Distance of a linear code: minimum Hamming weight among nonzero codewords
    (as an infimum in `WithTop ℕ`). -/
def distance (C : LinearCode F) : WithTop ℕ :=
  sInf { w : WithTop ℕ |
    ∃ x : Vec F C.n, x ≠ 0 ∧ w = ∥C ⇀ₑ x∥₀ }


lemma distance_le_weight_encode_nonzero
      (C : LinearCode F) (z : Vec F C.n) (hz : z ≠ 0) :
      distance C ≤ (∥C ⇀ₑ z∥₀ : WithTop ℕ) := by
  classical
  unfold distance
  refine sInf_le ?_
  exact ⟨z, hz, rfl⟩

lemma distance_le_weight_encode_distinct
      (C : LinearCode F) (x y : Vec F C.n) (hxy : x ≠ y) :
      distance C ≤ (∥encode C x - encode C y∥₀ : WithTop ℕ) := by
  classical
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hEnc :
      encode C x - encode C y = encode C (x - y) := by
    have h := (LinearMap.map_sub (Matrix.mulVecLin C.G) x y).symm
    simpa [encode, Matrix.mulVecLin_apply] using h
  simpa [hEnc] using
    distance_le_weight_encode_nonzero (C := C) (z := x - y) hz

lemma distance_le_weight_corruption
      (C : LinearCode F) (x δ : Vec F C.n) (hδ : δ ≠ 0) :
      distance C ≤ (∥C ⇀ₑ (x + δ) - C ⇀ₑ x∥₀ : WithTop ℕ) := by
  have hEnc : C ⇀ₑ (x + δ) - C ⇀ₑ x = C ⇀ₑ δ := by
    have h := (LinearMap.map_sub (Matrix.mulVecLin C.G) (x + δ) x).symm
    have hsub : x + δ - x = δ := by simpa using add_sub_cancel x δ
    simpa [encode, Matrix.mulVecLin_apply, hsub] using h
  simpa [hEnc] using distance_le_weight_encode_nonzero (C := C) (z := δ) hδ

lemma detect_corruption
      (C : LinearCode F) {x x' : Vec F C.n} (hx : x ≠ x')
      {d : WithTop ℕ} (hFew : ∥C ⇀ₑ x - C ⇀ₑ x'∥₀ < d) :
      (distance C : WithTop ℕ) < d := by
  have := distance_le_weight_encode_distinct (C := C) (x := x) (y := x') hx
  exact lt_of_le_of_lt this hFew

end Distance

section EvalCode

/-- Evaluation-code instance from Vandermonde at points `α`, degree bound `< n`. -/
def evalCode {m n : ℕ} (α : EvalPoints m F) : LinearCode F :=
  { m := m, n := n, G := vandermonde (F := F) α }

/-- Encoding with `evalCode α` equals evaluating the polynomial defined by `x`. -/
lemma evalCode_encode_eq_eval {m n : ℕ} (α : EvalPoints m F) (x : Vec F n) :
    (evalCode α) ⇀ₑ x
      = fun i : Fin m => evalPolyOfVec x (α i) := by
  simpa [evalCode, encode, vandermonde]
    using (eval_vec_eq_vandermonde_mul α x).symm

end EvalCode

end Codes
