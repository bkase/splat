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
import Mathlib.Topology.Algebra.Polynomial

noncomputable section
open scoped BigOperators
open Matrix

namespace SuccinctProofs

/-! ## Linear algebra on `F^n` and `F^{m×n}` -/

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

/-- `x ∈ N(C)` iff `C x = 0`. -/
lemma mem_nullspace_iff {m k : ℕ} (C : Mat F k m) (x : Vec F m) :
    x ∈ Mat.nullspace (F := F) C ↔
    Matrix.mulVec C x = 0 := by
  rfl

end SubspaceVec

/- Direct sums -/
structure IsDirectSum
    {F : Type*} [Field F] {n : ℕ}
    (V T U : Submodule F (Fin n → F)) : Prop
where
  (sup_eq : T ⊔ U = V)
  (disjoint : T ⊓ U = ⊥ )

end LinearAlgebra
end SuccinctProofs
