import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct

import Succinct.LinearAlgebra

noncomputable section
open scoped BigOperators
open Matrix

namespace SuccinctProofs

/-! ### Vandermonde matrices and polynomial evaluation view -/

def EvalPoints (m : ℕ) (F : Type*) [Field F] := Fin m → F

variable {F : Type*} [Field F]

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

end SuccinctProofs
