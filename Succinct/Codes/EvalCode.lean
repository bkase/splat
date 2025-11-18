import Succinct.LinearAlgebra
import Succinct.Vandermonde
import Succinct.Codes.Core

noncomputable section

namespace SuccinctProofs

section EvalCode

variable {F : Type*} [Field F]

/-- Evaluation-code instance from Vandermonde at points `α`, degree bound `< n`. -/
def evalCode {m n : ℕ} (α : EvalPoints m F) : LinearCode F :=
  { m := m, n := n, G := vandermonde (F := F) α }

/-- Encoding with `evalCode α` equals evaluating the polynomial defined by `x`. -/
lemma evalCode_encode_eq_eval {m n : ℕ} (α : EvalPoints m F) (x : Vec F n) :
    (evalCode α) ⇀ₑ x
      = fun i : Fin m => evalPolyOfVec x (α i) := by
  simpa [evalCode, encode, vandermonde]
    using (eval_vec_eq_vandermonde_mul (F := F) α x).symm

end EvalCode
end SuccinctProofs
