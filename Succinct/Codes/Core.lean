import Mathlib.Data.Finset.Basic
import Succinct.LinearAlgebra

noncomputable section

namespace SuccinctProofs

section Codes

variable {F : Type*} [Field F]

/-- A linear code represented by a generator matrix `G : F^{m×n}`. -/
structure LinearCode (F : Type*) [Field F] where
  (m n : ℕ)
  (G   : Mat F m n)

/-- Encode a message vector `x : F^n` to the codeword `G x : F^m`. -/
def encode (C : LinearCode F) (x : Vec F C.n) : Vec F C.m :=
  Matrix.mulVec C.G x

scoped infixl:70 " ⇀ₑ " => encode

/-- Generator matrix for the k‑repeated code: `k` vertical copies of `Iₙ`. -/
def repeatGen {F : Type*} [Field F] (k n : ℕ) : Mat F (k * n) n :=
  fun (i : Fin (k * n)) (j : Fin n) => if i.val % n = j.val then (1 : F) else 0

/-- The k‑repeated linear code of length `k*n` and dimension `n`. -/
def repeatCode {F : Type*} [Field F] (k n : ℕ) : LinearCode F :=
  { m := k * n, n := n, G := repeatGen (F := F) k n }

/-- Kronecker-delta sum: picks out the `j0` coordinate. -/
lemma sum_single_kronecker {F : Type*} [Field F] {n : ℕ}
    (x : Vec F n) (j0 : Fin n) :
    (∑ j : Fin n, (if j = j0 then (1 : F) else 0) * x j) = x j0 := by
  classical
  -- rewrite to an `ite (j=j0) (x j) 0` sum then collapse
  have h :
      (∑ j : Fin n, (if j = j0 then (1 : F) else 0) * x j)
        = ∑ j : Fin n, (if j = j0 then x j else 0) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases h' : j = j0
    · subst h'; simp
    · simp [h', mul_comm]
  have h' :
      (∑ j : Fin n, (if j = j0 then x j else 0)) = x j0 := by
    -- mathlib lemma collapses the Finset.ite sum
    simp
  exact h.trans h'

/-- Encoding with the k-repeated code simply repeats each coordinate every `n` steps. -/
lemma repeatCode_encode {F : Type*} [Field F] (k n : ℕ) (hn : 0 < n) (x : Vec F n) :
    (repeatCode (F := F) k n) ⇀ₑ x
      = fun i : Fin (k * n) => x ⟨i.val % n, Nat.mod_lt _ hn⟩ := by
  classical
  funext i
  let j0 : Fin n := ⟨i.val % n, Nat.mod_lt _ hn⟩
  have hsum :
      (∑ j : Fin n, repeatGen (F := F) k n i j * x j : F) = x j0 := by
    classical
    -- rewrite the row as a Kronecker delta at column `j0`
    have hcond : ∀ j : Fin n, (i.val % n = j.val) = (j = j0) := by
      intro j
      apply propext
      constructor
      · intro h; apply Fin.ext; simp [h.symm, j0]
      · intro h; simpa [j0] using congrArg Fin.val h.symm
    have hdelta :
        (∑ j : Fin n, repeatGen (F := F) k n i j * x j)
          = ∑ j : Fin n, (if j = j0 then (1 : F) else 0) * x j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      simp [repeatGen, hcond j]
    have hsingle :
        (∑ j : Fin n, (if j = j0 then (1 : F) else 0) * x j)
          = x j0 :=
      sum_single_kronecker (F := F) (n := n) x j0
    -- combine the two rewrites
    exact hdelta.trans hsingle
  simp [repeatCode, encode, Mat.mulVec_apply, hsum, j0]

end Codes
end SuccinctProofs
