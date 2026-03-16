import Succinct.Codes.Core
import Mathlib.Data.Fintype.Card

/-! ### Hadamard Code Core Definitions

This file contains the shared definitions used across multiple Hadamard code files.
These definitions were previously duplicated in:
- Succinct/Codes/Hadamard.lean
- Succinct/Codes/HadamardDistance.lean
- Succinct/Codes/HadamardDistanceStep4a.lean

Paper reference: Section 1.3.3

Key result: distance = |F|ⁿ - |F|ⁿ⁻¹
-/

noncomputable section

namespace SuccinctProofs

section HadamardCore

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {n : ℕ}

/-- Enumeration of all n-tuples over finite field F.

    This gives a bijection between `Fin m` and `Fin n → F` where m = |F|ⁿ.
    The function uses Fintype.equivFin to create the bijection. -/
def tupleEnum : Fin (Fintype.card (Fin n → F)) → (Fin n → F) :=
  fun i => Fintype.equivFin (Fin n → F) i

/-- A Hadamard code has ALL possible n-tuples as rows of the generator matrix.

    Block length: |F|ⁿ (all possible n-tuples)
    Message dimension: n
    Generator matrix: Row i is the i-th n-tuple from the enumeration -/
def hadamardCode : LinearCode F where
  m := Fintype.card (Fin n → F)  -- block length is |F|ⁿ
  n := n                            -- message dimension
  G := fun (row : Fin (Fintype.card (Fin n → F))) (j : Fin n) => (tupleEnum row) j

/-- The number of rows in a Hadamard code is |F|ⁿ. -/
lemma hadamard_block_length :
    (hadamardCode (F := F) (n := n)).m = Fintype.card (Fin n → F) := by
  rfl

/-- The message dimension of a Hadamard code is n. -/
lemma hadamard_message_dim :
    (hadamardCode (F := F) (n := n)).n = n := by
  rfl

end HadamardCore

end SuccinctProofs
