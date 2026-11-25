module

public import Succinct.Codes.Core
public import Succinct.Codes.Distance
public import Succinct.Codes.Hamming
public import Succinct.Codes.HadamardCore
public import Succinct.Codes.Aristotle.HadamardDistanceGatedV2
public import Succinct.Codes.Aristotle.HadamardDistanceBridgeGated
public import Mathlib.Data.Fintype.Perm

public section

noncomputable section
open scoped BigOperators

namespace SuccinctProofs

/-! ### Hadamard Codes

Hadamard codes use all possible tuples as codewords.
The generator matrix has every possible tuple as a row.

Paper reference: Section 1.3.3

Note: Hadamard codes require finite fields (Fintype F) since they enumerate all tuples.

Key result: distance = |F|ⁿ - |F|ⁿ⁻¹

Core definitions (tupleEnum, hadamardCode) are now in HadamardCore.lean
to avoid duplication across multiple files.
-/

section HadamardCode

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {n : ℕ}

/-- For any nonzero message x, at least one entry is nonzero. -/
lemma exists_nonzero_entry_of_nonzero {x : Vec F n} (hx : x ≠ 0) :
    ∃ i : Fin n, x i ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  ext i
  exact h i

-- Distance-count formulas are available in:
-- `Succinct.Codes.Aristotle.HadamardDistanceBridgeGated`
-- `Succinct.Codes.Aristotle.HadamardDistanceGatedV2`.

end HadamardCode

end SuccinctProofs
