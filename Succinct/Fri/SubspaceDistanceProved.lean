import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Module.Submodule.Basic
import Succinct.LinearAlgebra
import Succinct.Codes.Core
import Succinct.Codes.Hamming

noncomputable section

namespace SuccinctProofs

/-! ## Subspace Distance Theory (§3.2.3) - Proved Lemmas

This file contains lemmas proved by Aristotle:
- `unique_decoding_radius`: Uniqueness of decomposition within decoding radius
- `subspace_distance_contradiction`: Contradiction for linearly dependent rows

Project IDs:
- unique_decoding_radius: 7ae47fa0-e2b9-418f-82c9-ad0f85879527
- subspace_distance_contradiction: 16f2d5b3-0988-48f8-8fa3-d1149da3e57d
-/

section Definitions

variable {F : Type*} [Field F] [DecidableEq F]
variable {k n m : ℕ}

/-- Subspace distance: minimum weight of nonzero vectors in V -/
def subspaceDistance (V : Submodule F (Vec F k)) : WithTop ℕ :=
  sInf { w : WithTop ℕ | ∃ x : Vec F k, x ∈ V ∧ x ≠ 0 ∧ w = ∥x∥₀ }

scoped notation "∥" V "∥ₛ₀" => subspaceDistance V

/-- Number of nonzero rows in a matrix -/
def nonZeroRows (X : Mat F k n) : ℕ :=
  Fintype.card { i : Fin k | X.row i ≠ 0 }

/-- Column of a matrix -/
def col (A : Mat F k n) (j : Fin n) : Vec F k :=
  fun i => A i j

/-- q-Close to subspace -/
def qCloseToSubspace (X : Mat F k n) (V : Submodule F (Vec F k)) (q : ℕ) : Prop :=
  ∃ Y : Mat F k n,
    (∀ j : Fin n, col Y j ∈ V) ∧
    (nonZeroRows (X - Y) ≤ q)

/-- Code distance at least d: every nonzero codeword has weight ≥ d -/
def codeHasDistanceAtLeast (G : Mat F m n) (d : ℕ) : Prop :=
  ∀ x : Vec F n, x ≠ 0 → ∥Matrix.mulVec G x∥₀ ≥ d

end Definitions


section NonZeroRowsBounds

variable {F : Type*} [Field F] [DecidableEq F]
variable {k n : ℕ}

/-- The nonzero rows of a matrix difference are bounded by the sum of nonzero rows.

PROVED by Aristotle (project: b87e6e08-15f3-4bbd-8abc-dc41a7e8a5d7).

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma nonZeroRows_sub_le_add (A B : Mat F k n) :
    nonZeroRows (A - B) ≤ nonZeroRows A + nonZeroRows B := by
  unfold nonZeroRows
  simp only [Fintype.card_subtype]
  -- If both A.row i = 0 and B.row i = 0, then (A-B).row i = 0
  have h_subset : Finset.filter (fun i => (A - B).row i ≠ 0) Finset.univ ⊆
      Finset.filter (fun i => A.row i ≠ 0) Finset.univ ∪
      Finset.filter (fun i => B.row i ≠ 0) Finset.univ := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_contra h
    push_neg at h
    apply hi.2
    funext j
    have hA : A.row i = 0 := h.1 (Finset.mem_univ i)
    have hB : B.row i = 0 := h.2 (Finset.mem_univ i)
    calc (A - B).row i j = A.row i j - B.row i j := rfl
      _ = A i j - B i j := rfl
      _ = 0 - 0 := by rw [show A i j = 0 from congr_fun hA j, show B i j = 0 from congr_fun hB j]
      _ = 0 := sub_zero 0
  calc (Finset.filter (fun i => (A - B).row i ≠ 0) Finset.univ).card
      ≤ (Finset.filter (fun i => A.row i ≠ 0) Finset.univ ∪
         Finset.filter (fun i => B.row i ≠ 0) Finset.univ).card :=
            Finset.card_le_card h_subset
    _ ≤ (Finset.filter (fun i => A.row i ≠ 0) Finset.univ).card +
        (Finset.filter (fun i => B.row i ≠ 0) Finset.univ).card :=
            Finset.card_union_le _ _

end NonZeroRowsBounds


section SubspaceDistanceHelpers

variable {F : Type*} [Field F] [DecidableEq F]
variable {k n : ℕ}

/-- Weight of a column is bounded by number of nonzero rows.

PROVED by Aristotle (project: 5d9cfdef-870a-4a9d-bf77-4caa51ffd842).

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma col_weight_le_nonZeroRows (M : Mat F k n) (j : Fin n) :
    weightVec (col M j) ≤ nonZeroRows M := by
  unfold weightVec nonZeroRows col
  simp only [Fintype.card_subtype]
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  constructor
  · exact Finset.mem_univ i
  · intro h_row_zero
    exact hi.2 (congr_fun h_row_zero j)

/-- If all columns of M are in V and have weight < subspace distance, then M = 0.

PROVED by Aristotle (project: 5d9cfdef-870a-4a9d-bf77-4caa51ffd842).

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma matrix_zero_from_subspace_distance
    (V : Submodule F (Vec F k))
    (M : Mat F k n)
    (h_cols_in_V : ∀ j : Fin n, col M j ∈ V)
    (h_weight_bound : ∀ j : Fin n, (weightVec (col M j) : WithTop ℕ) < subspaceDistance V) :
    M = 0 := by
  have h_all_zero_cols : ∀ j, col M j = 0 := by
    intro j
    by_contra h_nonzero_col
    have h_weight_ge_subspaceDistance : weightVec (col M j) ≥ subspaceDistance V := by
      refine' csInf_le _ _ <;> aesop
    exact not_lt_of_ge h_weight_ge_subspaceDistance (h_weight_bound j)
  exact funext fun i => funext fun j => congr_fun (h_all_zero_cols j) i

end SubspaceDistanceHelpers


section UniqueDecodingRadius

variable {F : Type*} [Field F] [DecidableEq F]
variable {k n : ℕ}

/-- **Lemma**: Unique Decoding Radius

Let V ⊆ F^k be a subspace with distance d'.
Let X ∈ F^{k×n}.
If X is q-close to V with q < d'/2, then there exist unique
matrices Y, Ξ ∈ F^{k×n} such that:
1. X = Y + Ξ
2. The columns of Y are in V
3. Ξ has at most q nonzero rows

PROVED by Aristotle (project: 7ae47fa0-e2b9-418f-82c9-ad0f85879527).

Proof sketch:
- Existence: By definition of q-close
- Uniqueness: If X = Y₁ + Ξ₁ = Y₂ + Ξ₂, then Y₁ - Y₂ = Ξ₂ - Ξ₁
- Left side is in V (columns in V), right side has < d' nonzero rows
- By subspace distance property, both sides must be 0
- Therefore Y₁ = Y₂ and Ξ₁ = Ξ₂ -/
lemma unique_decoding_radius
    (V : Submodule F (Vec F k))
    (X : Mat F k n)
    (q : ℕ)
    (h_close : qCloseToSubspace X V q)
    (h_dist : ∥V∥ₛ₀ > (2 * q : ℕ))
    (hd' : ∥V∥ₛ₀ ≠ ⊤) :
    ∃! Y : Mat F k n,
      (∃ Ξ : Mat F k n,
        X = Y + Ξ ∧
        (∀ j : Fin n, col Y j ∈ V) ∧
        nonZeroRows Ξ ≤ q) := by
  rcases h_close with ⟨Y, hY⟩
  refine' ⟨Y, ⟨X - Y, ?_, hY.1, hY.2⟩, ?_⟩
  · -- Show X = Y + (X - Y)
    simp
  · -- Show uniqueness
    intro Y' hY'
    rcases hY' with ⟨Ξ', h_eq, hY'_in_V, h_Ξ'_rows⟩
    -- Proof that nonZeroRows (Y' - Y) ≤ 2 * q
    -- The set of nonzero rows of (Y' - Y) is contained in the union of
    -- nonzero rows of (X - Y) and nonzero rows of Ξ'
    -- Since X = Y' + Ξ', we have Y' - Y = X - Y - Ξ' = (X - Y) - Ξ'
    -- So if row i of both (X - Y) and Ξ' are zero, row i of (Y' - Y) is zero
    have h_diff : nonZeroRows (Y' - Y) ≤ 2 * q := by
      -- Y' - Y = (X - Y) - Ξ' since X = Y' + Ξ' implies Y' = X - Ξ'
      have h_Y'_eq : Y' = X - Ξ' := by rw [h_eq]; abel
      have h_diff_eq : Y' - Y = (X - Y) - Ξ' := by rw [h_Y'_eq]; abel
      calc nonZeroRows (Y' - Y)
          = nonZeroRows ((X - Y) - Ξ') := by rw [h_diff_eq]
        _ ≤ nonZeroRows (X - Y) + nonZeroRows Ξ' := nonZeroRows_sub_le_add _ _
        _ ≤ q + q := Nat.add_le_add hY.2 h_Ξ'_rows
        _ = 2 * q := by ring
    -- Now use subspace distance to show Y' - Y = 0
    -- Each column of (Y' - Y) is in V (since Y' and Y have columns in V)
    -- Each column has weight ≤ nonZeroRows (Y' - Y) ≤ 2*q < d'
    -- By subspace distance property, each column is zero
    have h_zero : Y' - Y = 0 := by
      -- Each column of (Y' - Y) is in V (since Y' and Y have columns in V)
      have h_cols_diff_in_V : ∀ j : Fin n, col (Y' - Y) j ∈ V := by
        intro j
        have h1 : col (Y' - Y) j = col Y' j - col Y j := by
          ext i; simp [col, Matrix.sub_apply]
        rw [h1]
        exact V.sub_mem (hY'_in_V j) (hY.1 j)
      -- Each column has weight ≤ nonZeroRows (Y' - Y) ≤ 2*q < d'
      have h_weight_bound : ∀ j : Fin n, (weightVec (col (Y' - Y) j) : WithTop ℕ) < subspaceDistance V := by
        intro j
        have h_col_weight := col_weight_le_nonZeroRows (Y' - Y) j
        calc (weightVec (col (Y' - Y) j) : WithTop ℕ)
            ≤ (nonZeroRows (Y' - Y) : WithTop ℕ) := by exact_mod_cast h_col_weight
          _ ≤ (2 * q : ℕ) := by exact_mod_cast h_diff
          _ < subspaceDistance V := h_dist
      exact matrix_zero_from_subspace_distance V (Y' - Y) h_cols_diff_in_V h_weight_bound
    exact sub_eq_zero.mp h_zero

end UniqueDecodingRadius


section SubspaceDistanceContradiction

variable {F : Type*} [Field F] [DecidableEq F]
variable {m : ℕ}

/-- **Lemma**: Subspace Distance Contradiction

Let G ∈ F^{m×2} with distance d.
Let R ⊆ {1, ..., m} with |R| > m - d.
If there exist scalars Y₁, Y₂ ∈ F, not both zero, such that for all r ∈ R:
  G_{r1}Y₁ + G_{r2}Y₂ = 0
This contradicts the distance property.

PROVED by Aristotle (project: 16f2d5b3-0988-48f8-8fa3-d1149da3e57d).

Proof sketch:
- Assume such Y₁, Y₂ exist, not both zero
- Let Y = (Y₁, Y₂) ∈ F², which is nonzero
- For all r ∈ R: (GY)_r = G_{r1}Y₁ + G_{r2}Y₂ = 0
- So GY has at least |R| zero coordinates
- Weight of GY ≤ m - |R| < m - (m - d) = d
- But G has distance d, so any nonzero codeword has weight ≥ d
- Contradiction: GY is nonzero but has weight < d -/
lemma subspace_distance_contradiction
    (G : Mat F m 2) (d : ℕ)
    (h_dist : codeHasDistanceAtLeast G d)
    (R : Finset (Fin m))
    (hR : R.card > m - d)
    (Y₁ Y₂ : F)
    (hY : Y₁ ≠ 0 ∨ Y₂ ≠ 0)
    (h_zero : ∀ r ∈ R, G r 0 * Y₁ + G r 1 * Y₂ = 0) :
    False := by
  -- Construct the nonzero vector x = (Y₁, Y₂)
  let x : Vec F 2 := fun i => if i = 0 then Y₁ else Y₂
  have hx_ne_zero : x ≠ 0 := by
    intro h_zero_x
    have h1 : x 0 = 0 := by simp [h_zero_x]
    have h2 : x 1 = 0 := by simp [h_zero_x]
    simp [x] at h1 h2
    rcases hY with hY₁ | hY₂
    · contradiction
    · contradiction
  -- Show that (G * x) has at least |R| zeros
  have h_zeros : ∀ r ∈ R, (Matrix.mulVec G x) r = 0 := by
    intro r hr
    simp [Matrix.mulVec, dotProduct, x]
    exact h_zero r hr
  -- This means weight of G*x is at most m - |R| < d
  have h_weight : ∥Matrix.mulVec G x∥₀ ≤ m - R.card := by
    simp only [weightVec]
    -- The support is contained in the complement of R
    have h_support_le : (Finset.univ.filter (fun i => (Matrix.mulVec G x) i ≠ 0)).card ≤ Rᶜ.card := by
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_compl]
      intro hR
      exact hi (h_zeros i hR)
    have h_card_eq : Fintype.card {i : Fin m | (Matrix.mulVec G x) i ≠ 0} =
        (Finset.univ.filter (fun i => (Matrix.mulVec G x) i ≠ 0)).card := by
      simp [Fintype.card_subtype]
    rw [h_card_eq]
    calc (Finset.univ.filter (fun i => (Matrix.mulVec G x) i ≠ 0)).card
        ≤ Rᶜ.card := h_support_le
      _ = Fintype.card (Fin m) - R.card := Finset.card_compl R
      _ = m - R.card := by simp
  -- But this contradicts the distance property
  have h_dist' := h_dist x hx_ne_zero
  -- hR : R.card > m - d, which implies m - R.card < d (with proper bounds)
  have h_R_le_m : R.card ≤ m := by
    calc R.card ≤ Fintype.card (Fin m) := Finset.card_le_univ R
      _ = m := Fintype.card_fin m
  -- We need: R.card > m - d → m - R.card < d
  -- This follows from: R.card + (m - R.card) = m and R.card > m - d
  have h_lt : m - R.card < d := by
    -- If d ≤ m: R.card > m - d, so R.card + d > m, so d > m - R.card
    -- If d > m: m - d = 0, so R.card > 0. And m - R.card ≤ m < d
    by_cases hd : d ≤ m
    · -- d ≤ m case: use direct arithmetic
      have h1 : R.card + (m - R.card) = m := Nat.add_sub_cancel' h_R_le_m
      have h2 : R.card > m - d := hR
      omega
    · -- d > m case: m - R.card ≤ m < d
      push_neg at hd
      calc m - R.card ≤ m := Nat.sub_le m R.card
        _ < d := hd
  omega

end SubspaceDistanceContradiction

end SuccinctProofs
