import Succinct.LinearAlgebra
import Succinct.Codes.Core
import Succinct.Codes.Distance
import Succinct.Codes.Hamming
import Succinct.Checks.Zero
import Succinct.Prob.Implication
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Notation

/-! ### Matrix Zero Check (§3.1.2)

Extends the zero check to matrices: if random row projection is zero,
then with high probability the entire matrix is zero.

Paper reference: Lemma "Matrix Zero Check" (§3.1.2)
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace SuccinctProofs

section MatrixZeroCheck

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Matrix Zero Check** (§3.1.2): Check if a matrix X is zero by testing
    random rows against code G.

    Statement: Let G ∈ 𝔽^{m×n} have distance d. Let X ∈ 𝔽^{k×n}.
    Let r be uniform on {1,…,m}. Then: X g̃_r = 0 ⇒_{1-d/m} X = 0

    Proof sketch: Apply zero_check to each row of X. -/
lemma matrix_zero_check {d m n k : ℕ} (G : LinearCode F)
    (h_dist : distance G ≥ d) (hd_pos : 0 < d) (hle : d ≤ G.m)
    (hGm : G.m = m) (hGn : G.n = n)
    {X : Fin k → Fin n → F} :
    Succinct.Prob.ProbImpEv (uniformOn (Set.univ : Set (Fin G.m)))
      { ω | ∀ j : Fin k, ∑ i : Fin G.n, G.G ω i * X j (⟨i, by omega⟩ : Fin n) = 0 }
      { ω | X = 0 }
      (1 - d / G.m) := by
  -- Key idea: Interpret each row of X as a message vector
  -- For each row xⱼ of X, apply the zero check to G xⱼ
  -- If all rows satisfy the zero check, then X = 0
  -- Apply the zero_check lemma to each row of X.
  have h_zero_check_rows : ∀ j : Fin k, {ω : Fin G.m | ∑ i : Fin G.n, G.G ω i * X j ⟨i, by linarith [Fin.is_lt i]⟩ = 0} ⟹[ProbabilityTheory.uniformOn Set.univ]_(1 - (d : ENNReal) / G.m) {ω : Fin G.m | X j = 0} := by
    intro j
    convert zero_check G h_dist hd_pos hle using 1
    aesop
  unfold Succinct.Prob.ProbImpEv at *
  by_cases h : ∃ ω : Fin G.m, ¬X = 0 ∧ ∀ j : Fin k, ∑ i : Fin G.n, G.G ω i * X j ⟨i, by linarith [Fin.is_lt i]⟩ = 0 <;> simp_all +decide [funext_iff]
  · obtain ⟨⟨j, i, hij⟩, ω, hω⟩ := h
    refine' le_trans _ (h_zero_check_rows j)
    refine' MeasureTheory.measure_mono _
    exact fun x hx => ⟨hx.1 j, fun hx' => hx.2 <| by aesop⟩
  · rw [Set.inter_comm]
    rw [show { ω : Fin G.m | ∀ x : Fin k, ∀ x_1 : Fin n, X x x_1 = 0 }ᶜ ∩ { ω : Fin G.m | ∀ j : Fin k, ∑ i : Fin G.n, G.G ω i * X j ⟨(i : ℕ), by linarith [Fin.is_lt i]⟩ = 0 } = ∅ from _] <;> norm_num
    simp +decide [Set.ext_iff]
    exact fun ω j i hi => h j i hi ω

/-- **Helper**: Row-wise zero check for matrix X.

    Tests each row of X independently against code G.
    If (G xⱼ)_r = 0 for all rows j with high probability, then X = 0. -/
lemma rowwise_zero_check {d m n k : ℕ} (G : LinearCode F)
    (h_dist : distance G ≥ d) (hd_pos : 0 < d) (hle : d ≤ G.m)
    (hGm : G.m = m) (hGn : G.n = n)
    {X : Fin k → Fin n → F} :
    Succinct.Prob.ProbImpEv (uniformOn (Set.univ : Set (Fin G.m)))
      { ω | ∀ j : Fin k, (G ⇀ₑ fun fi => X j (⟨fi, by omega⟩ : Fin n)) ω = 0 }
      { ω | ∀ j : Fin k, X j = 0 }
      (1 - d / G.m) := by
  -- Apply zero_check to each row independently
  -- Use the fact that the zero check probability is the same for each row
  convert matrix_zero_check G h_dist hd_pos hle hGm hGn using 1
  simp +decide [funext_iff]

/-- **Helper**: Row zero implies matrix zero (deterministic).

    If all rows of X are zero vectors, then X is the zero matrix. -/
lemma rows_zero_imp_matrix_zero {k n : ℕ} {X : Fin k → Fin n → F} :
    (∀ j : Fin k, X j = 0) → X = 0 := by
  intro h_rows
  ext j i
  have h_row : X j = 0 := h_rows j
  -- X j is a function Fin n → F, so (X j = 0) means it's the zero function
  -- We need to extract from this equality that (X j) i = 0
  exact congr_fun h_row i

/-- **Alternative formulation**: Using column interpretation.

    Treat columns of X as message vectors and check their encodings jointly. -/
lemma matrix_zero_check_columns {d m n k : ℕ} (G : LinearCode F)
    (h_dist : distance G ≥ d) (hd_pos : 0 < d) (hle : d ≤ G.m)
    (hGm : G.m = m) (hGn : G.n = n)
    {X : Fin k → Fin n → F} :
    Succinct.Prob.ProbImpEv (uniformOn (Set.univ : Set (Fin G.m)))
      { ω | ∀ j : Fin k, ∑ i : Fin G.n, G.G ω i * X j (⟨i, by omega⟩ : Fin n) = 0 }
      { ω | X = 0 }
      (1 - d / G.m) := by
  have := @SuccinctProofs.matrix_zero_check
  exact this G h_dist hd_pos hle hGm hGn

end MatrixZeroCheck

end SuccinctProofs
