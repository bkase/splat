import Succinct.LinearAlgebra
import Succinct.Codes.Core
import Succinct.Codes.Distance
import Succinct.Codes.Hamming
import Succinct.Codes.ReedSolomon
import Succinct.Codes.Lagrange
import Succinct.Checks.Zero
import Succinct.Prob.Implication
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Notation
import Mathlib.Data.Fintype.Card
import Succinct.Codes.Aristotle.PolynomialZeroViaEvaluation
import Succinct.Checks.Aristotle.PolynomialZeroCheckGated

/-! ### Polynomial Zero Check (§3.1.4)

Specialized zero check for testing whether a polynomial is zero using
Reed-Solomon codes. The key insight is:

    A polynomial p of degree < n is zero iff p evaluates to zero at n points.

For RS codes with m evaluation points (where m ≥ n), we can test polynomial
zero-ness by sampling a random evaluation point and checking if p evaluates to zero.

Paper reference: Lemma "Polynomial Zero Check" (§3.1.4)

Key theorem: For RS code with m points where m = |F|:
    (Gx)_r = 0 ⇒_{1-1/|F|} x = 0

This is better than the generic (n-1)/|F| bound because it works for any n.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial

namespace SuccinctProofs

section PolynomialZeroCheck

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **Helper 1**: Polynomial zero test via evaluation.

    A degree < n polynomial p is zero iff p(α) = 0 for n distinct points α.

    This is a fundamental fact: a nonzero polynomial of degree d has at most d roots.
    So if degree < n and p has n roots, p must be zero.

    This lemma connects polynomial zero-ness to RS code zero-ness. -/
theorem polynomial_zero_via_evaluation {C : RSCode F} (hle : C.n ≤ C.m)
    (p : Polynomial F) (hDeg : p.natDegree < C.n) :
    (∀ i : Fin C.m, p.eval (C.α i) = 0) ↔ p = 0 := by
  constructor
  · -- If p evaluates to zero at all m points (where m ≥ n),
    -- then in particular it evaluates to zero at n points
    -- Since degree < n, p must be zero
    intro h_all_zero
    -- Construct a function from Fin C.n to F for evaluation points
    let α' : Fin C.n → F := fun i => C.α (Fin.castLE hle i)
    have h_zero_at_n : ∀ i : Fin C.n, p.eval (α' i) = 0 := by
      intro i
      exact h_all_zero (Fin.castLE hle i)
    -- The α' are pairwise distinct (inherited from C.distinct)
    have h_distinct' : Pairwise (fun i j => α' i ≠ α' j) := by
      intro i j hij
      simp only [ne_eq, α']
      have h : (Fin.castLE hle i : Fin C.m) ≠ Fin.castLE hle j := by
        simp only [ne_eq, Fin.ext_iff, Fin.coe_castLE]
        exact Fin.val_ne_of_ne hij
      exact C.distinct (Fin.castLE hle i) (Fin.castLE hle j) h
    -- Use polynomial_zero_via_evaluations from Aristotle (Batch 11, ab486136)
    exact polynomial_zero_via_evaluations h_distinct' p hDeg h_zero_at_n
  · -- If p = 0, then p evaluates to zero everywhere
    intro hp i
    simp [hp]

/-- **Helper 2**: Convert polynomial evaluation to RS encoding.

    For a polynomial p of degree < n, let x be its coefficient vector.
    Then the RS encoding Gx is exactly [p(α₁), ..., p(αₘ)].

    This bridges between polynomial evaluation and RS code words. -/
lemma polynomial_eval_eq_rs_encode {C : RSCode F} (hle : C.n ≤ C.m)
    (p : Polynomial F) (hDeg : p.natDegree < C.n) (hn : 0 < C.n)
    (coeffs : Vec F C.n) (hcoeffs : coeffs = polyOfVecCoeffs p hDeg) :
    ∀ j : Fin C.m, (evalCode (α := C.α) (n := C.n) ⇀ₑ coeffs) j = p.eval (C.α j) := by
  intro j
  rw [hcoeffs]
  -- The core idea: evalCode encodes by evaluating polyOfVec coeffs at C.α j
  -- And polyOfVec (polyOfVecCoeffs p hDeg) = p by polyOfVec_coeff_right_inverse
  simp only [evalCode_encode_eq_eval]
  have h_eq : polyOfVec (polyOfVecCoeffs p hDeg) = p := polyOfVec_coeff_right_inverse p hDeg
  -- Need: evalPolyOfVec (polyOfVecCoeffs p hDeg) (C.α j) = p.eval (C.α j)
  -- By polyOfVec_eval: (polyOfVec x).eval β = evalPolyOfVec x β
  -- So evalPolyOfVec x β = (polyOfVec x).eval β
  rw [← polyOfVec_eval]
  rw [h_eq]

/-- Helper: Cardinality of preimage is bounded by number of roots.

    Since C.α is injective (evaluation points are distinct), the number of ω
    with p.eval (C.α ω) = 0 is at most the number of roots of p. -/
private lemma card_preimage_eval_zero' {C : RSCode F} (p : Polynomial F) (hp : p ≠ 0)
    (_hDeg : p.natDegree < C.n) :
    (Finset.filter (fun ω : Fin C.m => p.eval (C.α ω) = 0) Finset.univ).card ≤ p.natDegree := by
  have h_inj : Function.Injective C.α := by
    intro a b hab; by_contra hne; exact C.distinct a b hne hab
  have h_maps : ∀ ω ∈ (Finset.filter (fun ω : Fin C.m => p.eval (C.α ω) = 0) Finset.univ),
      C.α ω ∈ (Finset.filter (fun x : F => p.eval x = 0) Finset.univ) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact hω
  have h_inj_on : ∀ a ∈ (Finset.filter (fun ω : Fin C.m => p.eval (C.α ω) = 0) Finset.univ),
      ∀ b ∈ (Finset.filter (fun ω : Fin C.m => p.eval (C.α ω) = 0) Finset.univ),
      C.α a = C.α b → a = b := fun a _ b _ hab => h_inj hab
  calc (Finset.filter (fun ω : Fin C.m => p.eval (C.α ω) = 0) Finset.univ).card
      ≤ (Finset.filter (fun x : F => p.eval x = 0) Finset.univ).card :=
          Finset.card_le_card_of_injOn C.α h_maps h_inj_on
    _ = Fintype.card { x : F | p.eval x = 0 } := by rw [← Fintype.card_subtype]; rfl
    _ ≤ p.natDegree := poly_roots_fintype_card_bound p hp

/-- Helper: Bound uniform measure on evaluation zero set.

    The uniform probability of hitting a root via C.α is at most (n-1)/m. -/
private lemma uniformOn_eval_zero_bound {C : RSCode F} (p : Polynomial F) (hp : p ≠ 0)
    (hDeg : p.natDegree < C.n) :
    (uniformOn (Set.univ : Set (Fin C.m))) { ω | p.eval (C.α ω) = 0 } ≤ (C.n - 1) / C.m := by
  simp_all +decide [ uniformOn, ProbabilityTheory.cond_apply ]
  rw [ ENNReal.div_eq_inv_mul ]
  gcongr
  have h_card_bound : (Finset.filter (fun ω : Fin C.m => p.eval (C.α ω) = 0) Finset.univ).card ≤ p.natDegree :=
    card_preimage_eval_zero' p hp hDeg
  have h_deg_bound : p.natDegree ≤ C.n - 1 := by omega
  rw [ MeasureTheory.Measure.count_apply ]
  · have h_encard : ({ ω : Fin C.m | p.eval (C.α ω) = 0 } : Set (Fin C.m)).encard =
        (Finset.filter (fun ω : Fin C.m => p.eval (C.α ω) = 0) Finset.univ).card := by
      rw [Set.encard_eq_coe_toFinset_card]
      congr 1
      simp only [Set.toFinset_setOf]
    rw [h_encard]
    norm_cast
    calc (Finset.filter (fun ω : Fin C.m => p.eval (C.α ω) = 0) Finset.univ).card
        ≤ p.natDegree := h_card_bound
      _ ≤ C.n - 1 := h_deg_bound
  · exact MeasurableSpace.measurableSet_top

/-- **Main Theorem**: Polynomial Zero Check for RS codes (§3.1.4)

    Statement: Let C be an RS code with m = |F| evaluation points.
    Let p be a polynomial of degree < n.
    Sample a random evaluation point r ∈ {1,…,m} uniformly.
    Check if p(αᵣ) = 0.

    Then: The failure probability (p ≠ 0 but eval = 0) is ≤ (n-1)/|F|.

    The proof uses the Aristotle-proved `poly_roots_fintype_card_bound`:
    a nonzero polynomial of degree d has at most d roots.

    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem polynomial_zero_check {C : RSCode F}
    (_hle : C.n ≤ C.m)
    (hF : C.m = Fintype.card F)  -- m = |F|
    (_h_dist : distance (evalCode (α := C.α) (n := C.n)) ≥ C.m - C.n + 1)
    (_hn : 0 < C.n)
    {p : Polynomial F} (hDeg : p.natDegree < C.n) :
    Succinct.Prob.ProbImpEv (uniformOn (Set.univ : Set (Fin C.m)))
      { ω | p.eval (C.α ω) = 0 }
      { ω | p = 0 }
      ((C.n - 1) / Fintype.card F) := by
  unfold Succinct.Prob.ProbImpEv
  by_cases hp : p = 0
  · -- If p = 0, the consequent is always true, so A ∩ Bᶜ = ∅
    simp only [hp, Set.setOf_true, Set.compl_univ, Set.inter_empty, measure_empty]
    exact bot_le
  · -- If p ≠ 0, we use the roots bound
    have hBc : { ω : Fin C.m | p = 0 }ᶜ = Set.univ := by
      ext ω; simp [hp]
    rw [hBc, Set.inter_univ]
    -- Use our helper lemma and substitute hF
    calc (uniformOn (Set.univ : Set (Fin C.m))) { ω | p.eval (C.α ω) = 0 }
        ≤ (C.n - 1) / C.m := uniformOn_eval_zero_bound p hp hDeg
      _ = (C.n - 1) / Fintype.card F := by rw [hF]

/-- **Alternative formulation**: Using all m evaluation points.

    Instead of sampling one point, we could check all m points.
    This gives deterministic correctness (probability 1).

    This is often used as a subroutine in larger protocols. -/
theorem polynomial_zero_check_deterministic {C : RSCode F}
    (hle : C.n ≤ C.m)
    {p : Polynomial F} (hDeg : p.natDegree < C.n) :
    (∀ i : Fin C.m, p.eval (C.α i) = 0) ↔ p = 0 :=
  polynomial_zero_via_evaluation hle p hDeg

end PolynomialZeroCheck

end SuccinctProofs
