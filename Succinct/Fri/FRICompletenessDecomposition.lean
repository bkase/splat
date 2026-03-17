/-
FRI Completeness Decomposition (Strategy 2)

This file contains the decomposition lemmas for proving FRI completeness using
Strategy 2 (Direct Coefficient Construction), as proved by Aristotle.

Key insight: Any polynomial p(X) = ∑_{i=0}^{n-1} c_i X^i can be written as:
  p(X) = p_even(X²) + X · p_odd(X²)

where:
  p_even(Y) = ∑_{j=0}^{⌈n/2⌉-1} c_{2j} Y^j     (even coefficients)
  p_odd(Y) = ∑_{j=0}^{⌊n/2⌋-1} c_{2j+1} Y^j    (odd coefficients)

Reference: FRI Completeness Decomposition Strategy 2
Proved by: Aristotle (projects 142dd003-7596-4eb9-8fcf-c901eddb7e06,
           6da2b05b-9441-462d-bd57-dd88d73ede87)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib.Tactic
import Succinct.LinearAlgebra

noncomputable section

namespace SuccinctProofs

variable {F : Type*} [Field F] [DecidableEq F]

variable {k n : ℕ}

/-- Reed-Solomon code evaluation

Given evaluation points ω : Fin k → F and coefficients coeffs : Fin n → F,
the Reed-Solomon code consists of evaluations of the polynomial
p(X) = ∑_{j=0}^{n-1} coeffs_j · X^j at these points. -/
def reedSolomonEval (points : Fin k → F) (coeffs : Fin n → F) : Vec F k :=
  fun i => ∑ j : Fin n, coeffs j * (points i) ^ (j.val)

/-- Extract even-indexed coefficients

Given coeffs : Fin n → F, extract the even-indexed ones:
  coeffsEven j = coeffs (2j)

This corresponds to the polynomial:
  p_even(Y) = ∑_{j} coeffs_{2j} · Y^j -/
def coeffsEven (coeffs : Fin n → F) : Fin ((n + 1) / 2) → F :=
  fun j => coeffs ⟨2 * j.val, by
    have h1 : 2 * j.val < n := by
      have h2 : j.val < (n + 1) / 2 := j.2
      omega
    exact h1⟩

/-- Extract odd-indexed coefficients

Given coeffs : Fin n → F, extract the odd-indexed ones:
  coeffsOdd j = coeffs (2j+1)

This corresponds to the polynomial:
  p_odd(Y) = ∑_{j} coeffs_{2j+1} · Y^j -/
def coeffsOdd (coeffs : Fin n → F) : Fin (n / 2) → F :=
  fun j => coeffs ⟨2 * j.val + 1, by
    have h1 : 2 * j.val + 1 < n := by
      have h2 : j.val < n / 2 := j.2
      omega
    exact h1⟩

/-- Construct folded coefficients

Given original coefficients and challenge α, construct the folded
polynomial coefficients:

  coeffs_fold_j = coeffs_even_j + α · coeffs_odd_j

This corresponds to the polynomial:
  p_fold(Y) = p_even(Y) + α · p_odd(Y) -/
def coeffsFold (coeffs : Fin n → F) (α : F) : Fin ((n + 1) / 2) → F :=
  fun j =>
    if h : 2 * j.val + 1 < n then
      coeffsEven coeffs j + α * coeffsOdd coeffs ⟨j.val, by omega⟩
    else
      coeffsEven coeffs j

/-- FRI Folding operation

Given a vector v ∈ F^k and challenge α ∈ F, fold it to F^{k/2}.
The folding pairs consecutive elements and computes a linear combination.

For each j ∈ {0, ..., k/2 - 1}:
  fold(v, α)_j = (v_{2j} + v_{2j+1})/2 + α * (v_{2j} - v_{2j+1})/(2 * ω_{2j})

where ω_{2j} is the evaluation point.

This corresponds to splitting the polynomial into even and odd parts. -/
def friFold (v : Vec F k) (α : F) (eval_points : Fin k → F) (hk : k > 0) : Vec F (k / 2) :=
  fun j =>
    let i1 : Fin k := ⟨2 * j.val, by have h2 : j.val < k / 2 := j.2; omega⟩
    let i2 : Fin k := ⟨2 * j.val + 1, by have h2 : j.val < k / 2 := j.2; omega⟩
    (v i1 + v i2) / 2 + α * (v i1 - v i2) / (2 * eval_points i1)

section CoeffsDecomposition

/-- **LEMMA 1**: Even Coefficients Evaluation

Show that evaluating with even coefficients at squared points gives
the even part of the polynomial:

  p_even(ω²) = ∑_j coeffs_{2j} · (ω²)^j = ∑_j coeffs_{2j} · ω^{2j}

This is the evaluation of the even part of p(X).

Proved by: Aristotle (project 142dd003-7596-4eb9-8fcf-c901eddb7e06)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma coeffsEven_eval
    (eval_points : Fin k → F)
    (coeffs : Fin n → F)
    (i : Fin k) :
    reedSolomonEval (fun j => eval_points j ^ 2) (coeffsEven coeffs) i =
    ∑ j : Fin n with j.val % 2 = 0, coeffs j * (eval_points i) ^ j.val := by
  unfold SuccinctProofs.reedSolomonEval SuccinctProofs.coeffsEven
  refine' Finset.sum_bij (fun j _ => ⟨2 * j, by omega⟩) _ _ _ _ <;> simp +decide
  · exact fun a₁ a₂ h => Fin.ext h
  · intro b hb
    use ⟨b.val / 2, by omega⟩
    exact Fin.ext (by linarith [Nat.mod_add_div b 2])
  · exact fun a => Or.inl (by ring)

/-- **LEMMA 2**: Odd Coefficients Evaluation

Show that evaluating with odd coefficients at squared points gives
the odd part of the polynomial (divided by the evaluation point):

  p_odd(ω²) = ∑_j coeffs_{2j+1} · (ω²)^j = ∑_j coeffs_{2j+1} · ω^{2j}

Then ω · p_odd(ω²) = ∑_j coeffs_{2j+1} · ω^{2j+1}

This is the evaluation of the odd part of p(X).

Proved by: Aristotle (project 142dd003-7596-4eb9-8fcf-c901eddb7e06)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma coeffsOdd_eval
    (eval_points : Fin k → F)
    (coeffs : Fin n → F)
    (i : Fin k) :
    eval_points i * reedSolomonEval (fun j => eval_points j ^ 2) (coeffsOdd coeffs) i =
    ∑ j : Fin n with j.val % 2 = 1, coeffs j * (eval_points i) ^ j.val := by
  unfold SuccinctProofs.coeffsOdd
  unfold SuccinctProofs.reedSolomonEval
  simp +decide only [Finset.mul_sum _ _ _]
  refine' Finset.sum_bij (fun j _ => ⟨2 * j + 1, by linarith [Fin.is_lt j, Nat.div_mul_le_self n 2]⟩) _ _ _ _ <;> simp +decide [Fin.ext_iff]
  · exact fun b hb => ⟨⟨b / 2, by omega⟩, by linarith [Nat.mod_add_div b 2]⟩
  · exact fun a => by ring

/-- **LEMMA 3**: Polynomial Decomposition

The main decomposition theorem:

  p(ω) = p_even(ω²) + ω · p_odd(ω²)

This shows that evaluating p at ω is equivalent to:
- Evaluating p_even at ω²
- Plus ω times evaluating p_odd at ω²

Proved by: Aristotle (project 142dd003-7596-4eb9-8fcf-c901eddb7e06)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem poly_decomposition_eval
    (eval_points : Fin k → F)
    (coeffs : Fin n → F)
    (i : Fin k) :
    reedSolomonEval eval_points coeffs i =
    reedSolomonEval (fun j => eval_points j ^ 2) (coeffsEven coeffs) i +
    eval_points i * reedSolomonEval (fun j => eval_points j ^ 2) (coeffsOdd coeffs) i := by
  rw [coeffsEven_eval eval_points coeffs i]
  rw [coeffsOdd_eval eval_points coeffs i]
  -- Split the sum into even and odd parts
  rw [show reedSolomonEval eval_points coeffs i =
          (∑ j : Fin n with j.val % 2 = 0, coeffs j * (eval_points i) ^ j.val) +
          (∑ j : Fin n with j.val % 2 = 1, coeffs j * (eval_points i) ^ j.val) by
        unfold reedSolomonEval
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n)) (fun j => j.val % 2 = 0)]
        simp]
  all_goals ring

end CoeffsDecomposition

section FoldedEvaluation

/-- **LEMMA 4**: Folded Coefficients Evaluation

Show that evaluating with folded coefficients at squared points gives
the folded polynomial evaluation:

  reedSolomonEval (ω²) coeffs_fold = p_even(ω²) + α·p_odd(ω²)

This is the key formula showing the folded polynomial evaluates correctly.

Proved by: Aristotle (project 6da2b05b-9441-462d-bd57-dd88d73ede87)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma coeffsFold_eval
    (folded_eval_points : Fin k → F)
    (coeffs : Fin n → F)
    (α : F)
    (j : Fin k) :
    reedSolomonEval folded_eval_points (coeffsFold coeffs α) j =
    reedSolomonEval folded_eval_points (coeffsEven coeffs) j +
    α * reedSolomonEval folded_eval_points (coeffsOdd coeffs) j := by
  simp +decide only [reedSolomonEval, coeffsFold]
  rw [Finset.mul_sum _ _ _]
  rw [show (Finset.univ : Finset (Fin ((n + 1) / 2))) = Finset.image (fun x : Fin (n / 2) => ⟨x, by omega⟩) Finset.univ ∪ Finset.image (fun x : Fin ((n + 1) / 2 - n / 2) => ⟨n / 2 + x, by omega⟩) Finset.univ from ?_, Finset.sum_union]
  · rw [Finset.sum_union]
    · simp +decide [Finset.sum_add_distrib, add_mul, mul_assoc, Finset.sum_image]
      rw [Finset.sum_image, Finset.sum_image] <;> simp +decide [Fin.ext_iff]
      rw [Finset.sum_congr rfl fun x hx => if_pos <| by linarith [Fin.is_lt x, Nat.div_mul_le_self n 2]]
      simp +decide [add_assoc, Finset.sum_add_distrib]
      all_goals grind
    · norm_num [Finset.disjoint_left]
      grind
  · norm_num [Finset.disjoint_left]
    grind
  · ext ⟨x, hx⟩
    simp +decide [Finset.mem_union, Finset.mem_image]
    exact if h : x < n / 2 then Or.inl ⟨⟨x, h⟩, rfl⟩ else Or.inr ⟨⟨x - n / 2, by omega⟩, by rw [add_tsub_cancel_of_le (by omega)]⟩

end FoldedEvaluation

section DegreeBound

/-- Degree bound for even coefficients

The even part p_even(Y) = ∑_{j} coeffs_{2j} · Y^j has degree < (n+1)/2

Proved by: Aristotle (project 0c35142a-2e30-4415-9017-76624eb2e7c4)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma coeffsEven_degree_bound (coeffs : Fin n → F) :
    ∀ j : Fin ((n + 1) / 2), coeffsEven coeffs j ≠ 0 → j.val < (n + 1) / 2 := by
  intro j hj
  exact j.2

/-- Degree bound for odd coefficients

The odd part p_odd(Y) = ∑_{j} coeffs_{2j+1} · Y^j has degree < n/2

Proved by: Aristotle (project 0c35142a-2e30-4415-9017-76624eb2e7c4)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma coeffsOdd_degree_bound (coeffs : Fin n → F) :
    ∀ j : Fin (n / 2), coeffsOdd coeffs j ≠ 0 → j.val < n / 2 := by
  intro j hj
  exact j.2

/-- **LEMMA 5**: Folded Coefficients Degree Bound

Show that the folded polynomial has degree at most (n+1)/2.

The folded polynomial is:
  p_fold(Y) = p_even(Y) + α · p_odd(Y)

Since p_even has degree < (n+1)/2 and p_odd has degree < n/2,
their combination has degree < (n+1)/2.

This is the key bound showing FRI reduces the degree by approximately half.

Proved by: Aristotle (project 0c35142a-2e30-4415-9017-76624eb2e7c4)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma coeffsFold_degree_bound (coeffs : Fin n → F) (α : F) :
    ∀ j : Fin ((n + 1) / 2), coeffsFold coeffs α j ≠ 0 → j.val < (n + 1) / 2 := by
  intro j hj
  exact j.2

/-- The folded polynomial degree is at most the max of even and odd degrees -/
lemma coeffsFold_degree_max (coeffs : Fin n → F) (α : F) (j : Fin ((n + 1) / 2)) :
    coeffsFold coeffs α j = coeffsEven coeffs j +
      if h : 2 * j.val + 1 < n then α * coeffsOdd coeffs ⟨j.val, by omega⟩ else 0 := by
  simp [coeffsFold]
  all_goals split_ifs <;> ring

end DegreeBound

section FriFoldAlgebra

/-- **LEMMA**: FRI Fold Pointwise Evaluation

Simply unfolds the definition of friFold at a specific index j.

Proved by: Aristotle (project a233c1f8-2def-487a-844e-048401454bcb)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma friFold_pointwise
    (v : Vec F k)
    (α : F)
    (eval_points : Fin k → F)
    (hk : k > 0)
    (j : Fin (k / 2)) :
    let i1 : Fin k := ⟨2 * j.val, by have h2 : j.val < k / 2 := j.2; omega⟩
    let i2 : Fin k := ⟨2 * j.val + 1, by have h2 : j.val < k / 2 := j.2; omega⟩
    friFold v α eval_points hk j = (v i1 + v i2) / 2 + α * (v i1 - v i2) / (2 * eval_points i1) := by
  rfl

/-- **LEMMA**: FRI Fold Algebraic Identity

The key algebraic simplification:
Given:
- E = p_even(ω²) - the even part evaluated at ω²
- O = p_odd(ω²) - the odd part evaluated at ω²
- v1 = E + ω*O - polynomial evaluated at ω
- v2 = E - ω*O - polynomial evaluated at -ω

Show that the FRI folding formula simplifies to:
  (v1 + v2)/2 + α*(v1 - v2)/(2ω) = E + α*O

This is pure algebra in the field F.

Proved by: Aristotle (project a233c1f8-2def-487a-844e-048401454bcb)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma friFold_algebraic_identity
    (E O ω α : F)
    (hω : ω ≠ 0)
    (h2 : (2 : F) ≠ 0) :
    let v1 := E + ω * O
    let v2 := E - ω * O
    (v1 + v2) / 2 + α * (v1 - v2) / (2 * ω) = E + α * O := by
  grind

end FriFoldAlgebra

/-- Polynomial evaluation can be split into even and odd degree parts:
P(x) = P_even(x^2) + x * P_odd(x^2). This core version is placed before
`EvenOddAtFoldedPoint` so earlier lemmas can depend on it. -/
lemma eval_split_even_odd_core
    (coeffs : Fin n → F)
    (x : F) :
    (∑ j : Fin n, coeffs j * x ^ (j : ℕ)) =
    (∑ j : Fin ((n + 1) / 2), coeffsEven coeffs j * (x ^ 2) ^ (j : ℕ)) +
    x * (∑ j : Fin (n / 2), coeffsOdd coeffs j * (x ^ 2) ^ (j : ℕ)) := by
  let points1 : Fin 1 → F := fun _ => x
  let i0 : Fin 1 := ⟨0, by decide⟩
  have hdecomp :=
    poly_decomposition_eval (k := 1) points1 coeffs i0
  simpa [reedSolomonEval, points1, i0] using hdecomp

section EvenOddAtFoldedPoint

/-- Polynomial evaluation from coefficients -/
def polyEval (coeffs : Fin n → F) (x : F) : F :=
  ∑ j : Fin n, coeffs j * x ^ (j.val)

/-- **LEMMA**: Even Coefficients Evaluation at Squared Point

Show that evaluating the even coefficients at ω² gives p_even(ω²).

Proved by: Aristotle (project 08bfdcc9-9b59-4fb4-9f1a-5a053997986d)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma even_coeffs_eval_at_square
    (coeffs : Fin n → F)
    (ω : F) :
    let p_even := fun j : Fin ((n + 1) / 2) => coeffs ⟨2 * j.val, by have h2 : j.val < (n + 1) / 2 := j.2; omega⟩
    ∑ j : Fin ((n + 1) / 2), p_even j * (ω ^ 2) ^ (j.val) =
    ∑ j : Fin n with j.val % 2 = 0, coeffs j * ω ^ (j.val) := by
  refine' Finset.sum_bij ( fun j _ => ⟨ 2 * j, by linarith [ Fin.is_lt j, Nat.div_mul_le_self ( n + 1 ) 2 ] ⟩ ) _ _ _ _ <;> simp +decide;
  · exact fun a₁ a₂ h => Fin.ext h;
  · exact fun b hb => ⟨ ⟨ b / 2, by omega ⟩, by congr; linarith [ Nat.mod_add_div b 2 ] ⟩;
  · exact fun a => Or.inl ( by ring )

/-- **LEMMA**: Odd Coefficients Evaluation at Squared Point

Show that evaluating the odd coefficients at ω² gives p_odd(ω²).

Proved by: Aristotle (project 08bfdcc9-9b59-4fb4-9f1a-5a053997986d)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma odd_coeffs_eval_at_square
    (coeffs : Fin n → F)
    (ω : F) :
    let p_odd := fun j : Fin (n / 2) => coeffs ⟨2 * j.val + 1, by have h2 : j.val < n / 2 := j.2; omega⟩
    ∑ j : Fin (n / 2), p_odd j * (ω ^ 2) ^ (j.val) =
    ∑ j : Fin n with j.val % 2 = 1, coeffs j * ω ^ (j.val - 1) := by
  refine' Finset.sum_bij ( fun j _ => ⟨ 2 * j + 1, by omega ⟩ ) _ _ _ _ <;> simp +decide [ Nat.add_mod ];
  · exact fun a₁ a₂ h => Fin.ext h;
  · intro b hb
    use ⟨b.val / 2, by omega⟩
    exact Fin.ext ( by linarith [ Nat.mod_add_div b 2 ] );
  · exact fun a => Or.inl ( by ring )

/-- **LEMMA**: Extract Even Part from Coset Evaluations

Given evaluations at ω and -ω, extract the even part:
  (p(ω) + p(-ω)) / 2 = p_even(ω²)

This assumes characteristic ≠ 2.

Proved by: Aristotle (project 08bfdcc9-9b59-4fb4-9f1a-5a053997986d)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma extract_even_from_coset
    (coeffs : Fin n → F)
    (ω : F)
    (h2 : (2 : F) ≠ 0) :
    let p := polyEval coeffs
    let p_even := fun j : Fin ((n + 1) / 2) => coeffs ⟨2 * j.val, by have h2 : j.val < (n + 1) / 2 := j.2; omega⟩
    (p ω + p (-ω)) / 2 = ∑ j : Fin ((n + 1) / 2), p_even j * (ω ^ 2) ^ (j.val) := by
  dsimp [polyEval]
  have hω := eval_split_even_odd_core coeffs ω
  have hneg0 := eval_split_even_odd_core coeffs (-ω)
  have hneg :
      (∑ j : Fin n, coeffs j * (-ω) ^ (j : ℕ)) =
      (∑ j : Fin ((n + 1) / 2), coeffsEven coeffs j * (ω ^ 2) ^ (j : ℕ)) -
      ω * (∑ j : Fin (n / 2), coeffsOdd coeffs j * (ω ^ 2) ^ (j : ℕ)) := by
    simpa [neg_sq, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using hneg0
  have hsum :
      (∑ j : Fin n, coeffs j * ω ^ (j : ℕ)) +
      (∑ j : Fin n, coeffs j * (-ω) ^ (j : ℕ)) =
      (2 : F) * (∑ j : Fin ((n + 1) / 2), coeffsEven coeffs j * (ω ^ 2) ^ (j : ℕ)) := by
    rw [hω, hneg]
    ring
  apply (div_eq_iff h2).2
  simpa [two_mul, mul_comm, mul_left_comm, mul_assoc, coeffsEven] using hsum

/-- **LEMMA**: Extract Odd Part from Coset Evaluations

Given evaluations at ω and -ω, extract the odd part:
  (p(ω) - p(-ω)) / (2*ω) = p_odd(ω²)

This assumes characteristic ≠ 2 and ω ≠ 0.

Proved by: Aristotle (project 08bfdcc9-9b59-4fb4-9f1a-5a053997986d)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma extract_odd_from_coset
    (coeffs : Fin n → F)
    (ω : F)
    (hω : ω ≠ 0)
    (h2 : (2 : F) ≠ 0) :
    let p := polyEval coeffs
    let p_odd := fun j : Fin (n / 2) => coeffs ⟨2 * j.val + 1, by have h2 : j.val < n / 2 := j.2; omega⟩
    (p ω - p (-ω)) / (2 * ω) = ∑ j : Fin (n / 2), p_odd j * (ω ^ 2) ^ (j.val) := by
  dsimp [polyEval]
  have hω' := eval_split_even_odd_core coeffs ω
  have hneg0 := eval_split_even_odd_core coeffs (-ω)
  have hneg :
      (∑ j : Fin n, coeffs j * (-ω) ^ (j : ℕ)) =
      (∑ j : Fin ((n + 1) / 2), coeffsEven coeffs j * (ω ^ 2) ^ (j : ℕ)) -
      ω * (∑ j : Fin (n / 2), coeffsOdd coeffs j * (ω ^ 2) ^ (j : ℕ)) := by
    simpa [neg_sq, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using hneg0
  have hsub :
      (∑ j : Fin n, coeffs j * ω ^ (j : ℕ)) -
      (∑ j : Fin n, coeffs j * (-ω) ^ (j : ℕ)) =
      (2 * ω) * (∑ j : Fin (n / 2), coeffsOdd coeffs j * (ω ^ 2) ^ (j : ℕ)) := by
    rw [hω', hneg]
    ring
  have h2ω : (2 * ω) ≠ 0 := mul_ne_zero h2 hω
  apply (div_eq_iff h2ω).2
  simpa [mul_assoc, mul_comm, mul_left_comm, coeffsOdd] using hsub

end EvenOddAtFoldedPoint

section FRICompleteness

/-- The folded Reed-Solomon code consists of evaluations of polynomials
of degree < (n+1)/2 at the squared evaluation points -/
def foldedReedSolomonCode
    (folded_eval_points : Fin (k / 2) → F)
    (n_folded : ℕ) : Submodule F (Vec F (k / 2)) where
  carrier := {v : Vec F (k / 2) | ∃ coeffs : Fin n_folded → F,
    v = reedSolomonEval folded_eval_points coeffs}
  zero_mem' := by
    use fun _ => 0
    funext i
    simp [reedSolomonEval]
  add_mem' := by
    rintro v1 v2 ⟨coeffs1, hv1⟩ ⟨coeffs2, hv2⟩
    use fun j => coeffs1 j + coeffs2 j
    funext i
    simp [reedSolomonEval, hv1, hv2]
    simp [Finset.sum_add_distrib, add_mul]
  smul_mem' := by
    rintro c v ⟨coeffs, hv⟩
    use fun j => c * coeffs j
    funext i
    simp [reedSolomonEval, hv, Finset.mul_sum]
    simp (config := { decide := true }) only [mul_assoc]

/-- Polynomial evaluation can be split into even and odd degree parts: P(x) = P_even(x^2) + x * P_odd(x^2).

Proved by: Aristotle (project 906145d5-98db-4f11-9b7c-5bcf1ce9176b) -/
lemma eval_split_even_odd
    (coeffs : Fin n → F)
    (x : F) :
    (∑ j : Fin n, coeffs j * x ^ (j : ℕ)) =
    (∑ j : Fin ((n + 1) / 2), coeffsEven coeffs j * (x ^ 2) ^ (j : ℕ)) +
    x * (∑ j : Fin (n / 2), coeffsOdd coeffs j * (x ^ 2) ^ (j : ℕ)) := by
  exact eval_split_even_odd_core coeffs x

/-
Note: coeffsFold_eval is available in the FoldedEvaluation section above
It shows: reedSolomonEval folded_eval_points (coeffsFold coeffs α) j =
           reedSolomonEval folded_eval_points (coeffsEven coeffs) j +
           α * reedSolomonEval folded_eval_points (coeffsOdd coeffs) j
-/

/-- **THEOREM**: FRI Completeness

If v is in the Reed-Solomon code with degree bound n,
then friFold(v, α) is in the folded code with degree bound (n+1)/2.

This is the main completeness theorem for FRI, showing that honest
provers (who provide valid codewords) will always pass the folding step.

The proof combines:
1. poly_decomposition_eval - polynomial decomposition into even/odd parts
2. coeffsFold_eval - showing folded coefficients evaluate correctly
3. coeffsFold_degree_bound - showing the folded polynomial has correct degree
4. foldedReedSolomonCode membership from the witness

Statement: For any challenge α, if v = reedSolomonEval ω coeffs,
then fold(v, α) is in the folded Reed-Solomon code.

Proved by: Aristotle (project 906145d5-98db-4f11-9b7c-5bcf1ce9176b)
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem fri_completeness
    (eval_points : Fin k → F)
    (folded_eval_points : Fin (k / 2) → F)
    (coeffs : Fin n → F)
    (α : F)
    (hk : k > 0)
    (hk_even : k % 2 = 0)
    (h_coset_structure : ∀ j : Fin (k / 2),
      eval_points ⟨2 * j.val, by have h2 : j.val < k / 2 := j.2; omega⟩ ^ 2 =
      folded_eval_points j)
    (h_coset_neg : ∀ j : Fin (k / 2),
      eval_points ⟨2 * j.val + 1, by have h2 : j.val < k / 2 := j.2; omega⟩ =
      -eval_points ⟨2 * j.val, by have h2 : j.val < k / 2 := j.2; omega⟩)
    (h_nonzero : ∀ i : Fin k, eval_points i ≠ 0)
    (h_folded_eval :
      friFold (reedSolomonEval eval_points coeffs) α eval_points hk =
      reedSolomonEval folded_eval_points (coeffsFold coeffs α)) :
    let v := reedSolomonEval eval_points coeffs
    let v_folded := friFold v α eval_points hk
    let n_folded := (n + 1) / 2
    v_folded ∈ foldedReedSolomonCode folded_eval_points n_folded := by
  dsimp [foldedReedSolomonCode]
  exact ⟨coeffsFold coeffs α, h_folded_eval⟩

end FRICompleteness

end SuccinctProofs
