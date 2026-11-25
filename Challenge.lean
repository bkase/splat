module

public import Mathlib.Tactic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Probability.UniformOn

set_option warningAsError false
-- The deliberate `sorry`s below are the holes this repository's `Solution.lean`
-- discharges; they are expected by the Palomar Comparator layout.

public section

/-!
# Advertised statement

This module states eleven results from Evans and Angeris,
*Succinct Proofs and Linear Algebra* (eprint 2023/1478).

The FRI statements cover proximity preservation, the bad-challenge bound,
Reed-Solomon completeness, and soundness against a fixed witness under one
challenge or independent repetitions. The remaining statements cover unique
decoding, code-distance bounds, and randomized polynomial and matrix checks.
The repetition theorem concerns the same fold and witness throughout. The
complete recursive FRI protocol is outside these statements.

The declarations use Mathlib notions and the support definitions below.
Probability bounds measure acceptance together with a false conclusion,
following the paper's probabilistic implication calculus.
-/

namespace SPLAT

open scoped ENNReal

/-- The Hamming weight of a vector: the number of nonzero coordinates. -/
@[expose]
def weightVec {F : Type*} [Field F] [DecidableEq F] {k : ℕ} (x : Fin k → F) : ℕ :=
  Fintype.card { i : Fin k | x i ≠ 0 }

/-- The FRI fold of a vector `v` with challenge `α` and evaluation points
`eval_points`: coordinate `j` of the fold combines the pair
`(v_{2j}, v_{2j+1})` as

`(v_{2j} + v_{2j+1}) / 2 + α * (v_{2j} - v_{2j+1}) / (2 * eval_points_{2j})`,

the decomposition of the underlying polynomial into its even and odd
parts, as in §4 of the paper. -/
@[expose]
def friFold {F : Type*} [Field F] {k : ℕ} (v : Fin k → F) (α : F)
    (eval_points : Fin k → F) (hk : k > 0) : Fin (k / 2) → F :=
  fun j =>
    let i1 : Fin k := ⟨2 * j.val, Nat.lt_of_lt_of_le
      ((Nat.mul_lt_mul_left (a := 2) Nat.zero_lt_two).mpr j.isLt) (Nat.mul_div_le k 2)⟩
    let i2 : Fin k := ⟨2 * j.val + 1, Nat.lt_of_lt_of_le
      (Nat.succ_lt_succ (Nat.lt_succ_self (2 * j.val)))
      (Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt j.isLt))
        (Nat.mul_div_le k 2))⟩
    (v i1 + v i2) / 2 + α * (v i1 - v i2) / (2 * eval_points i1)

/-- **FRI one-step proximity reduction** (§4.2 of the paper).

Let `V ⊆ F^k` be a linear subspace all of whose nonzero elements have
Hamming weight at least `d`, and let `v` be `q`-close to `V`. For any
challenge `α`, the FRI fold of `v` is `q`-close to the set of folds of
elements of `V`: folding cannot increase the distance of `v` to the
code. -/
theorem fri_folding_preserves_proximity {F : Type*} [Field F] [DecidableEq F] {k : ℕ}
    (eval_points : Fin k → F)
    (h_distinct : ∀ i j : Fin k, i ≠ j → eval_points i ≠ eval_points j)
    (V : Submodule F (Fin k → F))
    (d : ℕ)
    (h_dist : ∀ v ∈ V, v ≠ 0 → weightVec v ≥ d)
    (v : Fin k → F)
    (q : ℕ)
    (h_close : ∃ w ∈ V, weightVec (v - w) ≤ q)
    (α : F)
    (hk : k > 0)
    (hk_even : k % 2 = 0) :
    ∃ w_next ∈ {w : Fin (k / 2) → F | ∃ v ∈ V, w = friFold v α eval_points hk},
      weightVec (friFold v α eval_points hk - w_next) ≤ q := by
  sorry

/-- **Bad-challenge bound** for the FRI fold (§4.2 of the paper).

For distinct vectors `v ≠ w` over an even-length domain with nonzero
evaluation points and `2 ≠ 0`, the set of challenges `α` for which the
folds of `v` and `w` agree has cardinality at most `k / 2`. -/
theorem bad_alpha_set_bound {F : Type*} [Field F] [DecidableEq F] [Fintype F] {k : ℕ}
    (v w : Fin k → F) (eval_points : Fin k → F)
    (hk : k > 0) (hk_even : k % 2 = 0)
    (hω : ∀ i : Fin k, eval_points i ≠ 0)
    (h2 : (2 : F) ≠ 0)
    (hvw : v ≠ w) :
    Fintype.card {α : F | friFold v α eval_points hk = friFold w α eval_points hk}
      ≤ k / 2 := by
  sorry

noncomputable section

/-- Evaluate a polynomial given by its first `n` coefficients. -/
@[expose]
def reedSolomonEval {F : Type*} [Field F] {k n : ℕ}
    (points : Fin k → F) (coeffs : Fin n → F) : Fin k → F :=
  fun i => ∑ j : Fin n, coeffs j * points i ^ j.val

/-- Minimum weight of an encoding of a nonzero message. -/
@[expose]
def codeDistance {F : Type*} [Field F] [DecidableEq F] {m n : ℕ}
    (G : Matrix (Fin m) (Fin n) F) : WithTop ℕ :=
  sInf {w : WithTop ℕ | ∃ x : Fin n → F, x ≠ 0 ∧ w = weightVec (G.mulVec x)}

/-- The Kronecker matrix, with pairs of indices flattened in row-major order. -/
@[expose]
def kroneckerMatrix {F : Type*} [Field F] {m n m' n' : ℕ}
    (G' : Matrix (Fin m') (Fin n') F) (G : Matrix (Fin m) (Fin n) F) :
    Matrix (Fin (m' * m)) (Fin (n' * n)) F :=
  fun p q =>
    G' ⟨p.val / m, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq p.isLt (Nat.mul_comm m' m))⟩
      ⟨q.val / n, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq q.isLt (Nat.mul_comm n' n))⟩ *
    G ⟨p.val % m, Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Nat.lt_of_le_of_lt (Nat.zero_le _) p.isLt))⟩
      ⟨q.val % n, Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Nat.lt_of_le_of_lt (Nat.zero_le _) q.isLt))⟩

/-- Minimum weight of a nonzero vector in a subspace. -/
@[expose]
def subspaceDistance {F : Type*} [Field F] [DecidableEq F] {k : ℕ}
    (V : Submodule F (Fin k → F)) : WithTop ℕ :=
  sInf {w : WithTop ℕ | ∃ x : Fin k → F, x ∈ V ∧ x ≠ 0 ∧ w = weightVec x}

/-- Number of rows containing a nonzero entry. -/
@[expose]
def nonZeroRows {F : Type*} [Field F] [DecidableEq F] {k n : ℕ}
    (X : Matrix (Fin k) (Fin n) F) : ℕ :=
  Fintype.card {i : Fin k | X.row i ≠ 0}

/-- A Reed-Solomon codeword folds to an evaluation with half as many coefficients. -/
theorem fri_completeness {F : Type*} [Field F] [DecidableEq F] {k n : ℕ}
    (eval_points : Fin k → F) (folded_eval_points : Fin (k / 2) → F)
    (coeffs : Fin n → F) (α : F) (hk : k > 0) (hk_even : k % 2 = 0)
    (h_coset_structure : ∀ j : Fin (k / 2),
      eval_points ⟨2 * j.val, Nat.lt_of_lt_of_le
        ((Nat.mul_lt_mul_left (a := 2) Nat.zero_lt_two).mpr j.isLt) (Nat.mul_div_le k 2)⟩ ^ 2 = folded_eval_points j)
    (h_coset_neg : ∀ j : Fin (k / 2),
      eval_points ⟨2 * j.val + 1, Nat.lt_of_lt_of_le
        (Nat.succ_lt_succ (Nat.lt_succ_self (2 * j.val)))
        (Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt j.isLt))
          (Nat.mul_div_le k 2))⟩ =
        -eval_points ⟨2 * j.val, Nat.lt_of_lt_of_le
        ((Nat.mul_lt_mul_left (a := 2) Nat.zero_lt_two).mpr j.isLt) (Nat.mul_div_le k 2)⟩)
    (h_nonzero : ∀ i : Fin k, eval_points i ≠ 0) (h2 : (2 : F) ≠ 0) :
    ∃ folded_coeffs : Fin ((n + 1) / 2) → F,
      friFold (reedSolomonEval eval_points coeffs) α eval_points hk =
        reedSolomonEval folded_eval_points folded_coeffs := by
  sorry

/-- A single fold check against a fixed witness has error at most `(k/2)/|F|`. -/
theorem fri_single_round_soundness {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    [MeasurableSpace F] [MeasurableSingletonClass F] {k : ℕ}
    (V : Submodule F (Fin k → F)) (v w : Fin k → F) (hwV : w ∈ V) (q : ℕ)
    (eval_points : Fin k → F) (hk : k > 0) (hk_even : k % 2 = 0)
    (hω : ∀ i : Fin k, eval_points i ≠ 0) (h2 : (2 : F) ≠ 0) :
    ProbabilityTheory.uniformOn (Set.univ : Set F)
      ({α : F | friFold v α eval_points hk = friFold w α eval_points hk} ∩
        {α : F | ∃ u ∈ V, weightVec (v - u) ≤ q}ᶜ) ≤
      (↑(k / 2) : ℝ≥0∞) / Fintype.card F := by
  sorry

/-- Independent repetitions of the same fixed-witness fold check multiply its error.
This is a repetition bound for one fold, without recursive protocol commitments. -/
theorem fri_multi_round_soundness {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    [MeasurableSpace F] [MeasurableSingletonClass F] {k : ℕ}
    (l : ℕ) (V : Submodule F (Fin k → F)) (v w : Fin k → F) (hwV : w ∈ V) (q : ℕ)
    (eval_points : Fin k → F) (hk : k > 0) (hk_even : k % 2 = 0)
    (hω : ∀ i : Fin k, eval_points i ≠ 0) (h2 : (2 : F) ≠ 0) :
    ProbabilityTheory.uniformOn (Set.univ : Set (Fin l → F))
      ({ρ : Fin l → F | ∀ i : Fin l,
          friFold v (ρ i) eval_points hk = friFold w (ρ i) eval_points hk} ∩
        {ρ : Fin l → F | ∃ u ∈ V, weightVec (v - u) ≤ q}ᶜ) ≤
      (↑(k / 2) : ℝ≥0∞) ^ l / (Fintype.card F ^ l) := by
  sorry

/-- Below half the subspace distance, the nearby matrix is unique. -/
theorem unique_decoding_radius {F : Type*} [Field F] [DecidableEq F] {k n : ℕ}
    (V : Submodule F (Fin k → F)) (X : Matrix (Fin k) (Fin n) F) (q : ℕ)
    (h_close : ∃ Y : Matrix (Fin k) (Fin n) F,
      (∀ j : Fin n, (fun i => Y i j) ∈ V) ∧ nonZeroRows (X - Y) ≤ q)
    (h_dist : subspaceDistance V > (2 * q : ℕ)) (hd' : subspaceDistance V ≠ ⊤) :
    ∃! Y : Matrix (Fin k) (Fin n) F,
      ∃ Ξ : Matrix (Fin k) (Fin n) F,
        X = Y + Ξ ∧ (∀ j : Fin n, (fun i => Y i j) ∈ V) ∧ nonZeroRows Ξ ≤ q := by
  sorry

/-- The Singleton bound for a generator matrix with a nonempty message space. -/
theorem singleton_bound {F : Type*} [Field F] [DecidableEq F] [Fintype F] {m n : ℕ}
    (G : Matrix (Fin m) (Fin n) F) (hn : 0 < n) :
    codeDistance G ≤ (m - n + 1 : ℕ) := by
  sorry

/-- The Kronecker product has distance at least the product of the component bounds. -/
theorem kronecker_product_distance {F : Type*} [Field F] [DecidableEq F]
    {m n m' n' d d' : ℕ}
    (G : Matrix (Fin m) (Fin n) F) (G' : Matrix (Fin m') (Fin n') F)
    (h_dist : codeDistance G ≥ d) (h_dist' : codeDistance G' ≥ d') :
    codeDistance (kroneckerMatrix G' G) ≥ d' * d := by
  sorry

/-- Every nonzero Hadamard message has the same encoding weight. -/
theorem hadamard_distance_formula {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (hn : n > 0) (x : Fin n → F) (hx : x ≠ 0) :
    Fintype.card {r : Fin n → F | (∑ i : Fin n, r i * x i) ≠ 0} =
      Fintype.card F ^ n - Fintype.card F ^ (n - 1) := by
  sorry

/-- A random polynomial evaluation has error at most `(n-1)/|F|`. -/
theorem polynomial_zero_check {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {m n : ℕ} (eval_points : Fin m → F)
    (h_distinct : ∀ i j, i ≠ j → eval_points i ≠ eval_points j)
    (hle : n ≤ m) (hF : m = Fintype.card F)
    (h_dist : codeDistance (fun (i : Fin m) (j : Fin n) => eval_points i ^ j.val) ≥
      (m : WithTop ℕ) - n + 1) (hn : 0 < n)
    {p : Polynomial F} (hDeg : p.natDegree < n) :
    ProbabilityTheory.uniformOn (Set.univ : Set (Fin m))
      ({ω : Fin m | p.eval (eval_points ω) = 0} ∩ {ω : Fin m | p = 0}ᶜ) ≤
      ((n : ℝ≥0∞) - 1) / Fintype.card F := by
  sorry

/-- Independent matrix zero checks have error at most `(1-d/m)^t`. -/
theorem reduced_matrix_zero_check {F : Type*} [Field F] [DecidableEq F]
    {d m n k t : ℕ} (G : Matrix (Fin m) (Fin n) F)
    (h_dist : codeDistance G ≥ d) (hd_pos : 0 < d) (hle : d ≤ m) (ht_pos : 0 < t)
    (X : Matrix (Fin k) (Fin n) F) :
    ProbabilityTheory.uniformOn (Set.univ : Set (Fin t → Fin m))
      ({ω : Fin t → Fin m | ∀ i : Fin t, ∀ j : Fin k,
          ∑ i' : Fin n, G (ω i) i' * X j i' = 0} ∩
        {ω : Fin t → Fin m | X = 0}ᶜ) ≤
      (1 - (d : ℝ≥0∞) / m) ^ t := by
  sorry

end

end SPLAT
