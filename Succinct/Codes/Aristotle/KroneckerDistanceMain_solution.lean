/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bd6fe8fc-a7e6-4520-910a-c228f9c0c22a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem kronecker_product_distance {k m n m' : ℕ}
    (G : LinearCode F) (G' : LinearCode F)
    (hGm : G.m = m) (hGn : G.n = n)
    (hGm' : G'.m = m') (hGn' : G'.n = k)
    {d : ℕ} {d' : ℕ}
    (h_dist : distance G ≥ d)
    (h_dist' : distance G' ≥ d') :
    distance (kroneckerCode G' G) ≥ d' * d

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
Target: kronecker_product_distance in Succinct/Codes/KroneckerDistance.lean:158

This proves the main theorem: distance(G' ⊗ G) ≥ d' * d

Key insight: The theorem follows from showing that for any nonzero message z,
the encoded weight is at least d' * d. We decompose z into "slices" and use
the distance properties of the component codes.
-/

import Mathlib.Tactic



noncomputable section

open scoped BigOperators

namespace KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

/-- Type alias for vectors -/
abbrev Vec (F : Type*) (n : ℕ) := Fin n → F

/-- Type alias for matrices -/
abbrev Mat (F : Type*) (m n : ℕ) := Fin m → Fin n → F

/-- Linear code structure -/
structure LinearCode (F : Type*) [Field F] where
  (m n : ℕ)
  (G : Mat F m n)

/-- Encode a message -/
def encode (C : LinearCode F) (x : Vec F C.n) : Vec F C.m :=
  Matrix.mulVec C.G x

infixl:70 " ⇀ₑ " => encode

/-- Hamming weight -/
def weightVec {n : ℕ} (x : Vec F n) : ℕ :=
  Fintype.card { i : Fin n | x i ≠ 0 }

notation "∥" x "∥₀" => weightVec x

/-- Code distance as infimum -/
def distance (C : LinearCode F) : WithTop ℕ :=
  sInf { w : WithTop ℕ | ∃ x : Vec F C.n, x ≠ 0 ∧ w = ∥C ⇀ₑ x∥₀ }

/-- Kronecker product code -/
def kroneckerCode (G' G : LinearCode F) : LinearCode F where
  m := G'.m * G.m
  n := G'.n * G.n
  G := fun (p : Fin (G'.m * G.m)) (q : Fin (G'.n * G.n)) =>
    let i := p.val / G.m
    let j := p.val % G.m
    let a := q.val / G.n
    let b := q.val % G.n
    have hi : i < G'.m := Nat.div_lt_of_lt_mul (by nlinarith [Fin.is_lt p])
    have hj : j < G.m := by
      have hp := Fin.is_lt p
      have : G'.m * G.m > 0 := by nlinarith
      have : G.m > 0 := Nat.pos_of_mul_pos_left this
      exact Nat.mod_lt p.val this
    have ha : a < G'.n := Nat.div_lt_of_lt_mul (by nlinarith [Fin.is_lt q])
    have hb : b < G.n := by
      have hq := Fin.is_lt q
      have : G'.n * G.n > 0 := by nlinarith
      have : G.n > 0 := Nat.pos_of_mul_pos_left this
      exact Nat.mod_lt q.val this
    G'.G ⟨i, hi⟩ ⟨a, ha⟩ * G.G ⟨j, hj⟩ ⟨b, hb⟩

/- Main Theorem: Kronecker Product Distance

    If G has distance ≥ d and G' has distance ≥ d',
    then G' ⊗ G has distance ≥ d' * d.

    Proof idea: For any nonzero z in the message space, view z as a matrix Z.
    Find a nonzero row Z_a. Use G's distance on Z_a to get d positions.
    For each position, use G''s distance to get d' positions.
    Total support ≥ d' * d. -/
noncomputable section AristotleLemmas

/-
Converts a vector of length m*n to an m x n matrix.
-/
open KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

def vecToMat {m n : ℕ} (v : Vec F (m * n)) : Mat F m n :=
  fun i j => v ⟨i.val * n + j.val, by
    nlinarith [ Fin.is_lt i, Fin.is_lt j ]⟩

/-
Definitions for the Hamming weight of a matrix (number of non-zero entries) and the number of non-zero columns.
-/
open KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

def weightMat {m n : ℕ} (M : Mat F m n) : ℕ :=
  Fintype.card { p : Fin m × Fin n | M p.1 p.2 ≠ 0 }

def nonZeroCols {m n : ℕ} (M : Mat F m n) : ℕ :=
  Fintype.card { j : Fin n | ∃ i, M i j ≠ 0 }

/-
The Hamming weight of a vector is equal to the Hamming weight of its matrix representation.
-/
open KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

lemma weight_eq_weight_mat {m n : ℕ} (v : Vec F (m * n)) :
    weightVec v = weightMat (vecToMat (m := m) (n := n) v) := by
  unfold KroneckerGated.weightMat;
  simp +decide only [weightVec, Fintype.card_ofFinset];
  refine' Finset.card_bij ( fun p hp => ⟨ ⟨ p / n, Nat.div_lt_of_lt_mul <| by linarith [ Fin.is_lt p ] ⟩, ⟨ p % n, Nat.mod_lt _ <| Nat.pos_of_ne_zero <| by aesop_cat ⟩ ⟩ ) _ _ _ <;> simp +decide [ Nat.div_add_mod' ];
  · intro a ha; convert ha; simp +decide [ KroneckerGated.vecToMat, Nat.div_add_mod' ] ;
  · exact fun a₁ ha₁ a₂ ha₂ h₁ h₂ => Fin.ext <| by nlinarith [ Nat.mod_add_div a₁ n, Nat.mod_add_div a₂ n ] ;
  · intro a b hb
    use ⟨a.val * n + b.val, by
      nlinarith [ Fin.is_lt a, Fin.is_lt b ]⟩
    generalize_proofs at *;
    simp_all +decide [ Fin.ext_iff, Nat.add_div ];
    exact ⟨ Nat.le_antisymm ( Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by linarith [ Fin.is_lt b ] ) ( Nat.le_div_iff_mul_le ( Nat.pos_of_ne_zero <| by aesop ) |>.2 <| by linarith [ Fin.is_lt b ] ), hb, Nat.mod_eq_of_lt <| Fin.is_lt b ⟩

/-
Matrix multiplication and transposition definitions.
-/
open KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

def matMul {m n p : ℕ} (A : Mat F m n) (B : Mat F n p) : Mat F m p :=
  fun i k => ∑ j, A i j * B j k

def matTranspose {m n : ℕ} (A : Mat F m n) : Mat F n m :=
  fun i j => A j i

/-
The encoding of a message using the Kronecker product code corresponds to the matrix operation G' X G^T, where X is the matrix representation of the message.
-/
open KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

lemma kronecker_encode_eq {m n m' n' : ℕ} (G : Mat F m n) (G' : Mat F m' n')
    (x : Vec F (n' * n)) :
    vecToMat (m := m') (n := m) (Matrix.mulVec (kroneckerCode (LinearCode.mk m' n' G') (LinearCode.mk m n G)).G x)
    = matMul (matMul G' (vecToMat (m := n') (n := n) x)) (matTranspose G) := by
  ext ⟨ i, hi ⟩ ⟨ j, hj ⟩ ; simp +decide [ KroneckerGated.kroneckerCode, Matrix.mulVec ]
  unfold KroneckerGated.vecToMat KroneckerGated.matMul KroneckerGated.matTranspose Matrix.mulVec
  generalize_proofs at *;
  simp +decide [ dotProduct, Finset.sum_mul _ _ _ ];
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine Finset.sum_eq_zero fun q _ => absurd q.isLt (by omega)
  · rw [ ← Finset.sum_product' ];
    refine' Finset.sum_bij ( fun q _ => ( ⟨ q.val % n, Nat.mod_lt _ hn ⟩, ⟨ q.val / n,
      Nat.div_lt_of_lt_mul <| by linarith [ Fin.is_lt q ] ⟩ ) ) _ _ _ _ <;> simp +decide [ Nat.div_add_mod' ]
    all_goals generalize_proofs at *;
    · intro a₁ _ a₂ _ hmod hdiv
      exact Fin.ext <| by nlinarith [ Nat.mod_add_div a₁ n, Nat.mod_add_div a₂ n ]
    · intro a b; use ⟨ b.val * n + a.val, by
        nlinarith [ Fin.is_lt a, Fin.is_lt b ] ⟩ ; simp +decide [ Nat.mod_eq_of_lt, Nat.div_eq_of_lt, * ]
      generalize_proofs at *;
      have hval : (↑b * n + ↑a) / n = ↑b := by
        rw [Nat.mul_comm ↑b n, Nat.mul_add_div hn, Nat.div_eq_of_lt (Fin.is_lt a)]
        simp
      exact ⟨Finset.mem_univ _, Fin.ext hval⟩
    · simp +decide [ Nat.add_div, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hi, mul_assoc, mul_comm, mul_left_comm ];
      simp +decide [ add_comm, Nat.add_mul_div_left _ _ ( Nat.pos_of_ne_zero ( by omega : m ≠ 0 ) ), mul_comm ];
      simp +decide [ Nat.div_eq_of_lt hj, mul_comm ];
      intro a _
      left
      ring

/-
If a matrix X is non-zero, then X * G^T has at least d non-zero columns, where d is the distance of G.
-/
open KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

lemma cols_nonzero_ge_dist {k : ℕ} (G : LinearCode F) (d : ℕ)
    (h_dist : distance G ≥ d) (X : Mat F k G.n) (hX : X ≠ 0) :
    nonZeroCols (matMul X (matTranspose G.G)) ≥ d := by
  -- Since X is non-zero, there exists a row i such that X_i is non-zero.
  obtain ⟨i, hi⟩ : ∃ i : Fin k, X i ≠ 0 := by
    contrapose! hX; aesop;
  -- Since $X_i$ is non-zero, the encoding $G(X_i)$ has weight at least $d$.
  have h_weight : weightVec (Matrix.mulVec G.G (X i)) ≥ d := by
    contrapose! h_dist;
    refine' lt_of_le_of_lt ( csInf_le _ _ ) _;
    exact ↑ ( KroneckerGated.weightVec ( Matrix.mulVec G.G ( X i ) ) );
    · exact ⟨ 0, fun w hw => hw.choose_spec.2.symm ▸ Nat.cast_nonneg _ ⟩;
    · exact ⟨ X i, hi, rfl ⟩;
    · exact WithTop.coe_lt_coe.mpr h_dist;
  refine' le_trans h_weight ( Fintype.card_le_of_injective _ _ );
  refine' fun x => ⟨ x.val, _ ⟩;
  all_goals simp +decide [ Function.Injective ];
  exact ⟨ i, by simpa [ Matrix.mulVec, dotProduct, mul_comm, KroneckerGated.matMul, KroneckerGated.matTranspose ] using x.2 ⟩

/-
The weight of the matrix product G'Z is at least d' times the number of non-zero columns of Z, given that G' has distance at least d'.
-/
open KroneckerGated

variable {F : Type*} [Field F] [DecidableEq F]

lemma weight_ge_dist_mul_cols {m n : ℕ} (G' : LinearCode F) (d' : ℕ)
    (h_dist' : distance G' ≥ d') (Z : Mat F G'.n n) :
    weightMat (matMul G'.G Z) ≥ d' * nonZeroCols Z := by
  -- For each non-zero column $z_j$ of $Z$, the weight of $G' * z_j$ is at least $d'$.
  have h_col_weight : ∀ j : Fin n, (∃ i : Fin G'.n, Z i j ≠ 0) → weightVec (fun i => ∑ k, G'.G i k * Z k j) ≥ d' := by
    intro j hj
    unfold distance at h_dist';
    refine' Nat.cast_le.mp ( le_trans h_dist' _ );
    refine' csInf_le _ ⟨ fun i => Z i j, _, rfl ⟩ <;> simp_all +decide [ funext_iff, Matrix.mulVec ];
  -- Summing the weights of the columns of $G' * Z$ gives us the total weight.
  have h_sum_weight : weightMat (KroneckerGated.matMul G'.G Z) = ∑ j : Fin n, weightVec (fun i => ∑ k, G'.G i k * Z k j) := by
    -- Matrix weight = sum of column weights (counting by fibers)
    -- The total number of nonzero entries in G'.G * Z equals the sum over columns j
    -- of the number of nonzero entries in column j.
    simp only [weightMat, weightVec, matMul]
    -- This is a standard counting argument: count pairs (i,j) by fiber over j
    have : Fintype.card { p : Fin G'.m × Fin n | ∑ j, G'.G p.1 j * Z j p.2 ≠ 0 } =
           ∑ j : Fin n, Fintype.card { i : Fin G'.m | ∑ k, G'.G i k * Z k j ≠ 0 } := by
      rw [← Fintype.card_sigma]
      refine Fintype.card_congr ⟨fun ⟨⟨i, j⟩, h⟩ => ⟨j, ⟨i, h⟩⟩, fun ⟨j, ⟨i, h⟩⟩ => ⟨⟨i, j⟩, h⟩, ?_, ?_⟩
      · intro ⟨⟨i, j⟩, h⟩; rfl
      · intro ⟨j, ⟨i, h⟩⟩; rfl
    exact this
  have h_sum_weight_ge : ∑ j : Fin n, weightVec (fun i => ∑ k, G'.G i k * Z k j) ≥ ∑ j : Fin n, if (∃ i : Fin G'.n, Z i j ≠ 0) then d' else 0 := by
    exact Finset.sum_le_sum fun j _ => by split_ifs <;> [ exact h_col_weight j ‹_›; exact Nat.zero_le _ ] ;
  convert h_sum_weight_ge using 1 ; simp +decide [ KroneckerGated.nonZeroCols, mul_comm ] ; ring;
  simp +decide [ Finset.sum_ite, Fintype.card_subtype ] ; ring;

end AristotleLemmas

theorem kronecker_product_distance {k m n m' : ℕ}
    (G : LinearCode F) (G' : LinearCode F)
    (hGm : G.m = m) (hGn : G.n = n)
    (hGm' : G'.m = m') (hGn' : G'.n = k)
    {d : ℕ} {d' : ℕ}
    (h_dist : distance G ≥ d)
    (h_dist' : distance G' ≥ d') :
    distance (kroneckerCode G' G) ≥ d' * d := by
  simp_all +decide [ KroneckerGated.distance ];
  intro b x hx hb
  have h_weight : weightVec (encode (kroneckerCode G' G) x) ≥ d' * d := by
    -- Let $X = \text{vecToMat } x$. Since $x \neq 0$, $X \neq 0$.
    set X : Mat F G'.n G.n := vecToMat (m := G'.n) (n := G.n) x
    have hX_nonzero : X ≠ 0 := by
      intro hX0
      apply hx
      funext q
      rcases Nat.eq_zero_or_pos G.n with h0 | hn
      · rw [show (KroneckerGated.kroneckerCode G' G).n = G'.n * G.n from rfl] at q
        rw [h0] at q
        exact absurd q.isLt (by omega)
      · have hi : (q : ℕ) / G.n < G'.n :=
          Nat.div_lt_of_lt_mul <|
            by linarith [Fin.is_lt q,
              show (KroneckerGated.kroneckerCode G' G).n = G'.n * G.n from rfl]
        have hj : (q : ℕ) % G.n < G.n := Nat.mod_lt _ hn
        have hval : X ⟨(q : ℕ) / G.n, hi⟩ ⟨(q : ℕ) % G.n, hj⟩ = x q := by
          have hdm : G.n * ((q : ℕ) / G.n) + (q : ℕ) % G.n = (q : ℕ) :=
            Nat.div_add_mod _ _
          have hcomm : (q : ℕ) / G.n * G.n = G.n * ((q : ℕ) / G.n) :=
            Nat.mul_comm _ _
          have heq : (q : ℕ) / G.n * G.n + (q : ℕ) % G.n = (q : ℕ) := by
            rw [hcomm]
            exact hdm
          have hlt : (q : ℕ) / G.n * G.n + (q : ℕ) % G.n
              < (KroneckerGated.kroneckerCode G' G).n := by
            rw [heq]
            exact q.isLt
          have h1 : X ⟨(q : ℕ) / G.n, hi⟩ ⟨(q : ℕ) % G.n, hj⟩
              = x ⟨(q : ℕ) / G.n * G.n + (q : ℕ) % G.n, hlt⟩ := rfl
          have h2 : (⟨(q : ℕ) / G.n * G.n + (q : ℕ) % G.n, hlt⟩ :
              Fin (KroneckerGated.kroneckerCode G' G).n) = q :=
            Fin.ext heq
          rw [h1, h2]
        show x q = 0
        rw [← hval, hX0]
        simp
    have hX_weight : weightVec (encode (kroneckerCode G' G) x) = weightMat (matMul G'.G (matMul X (matTranspose G.G))) := by
      have h1 := weight_eq_weight_mat (m := G'.m) (n := G.m) (encode (kroneckerCode G' G) x)
      have henc : vecToMat (m := G'.m) (n := G.m) (encode (kroneckerCode G' G) x)
          = matMul (matMul G'.G X) (matTranspose G.G) :=
        kronecker_encode_eq G.G G'.G x
      rw [henc] at h1
      have hassoc : matMul (matMul G'.G X) (matTranspose G.G)
          = matMul G'.G (matMul X (matTranspose G.G)) := by
        ext i j
        simp only [KroneckerGated.matMul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => by ring)
      rw [hassoc] at h1
      exact h1
    have hX_weight_ge : weightMat (matMul G'.G (matMul X (matTranspose G.G))) ≥ d' * nonZeroCols (matMul X (matTranspose G.G)) := by
      apply weight_ge_dist_mul_cols G' d' (by
      simp +decide [ KroneckerGated.distance ] at * ; aesop;) (matMul X (matTranspose G.G));
      exact 0
    have hX_nonzero_cols : nonZeroCols (matMul X (matTranspose G.G)) ≥ d := by
      apply cols_nonzero_ge_dist G d (by
        have hS : {w : WithTop ℕ | ∃ x : KroneckerGated.Vec F G.n, x ≠ 0 ∧
            w = ↑∥G ⇀ₑ x∥₀}.Nonempty := by
          by_cases h : ∃ x : KroneckerGated.Vec F G.n, x ≠ 0
          · exact ⟨_, h.choose, h.choose_spec, rfl⟩
          · exfalso
            apply hX_nonzero
            funext i j
            have hrow : ∀ i : Fin G'.n,
                (fun j => X i j : KroneckerGated.Vec F G.n) = 0 := by
              intro i
              by_contra hne
              exact h ⟨_, hne⟩
            simpa using congrFun (hrow i) j
        refine le_csInf hS ?_
        rintro w ⟨x, hx, rfl⟩
        exact WithTop.coe_le_coe.mpr (h_dist _ x hx rfl)) X hX_nonzero
    have hX_weight_final : weightVec (encode (kroneckerCode G' G) x) ≥ d' * d := by
      exact hX_weight.symm ▸ hX_weight_ge.trans' ( Nat.mul_le_mul_left _ hX_nonzero_cols )
    exact hX_weight_final
  exact_mod_cast h_weight.trans' (Nat.mul_le_mul (Nat.cast_le.mpr le_rfl) le_rfl)

end KroneckerGated

end
