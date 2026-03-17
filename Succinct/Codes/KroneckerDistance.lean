import Succinct.LinearAlgebra
import Succinct.Codes.Core
import Succinct.Codes.Distance
import Succinct.Codes.Hamming
import Succinct.Codes.Aristotle.KroneckerDistanceMain_solution
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.GeneralizeProofs

/-! ### Kronecker Product Distance (§3.1)

Kronecker product codes: distance of G' ⊗ G is at least d' · d.

Paper reference: Lemma "Kronecker Product Distance" (§3.1)
-/

noncomputable section
open scoped BigOperators

namespace SuccinctProofs

section KroneckerDistance

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Helper 0**: Support cardinality of product function

For functions f : A → F and g : B → F, the support (nonzero entries) of
the product function (a,b) ↦ f(a) * g(b) has cardinality equal to the
product of individual supports.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/
lemma support_product_card {A B : Type*} [Fintype A] [Fintype B]
    (f : A → F) (g : B → F) :
    Fintype.card {p : A × B | f p.1 * g p.2 ≠ 0} =
    Fintype.card {a : A | f a ≠ 0} * Fintype.card {b : B | g b ≠ 0} := by
  rw [← Fintype.card_prod]
  refine' Fintype.card_congr _
  exact ⟨fun p => ⟨⟨p.val.1, by aesop⟩, ⟨p.val.2, by aesop⟩⟩, fun p => ⟨⟨p.1.val, p.2.val⟩, by aesop⟩, fun p => rfl, fun p => rfl⟩

/-- **Helper 1**: Kronecker product of two vectors.

    For vectors x ∈ 𝔽^k and y ∈ 𝔽^n, their Kronecker product x ⊗ y
    is a vector in 𝔽^{k·n} defined by (x ⊗ y)_{(i,j)} = x_i · y_j.
    We represent this as Fin k → Fin n → F. -/
def kronecker_vec {k n : ℕ} (x : Fin k → F) (y : Fin n → F) :
    Fin (k * n) → F :=
  fun p =>
    let p_nat : ℕ := p
    let i_val : ℕ := p_nat / n
    let j_val : ℕ := p_nat % n
    let i : Fin k := ⟨i_val, by
      -- Since `Fin.val p` is less than `k * n` and `n` is positive, dividing `Fin.val p` by `n` gives a quotient less than `k`.
      have h_div_lt_k : p_nat / n < k := by
        have h_p_nat_lt_kn : p_nat < k * n := by
          exact p.2
        nlinarith [Nat.div_mul_le_self p_nat n]
      exact h_div_lt_k⟩
    let j : Fin n := ⟨j_val, by
      all_goals generalize_proofs at *
      -- By definition of modulo, the remainder when p_nat is divided by n is always less than n.
      apply Nat.mod_lt _ (Nat.pos_of_ne_zero (by grind))⟩
    x i * y j

/-- **Helper 2**: Support of encoded Kronecker product.

    For codes G' (m' × k) and G (m × n), the Kronecker product code
    encodes z = x ⊗ y as (G' ⊗ G)z = (G'y) ⊗ (Gx).
    The support (nonzero entries) has size equal to product of individual supports. -/
lemma kronecker_support_card {k m n : ℕ} {m' : ℕ} (G : LinearCode F) (G' : LinearCode F)
    (hGm : G.m = m) (hGn : G.n = n) (hGm' : G'.m = m') (hGn' : G'.n = k)
    {x : Fin G'.n → F} {y : Fin G.n → F} :
    Fintype.card {p : Fin (G'.m * G.m) | (kronecker_vec (G' ⇀ₑ x) (G ⇀ₑ y)) p ≠ 0} =
      Fintype.card {p : Fin G'.m | (G' ⇀ₑ x) p ≠ 0} * Fintype.card {q : Fin G.m | (G ⇀ₑ y) q ≠ 0} := by
  rw [Fintype.card_of_subtype]
  case s =>
    exact Finset.image (fun p : Fin G'.m × Fin G.m => ⟨p.1.val * G.m + p.2.val, by nlinarith [Fin.is_lt p.1, Fin.is_lt p.2]⟩)
      (Finset.univ.filter fun p : Fin G'.m × Fin G.m => (G' ⇀ₑ x) p.1 ≠ 0 ∧ (G ⇀ₑ y) p.2 ≠ 0)
  · rw [Finset.card_image_of_injective]
    · rw [Fintype.card_subtype, Fintype.card_subtype]
      rw [← Finset.card_product]
      congr
      ext
      aesop
    · intro p q h
      have := congr_arg Fin.val h
      simp_all +decide [Fin.ext_iff]
      have h_eq : (p.1 : ℕ) = (q.1 : ℕ) := by
        nlinarith [Fin.is_lt p.1, Fin.is_lt p.2, Fin.is_lt q.1, Fin.is_lt q.2]
      aesop
  · simp +decide [Fin.ext_iff, Prod.ext_iff]
    intro p
    constructor <;> intro h
    · rcases h with ⟨a, b, ⟨ha, hb⟩, hp⟩
      simp +decide [← hp, ha, hb, SuccinctProofs.kronecker_vec]
      simp +decide [Nat.add_div, Nat.mod_eq_of_lt, Fin.is_lt, ha, hb]
      convert ha using 2
      congr
      rw [Nat.add_div] <;> norm_num [Nat.div_eq_of_lt, Fin.is_lt]
      · rw [Nat.mul_div_cancel _ (by linarith [Fin.is_lt b]), if_neg (Nat.not_le_of_gt (Nat.mod_lt _ (by linarith [Fin.is_lt b])))]
        simp +decide
      · grind
    · contrapose! h
      unfold SuccinctProofs.kronecker_vec
      simp +decide [h]
      exact Classical.or_iff_not_imp_left.2 fun hx => Classical.not_not.1 fun hy => h _ _ ⟨hx, hy⟩ (by simp +decide [Nat.div_add_mod'])

/-- **Helper 4**: Define Kronecker product of two linear codes.

    The Kronecker product code G' ⊗ G has:
    - Block length: m' · m
    - Message dimension: k · n
    - Generator matrix: G' ⊗ G (Kronecker product of matrices) -/
def kroneckerCode (G' G : LinearCode F) : LinearCode F where
  m := G'.m * G.m
  n := G'.n * G.n
  G := fun (p : Fin (G'.m * G.m)) (q : Fin (G'.n * G.n)) =>
    let p_nat : ℕ := p
    let q_nat : ℕ := q
    let i_val : ℕ := p_nat / G.m
    let j_val : ℕ := p_nat % G.m
    let a_val : ℕ := q_nat / G.n
    let b_val : ℕ := q_nat % G.n
    let i : Fin G'.m := ⟨i_val, by exact Nat.div_lt_of_lt_mul <| by linarith [Fin.is_lt p]⟩
    let j : Fin G.m := ⟨j_val, by all_goals generalize_proofs at *; apply Nat.mod_lt _ (Nat.pos_of_ne_zero (by grind))⟩
    let a : Fin G'.n := ⟨a_val, by exact Nat.div_lt_of_lt_mul <| by nlinarith [Fin.is_lt q]⟩
    let b : Fin G.n := ⟨b_val, by all_goals generalize_proofs at *; apply Nat.mod_lt q_nat (Nat.pos_of_ne_zero (by grind))⟩
    G'.G i a * G.G j b

/-- **Helper 5**: Cardinality of Cartesian product of finite sets.

    If |A| = a and |B| = b, then |A × B| = a · b.
    This gives the weight of the Kronecker-encoded tensor. -/
lemma card_product {A B : Type*} [Fintype A] [Fintype B]
    {a : ℕ} {b : ℕ}
    (hA : Fintype.card A = a) (hB : Fintype.card B = b) :
    Fintype.card (A × B) = a * b := by
  all_goals generalize_proofs at *
  simpa [hA, hB]

/-- **Main theorem**: Kronecker Product Distance (§3.1).

    If G has distance d and G' has distance d',
    then G' ⊗ G has distance at least d' · d.

    Proof: Any nonzero z = x ⊗ y factors with x ≠ 0, y ≠ 0.
    Support of (G' ⊗ G)z has size |support(G'y)| · |support(Gx)|.
    By distance property: |support(G'y)| ≥ d' and |support(Gx)| ≥ d.
    Therefore: |support((G' ⊗ G)z)| ≥ d' · d. -/
-- Conversion between SuccinctProofs.LinearCode and KroneckerGated.LinearCode
private def toGatedCode (C : LinearCode F) : KroneckerGated.LinearCode F :=
  { m := C.m, n := C.n, G := C.G }

private def fromGatedCode (C : KroneckerGated.LinearCode F) : LinearCode F :=
  { m := C.m, n := C.n, G := C.G }

private lemma distance_eq_gated (C : LinearCode F) :
    distance C = KroneckerGated.distance (toGatedCode C) := rfl

private lemma kroneckerCode_eq_gated (G' G : LinearCode F) :
    toGatedCode (kroneckerCode G' G) = KroneckerGated.kroneckerCode (toGatedCode G') (toGatedCode G) := rfl

theorem kronecker_product_distance {k m n m' : ℕ}
    (G : LinearCode F) (G' : LinearCode F)
    (hGm : G.m = m) (hGn : G.n = n)
    (hGm' : G'.m = m') (hGn' : G'.n = k)
    {d : ℕ} {d' : ℕ}
    (h_dist : distance G ≥ d)
    (h_dist' : distance G' ≥ d') :
    distance (kroneckerCode G' G) ≥ d' * d := by
  -- Convert to the gated formulation and apply the Aristotle proof
  rw [distance_eq_gated, kroneckerCode_eq_gated]
  have h_dist_gated : KroneckerGated.distance (toGatedCode G) ≥ d := by
    rw [← distance_eq_gated]; exact h_dist
  have h_dist'_gated : KroneckerGated.distance (toGatedCode G') ≥ d' := by
    rw [← distance_eq_gated]; exact h_dist'
  exact KroneckerGated.kronecker_product_distance (toGatedCode G) (toGatedCode G') rfl rfl rfl rfl h_dist_gated h_dist'_gated

end KroneckerDistance

end SuccinctProofs
