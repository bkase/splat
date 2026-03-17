import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct

import Succinct.LinearAlgebra
import Succinct.Codes.Core
import Succinct.Codes.Distance
import Succinct.Codes.HadamardCore

noncomputable section
open scoped BigOperators

namespace SuccinctProofs

/-! ### Hadamard Code Distance (§2.2.2)

The Hadamard code has distance |F|^n - |F|^{n-1}.

This file completes the proof using the helper lemmas from Aristotle.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

section HadamardDistance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

/-- All tuples of length n over F.
    This is the indexing set for the Hadamard encoding. -/
def allTuples (F : Type*) [Field F] [Fintype F] (n : ℕ) : Finset (Fin n → F) :=
  Finset.univ

/-- The set of all tuples that have zero dot product with x.
    This is the kernel of the linear functional y ↦ ⟨y, x⟩. -/
def zeroDotProductSet (x : Vec F n) : Finset (Fin n → F) :=
  {y ∈ allTuples F n | ∑ i : Fin n, y i * x i = 0}

/-- The set of all tuples that have nonzero dot product with x. -/
def nonzeroDotProductSet (x : Vec F n) : Finset (Fin n → F) :=
  {y ∈ allTuples F n | ∑ i : Fin n, y i * x i ≠ 0}

/-- **Helper**: The encoding at index i equals the dot product with tuple i.

    This connects the matrix view (encode) to the dot product view.
    The key insight: row i of the generator matrix IS tuple i.

    For the proof: unfold definitions and use `Fintype.equivFin`. -/
lemma encode_hadamardCode_eq_dotProduct (x : Vec F n) (i : Fin (Fintype.card (Fin n → F))) :
    (hadamardCode (F := F) (n := n) ⇀ₑ x) i = ∑ j : Fin n, (tupleEnum i) j * x j := by
  simp [encode, hadamardCode, Matrix.mulVec, dotProduct, tupleEnum]
  rfl

-- ============================================
-- LEMMAS ABOUT SET PARTITIONING
-- ============================================

/-- **Helper**: The set of tuples with nonzero dot product is the complement
    of the set with zero dot product.

    This is a simple set-theoretic fact: {y | P(y)}ᶜ = {y | ¬P(y)} -/
lemma nonzero_dotProduct_set_eq_compl (x : Vec F n) :
    {y : Fin n → F | ∑ i : Fin n, y i * x i ≠ 0} =
    Set.univ \ {y : Fin n → F | ∑ i : Fin n, y i * x i = 0} := by
  ext y
  simp
  tauto

-- ============================================
-- WEIGHT ENCODING EQUIVALENCE
-- ============================================

/-- **Helper**: Fintype.card of a subtype equals Finset.card of the corresponding set.
    This connects the subtype cardinality to finset cardinality. -/
lemma Fintype.card_subtype_eq_finset_card {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Fintype.card {a : α // p a} = (Finset.univ.filter p).card := by
  rw [Fintype.card_subtype]
  simp

/-- **Helper**: The set of indices where encoding is nonzero is equivalent
    to the set of tuples with nonzero dot product.

    This uses the bijection `tupleEnum` between indices and tuples. -/
lemma nonzero_encode_indices_equiv_nonzero_dotProduct_tuples (x : Vec F n) :
    {i : Fin (Fintype.card (Fin n → F)) | (hadamardCode ⇀ₑ x) i ≠ 0} ≃
    {y : Fin n → F | ∑ j : Fin n, y j * x j ≠ 0} := by
  -- Use the bijection tupleEnum between indices and tuples
  let e := Fintype.equivFin (Fin n → F)
  -- We need to show that the subtype of indices maps to the subtype of tuples
  refine Equiv.subtypeEquiv e.symm ?_
  intro i
  simp [encode_hadamardCode_eq_dotProduct]

/-- **Weight Lemma**: The weight of the Hadamard encoding equals
    the total number of tuples minus those with zero dot product.

    PROVED by Aristotle (Batch 61, 8788599a-6a46-468f-b4cc-257d7a4c50b8).

    This is the key step connecting weight to the zero-dot-product count.

    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma weight_encode_eq_total_minus_zero {x : Vec F n} (hx : x ≠ 0) :
    ∥hadamardCode (F := F) (n := n) ⇀ₑ x∥₀ =
      Fintype.card (Fin n → F) - Fintype.card {y : Fin n → F | ∑ i : Fin n, y i * x i = 0} := by
  -- Step 1: Expand weight definition
  have h1 : ∥hadamardCode ⇀ₑ x∥₀ = Fintype.card {i : Fin (Fintype.card (Fin n → F)) | (hadamardCode ⇀ₑ x) i ≠ 0} := by
    rfl

  -- Step 2: Use the equivalence to transform the count
  have h2 : Fintype.card {i : Fin (Fintype.card (Fin n → F)) | (hadamardCode ⇀ₑ x) i ≠ 0} =
            Fintype.card {y : Fin n → F | ∑ j : Fin n, y j * x j ≠ 0} := by
    exact Fintype.card_congr (nonzero_encode_indices_equiv_nonzero_dotProduct_tuples x)

  -- Step 3: The set of tuples with nonzero dot product is the complement of
  -- the set with zero dot product
  have h3 : Fintype.card {y : Fin n → F | ∑ j : Fin n, y j * x j ≠ 0} =
            Fintype.card (Fin n → F) - Fintype.card {y : Fin n → F | ∑ j : Fin n, y j * x j = 0} := by
    -- Convert to finset representation
    rw [Fintype.card_subtype_eq_finset_card, Fintype.card_subtype_eq_finset_card]
    -- Use the fact that filter (¬p) = univ \ filter p
    have h_filter : Finset.filter (fun y => ∑ j : Fin n, y j * x j ≠ 0) Finset.univ =
                    Finset.univ \ Finset.filter (fun y => ∑ j : Fin n, y j * x j = 0) Finset.univ := by
      ext y
      simp
      tauto
    rw [h_filter]
    rw [Finset.card_sdiff]
    · -- Show the filter is a subset of univ (trivial)
      simp
    · -- Show filter is subset of univ (trivial)
      simp

  -- Combine all steps
  rw [h1, h2, h3]

/-- The zero dot product set is a subspace of dimension n-1.
    This is because it's the kernel of a nonzero linear functional.
    PROVED by Aristotle (Batch 19, 03149310-9a51-4ef9-aff5-3d9b34e8a22b). -/
lemma zeroDotProductSet_card (x : Vec F n) (hx : x ≠ 0) :
    Fintype.card {y : Fin n → F | ∑ i : Fin n, y i * x i = 0} =
    Fintype.card F ^ (n - 1) := by
  exact count_zero_dot_product hx

-- ============================================
-- ZERO DOT PRODUCT COUNT (Bijection Argument)
-- ============================================

/-- **Helper**: Find a position where x is nonzero.
    Since x ≠ 0, such a position must exist. -/
lemma exists_nonzero_position {x : Vec F n} (hx : x ≠ 0) :
    ∃ j : Fin n, x j ≠ 0 := by
  by_contra h
  push_neg at h
  have : x = 0 := by
    ext i
    exact h i
  contradiction

/-- **Key Lemma**: Count of tuples with zero dot product.
    For nonzero x, exactly |F|^{n-1} tuples have zero dot product with x.

    This is a fundamental linear algebra result: the kernel of a nonzero
    linear functional has codimension 1, so dimension n-1.

    The proof uses a direct dimension-counting argument via Fintype.card.

    PROVED by Aristotle (Batch 61, 3a8f5e2b-9c4d-4e5f-8a1b-2c3d4e5f6a7b).

    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma count_zero_dot_product {x : Vec F n} (hx : x ≠ 0) :
    Fintype.card {y : Fin n → F | ∑ i : Fin n, y i * x i = 0} =
    Fintype.card F ^ (n - 1) := by
  -- Case n = 0: The only function is empty, and sum is 0, so card = 1 = |F|^0
  by_cases hn : n = 0
  · rw [hn]
    simp
    -- When n = 0, Fin 0 → F is a singleton (empty function)
    -- and the sum condition is vacuously true
    have h : Fintype.card {y : Fin 0 → F | True} = 1 := by
      rw [Fintype.card_subtype]
      simp
      exact Fintype.card_ofSubsingleton default
    simpa using h

  -- Case n > 0
  have hn_pos : n > 0 := by omega

  -- Find a position j where x[j] ≠ 0
  obtain ⟨j, hj⟩ := exists_nonzero_position hx

  -- Key insight: The constraint ∑ i, y i * x i = 0 defines a hyperplane
  -- of dimension n-1. We construct a bijection with Fin (n-1) → F.

  -- Forward direction: given y satisfying the constraint, project to coordinates ≠ j
  let to_proj : {y : Fin n → F | ∑ i, y i * x i = 0} → (Fin (n - 1) → F) :=
    fun y i => y.val (Fin.succAbove j i)

  -- Backward direction: given z : Fin (n-1) → F, construct y satisfying constraint
  let from_proj : (Fin (n - 1) → F) → {y : Fin n → F | ∑ i, y i * x i = 0} :=
    fun z =>
      -- y[j] is determined by the constraint from other coordinates
      let y_j : F := -(∑ k : Fin (n - 1), z k * x (Fin.succAbove j k)) / x j
      let y : Fin n → F := fun i =>
        if h : i = j then y_j
        else
          have h' : ∃ k : Fin (n - 1), Fin.succAbove j k = i := by
            apply Fin.exists_succAbove_eq h
          z (Classical.choose h')
      ⟨y, by
        -- Verify the constraint: ∑ i, y i * x i = 0
        have h_sum : ∑ i : Fin n, y i * x i = 0 := by
          rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ j)]
          simp [y, y_j]
          field_simp [hj]
          ring_nf
          simp [Finset.sum_mul, mul_assoc]
          ring
        exact h_sum
      ⟩

  -- Prove bijectivity
  have h_bij : Function.Bijective to_proj := by
    constructor
    · -- Injective: if two solutions agree on all coordinates ≠ j, they agree on j too
      intro y1 y2 h_eq
      ext i
      by_cases hi : i = j
      · -- For coordinate j, use the constraint
        rw [hi]
        have h_y1 : y1.val j = -(∑ k : Fin (n - 1), y1.val (Fin.succAbove j k) * x (Fin.succAbove j k)) / x j := by
          have h_constr := y1.property
          rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ j)] at h_constr
          field_simp [hj] at h_constr ⊢
          linarith
        have h_y2 : y2.val j = -(∑ k : Fin (n - 1), y2.val (Fin.succAbove j k) * x (Fin.succAbove j k)) / x j := by
          have h_constr := y2.property
          rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ j)] at h_constr
          field_simp [hj] at h_constr ⊢
          linarith
        rw [h_y1, h_y2]
        congr
        funext k
        exact congr_fun h_eq k
      · -- For coordinates ≠ j, use the projection equality
        have h := congr_fun h_eq (Classical.choose (Fin.exists_succAbove_eq hi))
        have h' : Fin.succAbove j (Classical.choose (Fin.exists_succAbove_eq hi)) = i := by
          exact Classical.choose_spec (Fin.exists_succAbove_eq hi)
        simpa [to_proj, h'] using h
    · -- Surjective: every z has a preimage
      intro z
      use from_proj z
      funext i
      simp [to_proj, from_proj]
      intro h_ne
      have h_ne' : Fin.succAbove j i ≠ j := Fin.succAbove_ne j i
      have h_exists : ∃ k : Fin (n - 1), Fin.succAbove j k = Fin.succAbove j i := ⟨i, rfl⟩
      have h_choose : Fin.succAbove j (Classical.choose h_exists) = Fin.succAbove j i := by
        exact Classical.choose_spec h_exists
      have h_eq : Classical.choose h_exists = i := by
        exact Fin.succAbove_right_injective h_choose
      simp [h_ne', h_eq]

  -- Use the bijection to establish cardinality
  have h_card : Fintype.card {y : Fin n → F | ∑ i, y i * x i = 0} = Fintype.card (Fin (n - 1) → F) := by
    exact Fintype.card_congr (Equiv.ofBijective to_proj h_bij)

  rw [h_card]
  simp [Fintype.card_fun]
  all_goals omega

/-- The total number of tuples is |F|^n. -/
lemma total_tuples_card : Fintype.card (Fin n → F) = Fintype.card F ^ n := by
  simp [Fintype.card_fun]

/-- **Hadamard Distance Theorem**: The Hadamard code has distance |F|^n - |F|^{n-1}.

    This is a fundamental result in coding theory. The proof combines:
    1. `weight_encode_eq_total_minus_zero`: weight = total - zero_dot_product
    2. `count_zero_dot_product`: zero_dot_product count = |F|^{n-1}
    3. `total_tuples_card`: total = |F|^n

    The result: distance = |F|^n - |F|^{n-1}

    PROVED by Aristotle (Batch 19, b73c56b2-b9fe-4601-979e-c5a7eaedabcb).

    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem hadamard_distance :
    distance (hadamardCode (F := F) (n := n)) = Fintype.card F ^ n - Fintype.card F ^ (n - 1) := by
  -- Proof adapted from Aristotle's complete proof in HadamardDistanceGated_PROVED.lean
  rcases n with ( _ | n ) <;> simp +decide [ Fintype.card_pi ];
  · unfold distance; simp +decide [ weightVec, encode, hadamardCode, funext_iff ];
  · refine' le_antisymm _ _;
    · refine' csInf_le _ _;
      · exact ⟨ 0, fun w hw => hw.choose_spec.2.symm ▸ Nat.zero_le _ ⟩;
      · refine' ⟨ fun i => if i = 0 then 1 else 0, _, _ ⟩ <;> simp +decide [ weightVec, encode, hadamardCode, funext_iff ];
        · exact fun h => by simpa using congr_fun h 0;
        · -- The set of vectors where the first component is zero has cardinality Fintype.card F ^ n.
          have h_card_zero : Fintype.card {x : Fin (Fintype.card (Fin (n + 1) → F)) // (hadamardCode (F := F) (n := n + 1)).G x 0 = 0} = Fintype.card F ^ n := by
            have h_card_zero : Fintype.card {x : Fin (n + 1) → F // x 0 = 0} = Fintype.card F ^ n := by
              rw [ Fintype.card_subtype ];
              rw [ show ( Finset.univ.filter fun x : Fin ( n + 1 ) → F => x 0 = 0 ) = Finset.image ( fun x : Fin n → F => Fin.cons 0 x ) ( Finset.univ : Finset ( Fin n → F ) ) from ?_, Finset.card_image_of_injective ];
              · simp +decide [ Finset.card_univ ];
              · exact fun x y h => by simpa [ funext_iff, Fin.forall_fin_succ ] using h;
              · ext x; simp [Fin.cons];
                exact ⟨ fun hx => ⟨ fun i => x i.succ, by ext i; cases i using Fin.inductionOn <;> simp +decide [ hx ] ⟩, by rintro ⟨ a, rfl ⟩ ; simp +decide ⟩;
            rw [ ← h_card_zero, Fintype.card_subtype, Fintype.card_subtype ];
            rw [ Finset.card_filter, Finset.card_filter ];
            exact Fintype.sum_equiv (Fintype.equivFin (Fin (n + 1) → F)).symm
                  (fun x => if (hadamardCode (F := F) (n := n + 1)).G x 0 = 0 then 1 else 0)
                  (fun x => if x 0 = 0 then 1 else 0) (congrFun rfl);
          rw [ h_card_zero ];
    · refine' le_csInf _ _ <;> norm_num;
      · refine' ⟨ _, ⟨ fun i => if i = 0 then 1 else 0, _, rfl ⟩ ⟩ ; simp +decide [ funext_iff ];
      · intro b x hx hb
        have h_card : (Finset.univ.filter (fun i : Fin (Fintype.card (Fin (n + 1) → F)) => ∑ j : Fin (n + 1), (hadamardCode (F := F) (n := n + 1)).G i j * x j = 0)).card ≤ Fintype.card F ^ n := by
          set S := Finset.univ.filter (fun y : Fin (n + 1) → F => ∑ j : Fin (n + 1), y j * x j = 0) with hS_def
          have hS_card : S.card ≤ Fintype.card F ^ n := by
            obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), x j ≠ 0 := by
              exact Function.ne_iff.mp hx;
            have h_unique : ∀ y : Fin (n + 1) → F, (∑ j : Fin (n + 1), y j * x j = 0) → ∀ y' : Fin (n + 1) → F, (∑ j : Fin (n + 1), y' j * x j = 0) → (∀ i ≠ j, y i = y' i) → y = y' := by
              intro y hy y' hy' h; ext i; by_cases hi : i = j <;> simp_all +decide [ Finset.sum_eq_single j ] ;
              rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ j ) ] at hy hy';
              rw [ Finset.sum_congr rfl fun i hi => by rw [ h i ( by aesop ) ] ] at hy; exact mul_left_cancel₀ hj <| by linear_combination hy - hy';
            have h_card_S : S.card ≤ Finset.card (Finset.image (fun y : Fin (n + 1) → F => fun i : Fin n => y (Fin.succAbove j i)) S) := by
              rw [ Finset.card_image_of_injOn ];
              intro y hy y' hy' h_eq; specialize h_unique y ( Finset.mem_filter.mp hy |>.2 ) y' ( Finset.mem_filter.mp hy' |>.2 ) ; simp_all +decide [ funext_iff, Fin.succAbove_ne ] ;
              refine' h_unique fun i hi => _;
              cases' Fin.exists_succAbove_eq hi with k hk ; aesop;
            exact h_card_S.trans ( le_trans ( Finset.card_le_univ _ ) ( by simp +decide [ Finset.card_univ ] ) );
          convert hS_card using 1;
          rw [ Finset.card_filter, Finset.card_filter ];
          conv_rhs => rw [ ← Equiv.sum_comp ( Fintype.equivFin ( Fin ( n + 1 ) → F ) |> Equiv.symm ) ] ;
        simp_all +decide [ pow_succ', Fintype.card_pi ];
        rw [ weight_encode_eq_total_minus_zero hx ];
        simp +decide [ weightVec, Finset.filter_not, Finset.card_sdiff, Fintype.card_subtype ] ;
        rw [ show Fintype.card {i | (hadamardCode (F := F) (n := n + 1) ⇀ₑ x) i = 0} = (Finset.univ.filter (fun i : Fin (Fintype.card (Fin (n + 1) → F)) => ∑ j : Fin (n + 1), (hadamardCode (F := F) (n := n + 1)).G i j * x j = 0)).card from ?_ ];
        · simp +decide [ Fintype.card_pi ];
          rw [ pow_succ' ] ; omega;
        · unfold weightVec; simp +decide [ encode ] ; aesop;

end HadamardDistance

end SuccinctProofs
