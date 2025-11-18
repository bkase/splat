import Mathlib.Data.Finset.Card
import Succinct.LinearAlgebra

noncomputable section

namespace SuccinctProofs

section Hamming
variable {F : Type*} [Field F]
variable [DecidableEq F]  -- needed so `x i ≠ 0` is a decidable predicate
variable {n : ℕ}

/-- Hamming weight (ℓ₀ "norm") of a vector `x : F^n`. -/
def weightVec (x : Vec F n) : ℕ :=
  Fintype.card { i : Fin n | x i ≠ 0 }

scoped notation "∥" x "∥₀" => weightVec x

/-- **Definiteness** -/
lemma weightVec_eq_zero_iff (x : Fin n → F) :
    ∥x∥₀ = 0 ↔ x = 0 := by
  classical
  -- helper facts about the subtype `{ i // x i ≠ 0 }`
  have h0 :
      ∥x∥₀ = 0 ↔ IsEmpty { i : Fin n // x i ≠ 0 } := by
    simpa [weightVec] using
      (Fintype.card_eq_zero_iff :
        Fintype.card { i : Fin n // x i ≠ 0 } = 0 ↔ _)
  have h1 :
      IsEmpty { i : Fin n // x i ≠ 0 } ↔ ∀ i : Fin n, x i = 0 := by
    constructor
    · intro h i
      by_contra hxi
      exact h.elim ⟨i, hxi⟩
    · intro hx
      refine ⟨?_⟩
      rintro ⟨i, hi⟩
      exact hi (hx i)
  -- wrap up
  constructor
  · intro hx
    have hxzero : ∀ i : Fin n, x i = 0 := (h1.mp ((h0.mp hx)))
    funext i; simpa using hxzero i
  · intro hx
    subst hx
    simp [weightVec]

/-- **0-homogeneity (invariance under nonzero scaling)**:
    for `a ≠ 0`, `weightVec (a • x) = weightVec x`. -/
lemma weightVec_smul_of_ne_zero (a : F) (x : Vec F n) (ha : a ≠ 0) :
    ∥a • x∥₀ = ∥x∥₀ := by
  classical
  -- Equivalence between the two index subtypes
  refine Fintype.card_congr
    { toFun := ?_
      invFun := ?invFun 
      left_inv := ?left
      right_inv := ?right }
  · -- forward: {(i | (a•x)i ≠ 0)} → {(i | x i ≠ 0)}
    intro ⟨i, hi⟩
    -- hi : (a•x) i ≠ 0; rewrite and use ha to conclude x i ≠ 0
    have h' : a * x i ≠ 0 := by simpa [Pi.smul_apply] using hi
    refine ⟨i, ?_⟩
    -- If x i = 0, then a * x i = 0, contradicting h'
    intro hx
    exact h' (by simp [hx])
  · -- backward: {(i | x i ≠ 0)} → {(i | (a•x)i ≠ 0)}
    intro ⟨i, hi⟩
    -- From ha and hi we get a * x i ≠ 0
    refine ⟨i, ?_⟩
    simpa [Pi.smul_apply] using mul_ne_zero ha hi
  · -- left inverse/right inverse are trivial because we keep the same index
    intro ⟨i, _⟩; rfl
  · intro ⟨i, _⟩; rfl

@[simp] lemma weightVec_zero {n : ℕ} :
    ∥(0 : Vec F n)∥₀ = 0 := by
  classical
  simp [weightVec]

/-- **Triangle inequality** for the Hamming weight pseudonorm. -/
lemma weightVec_triangle (x y : Vec F n) :
    ∥x + y∥₀ ≤ ∥x∥₀ + ∥y∥₀ := by
  classical
  -- encode supports as finite subtypes and embed into a disjoint union
  let Sxy := { i : Fin n // (x + y) i ≠ 0 }
  let Sx  := { i : Fin n // x i ≠ 0 }
  let Sy  := { i : Fin n // y i ≠ 0 }
  -- build an injection from `Sxy` into the disjoint union `Sx ⊕ Sy`
  have hcard :
      Fintype.card Sxy ≤ Fintype.card Sx + Fintype.card Sy := by
    classical
    let f : Sxy → Sum Sx Sy := fun h =>
      if hx : x h.1 = 0 then
        Sum.inr
          ⟨h.1, by
            have : y h.1 ≠ 0 := by
              simpa [Pi.add_apply, hx] using h.2
            simpa using this⟩
      else
        Sum.inl ⟨h.1, by simpa using hx⟩
    have hf : Function.Injective f := by
      intro a b h
      rcases a with ⟨i, hi⟩
      rcases b with ⟨j, hj⟩
      dsimp [f] at h
      by_cases hxi : x i = 0
      · have hxj : x j = 0 := by
          by_contra hxj
          have hxj' : x j ≠ 0 := by simpa using hxj
          simp [hxi, hxj'] at h
        have hLeft :
            f ⟨i, hi⟩
              =
            Sum.inr (α := Sx)
              (⟨i, by
                  have : y i ≠ 0 := by
                    simpa [Pi.add_apply, hxi] using hi
                  simpa using this⟩ : Sy) := by
          simp [f, hxi]
        have hRight :
            f ⟨j, hj⟩
              =
            Sum.inr (α := Sx)
              (⟨j, by
                  have : y j ≠ 0 := by
                    simpa [Pi.add_apply, hxj] using hj
                  simpa using this⟩ : Sy) := by
          simp [f, hxj]
        have h' :=
          (Eq.trans hLeft.symm (Eq.trans h hRight))
        have : i = j := congrArg Subtype.val (Sum.inr.inj h')
        subst this
        simp
      · have hxj : x j ≠ 0 := by
          by_contra hxj
          have hxj' : x j = 0 := by simpa using hxj
          simp [hxi, hxj'] at h
        have hLeft :
            f ⟨i, hi⟩
              =
            Sum.inl (β := Sy)
              (⟨i, by
                  have : x i ≠ 0 := by simpa using hxi
                  simpa using this⟩ : Sx) := by
          simp [f, hxi]
        have hRight :
            f ⟨j, hj⟩
              =
            Sum.inl (β := Sy)
              (⟨j, by
                  have : x j ≠ 0 := by simpa using hxj
                  simpa using this⟩ : Sx) := by
          simp [f, hxj]
        have h' :=
          (Eq.trans hLeft.symm (Eq.trans h hRight))
        have : i = j := congrArg Subtype.val (Sum.inl.inj h')
        subst this
        simp
    have hle :
        Fintype.card Sxy ≤ Fintype.card (Sum Sx Sy) :=
      Fintype.card_le_of_injective f hf
    simpa [Fintype.card_sum] using hle
  simpa [Sxy, Sx, Sy, weightVec] using hcard

/-- Weight (ℓ₀ "norm") of a set of vectors:
    the minimum Hamming weight of any element, in `WithTop ℕ`
    so that empty sets give `⊤`. -/
def weightSet (S : Set (Vec F n)) : WithTop ℕ :=
  sInf { w : WithTop ℕ | ∃ x ∈ S, w = ∥x∥₀ }

scoped notation "∥" S "∥ₛ" => weightSet S

-- point-set difference: { x - y | y ∈ S }
def vecDiff (x : Vec F n) (S : Set (Vec F n)) : Set (Vec F n) :=
  { z | ∃ y ∈ S, z = fun i => x i - y i }

scoped infixl:70 " -ₛ " => vecDiff

-- The main identity:
lemma weightSet_vecDiff_eq_sInf
    (x : Vec F n) (S : Set (Vec F n)) :
    ∥x -ₛ S∥ₛ
      =
    sInf { w : WithTop ℕ | ∃ y ∈ S, w = ∥x - y∥₀ } := by
  classical
  -- identify the sets under the `sInf`
  have hSet :
      { w : WithTop ℕ | ∃ z ∈ x -ₛ S, w = ∥z∥₀ }
        = { w : WithTop ℕ | ∃ y ∈ S, w = ∥x - y∥₀ } := by
    ext w
    constructor
    · intro hw
      rcases hw with ⟨z, hz, rfl⟩
      rcases hz with ⟨y, hyS, hz⟩
      have hxsub : x - y = fun i => x i - y i := by
        ext i; rfl
      refine ⟨y, hyS, ?_⟩
      simp [hz, hxsub]
    · intro hw
      rcases hw with ⟨y, hyS, rfl⟩
      have hxsub : x - y = fun i => x i - y i := by
        ext i; rfl
      refine ⟨x - y, ?_, by simp [hxsub]⟩
      exact ⟨y, hyS, hxsub⟩
  unfold weightSet
  simp [hSet]

end Hamming
end SuccinctProofs
