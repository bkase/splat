import Succinct.Codes.Core
import Succinct.Codes.Hamming

noncomputable section

namespace SuccinctProofs

section Distance

variable {F : Type*} [Field F] [DecidableEq F]

/-- Distance of a linear code: minimum Hamming weight among nonzero codewords
    (as an infimum in `WithTop ℕ`). -/
def distance (C : LinearCode F) : WithTop ℕ :=
  sInf { w : WithTop ℕ |
    ∃ x : Vec F C.n, x ≠ 0 ∧ w = ∥C ⇀ₑ x∥₀ }

 lemma distance_le_weight_encode_nonzero
      (C : LinearCode F) (z : Vec F C.n) (hz : z ≠ 0) :
      distance C ≤ (∥C⇀ₑz∥₀ : WithTop ℕ) := by
  unfold distance
  refine sInf_le ?_
  exact ⟨z, hz, rfl⟩

lemma distance_le_weight_encode_distinct
      (C : LinearCode F) (x y : Vec F C.n) (hxy : x ≠ y) :
      distance C ≤ (∥C⇀ₑx - C⇀ₑy∥₀ : WithTop ℕ) := by
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hEnc :
      encode C x - encode C y = encode C (x - y) := by
    have h := (LinearMap.map_sub (Matrix.mulVecLin C.G) x y).symm
    simpa [encode, Matrix.mulVecLin_apply] using h
  simpa [hEnc] using
    distance_le_weight_encode_nonzero (C := C) (z := x - y) hz

lemma distance_le_weight_corruption
      (C : LinearCode F) (x δ : Vec F C.n) (hδ : δ ≠ 0) :
      distance C ≤ (∥C⇀ₑ(x + δ) - C⇀ₑx∥₀ : WithTop ℕ) := by
  have hEnc : C⇀ₑ(x + δ) - C⇀ₑx = C⇀ₑδ := by
    have h := (LinearMap.map_sub (Matrix.mulVecLin C.G) (x + δ) x).symm
    have hsub : x + δ - x = δ := by simp
    simpa [encode, Matrix.mulVecLin_apply, hsub] using h
  simpa [hEnc] using distance_le_weight_encode_nonzero (C := C) (z := δ) hδ

lemma detect_corruption
      (C : LinearCode F) {x x' : Vec F C.n} (hx : x ≠ x')
      {d : WithTop ℕ} (hFew : ∥C ⇀ₑ x - C ⇀ₑ x'∥₀ < d) :
      (distance C : WithTop ℕ) < d := by
  have := distance_le_weight_encode_distinct (C := C) (x := x) (y := x') hx
  exact lt_of_le_of_lt this hFew

end Distance
end SuccinctProofs
