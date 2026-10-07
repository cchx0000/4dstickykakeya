import Theorems.Thm_StickyKakeya4_native_anisotropic_slice_labels

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeTwoMapRetainedSliceLabels
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeAnisotropicSliceLabels
open NativeJointUniformCoarseRelations

abbrev XY (a b : ℕ) := ℤ × ((Fin a → ℤ) × (Fin b → ℤ))

/-- Concatenate tangent and normal integer labels into the three horizontal
coordinates, retaining exactly the original translated height as coordinate4. -/
def encode {a b : ℕ} (hd : a+b=3) (z : XY a b) : Index :=
  Fin.lastCases z.1 (fun i : Fin 3 => Fin.append z.2.1 z.2.2 (Fin.cast hd.symm i))

lemma encode_height {a b : ℕ} (hd : a+b=3) (z : XY a b) : encode hd z (3:Fin 4)=z.1 := by
  exact Fin.lastCases_last

lemma encode_left {a b : ℕ} (hd : a+b=3) (z : XY a b) (j : Fin a) :
    encode hd z (Fin.cast hd (Fin.castAdd b j)).castSucc=z.2.1 j := by
  have he : Fin.cast hd.symm (Fin.cast hd (Fin.castAdd b j))=Fin.castAdd b j := Fin.ext rfl
  simp only [encode,Fin.lastCases_castSucc,he,Fin.append_left]

lemma encode_right {a b : ℕ} (hd : a+b=3) (z : XY a b) (j : Fin b) :
    encode hd z (Fin.cast hd (Fin.natAdd a j)).castSucc=z.2.2 j := by
  have he : Fin.cast hd.symm (Fin.cast hd (Fin.natAdd a j))=Fin.natAdd a j := Fin.ext rfl
  simp only [encode,Fin.lastCases_castSucc,he,Fin.append_right]

theorem encode_injective {a b : ℕ} (hd : a+b=3) : Function.Injective (encode hd) := by
  intro x y he
  apply Prod.ext
  · simpa only [encode_height] using congrFun he (3:Fin 4)
  · apply Prod.ext
    · funext j
      simpa only [encode_left] using congrFun he (Fin.cast hd (Fin.castAdd b j)).castSucc
    · funext j
      simpa only [encode_right] using congrFun he (Fin.cast hd (Fin.natAdd a j)).castSucc

def coarse {a b : ℕ} (R : ℕ) (z : XY a b) : XY a b :=
  (z.1,(fun j => z.2.1 j/(R:ℤ),fun j => z.2.2 j/(R:ℤ)))

lemma append_div {a b : ℕ} (x : Fin a → ℤ) (y : Fin b → ℤ) (R : ℕ) (i : Fin (a+b)) :
    Fin.append (fun j => x j/(R:ℤ)) (fun j => y j/(R:ℤ)) i=Fin.append x y i/(R:ℤ) := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Fin.append_left]
  · intro j
    simp only [Fin.append_right]

/-- Exact compatibility with the existing horizontal grid coarsening. -/
lemma encode_coarse {a b : ℕ} (hd : a+b=3) (fine depth : ℕ) (z : XY a b) :
    encode hd (coarse (2^(fine-depth)) z)=horizontalCoarsen fine depth (encode hd z) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [show (Fin.last 3:Fin 4)=3 by rfl,encode_height,horizontalCoarsen_height,coarse]
  · have hj : j.castSucc≠(3:Fin 4) := Fin.castSucc_ne_last j
    simp only [encode,Fin.lastCases_castSucc,coarse,horizontalCoarsen,if_neg hj]
    exact append_div _ _ _ _

lemma image_encode_card {a b : ℕ} (hd : a+b=3) (S : Finset (XY a b)) :
    (S.image (encode hd)).card=S.card := card_image_of_injective _ (encode_injective hd)

lemma encoded_fiber_eq {A : Type*} {a b : ℕ} (hd : a+b=3)
    (T : Finset A) (f : A → XY a b) (x : A) :
    T.filter (fun y => encode hd (f y)=encode hd (f x))=T.filter (fun y => f y=f x) := by
  apply filter_congr
  intro y _hy
  exact (encode_injective hd).eq_iff

theorem encoded_uniformity {A : Type*} [DecidableEq A] {a b : ℕ} (hd : a+b=3)
    (T : Finset A) (f : A → XY a b) (Q : ℕ) (H : HasUniformFibers T Q f) :
    HasUniformFibers T Q (fun x => encode hd (f x)) := by
  intro x hx y hy
  rw [encoded_fiber_eq,encoded_fiber_eq]
  exact H x hx y hy

end NativeTwoMapRetainedSliceLabels
