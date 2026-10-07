import Theorems.Thm_StickyKakeya4_native_pointwise_angular_trim

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativePointwiseTrimPreservation
open Classical Finset
open scoped BigOperators

lemma filtered_point_image {A X : Type*} [DecidableEq A] [DecidableEq X]
    (I : Finset (A × X)) (P : X → Prop) :
    (I.filter (fun z => P z.2)).image Prod.snd=(I.image Prod.snd).filter P := by
  ext x
  simp only [mem_image,mem_filter]
  constructor
  · rintro ⟨z,⟨hz,hP⟩,rfl⟩
    exact ⟨⟨z,hz,rfl⟩,hP⟩
  · rintro ⟨⟨z,hz,rfl⟩,hP⟩
    exact ⟨z,⟨hz,hP⟩,rfl⟩

lemma filtered_point_fiber {A X : Type*} [DecidableEq A] [DecidableEq X]
    (I : Finset (A × X)) (P : X → Prop) (x : X) (hx : P x) :
    (I.filter (fun z => P z.2)).filter (fun z => z.2=x)=I.filter (fun z => z.2=x) := by
  ext z
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hz,_⟩,he⟩
    exact ⟨hz,he⟩
  · rintro ⟨hz,he⟩
    exact ⟨⟨hz,he ▸ hx⟩,he⟩

/-- Half retention at EVERY original point implies half retention inside
EVERY point-dependent class. This includes each fixed-parent old grain;
there is no new loss depending on the number of grains. -/
theorem point_class_half_retention {A X : Type*} [DecidableEq A] [DecidableEq X]
    (I T : Finset (A × X)) (hpoints : T.image Prod.snd=I.image Prod.snd)
    (hhalf : ∀x∈I.image Prod.snd,(I.filter (fun z => z.2=x)).card ≤
      2*(T.filter (fun z => z.2=x)).card) (P : X → Prop) :
    (I.filter (fun z => P z.2)).card ≤ 2*(T.filter (fun z => P z.2)).card := by
  let S := I.filter (fun z => P z.2)
  let U := T.filter (fun z => P z.2)
  have hsupp : U.image Prod.snd=S.image Prod.snd := by
    dsimp only [U,S]
    rw [filtered_point_image,filtered_point_image,hpoints]
  have hlocal (x : X) (hx : x∈S.image Prod.snd) :
      (S.filter (fun z => z.2=x)).card ≤ 2*(U.filter (fun z => z.2=x)).card := by
    have hmem : x∈I.image Prod.snd ∧ P x := by
      simpa only [S,filtered_point_image,mem_filter] using hx
    dsimp only [S,U]
    rw [filtered_point_fiber I P x hmem.2,filtered_point_fiber T P x hmem.2]
    exact hhalf x hmem.1
  calc
    _ = ∑x∈S.image Prod.snd,(S.filter (fun z => z.2=x)).card := card_eq_sum_card_image Prod.snd S
    _ ≤ ∑x∈S.image Prod.snd,2*(U.filter (fun z => z.2=x)).card := sum_le_sum hlocal
    _ = _ := by rw [←mul_sum,←hsupp,←card_eq_sum_card_image Prod.snd U]

/-- Every geometric image inside a point-dependent old grain is also exact.
In particular the final angular refinement does not change its X/Y sets. -/
theorem point_class_image_unchanged {A X Y : Type*}
    [DecidableEq A] [DecidableEq X] [DecidableEq Y]
    (I T : Finset (A × X)) (hpoints : T.image Prod.snd=I.image Prod.snd)
    (P : X → Prop) (g : X → Y) :
    (T.filter (fun z => P z.2)).image (fun z => g z.2)=
      (I.filter (fun z => P z.2)).image (fun z => g z.2) := by
  have hp : (T.filter (fun z => P z.2)).image Prod.snd=
      (I.filter (fun z => P z.2)).image Prod.snd := by
    rw [filtered_point_image,filtered_point_image,hpoints]
  exact NativePointwiseAngularTrim.point_image_unchanged _ _ hp g

end NativePointwiseTrimPreservation
