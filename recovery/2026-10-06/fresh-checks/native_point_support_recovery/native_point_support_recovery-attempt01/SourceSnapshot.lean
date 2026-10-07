import Theorems.Thm_StickyKakeya4_native_matrix_height_wholepoint

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
noncomputable section
namespace NativePointSupportRecovery
open Classical Finset NativeMatrixHeightWholePoint

/-- Restore precisely the pre-third source incidences at the final retained
points. Point-dependent geometry is unchanged, while each angle fiber is the
original source fiber. No final-edge weight uniformity is asserted for U. -/
theorem restore_original_fibers {A X : Type*} [DecidableEq A] [DecidableEq X]
    (S T : Finset A) (hTS : T⊆S) (point : A → X) :
    let U:=edgeLift S point (T.image point)
    T⊆U ∧ U⊆S ∧ U.image point=T.image point ∧
      (∀x∈T.image point,U.filter (fun z => point z=x)=S.filter (fun z => point z=x)) ∧
      (∀(Y : Type*) [DecidableEq Y] (f : X → Y),
        U.image (fun z => f (point z))=T.image (fun z => f (point z))) ∧
      T.card≤U.card := by
  intro U
  have hTU : T⊆U := by
    intro z hz
    exact mem_filter.mpr ⟨hTS hz,mem_image.mpr ⟨z,hz,rfl⟩⟩
  have hUS : U⊆S := filter_subset _ _
  have hImage : U.image point=T.image point := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨z,hz,rfl⟩:=mem_image.mp hx
      exact (mem_filter.mp hz).2
    · exact image_subset_image hTU
  refine ⟨hTU,hUS,hImage,fun x hx => edgeLift_fiber S point (T.image point) x hx,?_,card_le_card hTU⟩
  intro Y _ f
  calc
    U.image (fun z => f (point z))=(U.image point).image f := (image_image _ _ _).symm
    _=(T.image point).image f := congrArg (fun P : Finset X => P.image f) hImage
    _=T.image (fun z => f (point z)) := image_image _ _ _

end NativePointSupportRecovery
