/- UNVERIFIED exact image reader for the local base-XY population bound. -/
import Theorems.Thm_StickyKakeya4_native_actual_configured_residue
import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_actual_caps
import Theorems.Thm_StickyKakeya4_native_slice_class_balls
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeConfiguredBaseXYImage
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open CanonicalConfiguredE4Bridge CanonicalGridRecoding NativeActualConfiguredPoint
open NativeActualConfiguredResidue NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeTwoMapRetainedSliceLabels NativeTwoMapRetainedSliceActualCaps NativeSliceClassBalls
open NativeHorizontalGrainSlice

lemma split_dimensions (s : Split) : tangentDim s+normalDim s=3 := by cases s <;> decide

/-- At one coarse height, the two frozen fields make the actual point a
function of its literal realized base XY coordinates. Fine heights may
differ; only their coarse height and their own exact field readbacks enter. -/
theorem graphGrid_eq_of_realized_eq (s : Split) (mu : ℝ) (R : ℕ)
    (hmu : 0 < mu) (hR : 0 < R)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (z w : Label ℤ (tangentDim s) (normalDim s))
    (hz : F z.1=Fcfg (z.1/((8*R:ℕ):ℤ)))
    (hw : F w.1=Fcfg (w.1/((8*R:ℕ):ℤ)))
    (ht : z.1/((8*R:ℕ):ℤ)=w.1/((8*R:ℕ):ℤ))
    (he : realized ((R:ℝ)*mu) (encode (split_dimensions s) (coarse R z)) =
      realized ((R:ℝ)*mu) (encode (split_dimensions s) (coarse R w))) :
    NativeActualConfiguredPoint.graphGrid s mu R F Fcfg z =
      NativeActualConfiguredPoint.graphGrid s mu R F Fcfg w := by
  have hbase : 0 < (R:ℝ)*mu := mul_pos (by exact_mod_cast hR) hmu
  have hx : (fun j => z.2.1 j/(R:ℤ))=(fun j => w.2.1 j/(R:ℤ)) := by
    funext j
    have hcoord := congrFun he (Fin.cast (split_dimensions s) (Fin.castAdd (normalDim s) j))
    simp only [realized,encode_left,coarse] at hcoord
    have hc : ((z.2.1 j/(R:ℤ):ℤ):ℝ)=((w.2.1 j/(R:ℤ):ℤ):ℝ) := by
      nlinarith only [hcoord,hbase]
    exact_mod_cast hc
  have hy : (fun j => z.2.2 j/(R:ℤ))=(fun j => w.2.2 j/(R:ℤ)) := by
    funext j
    have hcoord := congrFun he (Fin.cast (split_dimensions s) (Fin.natAdd (tangentDim s) j))
    simp only [realized,encode_right,coarse] at hcoord
    have hc : ((z.2.2 j/(R:ℤ):ℤ):ℝ)=((w.2.2 j/(R:ℤ):ℤ):ℝ) := by
      nlinarith only [hcoord,hbase]
    exact_mod_cast hc
  apply (graphGrid_eq_iff_keys s mu R hmu hR F Fcfg z w).mpr
  refine ⟨ht,hx,?_⟩
  rw [hz,hw,sub_self,sub_self,ExactHeightNoDeletionRecoding.recodedY_zero,
    ExactHeightNoDeletionRecoding.recodedY_zero,coarseGrid_eq_ediv mu R hmu,
    coarseGrid_eq_ediv mu R hmu]
  exact hy

/-- Every literal configured point is represented by its unchanged
original base-XY key. A local key upper therefore bounds actual points
with constant1, without equating edge and point counts. -/
theorem actual_point_card_le_base_XY {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (p : Parent) (s : Split)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (hR : 0 < R) (E : Finset (Fin n × Index)) (height : ℤ)
    (Hheight : ∀ z ∈ E,
      NativeTranslatedGrainHeightOverlap.translatedHeight D a m z.2/((8*R:ℕ):ℤ)=height)
    (Hfreeze : ∀ z ∈ E,
      F (NativeTranslatedGrainHeightOverlap.translatedHeight D a m z.2)=Fcfg height) :
    (E.image (fun z => point D a m p s P hP hd F Fcfg R z.2)).card ≤
      (E.image (fun z => realized ((R:ℝ)*mu m)
        (encode (split_dimensions s) (coarse R (sourceLabel D a m p s P hP hd F z.2))))).card := by
  let pmap := fun z : Fin n × Index => point D a m p s P hP hd F Fcfg R z.2
  let xy := fun z : Fin n × Index => realized ((R:ℝ)*mu m)
    (encode (split_dimensions s) (coarse R (sourceLabel D a m p s P hP hd F z.2)))
  have hmap (z w : Fin n × Index) (hz : z ∈ E) (hw : w ∈ E) (he : xy z=xy w) :
      pmap z=pmap w := by
    apply graphGrid_eq_of_realized_eq s (mu m) R (mu_pos m) hR F Fcfg
      (sourceLabel D a m p s P hP hd F z.2) (sourceLabel D a m p s P hP hd F w.2)
    · simpa only [sourceLabel_height,Hheight z hz] using Hfreeze z hz
    · simpa only [sourceLabel_height,Hheight w hw] using Hfreeze w hw
    · simpa only [sourceLabel_height] using (Hheight z hz).trans (Hheight w hw).symm
    · exact he
  have hcount := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images E pmap xy 1 (by
    intro v hv
    obtain ⟨z,hz,he⟩ := mem_image.mp hv
    have hsub : (E.filter (fun w => xy w=v)).image pmap ⊆ {pmap z} := by
      intro y hy
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hy
      exact mem_singleton.mpr (hmap w z (mem_filter.mp hw).1 hz ((mem_filter.mp hw).2.trans he.symm))
    have hc := card_le_card hsub
    simp only [card_singleton] at hc
    exact_mod_cast hc)
  have hh : ((E.image pmap).card:ℝ) ≤ (E.image xy).card := by simpa only [one_mul] using hcount
  exact_mod_cast hh

end NativeConfiguredBaseXYImage
