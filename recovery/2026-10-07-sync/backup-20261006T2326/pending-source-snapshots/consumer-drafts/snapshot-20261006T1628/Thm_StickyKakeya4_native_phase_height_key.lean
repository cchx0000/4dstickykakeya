/- UNVERIFIED actual old-height/phase key, without a spatial-cell component. -/
import Theorems.Thm_StickyKakeya4_native_configured_third_relation
import Theorems.Thm_StickyKakeya4_native_relative_label_ancestry
import Theorems.Thm_StickyKakeya4_native_merged_point_offsets

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
noncomputable section
namespace NativePhaseHeightKey
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeConfiguredThirdRelation NativeRelativeParentLabels NativeDyadicParentCells NativeJointKeyDescent
open NativeTranslatedGrainHeightOverlap NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge
open NativeReferenceXYGridPoints

/-- Literal ORIGINAL translated height and actual uncharted relative phase. -/
def originalKey {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m c : ℕ) (p : Parent)
    (z : Fin n × Index) : ℤ × Parent :=
  (translatedHeight D a m z.2,relativeLabel D a (2^m) p (2^c) z.1)

section Actual
variable {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
  (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
  (hd : Module.finrank ℝ P=tangentDim s)
  (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
  (R u c : ℕ) (U : Finset (Fin n × Index))

/-- The single-old-height property supplies the only height identification.
No equality of raw physical times or spatial cells is needed. -/
theorem constant_on_pair (hR : 0 < R) (hc : c ≤ u+12)
    (Hsingle : ∀x∈U,∀y∈U,translatedHeight D a m x.2/((8*R:ℕ):ℤ)=
      translatedHeight D a m y.2/((8*R:ℕ):ℤ) → translatedHeight D a m x.2=translatedHeight D a m y.2)
    (x y : Fin n × Index) (hx : x∈U) (hy : y∈U)
    (he : geometricPairKey D a m p s P hP hd F Fcfg R u x=
      geometricPairKey D a m p s P hP hd F Fcfg R u y) :
    originalKey D a m c p x=originalKey D a m c p y := by
  have htime := congrArg (fun z : Parent × E4 => z.2 (3:Fin 4)) he
  change NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R x.2 (3:Fin 4)=
    NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R y.2 (3:Fin 4) at htime
  rw [NativeActualConfiguredPoint.point,NativeActualConfiguredPoint.point,
    NativeActualConfiguredPoint.graphGrid_height,NativeActualConfiguredPoint.graphGrid_height,
    NativeActualConfiguredPoint.sourceLabel_height,NativeActualConfiguredPoint.sourceLabel_height] at htime
  unfold NativeConfiguredTimeCoarsening.finalTime at htime
  have hb : mu m*(R:ℝ)/512 ≠ 0 := by have hp := mu_pos m; positivity
  have hhreal := add_right_cancel (mul_left_cancel₀ hb htime)
  have hcoarse : translatedHeight D a m x.2/((8*R:ℕ):ℤ)=
      translatedHeight D a m y.2/((8*R:ℕ):ℤ) := by exact_mod_cast hhreal
  have hphase := congrArg (fun z : Parent × E4 => ancestor (u+12) c z.1) he
  change ancestor (u+12) c (relativeLabel D a (2^m) p (2^(u+12)) x.1)=
    ancestor (u+12) c (relativeLabel D a (2^m) p (2^(u+12)) y.1) at hphase
  rw [relative_ancestor D a (2^m) p (u+12) c hc x.1,
    relative_ancestor D a (2^m) p (u+12) c hc y.1] at hphase
  exact Prod.ext (Hsingle x hx y hy hcoarse) hphase

/-- A total label on actual geometric pairs, with witness-independence
proved below on the fixed pre-third reference set. -/
def onPair : Parent × E4 → ℤ × Parent :=
  NativeMergedPointOffsets.pointOffset U (geometricPairKey D a m p s P hP hd F Fcfg R u)
    (originalKey D a m c p)

theorem onPair_readback (hR : 0 < R) (hc : c ≤ u+12)
    (Hsingle : ∀x∈U,∀y∈U,translatedHeight D a m x.2/((8*R:ℕ):ℤ)=
      translatedHeight D a m y.2/((8*R:ℕ):ℤ) → translatedHeight D a m x.2=translatedHeight D a m y.2)
    (x : Fin n × Index) (hx : x∈U) :
    onPair D a m p s P hP hd F Fcfg R u c U
      (geometricPairKey D a m p s P hP hd F Fcfg R u x)=originalKey D a m c p x := by
  obtain ⟨y,hy,he,hv⟩ := NativeMergedPointOffsets.pointOffset_witness U
    (geometricPairKey D a m p s P hP hd F Fcfg R u) (originalKey D a m c p)
    (geometricPairKey D a m p s P hP hd F Fcfg R u x) (mem_image_of_mem _ hx)
  exact hv.trans (constant_on_pair D a m p s P hP hd F Fcfg R u c U hR hc Hsingle y x hy hx he)

end Actual
end NativePhaseHeightKey
