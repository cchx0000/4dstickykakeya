import Theorems.Thm_StickyKakeya4_native_translated_height_freeze
import Theorems.Thm_StickyKakeya4_native_actual_configured_point
import Theorems.Thm_StickyKakeya4_native_translated_grain_height_chart

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeFrozenConfiguredHeightMetric
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeTranslatedHeightFreeze NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric
open NativeReferenceXYGridPoints NativeConfiguredTimeCoarsening NativeReferenceXYGridField
open NativeActualConfiguredPoint CanonicalConfiguredE4Bridge NativeOriginalParentSelection
open NativeHeightMetricMenu NativeTranslatedGrainHeightChart NativeTranslatedGrainHeightSelection
open scoped Matrix.Norms.Elementwise

/-- The old translated time lies within half a coarse bin of512 times the
literal configured time. This includes negative integer height labels. -/
lemma reference_height_rounding (m R : ℕ) (hR : 0< R) (z : ℤ) :
    |referenceHeight m z-512*finalTime (mu m*(R:ℝ)) (z/((8*R:ℕ):ℤ))| ≤
      (mu m*(R:ℝ))/2 := by
  have hb : 0< mu m*(R:ℝ) := by have hm:=mu_pos m; positivity
  have hlo := (le_div_iff₀ hb).mp (Int.floor_le (referenceHeight m z/(mu m*(R:ℝ))))
  have hhi := (div_lt_iff₀ hb).mp (Int.lt_floor_add_one (referenceHeight m z/(mu m*(R:ℝ))))
  rw [reference_height_coarse_floor] at hlo hhi
  unfold finalTime
  exact abs_le.mpr ⟨by linarith only [hlo],by linarith only [hhi]⟩

/-- The same residue8 time separation pays the whole rounding term. No
new time selection or assumed Lipschitz comparison is introduced. -/
lemma reference_height_comparison (m R : ℕ) (hR : 0< R) (z w : ℤ)
    (hsep : (mu m*(R:ℝ))/64 ≤
      |finalTime (mu m*(R:ℝ)) (z/((8*R:ℕ):ℤ))-
        finalTime (mu m*(R:ℝ)) (w/((8*R:ℕ):ℤ))|) :
    |referenceHeight m z-referenceHeight m w| ≤ 576*
      |finalTime (mu m*(R:ℝ)) (z/((8*R:ℕ):ℤ))-
        finalTime (mu m*(R:ℝ)) (w/((8*R:ℕ):ℤ))| := by
  let x:=finalTime (mu m*(R:ℝ)) (z/((8*R:ℕ):ℤ))
  let y:=finalTime (mu m*(R:ℝ)) (w/((8*R:ℕ):ℤ))
  have hz:=reference_height_rounding m R hR z
  have hw:=reference_height_rounding m R hR w
  change |referenceHeight m z-512*x|≤ (mu m*(R:ℝ))/2 at hz
  change |referenceHeight m w-512*y|≤ (mu m*(R:ℝ))/2 at hw
  have hxy : |referenceHeight m z-referenceHeight m w| ≤
      |referenceHeight m z-512*x|+|512*x-512*y|+|512*y-referenceHeight m w| := by
    calc
      _ ≤ |referenceHeight m z-512*x|+|512*x-referenceHeight m w| := abs_sub_le _ _ _
      _ ≤ |referenceHeight m z-512*x|+(|512*x-512*y|+|512*y-referenceHeight m w|) :=
        add_le_add_left (abs_sub_le _ _ _) _
      _ = _ := by ring
  have he : |512*x-512*y|=512*|x-y| := by
    rw [←mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)< 512)]
  rw [he,abs_sub_comm (512*y) (referenceHeight m w)] at hxy
  change (mu m*(R:ℝ))/64≤ |x-y| at hsep
  change |referenceHeight m z-referenceHeight m w|≤ 576*|x-y|
  linarith only [hxy,hz,hw,hsep]

/-- The source's fixed field already has its translated metric on EVERY
later edge subset; this readback does not wait for a third refinement. -/
theorem fixedField_metric_on_subset {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m ell : ℕ) (plane : Index → Submodule ℝ E4)
    (Sq U : Finset (Fin n × Index)) (hU : U⊆second D a m ell plane Sq)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (metric shift : ℝ) (hmetric : 0≤ metric)
    (Hraw : ∀z∈U,∀w∈U,‖Fraw (rawHeight D m z.2)-Fraw (rawHeight D m w.2)‖ ≤
      metric*|chartHeightCoordinate m shift (rawHeight D m z.2)-
        chartHeightCoordinate m shift (rawHeight D m w.2)|) :
    ∀z∈U,∀w∈U,
      ‖fixedField D a m ell plane Sq Fraw (translatedHeight D a m z.2)-
        fixedField D a m ell plane Sq Fraw (translatedHeight D a m w.2)‖ ≤
      (3*metric)*|referenceHeight m (translatedHeight D a m z.2)-
        referenceHeight m (translatedHeight D a m w.2)| := by
  intro z hz w hw
  have H:=mapped_chart_metric D a m ell plane Sq U hU Fraw metric shift hmetric Hraw
    _ (mem_image_of_mem _ hz) _ (mem_image_of_mem _ hw)
  rw [mapped_readback D a m ell plane Sq Fraw z (hU hz),
    mapped_readback D a m ell plane Sq Fraw w (hU hw)] at H
  rw [fixedField_readback D a m ell plane Sq Fraw z (hU hz),
    fixedField_readback D a m ell plane Sq Fraw w (hU hw)]
  exact H

/-- The same frozen matrix evaluated by its actual configured time. -/
def physicalField (s : Split) (m R : ℕ)
    (Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ) (t : ℝ) :
    Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ :=
  Fcfg ⌊t/((mu m*(R:ℝ))/512)⌋

lemma physicalField_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (hR : 0< R) (k : Index) :
    physicalField s m R Fcfg (point D a m p s P hP hd F Fcfg R k (3:Fin 4))=
      Fcfg (translatedHeight D a m k/((8*R:ℕ):ℤ)) := by
  have hb : 0< mu m*(R:ℝ) := by have hm:=mu_pos m; positivity
  unfold physicalField
  rw [point,graphGrid_height,sourceLabel_height]
  congr 1
  simpa only [Nat.cast_one,mul_one,Int.cast_one,Int.ediv_one] using
    floor_finalTime (mu m*(R:ℝ)) hb 1 (translatedHeight D a m k/((8*R:ℕ):ℤ))

/-- The original fixedField, with only the deterministic rank2/rank3 type
readback performed. This definition makes no field or source choice. -/
def fixedFieldForSplit {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (s : Split) (plane : Index → Submodule ℝ E4) (Sq : Finset (Fin n × Index))
    (Fraw : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ) :
    ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ := by
  cases s with
  | oneTwo => exact fixedField D a m 2 plane Sq Fraw
  | twoOne => exact fixedField D a m 3 plane Sq Fraw

lemma fixedFieldForSplit_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (s : Split) (plane : Index → Submodule ℝ E4) (Sq : Finset (Fin n × Index))
    (Fraw : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (z : Fin n × Index) (hz : z∈second D a m (tangentDim s+1) plane Sq) :
    fixedFieldForSplit D a m s plane Sq Fraw (translatedHeight D a m z.2)=
      Fraw (rawHeight D m z.2) := by
  cases s with
  | oneTwo => exact fixedField_readback D a m 2 plane Sq Fraw z hz
  | twoOne => exact fixedField_readback D a m 3 plane Sq Fraw z hz

/-- The actual matrix on the configured point is the OLD raw source matrix.
Its proof combines literal source membership, the proved raw/translated
fixedField reader, and the existing exact freeze equality. -/
theorem physicalField_raw_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (p : Parent) (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (plane : Index → Submodule ℝ E4) (Sq : Finset (Fin n × Index))
    (Fraw Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (hR : 0< R) (z : Fin n × Index)
    (hz : z∈second D a m (tangentDim s+1) plane Sq)
    (hfreeze : Fcfg (translatedHeight D a m z.2/((8*R:ℕ):ℤ))=
      fixedFieldForSplit D a m s plane Sq Fraw (translatedHeight D a m z.2)) :
    physicalField s m R Fcfg
      (point D a m p s P hP hd (fixedFieldForSplit D a m s plane Sq Fraw) Fcfg R z.2 (3:Fin 4))=
      Fraw (rawHeight D m z.2) := by
  exact (physicalField_readback D a m p s P hP hd
    (fixedFieldForSplit D a m s plane Sq Fraw) Fcfg R hR z.2).trans
      (hfreeze.trans (fixedFieldForSplit_readback D a m s plane Sq Fraw z hz))

/-- On occupied actual configured heights, the proved3*metric translated
bound becomes1728*metric. Equal heights use the same frozen value; distinct
heights use the SAME residue8 separation already paid before the third core. -/
theorem physicalField_metric_on_selected {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (p : Parent) (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (hR : 0< R) (U : Finset (Fin n × Index))
    (metric : ℝ) (hmetric : 0≤ metric)
    (hfreeze : ∀z∈U,Fcfg (translatedHeight D a m z.2/((8*R:ℕ):ℤ))=
      F (translatedHeight D a m z.2))
    (Hmetric : ∀z∈U,∀w∈U,‖F (translatedHeight D a m z.2)-F (translatedHeight D a m w.2)‖ ≤
      (3*metric)*|referenceHeight m (translatedHeight D a m z.2)-
        referenceHeight m (translatedHeight D a m w.2)|)
    (hsep : ∀z∈U,∀w∈U,
      point D a m p s P hP hd F Fcfg R z.2 (3:Fin 4)≠
        point D a m p s P hP hd F Fcfg R w.2 (3:Fin 4) →
      (mu m*(R:ℝ))/64≤ dist
        (point D a m p s P hP hd F Fcfg R z.2 (3:Fin 4))
        (point D a m p s P hP hd F Fcfg R w.2 (3:Fin 4))) :
    ∀z∈U,∀w∈U,
      ‖physicalField s m R Fcfg (point D a m p s P hP hd F Fcfg R z.2 (3:Fin 4))-
        physicalField s m R Fcfg (point D a m p s P hP hd F Fcfg R w.2 (3:Fin 4))‖ ≤
      (1728*metric)*|point D a m p s P hP hd F Fcfg R z.2 (3:Fin 4)-
        point D a m p s P hP hd F Fcfg R w.2 (3:Fin 4)| := by
  intro z hz w hw
  by_cases he : point D a m p s P hP hd F Fcfg R z.2 (3:Fin 4)=
      point D a m p s P hP hd F Fcfg R w.2 (3:Fin 4)
  · rw [he,sub_self,norm_zero,sub_self,abs_zero,mul_zero]
  have hs:=hsep z hz w hw he
  rw [Real.dist_eq,point,point,graphGrid_height,graphGrid_height,
    sourceLabel_height,sourceLabel_height] at hs
  have hcompare:=reference_height_comparison m R hR
    (translatedHeight D a m z.2) (translatedHeight D a m w.2) hs
  rw [physicalField_readback D a m p s P hP hd F Fcfg R hR z.2,
    physicalField_readback D a m p s P hP hd F Fcfg R hR w.2,hfreeze z hz,hfreeze w hw]
  have hh := (Hmetric z hz w hw).trans
    (mul_le_mul_of_nonneg_left hcompare (by positivity : (0:ℝ)≤ 3*metric))
  rw [point,point,graphGrid_height,graphGrid_height,sourceLabel_height,sourceLabel_height]
  nlinarith only [hh]

end NativeFrozenConfiguredHeightMetric
