import Theorems.Thm_StickyKakeya4_native_actual_window_XY_ad
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_support

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
noncomputable section
namespace NativeWindowHeightSupport
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeReferenceXYGridPoints
open NativeReferenceXYGridSupport NativeTranslatedGrainHeightOverlap NativeSquaredGrainQueries

lemma actual_height_bound {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m : ℕ) (p : Parent) (z : Fin n × Index) (hz : z∈incidences original) :
    |oldPoint D a m p z.2 (3:Fin 4)| ≤ 1/128 := by
  unfold oldPoint
  rw [NativeLocalCellCoherence.physicalCell_height,abs_div,abs_of_pos (by norm_num : (0:ℝ)<128)]
  have hh := (original_cell_bounds h original horiginal a ha hz).1
  change |NativeOriginalPaddedCells.oldTime D a z.2| ≤ 1 at hh
  exact div_le_div_of_nonneg_right hh (by norm_num)

/-- Actual translated labels occupy at most half the coarsest prepared
height window in each sign direction. No alignment of raw heights is used. -/
theorem translated_height_bound {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m : ℕ) (hm : 6 ≤ m) (p : Parent) (z : Fin n × Index) (hz : z∈incidences original) :
    |translatedHeight D a m z.2| ≤ ((4*NativeWindowQuotientTransport.factor m m:ℕ):ℤ) := by
  let B := 4*NativeWindowQuotientTransport.factor m m
  have hmb : m ≤ phaseDepth m := by unfold phaseDepth; omega
  have hh := NativeActualWindowXYAD.window_mesh_outer m m hm le_rfl hmb
  simp only [NativeSliceRadiusInterpolation.radius,Nat.sub_self,pow_zero,Nat.cast_one,mul_one] at hh
  have he : heightMesh m*(B:ℝ)=1/128 := by
    dsimp only [B]
    rw [heightMesh_eq,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith only [hh]
  have ht := actual_height_bound h original horiginal ha m p z hz
  have hratio : |oldPoint D a m p z.2 (3:Fin 4)/heightMesh m| ≤ (B:ℝ) := by
    rw [abs_div,abs_of_pos (heightMesh_pos m)]
    apply (div_le_iff₀ (heightMesh_pos m)).mpr
    nlinarith only [ht,he]
  rw [←pref_height D a m p z.2,pref_height_floor]
  apply abs_le.mpr
  have hlo := Int.floor_mono (abs_le.mp hratio).1
  have hhi := Int.floor_mono (abs_le.mp hratio).2
  exact ⟨by simpa using hlo,by simpa using hhi⟩

lemma ediv_eq_sign {t : ℤ} {H : ℕ} (hH : 0 < H) (ht : |t| < (H:ℤ)) :
    t/(H:ℤ)=if t < 0 then -1 else 0 := by
  have hHp : (0:ℤ)<H := by exact_mod_cast hH
  split_ifs with hn
  · apply (Int.ediv_eq_iff_of_pos hHp).mpr
    constructor <;> nlinarith only [(abs_lt.mp ht).1,hn]
  · apply (Int.ediv_eq_iff_of_pos hHp).mpr
    constructor
    · simpa using le_of_not_gt hn
    · simpa using (abs_lt.mp ht).2

/-- Every larger actual height window has exactly the same negative/positive
membership as the coarsest prepared window, on the original incidence set. -/
theorem large_window_height_stable {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m : ℕ) (hm : 6 ≤ m) (p : Parent) (z : Fin n × Index) (hz : z∈incidences original)
    (R : ℕ) (hR : NativeWindowQuotientTransport.factor m m ≤ R) :
    translatedHeight D a m z.2/((8*R:ℕ):ℤ)=
      translatedHeight D a m z.2/((8*NativeWindowQuotientTransport.factor m m:ℕ):ℤ) := by
  have hf : 0 < NativeWindowQuotientTransport.factor m m := by
    unfold NativeWindowQuotientTransport.factor
    positivity
  have hb := translated_height_bound h original horiginal ha m hm p z hz
  have hsmall : |translatedHeight D a m z.2| < ((8*NativeWindowQuotientTransport.factor m m:ℕ):ℤ) := by
    exact hb.trans_lt (by exact_mod_cast (by omega : 4*NativeWindowQuotientTransport.factor m m < 8*NativeWindowQuotientTransport.factor m m))
  have hbig : |translatedHeight D a m z.2| < ((8*R:ℕ):ℤ) :=
    hsmall.trans_le (by exact_mod_cast Nat.mul_le_mul_left 8 hR)
  rw [ediv_eq_sign (by omega) hbig,ediv_eq_sign (by omega) hsmall]

end NativeWindowHeightSupport
