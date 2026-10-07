import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_support
import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeJointTopSpatialCells
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeReferenceXYGridPoints NativeReferenceXYGridSupport NativeNormalizedCellRelativeMenu

/-- A width at least one sees only the sixteen sign cubes of the actual
bounded first-parent chart. This is an occupied-cell count. -/
theorem wide_cells_card {X : Type*} (E : Finset X) (point : X → E4)
    (hpoint : ∀z∈E,‖point z‖ ≤ (49/128:ℝ)) {width : ℝ} (hwidth : 1 ≤ width) :
    (E.image (fun z => wzDyadicCellIndex width (point z))).card ≤ 16 := by
  let Q : Finset Index := Fintype.piFinset (fun _ : Fin 4 => Icc (-1:ℤ) 0)
  have hsub : E.image (fun z => wzDyadicCellIndex width (point z))⊆Q := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
    apply Fintype.mem_piFinset.mpr
    intro j
    have hc : |point z j| ≤ (49/128:ℝ) := by
      have hh := (PiLp.norm_apply_le (point z) j).trans (hpoint z hz)
      simpa only [Real.norm_eq_abs] using hh
    have hw : 0 < width := zero_lt_one.trans_le hwidth
    have hlo : (-1:ℝ) ≤ point z j/width := (le_div_iff₀ hw).mpr (by
      have hh := (abs_le.mp hc).1
      linarith only [hh,hwidth])
    have hhi : point z j/width < 1 := (div_lt_one hw).mpr (by
      have hh := (abs_le.mp hc).2
      linarith only [hh,hwidth])
    have hl : (-1:ℤ) ≤ ⌊point z j/width⌋ := Int.le_floor.mpr hlo
    have hu : ⌊point z j/width⌋ < (1:ℤ) := Int.floor_lt.mpr hhi
    exact mem_Icc.mpr ⟨hl,by omega⟩
  have hcard : Q.card=16 := by
    simp only [Q,Fintype.card_piFinset,prod_const,card_univ,Fintype.card_fin]
    norm_num
  exact (card_le_card hsub).trans_eq hcard

/-- Source-derived top-interval spatial support on the same original
incidences, valid for every real tau at least1/512. The actual original
parent chart is used; neither Y dilation nor a new selection is required. -/
theorem source_wide_cells_card {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level : ℕ) (hml : m ≤ level) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (p : Parent) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hp : ∀z∈E,parentLabel D a (2^m) z.1=p) {tau : ℝ} (htau : (1/512:ℝ) ≤ tau) :
    (E.image (fun z => wzDyadicCellIndex (512*tau) (physicalPoint D a (2^m) p z.2))).card ≤ 16 := by
  have hpow : ((2^m:ℕ):ℝ) ≤ ((2^level:ℕ):ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hml
  have hunit : ((2^level:ℕ):ℝ)*D.thickness=1 := by
    rw [hdy,Nat.cast_pow,Nat.cast_ofNat,inv_pow,mul_inv_cancel₀ (by positivity)]
  have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 :=
    (mul_le_mul_of_nonneg_right hpow h.1.2.1.le).trans_eq hunit
  apply wide_cells_card E _ ?_ (by linarith only [htau])
  intro z hz
  exact oldPoint_norm h original horiginal ha m hscale p z.1 z.2 (hE hz) (hp z hz)

end NativeJointTopSpatialCells
