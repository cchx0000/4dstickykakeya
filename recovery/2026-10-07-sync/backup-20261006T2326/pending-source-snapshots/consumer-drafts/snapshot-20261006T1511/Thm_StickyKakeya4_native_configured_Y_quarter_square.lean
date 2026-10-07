/- UNVERIFIED literal final-Y diameter reader from original native incidence. -/
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_support
import Theorems.Thm_StickyKakeya4_native_configured_third_relation
import Theorems.Thm_StickyKakeya4_native_quotient_grid_centers

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeConfiguredYQuarterSquare
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeReferenceXYGridSupport NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeHorizontalGrainSlice NativeTranslatedGrainHeightOverlap NativeSquaredGrainQueries
open NativeConfiguredThirdRelation NativeQuotientGridCenters CanonicalConfiguredE4Bridge
open scoped Matrix.Norms.Elementwise

/-- Integer division, including negative labels, keeps the contracted
coarse midpoint in a fixed small interval. No support capacity is assumed. -/
lemma contracted_midpoint_bound {mu : ℝ} (hmu : 0 < mu) (R : ℕ) (hR : 0 < R)
    (hbase : mu*(R:ℝ) ≤ 1) (v : ℤ) (hv : |mu*(v:ℝ)| ≤ 1) :
    |(mu*(R:ℝ)/512)*(((v/(R:ℤ):ℤ):ℝ)+1/2)| ≤ 3/1024 := by
  have hRZ : (0:ℤ) < R := by exact_mod_cast hR
  have hb := (Int.ediv_eq_iff_of_pos hRZ).mp (rfl : v/(R:ℤ)=v/(R:ℤ))
  have hlo : ((v/(R:ℤ):ℤ):ℝ)*(R:ℝ) ≤ (v:ℝ) := by exact_mod_cast hb.1
  have hhi : (v:ℝ) ≤ ((v/(R:ℤ):ℤ):ℝ)*(R:ℝ)+(R:ℝ) := by exact_mod_cast hb.2.le
  have hml := mul_le_mul_of_nonneg_left hlo hmu.le
  have hmh := mul_le_mul_of_nonneg_left hhi hmu.le
  obtain ⟨hvl,hvu⟩ := abs_le.mp hv
  apply abs_le.mpr
  constructor <;> nlinarith only [hml,hmh,hvl,hvu,hbase]

/-- The actual fine XY support and exact height freeze put every final
normal-Y midpoint in the quarter-square. The scale and height labels are
literal; the planar input is not dilated to force its diameter premise. -/
theorem source_quarter_square {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hf : phaseDepth m ≤ level) (p : Parent) (T : Finset (Fin n × Index))
    (hT : T⊆incidences cells) (hp : ∀z∈T,parentLabel D a (2^m) z.1=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (R : ℕ) (hR : 0 < R) (hbase : mu m*(R:ℝ) ≤ 1)
    (hfreeze : ∀z∈T,F (translatedHeight D a m z.2)=
      Fcfg (translatedHeight D a m z.2/((8*R:ℕ):ℤ))) :
    ∀z∈T,∀j : Fin 2,
      |center (mu m*(R:ℝ)/512) (coarseYKey D a m p .oneTwo P hP hd F Fcfg R z.2).2 j| ≤ 1/4 := by
  intro z hz j
  have hsupport := (dyadic_pxy_support h cells hcells ha m level hm hdy hf p z.1 z.2
    (hT hz) (hp z hz) P hP 2 (by norm_num) (by norm_num) hd F hF).2 j
  have hcast : |((pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F z.2).2.2 j:ℝ)| ≤
      (2*(halfWidth m:ℝ)) := by exact_mod_cast hsupport
  have hvalue : |mu m*((pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F z.2).2.2 j:ℝ)| ≤ 1 := by
    rw [abs_mul,abs_of_pos (mu_pos m)]
    exact (mul_le_mul_of_nonneg_left hcast (mu_pos m).le).trans_eq (mu_fullWidth m (by omega))
  rw [coarseYKey_of_frozen D a m p .oneTwo P hP hd F Fcfg R z.2 (hfreeze z hz)]
  change |(mu m*(R:ℝ)/512)*
    ((((NativeActualConfiguredPoint.sourceLabel D a m p .oneTwo P hP hd F z.2).2.2 j/(R:ℤ):ℤ):ℝ)+1/2)| ≤ 1/4
  rw [NativeActualConfiguredPoint.sourceLabel_oneTwo]
  exact (contracted_midpoint_bound (mu_pos m) R hR hbase _ hvalue).trans (by norm_num)

end NativeConfiguredYQuarterSquare
