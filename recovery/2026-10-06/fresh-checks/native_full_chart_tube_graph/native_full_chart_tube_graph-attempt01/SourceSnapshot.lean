import Theorems.Thm_StickyKakeya4_native_full_chart_direction_bounds
import Theorems.Thm_StickyKakeya4_native_original_cell_chart_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeFullChartTubeGraph
open Classical StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeCoarseRepresentativeGeometry
open NativeCoarseCellSource NativeCoarseDirectionThinning NativeFullCoarseShadow
open NativeUnitParentNormalization NativeContractedUnitParent

/-- The actual center-height0 unit segment gives |time|≤1 after its small
Euclidean tube thickening. Graph residual6Delta is the existing native bound. -/
theorem centered_tube_bounds (l : MarkedLine) (hl : IsValidLine l)
    (hdir : (1/2:ℝ) ≤ direction l (3:Fin 4)) (hcenter : wzMarkedCenterHeight l=0)
    (Delta : ℝ) (hd : 0 < Delta) (hsmall : Delta ≤ 1/4)
    (x : E4) (hx : x∈markedUnitTube l Delta) :
    |x (3:Fin 4)| ≤ 1 ∧
      ∀ j : Fin 3, |x j.castSucc-intercept l j-slope l j*x (3:Fin 4)| ≤ 8*Delta := by
  have hdn : direction l (3:Fin 4) ≠ 0 := by linarith
  have hcommon : wzGraphTime l 0-mark l∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ) := by
    rw [wzGraphTime_sub_mark_eq _ _ hdn, hcenter]
    norm_num
  have hres := (tube_point_bounds l hl hdir hd hcommon hx).2
  refine ⟨?_, fun j => (hres j).trans (by linarith)⟩
  obtain ⟨t, ht, hdist⟩ := exists_rawFrontParam_dist_lt_of_infDist_le l x hx hd
  have htAbs : |t| ≤ 1/2 := abs_le.mpr ⟨ht.1, ht.2⟩
  have hu : |direction l (3:Fin 4)| ≤ 1 := (coordinate_abs_le_norm _ _).trans_eq hl.1
  have hformula : rawFrontParam (l,t) (3:Fin 4) = t*direction l (3:Fin 4) := by
    have hc := wzMarkedCenterHeight_eq l
    rw [hcenter] at hc
    simp only [rawFrontParam, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    nlinarith only [hc]
  have hfront : |rawFrontParam (l,t) (3:Fin 4)| ≤ 1/2 := by
    rw [hformula, abs_mul]
    exact (mul_le_mul htAbs hu (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hclose : |x (3:Fin 4)-rawFrontParam (l,t) (3:Fin 4)| ≤ 2*Delta :=
    (show _ ≤ dist x (rawFrontParam (l,t)) by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le x (rawFrontParam (l,t)) (3:Fin 4)).trans
      (by linarith only [hdist])
  have htri := abs_sub_le (x (3:Fin 4)) (rawFrontParam (l,t) (3:Fin 4)) 0
  simp only [sub_zero] at htri
  linarith

/-- Whole tubes of the SAME final full family lie in graph tubes of
analytic width8Delta. The source's actual Euclidean thickness staysDelta. -/
theorem full_source_graph_bounds {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level b : ℕ) (hb : 8 ≤ b) (E : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀ x : E4, O x (3:Fin 4)=x (3:Fin 4))
    (i : Fin (R.image (parentLabel D a (2^b))).card) (x : E4) :
    let l := MarkedIsometricChart.line O 0 ((fullSource h R a level b E).line i)
    x∈markedUnitTube l (64/((2^b:ℕ):ℝ)) →
      |x (3:Fin 4)| ≤ 1 ∧
        ∀ j : Fin 3, |x j.castSucc-intercept l j-slope l j*x (3:Fin 4)| ≤
          8*(64/((2^b:ℕ):ℝ)) := by
  intro l hx
  let t := representative h R a (2^b) (parentIndex (R.image (parentLabel D a (2^b))) i)
  have ht := zero_parent_valid_slab h a t
  have hvalid : IsValidLine l := MarkedIsometricChart.valid_line O 0 _ ht.1
  have hdir : (1/2:ℝ) ≤ direction l (3:Fin 4) := by
    change (1/2:ℝ) ≤ O (direction (NativeContractedUnitParent.line D a (0,0) t)) (3:Fin 4)
    rw [hO]
    exact ht.2.1
  have hold : wzMarkedCenterHeight (NativeContractedUnitParent.line D a (0,0) t)=0 := by
    rw [NativeContractedUnitParent.line, contractLine_center_height, newLine,
      NativeGraphMarkedLine.center_height, zero_div]
  have hcenter : wzMarkedCenterHeight l=0 := by
    change rawFrontParam (MarkedIsometricChart.line O 0
      (NativeContractedUnitParent.line D a (0,0) t),0) (3:Fin 4)=0
    rw [MarkedIsometricChart.raw_front_readback]
    simpa only [MarkedIsometricChart.point, sub_zero, hO] using hold
  have hpow : (256:ℝ) ≤ ((2^b:ℕ):ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hb
  have hsmall : 64/((2^b:ℕ):ℝ) ≤ 1/4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hpow]
  exact centered_tube_bounds l hvalid hdir hcenter _ (by positivity) hsmall x hx

end NativeFullChartTubeGraph
