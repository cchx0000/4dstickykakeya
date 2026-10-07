import Theorems.Thm_StickyKakeya4_native_rank_plane_tube_support

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeLocalDirectionTubeSupport
open Classical StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeOriginalParentPhysicalData
open NativeDirectionRankDichotomy NativeRankPlaneTubeSupport

/-- Localizing the genuine old tube in height improves angular error r to
r times its actual height length. The original marked times are retained. -/
theorem tube_local_displacement_near_plane {n : ℕ} (D : FiniteScaleSource n) (i : Fin n)
    (hc : direction (D.line i) (3:Fin 4) ≠ 0)
    (P : Submodule ℝ E4) {delta r length : ℝ}
    (hd : 0 < delta) (hr : 0 < r) (hl : 0 ≤ length)
    (hnear : Metric.infDist (slopeVector D i) (P:Set E4) ≤ r)
    {x y : E4} (hx : x∈markedUnitTube (D.line i) delta)
    (hy : y∈markedUnitTube (D.line i) delta)
    (hheight : |y (3:Fin 4)-x (3:Fin 4)| ≤ length) :
    Metric.infDist (y-x) (P:Set E4) ≤ 4*delta+2*r*(length+4*delta) := by
  obtain ⟨u,hu,hvu⟩ := (Metric.infDist_lt_iff
    (show (P:Set E4).Nonempty from ⟨0,P.zero_mem⟩)).mp
    (hnear.trans_lt (by linarith : r<2*r))
  obtain ⟨s,_hs,hxs⟩ := exists_rawFrontParam_dist_lt_of_infDist_le (D.line i) x hx hd
  obtain ⟨t,_ht,hyt⟩ := exists_rawFrontParam_dist_lt_of_infDist_le (D.line i) y hy hd
  let c := (t-s)*direction (D.line i) (3:Fin 4)
  have hraw : rawFrontParam (D.line i,t)-rawFrontParam (D.line i,s) = c • slopeVector D i := by
    have he : rawFrontParam (D.line i,t)-rawFrontParam (D.line i,s) =
        (t-s) • direction (D.line i) := by
      ext j
      simp only [rawFrontParam,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
      ring
    rw [he,direction_eq_height_slopeVector D i hc,smul_smul]
  have hleft : ‖y-rawFrontParam (D.line i,t)‖ ≤ 2*delta := by
    rw [←dist_eq_norm]
    simpa only [two_mul] using hyt.le
  have hright : ‖rawFrontParam (D.line i,s)-x‖ ≤ 2*delta := by
    rw [←dist_eq_norm,dist_comm]
    simpa only [two_mul] using hxs.le
  have hycoord : |rawFrontParam (D.line i,t) (3:Fin 4)-y (3:Fin 4)| ≤ 2*delta := by
    rw [abs_sub_comm]
    exact (coordinate_abs_le_norm (y-rawFrontParam (D.line i,t)) (3:Fin 4)).trans hleft
  have hxcoord : |x (3:Fin 4)-rawFrontParam (D.line i,s) (3:Fin 4)| ≤ 2*delta := by
    rw [abs_sub_comm]
    exact (coordinate_abs_le_norm (rawFrontParam (D.line i,s)-x) (3:Fin 4)).trans hright
  have hc3 : rawFrontParam (D.line i,t) (3:Fin 4)-
      rawFrontParam (D.line i,s) (3:Fin 4)=c := by
    have hh := congrArg (fun z : E4 => z (3:Fin 4)) hraw
    simpa only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,slopeVector_last,mul_one] using hh
  have hcabs : |c| ≤ length+4*delta := by
    calc
      |c| = |(rawFrontParam (D.line i,t) (3:Fin 4)-y (3:Fin 4))+
          (y (3:Fin 4)-x (3:Fin 4))+
          (x (3:Fin 4)-rawFrontParam (D.line i,s) (3:Fin 4))| := by
        congr 1
        linarith only [hc3]
      _ ≤ |rawFrontParam (D.line i,t) (3:Fin 4)-y (3:Fin 4)|+
          |y (3:Fin 4)-x (3:Fin 4)|+
          |x (3:Fin 4)-rawFrontParam (D.line i,s) (3:Fin 4)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (2*delta)+length+(2*delta) := add_le_add (add_le_add hycoord hheight) hxcoord
      _ = _ := by ring
  have hidentity : (y-x)-c•u =
      (y-rawFrontParam (D.line i,t))+(rawFrontParam (D.line i,s)-x)+c•(slopeVector D i-u) := by
    rw [smul_sub,←hraw]
    abel
  have hvector : ‖slopeVector D i-u‖ ≤ 2*r := by rw [←dist_eq_norm]; exact hvu.le
  have hmul : ‖c•(slopeVector D i-u)‖ ≤ 2*r*(length+4*delta) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hcabs hvector (norm_nonneg _) (by positivity)).trans_eq (by ring)
  apply (Metric.infDist_le_dist_of_mem (P.smul_mem c hu)).trans
  rw [dist_eq_norm,hidentity]
  calc
    _ ≤ (‖y-rawFrontParam (D.line i,t)‖+‖rawFrontParam (D.line i,s)-x‖)+
        ‖c•(slopeVector D i-u)‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (2*delta+2*delta)+2*r*(length+4*delta) := add_le_add (add_le_add hleft hright) hmul
    _ = _ := by ring

/-- An old incident tube, within height Delta of its literal incident-cell
center, lies in a radius 14 Delta^2 affine packet when its direction is
Delta-close to the fixed plane. No old error is replaced by a finer error. -/
theorem original_local_quadratic_packet {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    {i : Fin n} {k : Index} (hik : (i,k)∈incidences original)
    (P : Submodule ℝ E4) {Delta : ℝ} (hDelta : 0 < Delta) (hDelta1 : Delta ≤ 1)
    (hscale : D.thickness ≤ Delta^2)
    (hnear : Metric.infDist (slopeVector D i) (P:Set E4) ≤ Delta)
    {y : E4} (hy : y∈markedUnitTube (D.line i) D.thickness)
    (hheight : |y (3:Fin 4)-cellCenter (mesh D) k (3:Fin 4)| ≤ Delta) :
    Metric.infDist (y-cellCenter (mesh D) k) (P:Set E4) ≤ 14*Delta^2 := by
  have hx := original_cell_in_tube h original horiginal hik
  have he : 2*mesh D=D.thickness := by unfold mesh; ring
  rw [he] at hx
  have hc : direction (D.line i) (3:Fin 4) ≠ 0 := by
    have hh := h.2.1.1 i
    linarith
  have hh := tube_local_displacement_near_plane D i hc P h.1.2.1 hDelta hDelta.le hnear hx hy hheight
  apply hh.trans
  have hprod : D.thickness*Delta ≤ D.thickness := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hDelta1 h.1.2.1.le
  nlinarith

end NativeLocalDirectionTubeSupport
