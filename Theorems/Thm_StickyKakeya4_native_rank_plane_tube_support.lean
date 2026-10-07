import Theorems.Thm_StickyKakeya4_native_direction_rank_dichotomy
import Theorems.Thm_StickyKakeya4_native_original_parent_physical_data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeRankPlaneTubeSupport
open Classical StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeOriginalParentPhysicalData NativeDirectionRankDichotomy

lemma direction_eq_height_slopeVector {n : ℕ} (D : FiniteScaleSource n) (i : Fin n)
    (hc : direction (D.line i) (3:Fin 4) ≠ 0) :
    direction (D.line i)=direction (D.line i) (3:Fin 4) • slopeVector D i := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [PiLp.smul_apply,smul_eq_mul,show (Fin.last 3:Fin 4)=3 by rfl,slopeVector_last,mul_one]
  · rw [PiLp.smul_apply,smul_eq_mul,slopeVector,ActualSlopeSource.heightPoint_castSucc]
    change direction (D.line i) j.castSucc = direction (D.line i) (3:Fin 4) *
      (direction (D.line i) j.castSucc / direction (D.line i) (3:Fin 4))
    field_simp

/-- Actual points of one original marked tube lie near the affine plane
through any other actual tube point whenever its graph direction lies near
P. The old marked-segment times are retained throughout. -/
theorem tube_displacement_near_plane {n : ℕ} (D : FiniteScaleSource n) (i : Fin n)
    (hv : IsValidLine (D.line i)) (hc : direction (D.line i) (3:Fin 4) ≠ 0)
    (P : Submodule ℝ E4) {delta r : ℝ} (hd : 0 < delta) (hr : 0 < r)
    (hnear : Metric.infDist (slopeVector D i) (P:Set E4) ≤ r)
    {x y : E4} (hx : x∈markedUnitTube (D.line i) delta)
    (hy : y∈markedUnitTube (D.line i) delta) :
    Metric.infDist (y-x) (P:Set E4) ≤ 4*delta+2*r := by
  obtain ⟨u,hu,hvu⟩ := (Metric.infDist_lt_iff (show (P:Set E4).Nonempty from ⟨0,P.zero_mem⟩)).mp
    (hnear.trans_lt (by linarith : r<2*r))
  obtain ⟨s,hs,hxs⟩ := exists_rawFrontParam_dist_lt_of_infDist_le (D.line i) x hx hd
  obtain ⟨t,ht,hyt⟩ := exists_rawFrontParam_dist_lt_of_infDist_le (D.line i) y hy hd
  let c := (t-s)*direction (D.line i) (3:Fin 4)
  have hgap : |t-s| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1,hs.2],by linarith [ht.2,hs.1]⟩
  have hdirection : |direction (D.line i) (3:Fin 4)| ≤ 1 := by
    simpa only [hv.1] using coordinate_abs_le_norm (direction (D.line i)) (3:Fin 4)
  have hcabs : |c| ≤ 1 := by
    dsimp [c]
    rw [abs_mul]
    exact (mul_le_mul hgap hdirection (abs_nonneg _) zero_le_one).trans_eq (by norm_num)
  have hraw : rawFrontParam (D.line i,t)-rawFrontParam (D.line i,s) = c • slopeVector D i := by
    have he : rawFrontParam (D.line i,t)-rawFrontParam (D.line i,s) =
        (t-s) • direction (D.line i) := by
      ext j
      simp only [rawFrontParam,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
      ring
    rw [he,direction_eq_height_slopeVector D i hc,smul_smul]
  have hidentity : (y-x)-c•u =
      (y-rawFrontParam (D.line i,t))+(rawFrontParam (D.line i,s)-x)+c•(slopeVector D i-u) := by
    rw [smul_sub,←hraw]
    abel
  have hleft : ‖y-rawFrontParam (D.line i,t)‖ ≤ 2*delta := by
    rw [←dist_eq_norm]
    simpa only [two_mul] using hyt.le
  have hright : ‖rawFrontParam (D.line i,s)-x‖ ≤ 2*delta := by
    rw [←dist_eq_norm,dist_comm]
    simpa only [two_mul] using hxs.le
  have hvector : ‖slopeVector D i-u‖ ≤ 2*r := by
    rw [←dist_eq_norm]
    exact hvu.le
  have hmul : ‖c•(slopeVector D i-u)‖ ≤ 2*r := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hcabs hvector (norm_nonneg _) zero_le_one).trans_eq (by ring)
  apply (Metric.infDist_le_dist_of_mem (P.smul_mem c hu)).trans
  rw [dist_eq_norm,hidentity]
  calc
    _ ≤ (‖y-rawFrontParam (D.line i,t)‖+‖rawFrontParam (D.line i,s)-x‖)+
        ‖c•(slopeVector D i-u)‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (2*delta+2*delta)+2*r := add_le_add (add_le_add hleft hright) hmul
    _ = _ := by ring

/-- The actual original incident-cell center anchors the affine plane; no
chosen unrelated center or new tube incidence is introduced. -/
theorem original_incident_tube_near_plane {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    {i : Fin n} {k : Index} (hik : (i,k)∈incidences original)
    (P : Submodule ℝ E4) {r : ℝ} (hr : 0 < r)
    (hnear : Metric.infDist (slopeVector D i) (P:Set E4) ≤ r) :
    ∀y∈markedUnitTube (D.line i) D.thickness,
      Metric.infDist (y-cellCenter (mesh D) k) (P:Set E4) ≤ 4*D.thickness+2*r := by
  have hx := original_cell_in_tube h original horiginal hik
  have he : 2*mesh D=D.thickness := by unfold mesh; ring
  rw [he] at hx
  have hc : direction (D.line i) (3:Fin 4) ≠ 0 := by
    have hh := h.2.1.1 i
    linarith
  intro y hy
  exact tube_displacement_near_plane D i (h.1.2.2.2.2.1 i) hc P h.1.2.1 hr hnear hx hy

end NativeRankPlaneTubeSupport
