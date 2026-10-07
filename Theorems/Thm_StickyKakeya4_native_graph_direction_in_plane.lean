import Theorems.Thm_StickyKakeya4_native_preserved_node_planes

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeGraphDirectionInPlane
open Classical StickyKakeya4

/-- Projecting an actual graph direction and normalizing its nonzero height
constructs a genuine graph direction INSIDE the chosen plane. -/
theorem exists_near_graph_direction (P : Submodule ℝ E4) (w : E4) (epsilon : ℝ)
    (hw : w (3:Fin 4)=1) (hwn : ‖w‖ ≤ 2) (he : epsilon ≤ 1/2)
    (hnear : Metric.infDist w (P:Set E4) ≤ epsilon) :
    ∃v∈P,v (3:Fin 4)=1 ∧ dist v w ≤ 5*epsilon ∧ ‖v‖ ≤ 2+5*epsilon := by
  let y := P.starProjection w
  have hyP : y∈P := (P.orthogonalProjectionOnto w).property
  have hyr : ‖w-y‖ ≤ epsilon := by
    rw [NativeEqualRankPlaneTransfer.projection_residual_eq_infDist]
    exact hnear
  have he0 : 0 ≤ epsilon := (norm_nonneg _).trans hyr
  have hc : |1-y (3:Fin 4)| ≤ epsilon := by
    have hh := PiLp.norm_apply_le (w-y) (3:Fin 4)
    have hh' : |1-y (3:Fin 4)| ≤ ‖w-y‖ := by
      simpa only [PiLp.sub_apply,hw,Real.norm_eq_abs] using hh
    exact hh'.trans hyr
  have hyhalf : (1/2:ℝ) ≤ y (3:Fin 4) := by
    have hh := (abs_le.mp hc).2
    linarith only [hh,he]
  have hyp : 0 < y (3:Fin 4) := lt_of_lt_of_le (by norm_num) hyhalf
  have hyn : ‖y‖ ≤ 2 := (P.norm_orthogonalProjectionOnto_apply_le w).trans hwn
  let v := (1/y (3:Fin 4)) • y
  have hvP : v∈P := P.smul_mem _ hyP
  have hvh : v (3:Fin 4)=1 := by
    change (1/y (3:Fin 4))*y (3:Fin 4)=1
    field_simp
  have hcoeff : |1/y (3:Fin 4)-1| ≤ 2*epsilon := by
    have hid : 1/y (3:Fin 4)-1=(1-y (3:Fin 4))/y (3:Fin 4) := by field_simp
    rw [hid,abs_div,abs_of_pos hyp]
    apply (div_le_iff₀ hyp).mpr
    nlinarith only [hc,hyhalf,he0]
  have hvy : dist v y ≤ 4*epsilon := by
    have hid : v-y=(1/y (3:Fin 4)-1) • y := by
      dsimp [v]
      rw [sub_smul,one_smul]
    rw [dist_eq_norm,hid,norm_smul,Real.norm_eq_abs]
    have hh := mul_le_mul hcoeff hyn (norm_nonneg _) (by positivity : 0 ≤ 2*epsilon)
    linarith only [hh]
  have hyv : dist y w ≤ epsilon := by simpa only [dist_eq_norm,norm_sub_rev] using hyr
  have hvw : dist v w ≤ 5*epsilon := by
    have hh := dist_triangle v y w
    linarith only [hh,hvy,hyv]
  have hvn : ‖v‖ ≤ 2+5*epsilon := by
    have hh : ‖v‖ ≤ dist v w+‖w‖ := by
      calc
        ‖v‖ = ‖(v-w)+w‖ := by rw [sub_add_cancel]
        _ ≤ ‖v-w‖+‖w‖ := norm_add_le _ _
        _ = dist v w+‖w‖ := by rw [dist_eq_norm]
    linarith only [hh,hvw,hwn]
  exact ⟨v,hvP,hvh,hvw,hvn⟩

end NativeGraphDirectionInPlane
