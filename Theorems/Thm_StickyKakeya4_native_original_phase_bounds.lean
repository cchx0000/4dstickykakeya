import Theorems.Thm_StickyKakeya4_original_menu_bc_graph
import Theorems.Thm_StickyKakeya4_original_slope_graph_nonconcentration
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeOriginalPhaseBounds
open Classical OriginalWNormalizedPhase OriginalPhaseGridPopulation OriginalPhaseGridError
open OriginalPhaseWindowGraph NativeOriginalPhaseWindowGraph NativeOriginalPhaseWindowPopulation
open OriginalWCoreDynamics OriginalWCoarseEscapeMenus
theorem original_macro_phase_bound {rho Lip C x x₀ : ℝ}
    (hrho : 0 < rho) (hLip : 1 ≤ Lip) (hC : 0 ≤ C) (xi xi₀ field : ℝ × ℝ) (hx : |x-x₀| ≤ rho)
    (hxi : ‖xi-field‖ ≤ C*rho) (hxi₀ : ‖xi₀-field‖ ≤ C*rho) :
    ‖phaseCoordinates rho Lip x₀ xi₀ x xi‖ ≤ max 1 (2*C) := by
  have hLp : 0 < Lip := by linarith
  have hden : 0 < Lip*rho := mul_pos hLp hrho
  have hoff : ‖xi-xi₀‖ ≤ 2*C*rho := by
    calc
      _ = ‖(xi-field)+(field-xi₀)‖ := by congr 1; abel
      _ ≤ ‖xi-field‖+‖field-xi₀‖ := norm_add_le _ _
      _ ≤ C*rho+C*rho := add_le_add hxi (by simpa only [norm_sub_rev] using hxi₀)
      _ = _ := by ring
  apply max_le
  · change |(x-x₀)/rho| ≤ max 1 (2*C)
    rw [abs_div,abs_of_pos hrho]
    exact ((div_le_one hrho).mpr hx).trans (le_max_left _ _)
  · change ‖-((Lip*rho)⁻¹) • (xi-xi₀)‖ ≤ max 1 (2*C)
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (inv_pos.mpr hden)]
    have hh : (Lip*rho)⁻¹*‖xi-xi₀‖ ≤ 2*C := by
      rw [mul_comm,← div_eq_mul_inv]
      apply (div_le_iff₀ hden).mpr
      calc
        _ ≤ 2*C*rho := hoff
        _ ≤ 2*C*(Lip*rho) := by nlinarith [mul_nonneg hC (sub_nonneg.mpr hLip)]
    exact hh.trans (le_max_right _ _)
variable {P T : Type*} [DecidableEq P] [DecidableEq T]
theorem enlarged_original_phase_grid_bound
    (I : Finset (P × T)) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height)
    (z x₀ : ℝ) (xi₀ field : ℝ × ℝ) {rho Lip C mesh width : ℝ}
    (hrho : 0 < rho) (hLip : 1 ≤ Lip) (hC : 0 ≤ C) (hmesh : 0 < mesh)
    (hx : ∀ p ∈ TwoTubePathCollisionCount.points I, |x p-x₀| ≤ rho)
    (hfield : ∀ p ∈ TwoTubePathCollisionCount.points I, ‖offset p-field‖ ≤ C*rho)
    (hcenter : ‖xi₀-field‖ ≤ C*rho) (k : GrainLabel) (a : Label)
    (ha : a ∈ expanded (heightSlice S z)
      (fun s => grainCell width (OriginalWGrainDrift.grainCoordinate height x y F (rep I height S hSV s)))
      (fun s => phaseLabel (mesh*rho) (mesh*Lip*rho) x₀ xi₀ x offset (rep I height S hSV s)) k) :
    ‖gridPoint mesh a‖ ≤ mesh+max 1 (2*C) := by
  rw [expanded_eq_phase_image] at ha
  obtain ⟨s,_hs,hsa⟩ := Finset.mem_image.mp ha
  have hp := Finset.mem_image_of_mem Prod.fst (rep_spec I height S hSV s).1
  have herr := original_phase_grid_error hmesh rho Lip x₀ xi₀ x offset (rep I height S hSV s)
  have hbound := original_macro_phase_bound hrho hLip hC (offset (rep I height S hSV s)) xi₀ field (hx _ hp) (hfield _ hp) hcenter
  rw [← hsa]
  exact (norm_le_norm_sub_add _ _).trans (add_le_add herr hbound)
lemma gridPoint_rescale (mesh scale : ℝ) (a : Label) : scale⁻¹ • gridPoint mesh a=gridPoint (mesh/scale) a := by
  apply Prod.ext
  · change scale⁻¹*(mesh*(a.1:ℝ))=(mesh/scale)*(a.1:ℝ)
    ring
  · apply Prod.ext <;> change scale⁻¹*(mesh*(_ : ℝ))=(mesh/scale)*(_ : ℝ) <;> ring
theorem common_rescaling_relation (a target b anchor : Point) (c : ℝ) {scale error : ℝ}
    (hscale : 0 < scale) (hrel : ‖target-a-c • (b-anchor)‖ ≤ error) :
    ‖scale⁻¹ • target-scale⁻¹ • a-c • (scale⁻¹ • b-scale⁻¹ • anchor)‖ ≤ error/scale := by
  have hid : scale⁻¹ • target-scale⁻¹ • a-c • (scale⁻¹ • b-scale⁻¹ • anchor)=scale⁻¹ • (target-a-c • (b-anchor)) := by module
  rw [hid,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hscale)]
  simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left hrel (inv_pos.mpr hscale).le
end NativeOriginalPhaseBounds
