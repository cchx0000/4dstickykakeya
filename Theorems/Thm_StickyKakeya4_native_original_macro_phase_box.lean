import Theorems.Thm_StickyKakeya4_native_original_phase_source_kt
import Theorems.Thm_StickyKakeya4_native_original_phase_bounds
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeOriginalMacroPhaseBox
open Classical NativeOriginalPhaseSourceKT NativeOriginalPhaseBounds OriginalWNormalizedPhase
open OriginalPhaseCellPopulation OriginalPhaseGridPopulation OriginalPhaseGridError
open OriginalPhaseWindowGraph NativeOriginalPhaseWindowGraph NativeOriginalPhaseWindowPopulation
open OriginalWCoreDynamics OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWGrainDrift
/-- Physical macro-cell membership controls the actual x-coordinate gap. -/
theorem same_physical_cell_x_gap {P : Type*} (height x : P → ℝ) (y : P → ℝ × ℝ)
    {q : ℝ} (hq : 0 < q) (p p0 : P) (hc : physicalCell q height x y p=physicalCell q height x y p0) :
    |x p-x p0| ≤ q := by
  have hf : ⌊x p/q⌋=⌊x p0/q⌋ := congrArg (fun c => c.2.1) hc
  have hl := (le_div_iff₀ hq).mp (Int.floor_le (x p/q))
  have hu := (div_lt_iff₀ hq).mp (Int.lt_floor_add_one (x p/q))
  have hl0 := (le_div_iff₀ hq).mp (Int.floor_le (x p0/q))
  have hu0 := (div_lt_iff₀ hq).mp (Int.lt_floor_add_one (x p0/q))
  rw [hf] at hl hu
  exact abs_le.mpr ⟨by linarith only [hl,hu0],by linarith only [hu,hl0]⟩
/-- The literal single macro xi witness gives the bounded normalized phase
 coordinates of the SAME original points, with the scheduled overshoot M. -/
theorem original_macro_phase_bound {P : Type*} (E : Finset P)
    (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    {q rho Lip C0 M : ℝ} (hq : 0 < q) (hrho : 0 < rho)
    (hLip : 1 ≤ Lip) (hC0 : 1 ≤ C0) (hM : 1 ≤ M) (hqscale : q ≤ M*rho)
    (hSource : OriginalXiLaw E height x y offset q C0)
    (p p0 : P) (hp : p ∈ E) (hp0 : p0 ∈ E)
    (hcell : physicalCell q height x y p=physicalCell q height x y p0) :
    ‖phaseCoordinates rho Lip (x p0) (offset p0) (x p) (offset p)‖ ≤ 2*C0*M := by
  have hC00 : 0 ≤ C0 := by linarith only [hC0]
  have hM0 : 0 ≤ M := by linarith only [hM]
  have hLip0 : 0 < Lip := by linarith only [hLip]
  have hq0 : physicalCell q height x y p0 ∈ physicalCells E q height x y := Finset.mem_image_of_mem _ hp0
  obtain ⟨center,_hcenter,hXi⟩ := hSource _ hq0
  have hx := same_physical_cell_x_gap height x y hq p p0 hcell
  have hxi : ‖offset p-offset p0‖ ≤ 2*C0*q := by
    calc
      _ = ‖(offset p-center)+(center-offset p0)‖ := by congr 1; abel
      _ ≤ ‖offset p-center‖+‖center-offset p0‖ := norm_add_le _ _
      _ ≤ C0*q+C0*q := add_le_add (hXi p hp hcell) (by simpa only [norm_sub_rev] using hXi p0 hp0 rfl)
      _ = _ := by ring
  apply max_le
  · change |(x p-x p0)/rho| ≤ 2*C0*M
    rw [abs_div,abs_of_pos hrho]
    have hh : |x p-x p0|/rho ≤ M := (div_le_iff₀ hrho).mpr (hx.trans hqscale)
    have hc := mul_nonneg hM0 (sub_nonneg.mpr hC0)
    nlinarith only [hh,hc,hM0]
  · change ‖-((Lip*rho)⁻¹) • (offset p-offset p0)‖ ≤ 2*C0*M
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (inv_pos.mpr (mul_pos hLip0 hrho))]
    rw [mul_comm,← div_eq_mul_inv]
    apply (div_le_iff₀ (mul_pos hLip0 hrho)).mpr
    have hh := mul_le_mul_of_nonneg_left hqscale (show 0 ≤ 2*C0 by positivity)
    have hl := mul_le_mul_of_nonneg_right hLip (show 0 ≤ 2*C0*M*rho by positivity)
    nlinarith only [hxi,hh,hl]
/-- The actual expanded phase image lies in the unit box after the explicit
 common scaling S0=4*C0*M. No boundedness certificate for A is assumed. -/
theorem actual_window_source_box {P T : Type*} [DecidableEq P] [DecidableEq T]
    (E : Finset P) (I : Finset (P × T)) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (hOriginal : TwoTubePathCollisionCount.points I ⊆ E)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height) (z : ℝ) (k : GrainLabel)
    (p0 : P) (hp0 : p0 ∈ E)
    {q rho Lip C0 M mesh width : ℝ} (hq : 0 < q) (hrho : 0 < rho)
    (hLip : 1 ≤ Lip) (hC0 : 1 ≤ C0) (hM : 1 ≤ M) (hqscale : q ≤ M*rho)
    (hSource : OriginalXiLaw E height x y offset q C0)
    (hroot : ∀ p ∈ TwoTubePathCollisionCount.points I,
      physicalCell q height x y p=physicalCell q height x y p0)
    (hmesh : 0 < mesh) (hmesh1 : mesh ≤ 1) :
    ∀ a ∈ expanded (heightSlice S z)
      (fun s => grainCell width (grainCoordinate height x y F (rep I height S hSV s)))
      (fun s => phaseLabel (mesh*rho) (mesh*Lip*rho) (x p0) (offset p0) x offset (rep I height S hSV s)) k,
      ‖gridPoint (mesh/(4*C0*M)) a‖ ≤ 1 := by
  intro a ha
  rw [expanded_eq_phase_image] at ha
  obtain ⟨s,_hs,hsa⟩ := Finset.mem_image.mp ha
  have hpI := Finset.mem_image_of_mem Prod.fst (rep_spec I height S hSV s).1
  have hbound := original_macro_phase_bound E height x y offset hq hrho hLip hC0 hM hqscale hSource
    (rep I height S hSV s) p0 (hOriginal hpI) hp0 (hroot _ hpI)
  have herr := original_phase_grid_error hmesh rho Lip (x p0) (offset p0) x offset (rep I height S hSV s)
  have hgrid : ‖gridPoint mesh a‖ ≤ mesh+2*C0*M := by
    rw [← hsa]
    exact (norm_le_norm_sub_add _ _).trans (add_le_add herr hbound)
  have hscale : 0 < 4*C0*M := by positivity
  have hG : 1 ≤ C0*M := by nlinarith only [hC0,hM]
  rw [← gridPoint_rescale mesh (4*C0*M) a,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hscale)]
  rw [mul_comm,← div_eq_mul_inv]
  apply (div_le_one hscale).mpr
  nlinarith only [hgrid,hmesh1,hG]
end NativeOriginalMacroPhaseBox
