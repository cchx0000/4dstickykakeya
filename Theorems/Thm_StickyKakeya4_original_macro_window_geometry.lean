import Theorems.Thm_StickyKakeya4_native_original_macro_printed_core
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace OriginalMacroWindowGeometry
open Classical Finset OriginalWeightedMacroSelection OriginalPhaseCellPopulation
open NativeOriginalMacroSourceDensity OriginalLiteralGrainProfiles
/-- The source quarter-scale choice supplies the honest phase radius,
 including the original scalar realization error. -/
theorem source_phase_radius {delta q K C0 : ℝ} (hd : 0 ≤ delta) (hq : 0 < q)
    (hC : 0 ≤ C0) (hCK : C0 ≤ K) (hsmall : K*q ≤ 1/8) (hq4 : 4*q ≤ 1)
    (hdq2 : delta ≤ q^2) :
    0 < q+C0*delta ∧ q ≤ q+C0*delta ∧ q+C0*delta ≤ 2*q ∧
      q+C0*delta ≤ 1 ∧ delta ≤ (q+C0*delta)^2 := by
  have hcq : C0*q ≤ 1/8 := (mul_le_mul_of_nonneg_right hCK hq.le).trans hsmall
  have hcd : C0*delta ≤ q/8 := by
    calc
      _ ≤ C0*q^2 := mul_le_mul_of_nonneg_left hdq2 hC
      _ = (C0*q)*q := by ring
      _ ≤ (1/8)*q := mul_le_mul_of_nonneg_right hcq hq.le
      _ = _ := by ring
  have hnon : 0 ≤ C0*delta := mul_nonneg hC hd
  refine ⟨by linarith,by linarith,by linarith,by linarith,?_⟩
  nlinarith
variable {P : Type*}
/-- Every height in the whole selected macro-cell uses the literal original
 q-height bin. Hence its diameter and slope cluster follow from the source. -/
theorem original_macro_height_geometry (E : Finset P) (height x : P → ℝ)
    (y : P → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (k : ℤ × (ℤ × (ℤ × ℤ))) {q rho L : ℝ} (hq : 0 < q) (hqr : q ≤ rho) (hL : 0 ≤ L)
    (hMat : ∀ z ∈ E.image height, |(F z 1).1| ≤ 1 ∧ |(F z 1).2| ≤ 1)
    (hosc : ∀ z ∈ E.image height, ∀ w ∈ E.image height,
      ⌊z/q⌋=⌊w/q⌋ → ‖F z-F w‖ ≤ L*q) :
    let Z := localHeights E (physicalCell q height x y) height k
    (∀ z ∈ Z, ‖F z‖ ≤ 1) ∧
      (∀ z ∈ Z, ∀ w ∈ Z, ‖F z-F w‖ ≤ L*rho) ∧
      (∀ z ∈ Z, ∀ w ∈ Z, |z-w| ≤ rho) := by
  let Z := localHeights E (physicalCell q height x y) height k
  have hZE : Z ⊆ E.image height := image_subset_image (filter_subset _ _)
  have hbin : ∀ z ∈ Z, ⌊z/q⌋=k.1 := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hz
    exact congrArg Prod.fst (mem_filter.mp hp).2
  refine ⟨?_,?_,?_⟩
  · intro z hz
    exact OriginalLiteralMacroDensity.matrix_entry_operator_bound (F z) (hMat z (hZE hz)).1 (hMat z (hZE hz)).2
  · intro z hz w hw
    exact (hosc z (hZE hz) w (hZE hw) ((hbin z hz).trans (hbin w hw).symm)).trans
      (mul_le_mul_of_nonneg_left hqr hL)
  · intro z hz w hw
    exact (SpineColumnCounting.same_floor_scaled_close hq ((hbin z hz).trans (hbin w hw).symm)).le.trans hqr
/-- Actual scalar slopes are bounded using the unchanged original Phi and
 its honest reference error. -/
theorem original_slope_bound {T : Type*} (tubes : Finset T) (u angle : T → ℝ)
    (Phi : Finset ℝ) {rho : ℝ} (hr : rho ≤ 1)
    (hbox : ∀ a ∈ Phi, |a| ≤ 1)
    (hnear : ∀ t ∈ tubes, angle t ∈ Phi ∧ |u t-angle t| ≤ rho) :
    ∀ t ∈ tubes, ‖u t‖ ≤ 2 := by
  intro t ht
  have hn := hnear t ht
  have ha := hbox _ hn.1
  rw [Real.norm_eq_abs]
  have hh : |u t| ≤ |u t-angle t|+|angle t| := by
    simpa only [sub_add_cancel] using abs_add_le (u t-angle t) (angle t)
  linarith only [hh,hn.2,ha,hr]
end OriginalMacroWindowGeometry
