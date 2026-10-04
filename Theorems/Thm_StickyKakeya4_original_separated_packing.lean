import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
import Theorems.Thm_StickyKakeya4_actual_planar_rounded_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
namespace OriginalSeparatedPacking
open NativeTangentGridCoarsening ActualRoundedAdditiveEnergy ActualPlanarRoundedEnergy
open PlanarShiftedNearEnergy

/-- A literal separated original scalar carrier has a packing bound in every
centered interval, without an original grid-membership premise. -/
theorem scalar_ball_card (C : Finset ℝ) {delta R : ℝ} (hdelta : 0 < delta) (hR : 0 ≤ R)
    (hsep : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → delta ≤ |c-c'|) (z : ℝ) :
    ((C.filter (fun c => |c-z| ≤ R)).card : ℝ) ≤ 2*(R/delta)+2 := by
  let D := C.filter (fun c => |c-z| ≤ R)
  have hinj : Set.InjOn (fun c : ℝ => ⌊c/delta⌋) (↑D) := by
    apply (rounding_injOn C hdelta hsep).mono
    exact Finset.filter_subset _ _
  apply scalar_injective_grid_centered_card D id hdelta (show 0 ≤ R/delta by positivity) hinj
  intro c hc
  simpa only [id_eq, div_mul_cancel₀ R hdelta.ne'] using (Finset.mem_filter.mp hc).2

/-- Native-sup-norm planar separation gives an actual point packing count in
all centered boxes; the original finite points are not replaced by grid labels. -/
theorem planar_ball_card (A : Finset (ℝ × ℝ)) {delta R : ℝ}
    (hdelta : 0 < delta) (hR : 0 ≤ R)
    (hsep : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → delta ≤ ‖a-a'‖) (z : ℝ × ℝ) :
    ((A.filter (fun a => ‖a-z‖ ≤ R)).card : ℝ) ≤ (2*(R/delta)+2)^2 := by
  let D := A.filter (fun a => ‖a-z‖ ≤ R)
  have hsep' : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → (2*delta)/2 ≤ ‖a-a'‖ := by
    simpa only [mul_div_cancel_left₀ _ (show (2:ℝ) ≠ 0 by norm_num)] using hsep
  have hinj' := planar_rounding_injOn A (show 0 < 2*delta by positivity) hsep'
  have hinj : Set.InjOn (fun a : ℝ × ℝ => (⌊a.1/delta⌋,⌊a.2/delta⌋)) (↑D) := by
    intro a ha b hb hab
    apply hinj' (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
    simpa only [roundPoint,rounded,mul_div_cancel_left₀ _ (show (2:ℝ) ≠ 0 by norm_num)] using hab
  apply planar_injective_grid_centered_card D id z hdelta (show 0 ≤ R/delta by positivity) hinj
  intro a ha
  have hh := (Finset.mem_filter.mp ha).2
  simpa only [id_eq, div_mul_cancel₀ R hdelta.ne',Prod.norm_def,Prod.fst_sub,
    Prod.snd_sub,Real.norm_eq_abs,max_le_iff] using hh

/-- Real-valued fiber bound for an actual finite map. -/
lemma card_le_real_mul_image {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (P : Finset X) (f : X → Y) {M : ℝ}
    (hfib : ∀ y ∈ P.image f, ((P.filter (fun x => f x=y)).card : ℝ) ≤ M) :
    (P.card : ℝ) ≤ M*(P.image f).card := by
  calc
    _ = ∑ y ∈ P.image f, ((P.filter (fun x => f x=y)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image f P
    _ ≤ ∑ _y ∈ P.image f, M := Finset.sum_le_sum hfib
    _ = _ := by simp [mul_comm]
end OriginalSeparatedPacking
