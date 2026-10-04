import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
import Theorems.Thm_StickyKakeya4_original_w_witness_counts
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace ActualPlanarTargetCover
open Classical NativeTangentGridCoarsening
open scoped BigOperators
theorem actual_target_grid_cover {W T : Type*} [DecidableEq T]
    (E : Finset W) (targets : Finset T) (output : W → ℝ × ℝ) (targetPoint : T → ℝ × ℝ)
    {mesh error : ℝ} (hmesh : 0 < mesh) (herror : 0 ≤ error)
    (htarget : ∀ e ∈ E, ∃ t ∈ targets, ‖output e-targetPoint t‖ ≤ error) :
    ((planarCells E output mesh).card : ℝ) ≤ (targets.card : ℝ)*(2*error/mesh+2)^2 := by
  let F := fun t => planarCells (E.filter (fun e => ‖output e-targetPoint t‖ ≤ error)) output mesh
  have hsub : planarCells E output mesh ⊆ targets.biUnion F := by
    intro k hk
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨t,ht,het⟩ := htarget e he
    exact Finset.mem_biUnion.mpr ⟨t,ht,Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨he,het⟩)⟩
  have hF : ∀ t ∈ targets, ((F t).card : ℝ) ≤ (2*error/mesh+2)^2 := by
    intro t _ht
    have hr : ∀ e ∈ E.filter (fun e => ‖output e-targetPoint t‖ ≤ error),
        ((targetPoint t).1-error ≤ (output e).1 ∧ (output e).1 ≤ (targetPoint t).1-error+2*error) ∧
        ((targetPoint t).2-error ≤ (output e).2 ∧ (output e).2 ≤ (targetPoint t).2-error+2*error) := by
      intro e he
      have hh := max_le_iff.mp (Finset.mem_filter.mp he).2
      have hx := abs_le.mp hh.1
      have hy := abs_le.mp hh.2
      simp only [Prod.fst_sub,Prod.snd_sub] at hx hy
      exact ⟨⟨by linarith [hx.1],by linarith [hx.2]⟩,⟨by linarith [hy.1],by linarith [hy.2]⟩⟩
    have hc := planar_rectangle_grid_card _ output hmesh (by positivity : 0 ≤ 2*error) (by positivity : 0 ≤ 2*error) hr
    simpa only [pow_two] using hc
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (OriginalWWitnessCounts.card_biUnion_le_real targets F (sq_nonneg _) (le_refl _) hF)
theorem retained_target_cover {W T A : Type*} [DecidableEq T]
    (E : Finset W) (targets : Finset T) (Aout : Finset A) (output : W → ℝ × ℝ) (targetPoint : T → ℝ × ℝ)
    {mesh error beta loss : ℝ} (hmesh : 0 < mesh) (herror : 0 ≤ error) (hbeta : 0 < beta)
    (htarget : ∀ e ∈ E, ∃ t ∈ targets, ‖output e-targetPoint t‖ ≤ error)
    (hretention : beta*(targets.card : ℝ) ≤ loss*(Aout.card : ℝ)) :
    ((planarCells E output mesh).card : ℝ) ≤ (loss/beta)*(2*error/mesh+2)^2*(Aout.card : ℝ) := by
  have hc := actual_target_grid_cover E targets output targetPoint hmesh herror htarget
  have hpop : (targets.card : ℝ) ≤ (loss/beta)*(Aout.card : ℝ) := by
    have hh : (targets.card : ℝ) ≤ loss*(Aout.card : ℝ)/beta := (le_div_iff₀ hbeta).mpr (by nlinarith only [hretention])
    convert hh using 1; ring
  calc
    _ ≤ (targets.card : ℝ)*(2*error/mesh+2)^2 := hc
    _ ≤ ((loss/beta)*(Aout.card : ℝ))*(2*error/mesh+2)^2 := mul_le_mul_of_nonneg_right hpop (sq_nonneg _)
    _ = _ := by ring
end ActualPlanarTargetCover
