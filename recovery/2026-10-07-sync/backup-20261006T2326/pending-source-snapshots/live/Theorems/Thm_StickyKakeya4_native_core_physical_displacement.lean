import Theorems.Thm_StickyKakeya4_original_w_physical_displacement
import Theorems.Thm_StickyKakeya4_original_w_core_dynamics

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeCorePhysicalDisplacement
open Classical OriginalWWitnessCounts OriginalWPhysicalDisplacement OriginalWCoreDynamics

variable {P T K A V : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq K]
  [DecidableEq A] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The physical endpoint displacement uses the actual bounded tube slopes.
No angular clustering or field Lipschitz estimate is required for this bound. -/
theorem witness_representative_bound
    (I : Finset (P × T)) (height : P → ℝ) (cell : T → K)
    (position : P → V) (base slope : T → V) (Z : Finset ℝ)
    {epsilon rho B : ℝ} (hrho : 0 ≤ rho)
    (hinc : ∀p t, (p,t)∈I → ‖incidenceResidual height position base slope p t‖ ≤ epsilon)
    (hslope : ∀t∈TwoTubePathCollisionCount.tubes I, ‖slope t‖ ≤ B)
    (hheight : ∀p∈TwoTubePathCollisionCount.points I, height p∈Z)
    (hdiam : ∀s∈Z, ∀t∈Z, |s-t| ≤ rho)
    (w : Path P T × Path P T) (hw : w∈witnesses I height cell)
    (p₁ p₂ : P) (hp₁ : (p₁,w.1.tube₂)∈I) (hp₂ : (p₂,w.2.tube₂)∈I)
    (hz₁ : height p₁=height w.1.point₂) (hz₂ : height p₂=height w.2.point₂) :
    ‖position p₂-position p₁‖ ≤ 4*B*rho+12*epsilon := by
  obtain ⟨ha,hb,_hstart,_hmiddle,_hend,_hcell⟩ := witness_conditions I height cell hw
  obtain ⟨ha0,ha1,ha2,ha3⟩ := (TwoTubePathCollisionCount.mem_paths I w.1).mp ha
  obtain ⟨hb0,_hb1,hb2,hb3⟩ := (TwoTubePathCollisionCount.mem_paths I w.2).mp hb
  have hd1 : ‖slope w.2.tube₁-slope w.1.tube₁‖ ≤ 2*B :=
    (norm_sub_le _ _).trans (by linarith only [
      hslope _ (Finset.mem_image_of_mem Prod.snd hb0),
      hslope _ (Finset.mem_image_of_mem Prod.snd ha0)])
  have hd2 : ‖slope w.2.tube₂-slope w.1.tube₂‖ ≤ 2*B :=
    (norm_sub_le _ _).trans (by linarith only [
      hslope _ (Finset.mem_image_of_mem Prod.snd hb2),
      hslope _ (Finset.mem_image_of_mem Prod.snd ha2)])
  have ht0 := hheight _ (Finset.mem_image_of_mem Prod.fst ha0)
  have ht1 := hheight _ (Finset.mem_image_of_mem Prod.fst ha1)
  have ht2 := hheight _ (Finset.mem_image_of_mem Prod.fst ha3)
  have hterm1 : ‖(height w.1.point₁-height w.1.point₀) •
      (slope w.2.tube₁-slope w.1.tube₁)‖ ≤ rho*(2*B) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hdiam _ ht1 _ ht0) hd1 (norm_nonneg _) hrho
  have hterm2 : ‖(height w.1.point₂-height w.1.point₁) •
      (slope w.2.tube₂-slope w.1.tube₂)‖ ≤ rho*(2*B) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hdiam _ ht2 _ ht1) hd2 (norm_nonneg _) hrho
  have hres := witness_two_leg_residual I height cell position base slope hinc w hw
  have hmain : ‖position w.2.point₂-position w.1.point₂‖ ≤ 4*B*rho+8*epsilon := by
    let d₁ := (height w.1.point₁-height w.1.point₀) • (slope w.2.tube₁-slope w.1.tube₁)
    let d₂ := (height w.1.point₂-height w.1.point₁) • (slope w.2.tube₂-slope w.1.tube₂)
    have he : position w.2.point₂-position w.1.point₂ =
        ((position w.2.point₂-position w.1.point₂-d₁-d₂)+d₁)+d₂ := by abel
    rw [he]
    exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
      (by dsimp only [d₁,d₂]; linarith only [hres,hterm1,hterm2])
  have he1 := same_tube_same_height_error I height position base slope hinc ha3 hp₁ hz₁
  have he2 := same_tube_same_height_error I height position base slope hinc hb3 hp₂ hz₂
  have he : position p₂-position p₁ =
      ((position p₂-position w.2.point₂)+(position w.2.point₂-position w.1.point₂))-
        (position p₁-position w.1.point₂) := by abel
  rw [he]
  exact ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    (by linarith only [hmain,he1,he2])

/-- The bound applies to the already chosen core, representatives and
successor map. Every point in the argument remains an actual incidence of I. -/
theorem constructed_successor_bound
    (I : Finset (P × T)) (height : P → ℝ) (cell : T → K) (angle : T → A)
    (position : P → V) (base slope : T → V) (Z : Finset ℝ)
    (S : Finset (ℝ × T)) (hSV : S⊆OriginalWCoarseEscapeMenus.vertices I height)
    {epsilon rho B : ℝ} (hrho : 0 ≤ rho)
    (hinc : ∀p t, (p,t)∈I → ‖incidenceResidual height position base slope p t‖ ≤ epsilon)
    (hslope : ∀t∈TwoTubePathCollisionCount.tubes I, ‖slope t‖ ≤ B)
    (hheight : ∀p∈TwoTubePathCollisionCount.points I, height p∈Z)
    (hdiam : ∀s∈Z, ∀t∈Z, |s-t| ≤ rho)
    (state : Core S) (g : (ℝ × ℝ) × (A × A)) (hg : g∈M I height cell angle S state) :
    ‖position (rep I height S hSV (next I height cell angle S state g))-
      position (rep I height S hSV state)‖ ≤ 4*B*rho+12*epsilon := by
  obtain ⟨_hn,w,hw,hl,hr,_hm⟩ := next_spec I height cell angle S state g hg
  let target := next I height cell angle S state g
  have hlt : w.1.tube₂=state.val.2 := congrArg Prod.snd hl
  have hrt : w.2.tube₂=target.val.2 := congrArg Prod.snd hr
  have hp := rep_spec I height S hSV state
  have hq := rep_spec I height S hSV target
  apply witness_representative_bound I height cell position base slope Z hrho
    hinc hslope hheight hdiam w hw (rep I height S hSV state) (rep I height S hSV target)
  · simpa only [hlt] using hp.1
  · simpa only [hrt] using hq.1
  · exact hp.2.trans (congrArg Prod.fst hl).symm
  · exact hq.2.trans (congrArg Prod.fst hr).symm

lemma configured_radius_bound {rho delta : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hd : delta ≤ rho^2) : 4*(2:ℝ)*rho+12*delta ≤ 20*rho := by
  nlinarith only [hrho,hrho1,hd]

end NativeCorePhysicalDisplacement
