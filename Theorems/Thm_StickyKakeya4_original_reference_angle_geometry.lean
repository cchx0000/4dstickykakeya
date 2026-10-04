import Theorems.Thm_StickyKakeya4_original_reference_angle_selection
import Theorems.Thm_StickyKakeya4_original_w_grain_drift
import Theorems.Thm_StickyKakeya4_original_w_normalized_phase
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalReferenceAngleGeometry
open Classical OriginalWWitnessCounts OriginalWCoreDynamics OriginalWCoarseEscapeMenus
open OriginalWPhysicalDisplacement OriginalWGrainDrift OriginalWJointPhase OriginalWNormalizedPhase
variable {P T K A : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq K] [DecidableEq A]
theorem constructed_reference_grain_drift
    (I : Finset (P × T)) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (baseU u : T → ℝ) (baseV v : T → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (Z : Finset ℝ) (cell : T → K) (angle : T → A) (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height)
    {Aop B IncErr DirErr Lip delta rho : ℝ}
    (hA : 0 ≤ Aop) (hB : 0 ≤ B) (hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr) (hLip : 0 ≤ Lip)
    (hd : 0 ≤ delta) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (hdscale : delta ≤ rho^2)
    (hincU : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height x baseU u p t‖ ≤ IncErr*delta)
    (hincV : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height y baseV v p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (u t)‖ ≤ DirErr*delta)
    (hu : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ‖u t‖ ≤ B)
    (hF : ∀ z ∈ Z, ‖F z‖ ≤ Aop) (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ Lip*rho)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho) (hcell : ∀ s t, cell s=cell t → ‖u s-u t‖ ≤ rho)
    (state : Core S) (g : (ℝ × ℝ) × (A × A)) (hg : g ∈ M I height cell angle S state) :
    ‖grainCoordinate height x y F (rep I height S hSV (next I height cell angle S state g))-
      grainCoordinate height x y F (rep I height S hSV state)‖ ≤
      ((4*B+1)*Lip+(12+4*Aop)*max DirErr (2*IncErr))*rho^2 := by
  obtain ⟨_hn,w,hw,hl,hr,_hm⟩ := next_spec I height cell angle S state g hg
  let target := next I height cell angle S state g
  have hlt : w.1.tube₂=state.val.2 := congrArg Prod.snd hl
  have hrt : w.2.tube₂=target.val.2 := congrArg Prod.snd hr
  have hp := rep_spec I height S hSV state
  have hq := rep_spec I height S hSV target
  apply original_witness_grain_drift I height cell x y offset baseU u baseV v F Z
    hA hB hInc hDir hLip hd hrho hrho1 hdscale hincU hincV hdir hu hF hcluster hheight hdiam hcell
    w hw (rep I height S hSV state) (rep I height S hSV target)
  · simpa only [hlt] using hp.1
  · simpa only [hrt] using hq.1
  · exact hp.2.trans (congrArg Prod.fst hl).symm
  · exact hq.2.trans (congrArg Prod.fst hr).symm
theorem reference_original_normalized_phase
    (I : Finset (P × T)) (height x : P → ℝ) (base u angle : T → ℝ) (cell : T → K)
    (offset : P → ℝ × ℝ) (v : T → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (Z : Finset ℝ)
    (x₀ z₀ : ℝ) (xi₀ f₀ : ℝ × ℝ) {delta rho IncErr DirErr Lip : ℝ}
    (hrho : 0 < rho) (hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr) (hLip : 1 ≤ Lip) (hdelta : delta ≤ rho^2)
    (hinc : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height x base u p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (u t)‖ ≤ DirErr*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho) (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ Lip*rho)
    (hangle : ∀ t ∈ TwoTubePathCollisionCount.tubes I, |u t-angle t| ≤ rho)
    (hcell : ∀ s t, cell s=cell t → |u s-u t| ≤ rho)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height cell)
    (p₁ p₂ : P) (hp₁ : (p₁,w.1.tube₂) ∈ I) (hp₂ : (p₂,w.2.tube₂) ∈ I)
    (hz₁ : height p₁=height w.1.point₂) (hz₂ : height p₂=height w.2.point₂) :
    ‖phaseCoordinates rho Lip x₀ xi₀ (x p₂) (offset p₂)-phaseCoordinates rho Lip x₀ xi₀ (x p₁) (offset p₁)-
      (angle w.2.tube₁-angle w.1.tube₁) •
        (graphCoordinates rho Lip z₀ f₀ (height w.1.point₁) (F (height w.1.point₁))-
          graphCoordinates rho Lip z₀ f₀ (height w.1.point₀) (F (height w.1.point₀)))‖ ≤
      max (3+12*IncErr) (3+8*DirErr)*rho := by
  have hwc := witness_conditions I height cell hw
  have hp := (TwoTubePathCollisionCount.mem_paths I w.1).mp hwc.1
  have hq := (TwoTubePathCollisionCount.mem_paths I w.2).mp hwc.2.1
  have h₀ := hheight _ (Finset.mem_image_of_mem Prod.fst hp.1)
  have h₁ := hheight _ (Finset.mem_image_of_mem Prod.fst hp.2.1)
  have h₂ := hheight _ (Finset.mem_image_of_mem Prod.fst hp.2.2.2)
  have hu₁ := hangle _ (Finset.mem_image_of_mem Prod.snd hp.1)
  have hu₂ := hangle _ (Finset.mem_image_of_mem Prod.snd hq.1)
  have hc := hcell _ _ hwc.2.2.2.2.2
  have hx := fixed_representative_displacement I height cell x base u angle hrho.le hinc w hw
    p₁ p₂ hp₁ hp₂ hz₁ hz₂ (hdiam _ h₁ _ h₀) (hdiam _ h₂ _ h₁) hu₁ hu₂ hc
  have hxi := original_coarse_offset_displacement I height cell offset u angle v F hrho.le
    (show 0 ≤ Lip by linarith) hdir w hw p₁ p₂ hp₁ hp₂ hz₁ hz₂
    (hcluster _ h₀ _ h₁) (hcluster _ h₁ _ h₂) hu₁ hu₂ hc
  apply normalized_phase_error rho Lip x₀ z₀ (x p₁) (x p₂) (height w.1.point₀) (height w.1.point₁)
    (angle w.2.tube₁-angle w.1.tube₁) IncErr DirErr xi₀ (offset p₁) (offset p₂) f₀
    (F (height w.1.point₀)) (F (height w.1.point₁)) hrho hLip hDir
  · have hh := mul_le_mul_of_nonneg_left hdelta (show 0 ≤ 12*IncErr by positivity)
    change |x p₂-x p₁-(height w.1.point₁-height w.1.point₀)*(angle w.2.tube₁-angle w.1.tube₁)| ≤ _
    change |x p₂-x p₁-(height w.1.point₁-height w.1.point₀)*(angle w.2.tube₁-angle w.1.tube₁)| ≤ _ at hx
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hdelta (show 0 ≤ 8*DirErr by positivity)
    nlinarith
end OriginalReferenceAngleGeometry
