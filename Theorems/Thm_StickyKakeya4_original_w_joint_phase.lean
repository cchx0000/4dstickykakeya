import Theorems.Thm_StickyKakeya4_original_w_adapted_boxes

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalWJointPhase
open Classical OriginalWWitnessCounts OriginalWPhysicalDisplacement
open OriginalWAdaptedBoxes TwoWalkBoxComparison

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def terminalOffsetResidual (D : Data U V) (w : Walk U V) (xi : V) : V :=
  w.terminalV-xi-D.F₂ w.terminalU

/-- Exact W phase identity. The sign is F_start-F_middle, opposite to
 the printed Section21 display when x uses middle-start. -/
theorem offset_identity (D : Data U V) (xi₁ xi₂ : V) :
    xi₂-xi₁-(D.F₀-D.F₁) D.initialDu-(D.F₁-D.F₂) D.du =
      (D.initialResidual D.second-D.initialResidual D.first)-
      (D.middleResidual D.second-D.middleResidual D.first)+
      (D.terminalResidual D.second-D.terminalResidual D.first)-
      (terminalOffsetResidual D D.second xi₂-terminalOffsetResidual D D.first xi₁) := by
  simp only [Data.initialDu,Data.du,Data.initialResidual,Data.middleResidual,
    Data.terminalResidual,terminalOffsetResidual,sub_apply,map_sub]
  abel

/-- The eight errors in the exact phase identity are original same-point
 direction residuals; no endpoint phase displacement is assumed. -/
theorem offset_error_bound (D : Data U V) (xi₁ xi₂ : V) (e : ℝ)
    (h₀₁ : ‖D.initialResidual D.first‖ ≤ e)
    (h₀₂ : ‖D.initialResidual D.second‖ ≤ e)
    (h₁₁ : ‖D.middleResidual D.first‖ ≤ e)
    (h₁₂ : ‖D.middleResidual D.second‖ ≤ e)
    (h₂₁ : ‖D.terminalResidual D.first‖ ≤ e)
    (h₂₂ : ‖D.terminalResidual D.second‖ ≤ e)
    (h₃₁ : ‖terminalOffsetResidual D D.first xi₁‖ ≤ e)
    (h₃₂ : ‖terminalOffsetResidual D D.second xi₂‖ ≤ e) :
    ‖xi₂-xi₁-(D.F₀-D.F₁) D.initialDu-(D.F₁-D.F₂) D.du‖ ≤ 8*e := by
  have h₀ := Data.residual_difference_bound _ _ e h₀₂ h₀₁
  have h₁ := Data.residual_difference_bound _ _ e h₁₂ h₁₁
  have h₂ := Data.residual_difference_bound _ _ e h₂₂ h₂₁
  have h₃ := Data.residual_difference_bound _ _ e h₃₂ h₃₁
  rw [offset_identity]
  calc
    _ ≤ ((‖D.initialResidual D.second-D.initialResidual D.first‖+
        ‖D.middleResidual D.second-D.middleResidual D.first‖)+
        ‖D.terminalResidual D.second-D.terminalResidual D.first‖)+
        ‖terminalOffsetResidual D D.second xi₂-terminalOffsetResidual D D.first xi₁‖ :=
      (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ 8*e := by linarith

variable {P T K : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq K]

/-- Original terminal representatives inherit the exact signed phase relation
 directly from genuine W path pairs and the original direction graph at all
 eight actual incidences. Physical-coordinate incidence is not needed here. -/
theorem original_witness_offset_remainder (I : Finset (P × T)) (height : P → ℝ)
    (cell : T → K) (offset : P → V) (u : T → U) (v : T → V)
    (F : ℝ → U →L[ℝ] V) {e : ℝ}
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (u t)‖ ≤ e)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height cell)
    (p₁ p₂ : P) (hp₁ : (p₁,w.1.tube₂) ∈ I) (hp₂ : (p₂,w.2.tube₂) ∈ I)
    (hz₁ : height p₁=height w.1.point₂) (hz₂ : height p₂=height w.2.point₂) :
    ‖offset p₂-offset p₁-
      (F (height w.1.point₀)-F (height w.1.point₁)) (u w.2.tube₁-u w.1.tube₁)-
      (F (height w.1.point₁)-F (height w.1.point₂)) (u w.2.tube₂-u w.1.tube₂)‖ ≤ 8*e := by
  obtain ⟨ha,hb,hp,hzmid,hzend,_hc⟩ := witness_conditions I height cell hw
  obtain ⟨ha₀,ha₁,ha₂,_ha₃⟩ := (TwoTubePathCollisionCount.mem_paths I w.1).mp ha
  obtain ⟨hb₀,hb₁,hb₂,_hb₃⟩ := (TwoTubePathCollisionCount.mem_paths I w.2).mp hb
  let D := originalData height (fun _ : P => (0:U)) (fun _ : P => (0:V)) offset u v F w p₁ p₂
  apply offset_error_bound D (offset p₁) (offset p₂) e
  · exact hdir _ _ ha₀
  · simpa only [D,originalData,originalWalk,Data.initialResidual,hp] using hdir _ _ hb₀
  · exact hdir _ _ ha₁
  · simpa only [D,originalData,originalWalk,Data.middleResidual,hzmid] using hdir _ _ hb₁
  · exact hdir _ _ ha₂
  · simpa only [D,originalData,originalWalk,Data.terminalResidual,hzmid] using hdir _ _ hb₂
  · simpa only [D,originalData,originalWalk,terminalOffsetResidual,hz₁] using hdir _ _ hp₁
  · simpa only [D,originalData,originalWalk,terminalOffsetResidual,hz₂,hzend] using hdir _ _ hp₂

/-- Retain the genuine signed main term while replacing original tangent
 slopes by their deterministic coarse labels. The Lipschitz loss K remains
 explicit instead of being silently absorbed into a fixed box constant. -/
theorem original_coarse_offset_displacement (I : Finset (P × T)) (height : P → ℝ)
    (cell : T → K) (offset : P → V) (u coarse : T → U) (v : T → V)
    (F : ℝ → U →L[ℝ] V) {e rho Lip : ℝ} (hrho : 0 ≤ rho) (hLip : 0 ≤ Lip)
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (u t)‖ ≤ e)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height cell)
    (p₁ p₂ : P) (hp₁ : (p₁,w.1.tube₂) ∈ I) (hp₂ : (p₂,w.2.tube₂) ∈ I)
    (hz₁ : height p₁=height w.1.point₂) (hz₂ : height p₂=height w.2.point₂)
    (hF₀ : ‖F (height w.1.point₀)-F (height w.1.point₁)‖ ≤ Lip*rho)
    (hF₁ : ‖F (height w.1.point₁)-F (height w.1.point₂)‖ ≤ Lip*rho)
    (hcoarse₁ : ‖u w.1.tube₁-coarse w.1.tube₁‖ ≤ rho)
    (hcoarse₂ : ‖u w.2.tube₁-coarse w.2.tube₁‖ ≤ rho)
    (hterminal : ‖u w.2.tube₂-u w.1.tube₂‖ ≤ rho) :
    ‖offset p₂-offset p₁-(F (height w.1.point₀)-F (height w.1.point₁))
      (coarse w.2.tube₁-coarse w.1.tube₁)‖ ≤ 3*Lip*rho^2+8*e := by
  let A := F (height w.1.point₀)-F (height w.1.point₁)
  let B := F (height w.1.point₁)-F (height w.1.point₂)
  let d := u w.2.tube₁-u w.1.tube₁
  let c := coarse w.2.tube₁-coarse w.1.tube₁
  let t := u w.2.tube₂-u w.1.tube₂
  have he := original_witness_offset_remainder I height cell offset u v F hdir w hw p₁ p₂ hp₁ hp₂ hz₁ hz₂
  have hdiff := difference_approximation_bound _ _ _ _ hcoarse₁ hcoarse₂
  have hA : ‖A (d-c)‖ ≤ 2*Lip*rho^2 := by
    calc
      _ ≤ ‖A‖*‖d-c‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (Lip*rho)*(2*rho) := mul_le_mul hF₀ hdiff (norm_nonneg _) (mul_nonneg hLip hrho)
      _ = _ := by ring
  have hB : ‖B t‖ ≤ Lip*rho^2 := by
    calc
      _ ≤ ‖B‖*‖t‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (Lip*rho)*rho := mul_le_mul hF₁ hterminal (norm_nonneg _) (mul_nonneg hLip hrho)
      _ = _ := by ring
  calc
    _ = ‖(offset p₂-offset p₁-A d-B t)+A (d-c)+B t‖ := by
      congr 1
      dsimp [A,B,d,c,t]
      simp only [map_sub]
      abel
    _ ≤ (‖offset p₂-offset p₁-A d-B t‖+‖A (d-c)‖)+‖B t‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 3*Lip*rho^2+8*e := by dsimp [A,B,d,t] at *; linarith

/-- Native scalar joint displacement from literal original W incidences and
 the literal full three-coordinate terminal grid. K is the actual slope
 variation loss; it remains present in the normal phase error. -/
theorem scalar_native_joint_displacement
    (I : Finset (P × T)) (height : P → ℝ) (x : P → ℝ) (base : T → ℝ)
    (theta : T → Fin 3 → ℝ) (offset : P → V) (v : T → V)
    (F : ℝ → ℝ →L[ℝ] V) (Z : Finset ℝ)
    {delta rho q IncErr DirErr Lip : ℝ}
    (hrho : 0 < rho) (hq : 0 < q) (hqρ : q ≤ rho)
    (hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr) (hLip : 0 ≤ Lip) (hdelta : delta ≤ rho^2)
    (hinc : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height x base (scalarSlope theta) p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I →
      ‖v t-offset p-F (height p) (scalarSlope theta t)‖ ≤ DirErr*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ Lip*rho)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height (terminalGrid q theta))
    (p₁ p₂ : P) (hp₁ : (p₁,w.1.tube₂) ∈ I) (hp₂ : (p₂,w.2.tube₂) ∈ I)
    (hz₁ : height p₁=height w.1.point₂) (hz₂ : height p₂=height w.2.point₂) :
    let c := scalarDecode q (scalarAngle q theta w.2.tube₁)-scalarDecode q (scalarAngle q theta w.1.tube₁)
    ‖(x p₂-x p₁-(height w.1.point₁-height w.1.point₀)*c,
      offset p₂-offset p₁-(F (height w.1.point₀)-F (height w.1.point₁)) c)‖ ≤
      max (3+12*IncErr) (3*Lip+8*DirErr)*rho^2 := by
  have hx := scalar_native_witness_displacement I height x base theta Z hrho.le hq hqρ hInc hdelta
    hinc hheight hdiam w hw p₁ p₂ hp₁ hp₂ hz₁ hz₂
  have hwc := witness_conditions I height (terminalGrid q theta) hw
  have hp := (TwoTubePathCollisionCount.mem_paths I w.1).mp hwc.1
  have h₀ := hheight _ (Finset.mem_image_of_mem Prod.fst hp.1)
  have h₁ := hheight _ (Finset.mem_image_of_mem Prod.fst hp.2.1)
  have h₂ := hheight _ (Finset.mem_image_of_mem Prod.fst hp.2.2.2)
  have hc := hwc.2.2.2.2.2
  have hxi := original_coarse_offset_displacement I height (terminalGrid q theta) offset
    (scalarSlope theta) (fun t => scalarDecode q (scalarAngle q theta t)) v F hrho.le hLip
    hdir w hw p₁ p₂ hp₁ hp₂ hz₁ hz₂ (hcluster _ h₀ _ h₁) (hcluster _ h₁ _ h₂)
    ((scalar_grid_approximation q hq theta w.1.tube₁).trans hqρ)
    ((scalar_grid_approximation q hq theta w.2.tube₁).trans hqρ)
    ((scalar_terminal_grid_gap q hq theta w.2.tube₂ w.1.tube₂ hc).trans hqρ)
  have hxi' :
      ‖offset p₂-offset p₁-(F (height w.1.point₀)-F (height w.1.point₁))
        (scalarDecode q (scalarAngle q theta w.2.tube₁)-scalarDecode q (scalarAngle q theta w.1.tube₁))‖ ≤
        (3*Lip+8*DirErr)*rho^2 := by
    have he := mul_le_mul_of_nonneg_left hdelta (show 0 ≤ 8*DirErr by positivity)
    nlinarith [hxi]
  exact max_le (hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg rho)))
    (hxi'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg rho)))

end OriginalWJointPhase
