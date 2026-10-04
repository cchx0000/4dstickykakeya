import Theorems.Thm_StickyKakeya4_original_w_joint_phase

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalWNormalizedPhase
open Classical OriginalWWitnessCounts OriginalWPhysicalDisplacement OriginalWJointPhase

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The original pointwise plane intercept is reflected and scaled by K*rho.
 It is not silently divided by rho while the slope graph uses K*rho. -/
def phaseCoordinates (rho Lip x₀ : ℝ) (xi₀ : V) (x : ℝ) (xi : V) : ℝ × V :=
  ((x-x₀)/rho,-((Lip*rho)⁻¹) • (xi-xi₀))

def graphCoordinates (rho Lip z₀ : ℝ) (f₀ : V) (z : ℝ) (F : ℝ →L[ℝ] V) : ℝ × V :=
  ((z-z₀)/rho,(Lip*rho)⁻¹ • (F 1-f₀))

lemma scalar_operator_apply (F : ℝ →L[ℝ] V) (c : ℝ) : F c=c • F 1 := by
  simpa only [smul_eq_mul,mul_one] using F.map_smul c (1:ℝ)

/-- Exact normalization of the signed original W relation. The sign change
 and the anisotropic K factor are explicit in the actual coordinate maps. -/
theorem phase_error_identity (rho Lip x₀ z₀ x₁ x₂ t s c : ℝ)
    (xi₀ xi₁ xi₂ f₀ : V) (F₀ F₁ : ℝ →L[ℝ] V) :
    phaseCoordinates rho Lip x₀ xi₀ x₂ xi₂-phaseCoordinates rho Lip x₀ xi₀ x₁ xi₁-
      c • (graphCoordinates rho Lip z₀ f₀ s F₁-graphCoordinates rho Lip z₀ f₀ t F₀) =
      (rho⁻¹*(x₂-x₁-(s-t)*c),
        -((Lip*rho)⁻¹) • (xi₂-xi₁-(F₀-F₁) c)) := by
  apply Prod.ext
  · change (x₂-x₀)/rho-(x₁-x₀)/rho-c*((s-z₀)/rho-(t-z₀)/rho)=rho⁻¹*(x₂-x₁-(s-t)*c)
    simp only [div_eq_mul_inv]
    ring
  · change -((Lip*rho)⁻¹) • (xi₂-xi₀)-(-((Lip*rho)⁻¹) • (xi₁-xi₀))-
      c • ((Lip*rho)⁻¹ • (F₁ 1-f₀)-(Lip*rho)⁻¹ • (F₀ 1-f₀)) =
      -((Lip*rho)⁻¹) • (xi₂-xi₁-(F₀-F₁) c)
    rw [scalar_operator_apply (F₀-F₁) c,sub_apply]
    module

/-- Normalizing a genuine rho-squared scalar error costs exactly rho. -/
lemma scaled_scalar_error {rho E a : ℝ} (hrho : 0 < rho) (ha : |a| ≤ E*rho^2) :
    |rho⁻¹*a| ≤ E*rho := by
  calc
    _ = rho⁻¹*|a| := by rw [abs_mul,abs_of_pos (inv_pos.mpr hrho)]
    _ ≤ rho⁻¹*(E*rho^2) := mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr hrho.le)
    _ = (E*rho)*(rho⁻¹*rho) := by ring
    _ = E*rho := by rw [inv_mul_cancel₀ hrho.ne',mul_one]

/-- The normal K loss cancels against the EXPLICIT anisotropic coordinate
 scale. The resulting phase error has a fixed original-incidence constant. -/
lemma scaled_normal_error (a : V) {rho Lip DirErr : ℝ}
    (hrho : 0 < rho) (hLip : 1 ≤ Lip) (hDir : 0 ≤ DirErr)
    (ha : ‖a‖ ≤ (3*Lip+8*DirErr)*rho^2) :
    ‖-((Lip*rho)⁻¹) • a‖ ≤ (3+8*DirErr)*rho := by
  have hLipPos : 0 < Lip := by linarith
  have hden : 0 < Lip*rho := mul_pos hLipPos hrho
  calc
    _ = (Lip*rho)⁻¹*‖a‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (inv_pos.mpr hden)]
    _ ≤ (Lip*rho)⁻¹*((3*Lip+8*DirErr)*rho^2) :=
      mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr hden.le)
    _ = ((3*Lip+8*DirErr)*rho^2)/(Lip*rho) := by rw [div_eq_mul_inv]; ring
    _ ≤ (3+8*DirErr)*rho := by
      apply (div_le_iff₀ hden).mpr
      have hh : 0 ≤ 8*DirErr*(Lip-1)*rho^2 :=
        mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hLip)) (sq_nonneg rho)
      nlinarith

/-- The normalized scalar-tangent phase identity with all centers arbitrary.
 Its two residual hypotheses are supplied by original W theorems below. -/
theorem normalized_phase_error (rho Lip x₀ z₀ x₁ x₂ t s c IncErr DirErr : ℝ)
    (xi₀ xi₁ xi₂ f₀ : V) (F₀ F₁ : ℝ →L[ℝ] V)
    (hrho : 0 < rho) (hLip : 1 ≤ Lip) (hDir : 0 ≤ DirErr)
    (hx : |x₂-x₁-(s-t)*c| ≤ (3+12*IncErr)*rho^2)
    (hxi : ‖xi₂-xi₁-(F₀-F₁) c‖ ≤ (3*Lip+8*DirErr)*rho^2) :
    ‖phaseCoordinates rho Lip x₀ xi₀ x₂ xi₂-phaseCoordinates rho Lip x₀ xi₀ x₁ xi₁-
      c • (graphCoordinates rho Lip z₀ f₀ s F₁-graphCoordinates rho Lip z₀ f₀ t F₀)‖ ≤
      max (3+12*IncErr) (3+8*DirErr)*rho := by
  rw [phase_error_identity]
  exact max_le
    ((scaled_scalar_error hrho hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrho.le))
    ((scaled_normal_error _ hrho hLip hDir hxi).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hrho.le))

variable {P T : Type*} [DecidableEq P] [DecidableEq T]

/-- Native original-data caller for the normalized Section21 relation. Both
 residuals are derived from original W witnesses; neither is an input. -/
theorem scalar_original_normalized_phase
    (I : Finset (P × T)) (height : P → ℝ) (x : P → ℝ) (base : T → ℝ)
    (theta : T → Fin 3 → ℝ) (offset : P → V) (v : T → V)
    (F : ℝ → ℝ →L[ℝ] V) (Z : Finset ℝ)
    (x₀ z₀ : ℝ) (xi₀ f₀ : V)
    {delta rho q IncErr DirErr Lip : ℝ}
    (hrho : 0 < rho) (hq : 0 < q) (hqρ : q ≤ rho)
    (hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr) (hLip : 1 ≤ Lip) (hdelta : delta ≤ rho^2)
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
    ‖phaseCoordinates rho Lip x₀ xi₀ (x p₂) (offset p₂)-
      phaseCoordinates rho Lip x₀ xi₀ (x p₁) (offset p₁)-
      c • (graphCoordinates rho Lip z₀ f₀ (height w.1.point₁) (F (height w.1.point₁))-
        graphCoordinates rho Lip z₀ f₀ (height w.1.point₀) (F (height w.1.point₀)))‖ ≤
      max (3+12*IncErr) (3+8*DirErr)*rho := by
  have hx := scalar_native_witness_displacement I height x base theta Z hrho.le hq hqρ hInc hdelta
    hinc hheight hdiam w hw p₁ p₂ hp₁ hp₂ hz₁ hz₂
  have hwc := witness_conditions I height (terminalGrid q theta) hw
  have hp := (TwoTubePathCollisionCount.mem_paths I w.1).mp hwc.1
  have h₀ := hheight _ (Finset.mem_image_of_mem Prod.fst hp.1)
  have h₁ := hheight _ (Finset.mem_image_of_mem Prod.fst hp.2.1)
  have h₂ := hheight _ (Finset.mem_image_of_mem Prod.fst hp.2.2.2)
  have hc := hwc.2.2.2.2.2
  have hxi := original_coarse_offset_displacement I height (terminalGrid q theta) offset
    (scalarSlope theta) (fun t => scalarDecode q (scalarAngle q theta t)) v F hrho.le (show 0 ≤ Lip by linarith)
    hdir w hw p₁ p₂ hp₁ hp₂ hz₁ hz₂ (hcluster _ h₀ _ h₁) (hcluster _ h₁ _ h₂)
    ((scalar_grid_approximation q hq theta w.1.tube₁).trans hqρ)
    ((scalar_grid_approximation q hq theta w.2.tube₁).trans hqρ)
    ((scalar_terminal_grid_gap q hq theta w.2.tube₂ w.1.tube₂ hc).trans hqρ)
  apply normalized_phase_error rho Lip x₀ z₀ (x p₁) (x p₂)
    (height w.1.point₀) (height w.1.point₁) _ IncErr DirErr
    xi₀ (offset p₁) (offset p₂) f₀ (F (height w.1.point₀)) (F (height w.1.point₁)) hrho hLip hDir hx
  have he := mul_le_mul_of_nonneg_left hdelta (show 0 ≤ 8*DirErr by positivity)
  nlinarith [hxi]

end OriginalWNormalizedPhase
