import Theorems.Thm_StickyKakeya4_angular_residual_shell
import Theorems.Thm_StickyKakeya4_actual_packing_reference_source
import Theorems.Thm_StickyKakeya4_residual_carrier_proximity
import Theorems.Thm_StickyKakeya4_residual_phase_localization

/-!
# The literal angular-shell graph on the actual restricted slope source

The weight below is exactly the angular-shell restriction of the original
residual content, multiplied by the shell's lower endpoint. The explicit
source cut gives pointwise physical support and is invisible to the original
restricted product measure. Neither the closest collision time nor the
physical residual is changed.
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.ActualShellGraph

open ActualSlopeSource ResidualPhaseLocalization

/-- A literal shell, with a pointwise cut to the chosen actual source. -/
def shellGraphWeight (B : Set E3) (b : E3 → E3) (J : Set ℝ)
    (ρ τ : ℝ) (p : E3 × E3) : ℝ≥0∞ :=
  ((B ×ˢ B) ∩ {p : E3 × E3 | τ < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ 2 * τ}).indicator
    (fun p => ENNReal.ofReal τ * residualContentWeight J
      (p.1 - p.2) (b p.1 - b p.2) ρ) p

theorem measurable_shellGraphWeight (B : Set E3) (hB : MeasurableSet B)
    (b : E3 → E3) (hb : Measurable b) (J : Set ℝ) (hJ : MeasurableSet J)
    (ρ τ : ℝ) : Measurable (shellGraphWeight B b J ρ τ) := by
  apply (measurable_const.mul (measurable_residualContentWeight
    (fun p : E3 × E3 => p.1 - p.2) (fun p => b p.1 - b p.2)
    (measurable_fst.sub measurable_snd)
    ((hb.comp measurable_fst).sub (hb.comp measurable_snd)) J hJ ρ)).indicator
  exact (hB.prod hB).inter
    ((measurableSet_lt measurable_const (measurable_fst.sub measurable_snd).norm).inter
      (measurableSet_le (measurable_fst.sub measurable_snd).norm measurable_const))

/-- Angular separation bounds the genuine inverse-secant normalization. -/
theorem shellGraphWeight_le_one (B : Set E3) (b : E3 → E3) (J : Set ℝ)
    (ρ τ : ℝ) (hτ : 0 < τ) (p : E3 × E3) : shellGraphWeight B b J ρ τ p ≤ 1 := by
  classical
  unfold shellGraphWeight
  by_cases hp : p ∈ (B ×ˢ B) ∩
      {p : E3 × E3 | τ < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ 2 * τ}
  · rw [Set.indicator_of_mem hp]
    unfold residualContentWeight
    split_ifs
    · calc
        _ ≤ ENNReal.ofReal ‖p.1 - p.2‖ * (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹ :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hp.2.1.le) le_rfl
        _ = 1 := ENNReal.mul_inv_cancel
          (ne_of_gt (ENNReal.ofReal_pos.mpr (hτ.trans hp.2.1))) ENNReal.ofReal_ne_top
    · simp
  · rw [Set.indicator_of_notMem hp]
    exact zero_le

/-- Nonzero graph edges retain the literal source, angular, residual, and
original closest-time cutoffs. -/
theorem shellGraphWeight_ne_zero_support (B : Set E3) (b : E3 → E3) (J : Set ℝ)
    (ρ τ : ℝ) (p : E3 × E3) (hp : shellGraphWeight B b J ρ τ p ≠ 0) :
    p.1 ∈ B ∧ p.2 ∈ B ∧ τ < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ 2 * τ ∧
      ‖collisionResidual (p.1 - p.2) (b p.1 - b p.2)‖ ≤ ρ ∧
      collisionTime (p.1 - p.2) (b p.1 - b p.2) ∈ J := by
  classical
  unfold shellGraphWeight at hp
  by_cases hcut : p ∈ (B ×ˢ B) ∩
      {p : E3 × E3 | τ < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ 2 * τ}
  · rw [Set.indicator_of_mem hcut] at hp
    unfold residualContentWeight at hp
    split_ifs at hp with hc
    · exact ⟨hcut.1.1, hcut.1.2, hcut.2.1, hcut.2.2, hc.2⟩
    · simp at hp
  · simp only [Set.indicator_of_notMem hcut] at hp
    exact (hp rfl).elim

/-- Conversely, the original shell and physical cutoffs give a nonzero edge;
there is no extra hidden edge condition. -/
theorem shellGraphWeight_ne_zero_iff (B : Set E3) (b : E3 → E3) (J : Set ℝ)
    (ρ τ : ℝ) (hτ : 0 < τ) (p : E3 × E3) :
    shellGraphWeight B b J ρ τ p ≠ 0 ↔
      p.1 ∈ B ∧ p.2 ∈ B ∧ τ < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ 2 * τ ∧
        ‖collisionResidual (p.1 - p.2) (b p.1 - b p.2)‖ ≤ ρ ∧
        collisionTime (p.1 - p.2) (b p.1 - b p.2) ∈ J := by
  classical
  constructor
  · exact shellGraphWeight_ne_zero_support B b J ρ τ p
  · rintro ⟨hfirst, hsecond, hlo, hhi, hres, htime⟩
    have hsecant : p.1 - p.2 ≠ 0 := norm_pos_iff.mp (hτ.trans hlo)
    have hcut : p ∈ (B ×ˢ B) ∩
        {p : E3 × E3 | τ < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ 2 * τ} :=
      ⟨⟨hfirst, hsecond⟩, hlo, hhi⟩
    rw [shellGraphWeight, Set.indicator_of_mem hcut, residualContentWeight,
      if_pos ⟨hsecant, hres, htime⟩]
    exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hτ))
      (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)

/-- The source cut costs no mass for any source already supported on `B`. -/
theorem graphMeasure_mass_eq_angularShellContent_of_ae_mem
    (σ : Measure E3) (B : Set E3) (hσ : ∀ᵐ a ∂σ, a ∈ B)
    (b : E3 → E3) (J : Set ℝ) (ρ τ : ℝ) :
    graphMeasure σ (shellGraphWeight B b J ρ τ) univ =
      ENNReal.ofReal τ * AngularResidualShell.angularShellContent (σ.prod σ)
        (fun p => p.1 - p.2) (fun p => b p.1 - b p.2) J ρ τ (2 * τ) := by
  classical
  have hprod : ∀ᵐ p : E3 × E3 ∂σ.prod σ, p ∈ B ×ˢ B := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hσ,
      Measure.quasiMeasurePreserving_snd.ae hσ] with p hp₁ hp₂
    exact ⟨hp₁, hp₂⟩
  rw [graphMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have heq : shellGraphWeight B b J ρ τ =ᵐ[σ.prod σ]
      {p : E3 × E3 | τ < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ 2 * τ}.indicator
        (fun p => ENNReal.ofReal τ * residualContentWeight J
          (p.1 - p.2) (b p.1 - b p.2) ρ) := by
    filter_upwards [hprod] with p hp
    simp only [shellGraphWeight, Set.indicator, Set.mem_inter_iff, hp, true_and]
  rw [lintegral_congr_ae heq]
  have hA : MeasurableSet
      {p : E3 × E3 | τ < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ 2 * τ} :=
    (measurableSet_lt measurable_const (measurable_fst.sub measurable_snd).norm).inter
      (measurableSet_le (measurable_fst.sub measurable_snd).norm measurable_const)
  rw [lintegral_indicator hA, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

/-- Exact mass identity for the actual source, literally `volume.restrict B`. -/
theorem graphMeasure_mass_eq_angularShellContent
    (B : Set E3) (hB : MeasurableSet B) (b : E3 → E3) (J : Set ℝ) (ρ τ : ℝ) :
    graphMeasure ((volume : Measure E3).restrict B) (shellGraphWeight B b J ρ τ) univ =
      ENNReal.ofReal τ * AngularResidualShell.angularShellContent
        (((volume : Measure E3).restrict B).prod ((volume : Measure E3).restrict B))
        (fun p => p.1 - p.2) (fun p => b p.1 - b p.2) J ρ τ (2 * τ) :=
  graphMeasure_mass_eq_angularShellContent_of_ae_mem _ B (ae_restrict_mem hB) b J ρ τ

/-- The selected marked lines have exactly the slope/intercept secant used
in the shell density, pointwise and before any restriction. -/
theorem actual_secant_eq
    (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) (p : E3 × E3) :
    northGraphSecant (slopeLine selector hmeas hvalid hselector p.1)
      (slopeLine selector hmeas hvalid hselector p.2) =
      (p.1 - p.2, intercept selector hmeas hvalid hselector p.1 -
        intercept selector hmeas hvalid hselector p.2) := by
  simp [northGraphSecant, slope_slopeLine, intercept]

/-- The closest-time readout is exactly that of the original marked lines. -/
theorem actual_collisionTime_eq
    (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) (p : E3 × E3) :
    collisionTime
        (northGraphSecant (slopeLine selector hmeas hvalid hselector p.1)
          (slopeLine selector hmeas hvalid hselector p.2)).1
        (northGraphSecant (slopeLine selector hmeas hvalid hselector p.1)
          (slopeLine selector hmeas hvalid hselector p.2)).2 =
      collisionTime (p.1 - p.2) (intercept selector hmeas hvalid hselector p.1 -
        intercept selector hmeas hvalid hselector p.2) := by
  rw [actual_secant_eq]

/-- The closest residual is likewise unchanged, including its vector value. -/
theorem actual_collisionResidual_eq
    (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) (p : E3 × E3) :
    collisionResidual
        (northGraphSecant (slopeLine selector hmeas hvalid hselector p.1)
          (slopeLine selector hmeas hvalid hselector p.2)).1
        (northGraphSecant (slopeLine selector hmeas hvalid hselector p.1)
          (slopeLine selector hmeas hvalid hselector p.2)).2 =
      collisionResidual (p.1 - p.2) (intercept selector hmeas hvalid hselector p.1 -
        intercept selector hmeas hvalid hselector p.2) := by
  rw [actual_secant_eq]

/-- An arbitrary inherited time is preserved exactly: the contact vector
at that same time is the original marked-line contact vector. -/
theorem actual_contact_at_time_eq
    (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) (p : E3 × E3) (t : ℝ) :
    (northGraphSecant (slopeLine selector hmeas hvalid hselector p.1)
      (slopeLine selector hmeas hvalid hselector p.2)).2 +
      t • (northGraphSecant (slopeLine selector hmeas hvalid hselector p.1)
        (slopeLine selector hmeas hvalid hselector p.2)).1 =
      (intercept selector hmeas hvalid hselector p.1 -
        intercept selector hmeas hvalid hselector p.2) + t • (p.1 - p.2) := by
  rw [actual_secant_eq]

/-- Original carrier proximity is derived from the literal residual shell,
not supplied as an additional localization assumption. -/
theorem actual_shellGraphWeight_carrier_dist_le
    (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) (k : ℤ)
    (B : Set E3) (hBsource : B ⊆ sourceSet selector hmeas hvalid hselector k)
    (ambient : Set MarkedLine) (hsubset : selector ⊆ ambient)
    (R : ℝ) (hR : ∀ line ∈ ambient, ‖offset line‖ ≤ R)
    (J : Set ℝ) (S : ℝ) (hJS : ∀ t ∈ J, |t| ≤ S)
    (ρ τ : ℝ) (hρτ : ρ ≤ τ) (hτ : 0 < τ)
    (p : E3 × E3)
    (hp : shellGraphWeight B (intercept selector hmeas hvalid hselector) J ρ τ p ≠ 0) :
    dist (slopeCarrierMap selector hmeas hvalid hselector p.1)
      (slopeCarrierMap selector hmeas hvalid hselector p.2) ≤
      (6 + 24 * R + 16 * S) * τ := by
  obtain ⟨hp₁, hp₂, _hlo, hhi, hres, htime⟩ :=
    shellGraphWeight_ne_zero_support B _ J ρ τ p hp
  have hchart (a : E3) (ha : a ∈ B) :
      (1 / 2 : ℝ) ≤ direction (slopeLine selector hmeas hvalid hselector a) (3 : Fin 4) := by
    rw [direction_slopeLine]
    exact northSlopeDirection_fourth_ge_half (hBsource ha).1
  have heq := actual_secant_eq selector hmeas hvalid hselector p
  apply residual_shell_carrier_dist_le _ _
    (hvalid _ (slopeLine_mem selector hmeas hvalid hselector p.1))
    (hvalid _ (slopeLine_mem selector hmeas hvalid hselector p.2))
    (hchart p.1 hp₁) (hchart p.2 hp₂) R S τ ρ hτ.le
    (hR _ (hsubset (slopeLine_mem selector hmeas hvalid hselector p.2)))
  · simpa only [heq] using hhi
  · exact hρτ
  · simpa only [heq] using hres
  · simpa only [heq] using hJS _ htime

end StickyKakeya4.ActualShellGraph
