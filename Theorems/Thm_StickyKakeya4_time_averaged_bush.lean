import Theorems.Thm_StickyKakeya4_residual_collision_bridge

/-!
# A quantitative physical bush from the original collision graph

A root edge whose closest time is in `[u,v]`, transverse residual is at most
`r`, and directional separation is at most two spends at least time `r`
in the physical `2r` collision relation on `[u-1,v+1]`. Tonelli and product
domination then produce a bush with quantitatively positive original source
mass. No four-cycle, rank, descendant-density, or frozen-edge-mass hypothesis
is used.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace StickyKakeya4

/-- The original affine trajectories meeting a physical ball at time `t`. -/
def physicalAffineBush (b : E3 → E3) (t : ℝ) (p : E3) (R : ℝ) : Set E3 :=
  {a | ‖(b a + t • a) - (b p + t • p)‖ ≤ R}

theorem measurableSet_physicalAffineBush (b : E3 → E3) (hb : Measurable b)
    (t : ℝ) (p : E3) (R : ℝ) : MeasurableSet (physicalAffineBush b t p R) := by
  exact measurableSet_le (by fun_prop) measurable_const

/-- Residual control persists for a time interval of length `r`, including
zero directional difference; no off-diagonal assumption is needed. -/
theorem closest_interval_subset_collisionTimeFiber
    (α β : E3) (u v r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hα : ‖α‖ ≤ 2) (hβ : ‖collisionResidual α β‖ ≤ r)
    (ht : collisionTime α β ∈ Icc u v) :
    Icc (collisionTime α β - r / 2) (collisionTime α β + r / 2) ⊆
      collisionTimeFiber (Icc (u - 1) (v + 1)) α β (2 * r) := by
  intro t ht'
  have habs : |t - collisionTime α β| ≤ r / 2 := by
    apply abs_le.mpr
    constructor <;> linarith [ht'.1, ht'.2]
  refine ⟨⟨by linarith [ht.1, ht'.1], by linarith [ht.2, ht'.2]⟩, ?_⟩
  have hid : β + t • α = collisionResidual α β + (t - collisionTime α β) • α := by
    unfold collisionResidual
    module
  rw [hid]
  calc
    ‖collisionResidual α β + (t - collisionTime α β) • α‖ ≤
        ‖collisionResidual α β‖ + ‖(t - collisionTime α β) • α‖ := norm_add_le _ _
    _ ≤ r + (r / 2) * 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add hβ (mul_le_mul habs hα (norm_nonneg _) (by positivity))
    _ = 2 * r := by ring

theorem collisionTimeFiber_volume_ge_of_residual
    (α β : E3) (u v r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hα : ‖α‖ ≤ 2) (hβ : ‖collisionResidual α β‖ ≤ r)
    (ht : collisionTime α β ∈ Icc u v) :
    ENNReal.ofReal r ≤ volume (collisionTimeFiber (Icc (u - 1) (v + 1)) α β (2 * r)) := by
  have h := measure_mono (μ := (volume : Measure ℝ))
    (closest_interval_subset_collisionTimeFiber α β u v r hr hr1 hα hβ ht)
  rw [Real.volume_Icc] at h
  convert h using 1 <;> congr 1 <;> ring

/-- The lower time-integrated mass retains the whole original root graph. -/
theorem time_averaged_root_collision_mass_ge
    (Γ : Measure (E3 × E3)) [SFinite Γ]
    (b : E3 → E3) (hb : Measurable b) (u v r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hsupport : ∀ᵐ e ∂Γ, ‖e.1 - e.2‖ ≤ 2 ∧
      ‖collisionResidual (e.1 - e.2) (b e.1 - b e.2)‖ ≤ r ∧
      collisionTime (e.1 - e.2) (b e.1 - b e.2) ∈ Icc u v) :
    ENNReal.ofReal r * Γ univ ≤
      ∫⁻ t in Icc (u - 1) (v + 1),
        Γ {e | ‖(b e.1 - b e.2) + t • (e.1 - e.2)‖ ≤ 2 * r} := by
  rw [lintegral_collision_mass_eq_fiber_volume Γ
    (fun e => e.1 - e.2) (fun e => b e.1 - b e.2)
    (by fun_prop) (by fun_prop)]
  calc
    ENNReal.ofReal r * Γ univ = ∫⁻ _e, ENNReal.ofReal r ∂Γ := (lintegral_const _).symm
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [hsupport] with e he
      exact collisionTimeFiber_volume_ge_of_residual _ _ _ _ _ hr hr1 he.1 he.2.1 he.2.2

/-- Product mass is exactly the source average of genuine physical bushes. -/
theorem product_collision_mass_eq_bush_average
    (σ : Measure E3) [SFinite σ] (b : E3 → E3) (hb : Measurable b)
    (t R : ℝ) :
    (σ.prod σ) {e | ‖(b e.1 - b e.2) + t • (e.1 - e.2)‖ ≤ R} =
      ∫⁻ p, σ (physicalAffineBush b t p R) ∂σ := by
  rw [Measure.prod_apply_symm (measurableSet_le (by fun_prop) measurable_const)]
  apply lintegral_congr
  intro p
  congr 1
  ext a
  change (‖b a - b p + t • (a - p)‖ ≤ R) ↔
    (‖(b a + t • a) - (b p + t • p)‖ ≤ R)
  have hid : b a - b p + t • (a - p) = (b a + t • a) - (b p + t • p) := by module
  rw [hid]

/-- Tonelli plus domination, before choosing any center or time. -/
theorem time_averaged_physical_bush_mass_ge
    (σ : Measure E3) [IsFiniteMeasure σ] (Γ : Measure (E3 × E3))
    (hΓ : Γ ≤ σ.prod σ) (b : E3 → E3) (hb : Measurable b)
    (u v r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hsupport : ∀ᵐ e ∂Γ, ‖e.1 - e.2‖ ≤ 2 ∧
      ‖collisionResidual (e.1 - e.2) (b e.1 - b e.2)‖ ≤ r ∧
      collisionTime (e.1 - e.2) (b e.1 - b e.2) ∈ Icc u v) :
    ENNReal.ofReal r * Γ univ ≤
      ∫⁻ t in Icc (u - 1) (v + 1), ∫⁻ p, σ (physicalAffineBush b t p (2 * r)) ∂σ := by
  letI : IsFiniteMeasure Γ := isFiniteMeasure_of_le (σ.prod σ) hΓ
  refine (time_averaged_root_collision_mass_ge Γ b hb u v r hr hr1 hsupport).trans ?_
  apply lintegral_mono
  intro t
  dsimp only
  rw [← product_collision_mass_eq_bush_average σ b hb t (2 * r)]
  exact hΓ _

/-- Every threshold below the actual time average is exceeded by a physical
bush. The strict budget avoids an unjustified supremum-attainment argument. -/
theorem exists_physicalAffineBush_mass_gt_of_budget
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ univ ≤ 1)
    (Γ : Measure (E3 × E3)) (hΓ : Γ ≤ σ.prod σ)
    (b : E3 → E3) (hb : Measurable b) (u v r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hsupport : ∀ᵐ e ∂Γ, ‖e.1 - e.2‖ ≤ 2 ∧
      ‖collisionResidual (e.1 - e.2) (b e.1 - b e.2)‖ ≤ r ∧
      collisionTime (e.1 - e.2) (b e.1 - b e.2) ∈ Icc u v)
    (q : ℝ≥0∞) (hq : q * ENNReal.ofReal (v - u + 2) < ENNReal.ofReal r * Γ univ) :
    ∃ t ∈ Icc (u - 1) (v + 1), ∃ p : E3, q < σ (physicalAffineBush b t p (2 * r)) := by
  by_contra! hn
  have hlow := time_averaged_physical_bush_mass_ge σ Γ hΓ b hb u v r hr hr1 hsupport
  have hupp :
      (∫⁻ t in Icc (u - 1) (v + 1), ∫⁻ p, σ (physicalAffineBush b t p (2 * r)) ∂σ) ≤
        q * ENNReal.ofReal (v - u + 2) := by
    calc
      _ ≤ ∫⁻ _t in Icc (u - 1) (v + 1), q := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        calc
          (∫⁻ p, σ (physicalAffineBush b t p (2 * r)) ∂σ) ≤ ∫⁻ _p, q ∂σ :=
            lintegral_mono (hn t ht)
          _ = q * σ univ := lintegral_const _
          _ ≤ q * 1 := by simpa [mul_comm] using mul_le_mul_left hσ q
          _ = q := mul_one _
      _ = q * ENNReal.ofReal (v - u + 2) := by
        rw [setLIntegral_const, Real.volume_Icc]
        congr 2
        ring
  exact (not_lt_of_ge (hlow.trans hupp)) hq

/-- A definite quantitative original-source bush, with the half-average
constant and the actual inherited closest-time window retained. -/
theorem exists_physicalAffineBush_mass_gt
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ univ ≤ 1)
    (Γ : Measure (E3 × E3)) (hΓ : Γ ≤ σ.prod σ) (hM : 0 < Γ univ)
    (b : E3 → E3) (hb : Measurable b) (u v r : ℝ)
    (huv : u ≤ v) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsupport : ∀ᵐ e ∂Γ, ‖e.1 - e.2‖ ≤ 2 ∧
      ‖collisionResidual (e.1 - e.2) (b e.1 - b e.2)‖ ≤ r ∧
      collisionTime (e.1 - e.2) (b e.1 - b e.2) ∈ Icc u v) :
    ∃ t ∈ Icc (u - 1) (v + 1), ∃ p : E3,
      ENNReal.ofReal (r * (Γ univ).toReal / (2 * (v - u + 2))) <
        σ (physicalAffineBush b t p (2 * r)) := by
  letI : IsFiniteMeasure Γ := isFiniteMeasure_of_le (σ.prod σ) hΓ
  have hMtop : Γ univ ≠ ∞ := measure_ne_top _ _
  have hMreal : 0 < (Γ univ).toReal := ENNReal.toReal_pos hM.ne' hMtop
  have hL : 0 < v - u + 2 := by linarith
  have hq : 0 ≤ r * (Γ univ).toReal / (2 * (v - u + 2)) := by positivity
  apply exists_physicalAffineBush_mass_gt_of_budget σ hσ Γ hΓ b hb u v r hr.le hr1 hsupport
  rw [← ENNReal.ofReal_mul hq]
  have heq : ENNReal.ofReal r * Γ univ = ENNReal.ofReal (r * (Γ univ).toReal) := by
    rw [ENNReal.ofReal_mul hr.le, ENNReal.ofReal_toReal hMtop]
  rw [heq]
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < r * (Γ univ).toReal)).2
  have hhalf : r * (Γ univ).toReal / (2 * (v - u + 2)) * (v - u + 2) =
      r * (Γ univ).toReal / 2 := by
    field_simp [hL.ne']
  rw [hhalf]
  linarith [mul_pos hr hMreal]

/-- Asymmetric product disintegration: source mass is averaged over original
targets, which need not have the same measure as the source. -/
theorem product_collision_mass_eq_source_bush_average
    (μ ν : Measure E3) [SFinite μ] [SFinite ν] (b : E3 → E3) (hb : Measurable b)
    (t R : ℝ) :
    (μ.prod ν) {e | ‖(b e.1 - b e.2) + t • (e.1 - e.2)‖ ≤ R} =
      ∫⁻ p, μ (physicalAffineBush b t p R) ∂ν := by
  rw [Measure.prod_apply_symm (measurableSet_le (by fun_prop) measurable_const)]
  apply lintegral_congr
  intro p
  congr 1
  ext a
  change (‖b a - b p + t • (a - p)‖ ≤ R) ↔
    (‖(b a + t • a) - (b p + t • p)‖ ≤ R)
  have hid : b a - b p + t • (a - p) = (b a + t • a) - (b p + t • p) := by module
  rw [hid]

/-- Asymmetric Tonelli bound. The whole target measure survives restriction
of the source marginal. -/
theorem time_averaged_source_bush_mass_ge
    (μ ν : Measure E3) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (Γ : Measure (E3 × E3))
    (hΓ : Γ ≤ μ.prod ν) (b : E3 → E3) (hb : Measurable b)
    (u v r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hsupport : ∀ᵐ e ∂Γ, ‖e.1 - e.2‖ ≤ 2 ∧
      ‖collisionResidual (e.1 - e.2) (b e.1 - b e.2)‖ ≤ r ∧
      collisionTime (e.1 - e.2) (b e.1 - b e.2) ∈ Icc u v) :
    ENNReal.ofReal r * Γ univ ≤
      ∫⁻ t in Icc (u - 1) (v + 1), ∫⁻ p, μ (physicalAffineBush b t p (2 * r)) ∂ν := by
  letI : IsFiniteMeasure Γ := isFiniteMeasure_of_le (μ.prod ν) hΓ
  refine (time_averaged_root_collision_mass_ge Γ b hb u v r hr hr1 hsupport).trans ?_
  apply lintegral_mono
  intro t
  dsimp only
  rw [← product_collision_mass_eq_source_bush_average μ ν b hb t (2 * r)]
  exact hΓ _

/-- Every threshold below the actual time average is exceeded by a physical
bush. The strict budget avoids an unjustified supremum-attainment argument. -/
theorem exists_source_bush_mass_gt_of_budget
    (μ ν : Measure E3) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hν : ν univ ≤ 1)
    (Γ : Measure (E3 × E3)) (hΓ : Γ ≤ μ.prod ν)
    (b : E3 → E3) (hb : Measurable b) (u v r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hsupport : ∀ᵐ e ∂Γ, ‖e.1 - e.2‖ ≤ 2 ∧
      ‖collisionResidual (e.1 - e.2) (b e.1 - b e.2)‖ ≤ r ∧
      collisionTime (e.1 - e.2) (b e.1 - b e.2) ∈ Icc u v)
    (q : ℝ≥0∞) (hq : q * ENNReal.ofReal (v - u + 2) < ENNReal.ofReal r * Γ univ) :
    ∃ t ∈ Icc (u - 1) (v + 1), ∃ p : E3, q < μ (physicalAffineBush b t p (2 * r)) := by
  by_contra! hn
  have hlow := time_averaged_source_bush_mass_ge μ ν Γ hΓ b hb u v r hr hr1 hsupport
  have hupp :
      (∫⁻ t in Icc (u - 1) (v + 1), ∫⁻ p, μ (physicalAffineBush b t p (2 * r)) ∂ν) ≤
        q * ENNReal.ofReal (v - u + 2) := by
    calc
      _ ≤ ∫⁻ _t in Icc (u - 1) (v + 1), q := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        calc
          (∫⁻ p, μ (physicalAffineBush b t p (2 * r)) ∂ν) ≤ ∫⁻ _p, q ∂ν :=
            lintegral_mono (hn t ht)
          _ = q * ν univ := lintegral_const _
          _ ≤ q * 1 := by simpa [mul_comm] using mul_le_mul_left hν q
          _ = q := mul_one _
      _ = q * ENNReal.ofReal (v - u + 2) := by
        rw [setLIntegral_const, Real.volume_Icc]
        congr 2
        ring
  exact (not_lt_of_ge (hlow.trans hupp)) hq


end StickyKakeya4
