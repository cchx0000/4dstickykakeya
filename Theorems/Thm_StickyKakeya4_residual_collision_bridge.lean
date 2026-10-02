import Theorems.Thm_StickyKakeya4_exact_collision_identity

/-!
# From the exact collision identity to weighted residual content

The sublevel-set form of the analytic step in Definition 6.26 and Theorem 6.27
of the original manuscript (pp. 33–34).  An affine collision fibre has length
at most `2 * ρ / ‖α‖`; it is empty unless the transverse residual is at most
`ρ`, and the closest time lies in the corresponding enlarged time interval.

The estimates below are quantitative consequences of the exact collision
identity, not assumptions of a residual/Frostman certificate.  In particular,
they do not assert the geometric residual-content bound or the final
finite-energy/Hausdorff-dimension conclusion of Theorem 6.27.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- Times in a specified set at which two affine trajectories are within `ρ`.
For the manuscript's endpoint pair, `α = a - a'` and `β = b(a) - b(a')`. -/
def collisionTimeFiber (J : Set ℝ) (α β : E3) (ρ : ℝ) : Set ℝ :=
  {s | s ∈ J ∧ ‖β + s • α‖ ≤ ρ}

/-- An actual collision controls both its closest time and its residual. -/
theorem collision_sublevel_localization (α β : E3) (hα : α ≠ 0)
    (ρ s : ℝ) (hρ : 0 ≤ ρ) (hs : ‖β + s • α‖ ≤ ρ) :
    |collisionTime α β - s| ≤ ρ / ‖α‖ ∧ ‖collisionResidual α β‖ ≤ ρ :=
  collision_time_local_and_residual_bound α β hα s ρ ‖α‖ hs hρ
    (norm_pos_iff.mpr hα) le_rfl

/-- All colliding times lie in an interval of radius `ρ / ‖α‖`. -/
theorem collisionTimeFiber_subset_closest_interval (J : Set ℝ) (α β : E3)
    (hα : α ≠ 0) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    collisionTimeFiber J α β ρ ⊆
      Icc (collisionTime α β - ρ / ‖α‖) (collisionTime α β + ρ / ‖α‖) := by
  intro s hs
  have ht := (collision_sublevel_localization α β hα ρ s hρ hs.2).1
  obtain ⟨hlo, hhi⟩ := abs_le.mp ht
  constructor <;> linarith

/-- The exact factor two in the one-dimensional collision-fibre estimate. -/
theorem collisionTimeFiber_volume_le (J : Set ℝ) (α β : E3) (hα : α ≠ 0)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    volume (collisionTimeFiber J α β ρ) ≤ ENNReal.ofReal (2 * ρ / ‖α‖) := by
  calc
    volume (collisionTimeFiber J α β ρ) ≤
        volume (Icc (collisionTime α β - ρ / ‖α‖)
          (collisionTime α β + ρ / ‖α‖)) :=
      measure_mono (collisionTimeFiber_subset_closest_interval J α β hα ρ hρ)
    _ = ENNReal.ofReal (2 * ρ / ‖α‖) := by
      rw [Real.volume_Icc]
      congr 1
      ring

/-- A collision in `[u,v]` forces its closest time into the enlargement by
`ρ / ‖α‖`, as well as forcing the transverse residual to be at most `ρ`. -/
theorem collisionTimeFiber_nonempty_imp_residual_and_time
    (α β : E3) (hα : α ≠ 0) (u v ρ : ℝ) (hρ : 0 ≤ ρ)
    (hne : (collisionTimeFiber (Icc u v) α β ρ).Nonempty) :
    ‖collisionResidual α β‖ ≤ ρ ∧
      collisionTime α β ∈ Icc (u - ρ / ‖α‖) (v + ρ / ‖α‖) := by
  obtain ⟨s, hs⟩ := hne
  obtain ⟨ht, hr⟩ := collision_sublevel_localization α β hα ρ s hρ hs.2
  obtain ⟨hlo, hhi⟩ := abs_le.mp ht
  exact ⟨hr, ⟨by linarith [hs.1.1], by linarith [hs.1.2]⟩⟩

/-- A sublevel-fibre bound with both residual and closest-time cutoffs. -/
theorem collisionTimeFiber_volume_le_localized
    (α β : E3) (hα : α ≠ 0) (u v ρ : ℝ) (hρ : 0 ≤ ρ) :
    volume (collisionTimeFiber (Icc u v) α β ρ) ≤
      if ‖collisionResidual α β‖ ≤ ρ ∧
          collisionTime α β ∈ Icc (u - ρ / ‖α‖) (v + ρ / ‖α‖)
      then ENNReal.ofReal (2 * ρ / ‖α‖) else 0 := by
  split_ifs with h
  · exact collisionTimeFiber_volume_le _ α β hα ρ hρ
  · have he : collisionTimeFiber (Icc u v) α β ρ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro s hs
      exact h (collisionTimeFiber_nonempty_imp_residual_and_time α β hα u v ρ hρ
        ⟨s, hs⟩)
    rw [he, measure_empty]

/-- Fixed-buffer version suitable for integrating a separated angular shell.
The explicit condition `ρ ≤ d * ‖α‖` guarantees that an observed collision
has closest time in the fixed enlargement `[u-d,v+d]`. -/
theorem collisionTimeFiber_volume_le_fixed_buffer
    (α β : E3) (hα : α ≠ 0) (u v d ρ : ℝ) (hρ : 0 ≤ ρ)
    (hbuffer : ρ ≤ d * ‖α‖) :
    volume (collisionTimeFiber (Icc u v) α β ρ) ≤
      if ‖collisionResidual α β‖ ≤ ρ ∧
          collisionTime α β ∈ Icc (u - d) (v + d)
      then ENNReal.ofReal (2 * ρ / ‖α‖) else 0 := by
  split_ifs with h
  · exact collisionTimeFiber_volume_le _ α β hα ρ hρ
  · have he : collisionTimeFiber (Icc u v) α β ρ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro s hs
      obtain ⟨hr, ht⟩ := collisionTimeFiber_nonempty_imp_residual_and_time
        α β hα u v ρ hρ ⟨s, hs⟩
      have hquot : ρ / ‖α‖ ≤ d := (div_le_iff₀ (norm_pos_iff.mpr hα)).2 hbuffer
      exact h ⟨hr, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
    rw [he, measure_empty]

/-- Collision fibres are measurable for measurable time windows. -/
theorem measurableSet_collisionTimeFiber (J : Set ℝ) (hJ : MeasurableSet J)
    (α β : E3) (ρ : ℝ) : MeasurableSet (collisionTimeFiber J α β ρ) := by
  have hm : Measurable (fun s : ℝ => ‖β + s • α‖) := by fun_prop
  exact hJ.inter (measurableSet_le hm measurable_const)

/-- The pointwise density from Definition 6.26, retaining the off-diagonal
condition explicitly.  `Jplus` is the enlarged longitudinal time window. -/
def residualContentWeight (Jplus : Set ℝ) (α β : E3) (ρ : ℝ) : ℝ≥0∞ :=
  if α ≠ 0 ∧ ‖collisionResidual α β‖ ≤ ρ ∧ collisionTime α β ∈ Jplus
  then (ENNReal.ofReal ‖α‖)⁻¹ else 0

/-- The weighted residual content of a measure on endpoint-pair data.
Taking `X = E3 × E3`, `μ = σ.prod σ`, `α(a,a') = a-a'`, and
`β(a,a') = b(a)-b(a')` recovers Definition 6.26 exactly. -/
def weightedResidualContent {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (α β : X → E3) (Jplus : Set ℝ) (ρ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, residualContentWeight Jplus (α x) (β x) ρ ∂μ

/-- The fibre bound in the multiplicative form used by residual content. -/
theorem collisionTimeFiber_volume_le_residualContentWeight
    (α β : E3) (hα : α ≠ 0) (u v d ρ : ℝ) (hρ : 0 ≤ ρ)
    (hbuffer : ρ ≤ d * ‖α‖) :
    volume (collisionTimeFiber (Icc u v) α β ρ) ≤
      ENNReal.ofReal (2 * ρ) * residualContentWeight (Icc (u - d) (v + d)) α β ρ := by
  have h := collisionTimeFiber_volume_le_fixed_buffer α β hα u v d ρ hρ hbuffer
  by_cases hc : ‖collisionResidual α β‖ ≤ ρ ∧
      collisionTime α β ∈ Icc (u - d) (v + d)
  · simpa [residualContentWeight, hα, hc, ENNReal.ofReal_div_of_pos
      (norm_pos_iff.mpr hα), div_eq_mul_inv] using h
  · simpa [residualContentWeight, hα, hc] using h

/-- Integrated collision-fibre estimate.  The quantitative angular-buffer
hypothesis is stated almost everywhere, so the measure may already have
been restricted to any measurable angular shell. -/
theorem lintegral_collisionTimeFiber_le_weightedResidualContent
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (α β : X → E3)
    (u v d ρ : ℝ) (hρ : 0 ≤ ρ)
    (hα : ∀ᵐ x ∂μ, α x ≠ 0)
    (hbuffer : ∀ᵐ x ∂μ, ρ ≤ d * ‖α x‖) :
    (∫⁻ x, volume (collisionTimeFiber (Icc u v) (α x) (β x) ρ) ∂μ) ≤
      ENNReal.ofReal (2 * ρ) *
        weightedResidualContent μ α β (Icc (u - d) (v + d)) ρ := by
  calc
    (∫⁻ x, volume (collisionTimeFiber (Icc u v) (α x) (β x) ρ) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (2 * ρ) *
          residualContentWeight (Icc (u - d) (v + d)) (α x) (β x) ρ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hα, hbuffer] with x hx hbx
      exact collisionTimeFiber_volume_le_residualContentWeight
        (α x) (β x) hx u v d ρ hρ hbx
    _ = ENNReal.ofReal (2 * ρ) *
        weightedResidualContent μ α β (Icc (u - d) (v + d)) ρ := by
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Tonelli identifies the pair-first integral of collision-fibre lengths
with the time-first integral of near-colliding pair masses. -/
theorem lintegral_collision_mass_eq_fiber_volume
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (α β : X → E3) (hα : Measurable α) (hβ : Measurable β)
    (u v ρ : ℝ) :
    (∫⁻ s in Icc u v, μ {x | ‖β x + s • α x‖ ≤ ρ}) =
      ∫⁻ x, volume (collisionTimeFiber (Icc u v) (α x) (β x) ρ) ∂μ := by
  let f : ℝ → X → ℝ≥0∞ := fun s x =>
    {x | ‖β x + s • α x‖ ≤ ρ}.indicator (fun _ => 1) x
  have hfm : Measurable (Function.uncurry f) := by
    have hm : MeasurableSet {p : ℝ × X | ‖β p.2 + p.1 • α p.2‖ ≤ ρ} :=
      measurableSet_le (by fun_prop) measurable_const
    exact measurable_const.indicator hm
  have hfiber (x : X) :
      (∫⁻ s in Icc u v, f s x) =
        volume (collisionTimeFiber (Icc u v) (α x) (β x) ρ) := by
    have hs : MeasurableSet {s : ℝ | ‖β x + s • α x‖ ≤ ρ} :=
      measurableSet_le (by fun_prop) measurable_const
    rw [show (fun s => f s x) =
        {s : ℝ | ‖β x + s • α x‖ ≤ ρ}.indicator (fun _ => 1) by rfl,
      lintegral_indicator_const hs, one_mul, Measure.restrict_apply hs]
    congr 1
    ext s
    exact and_comm
  calc
    (∫⁻ s in Icc u v, μ {x | ‖β x + s • α x‖ ≤ ρ}) =
        ∫⁻ s in Icc u v, ∫⁻ x, f s x ∂μ := by
      apply lintegral_congr
      intro s
      have hs : MeasurableSet {x | ‖β x + s • α x‖ ≤ ρ} :=
        measurableSet_le (by fun_prop) measurable_const
      symm
      simpa only [f, lintegral_indicator_const hs, one_mul]
    _ = ∫⁻ x, ∫⁻ s in Icc u v, f s x ∂μ :=
      lintegral_lintegral_swap hfm.aemeasurable
    _ = ∫⁻ x, volume (collisionTimeFiber (Icc u v) (α x) (β x) ρ) ∂μ :=
      lintegral_congr hfiber

/-- An actual averaged near-collision bound by the manuscript's weighted
residual content, with an explicit angular-shell/buffer hypothesis. -/
theorem averaged_collision_mass_le_weightedResidualContent
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (α β : X → E3) (hαm : Measurable α) (hβm : Measurable β)
    (u v d ρ : ℝ) (hρ : 0 ≤ ρ)
    (hα : ∀ᵐ x ∂μ, α x ≠ 0)
    (hbuffer : ∀ᵐ x ∂μ, ρ ≤ d * ‖α x‖) :
    (∫⁻ s in Icc u v, μ {x | ‖β x + s • α x‖ ≤ ρ}) ≤
      ENNReal.ofReal (2 * ρ) *
        weightedResidualContent μ α β (Icc (u - d) (v + d)) ρ := by
  rw [lintegral_collision_mass_eq_fiber_volume μ α β hαm hβm]
  exact lintegral_collisionTimeFiber_le_weightedResidualContent μ α β u v d ρ
    hρ hα hbuffer

/-- The other branch of the manuscript's energy split: a separated closest
time gives a quantitative lower bound for the spatial distance. -/
theorem collision_norm_lower_of_closest_time_separation
    (α β : E3) (hα : α ≠ 0) (s d : ℝ)
    (hsep : d ≤ |collisionTime α β - s|) :
    d * ‖α‖ ≤ ‖β + s • α‖ := by
  have ht := (collision_sublevel_localization α β hα ‖β + s • α‖ s
    (norm_nonneg _) le_rfl).1
  exact (le_div_iff₀ (norm_pos_iff.mpr hα)).mp (hsep.trans ht)

/-- Closest times outside the fixed enlarged window have spatial distance
at least the buffer width times the angular separation throughout `[u,v]`. -/
theorem collision_norm_lower_outside_enlarged_interval
    (α β : E3) (hα : α ≠ 0) (u v d s : ℝ) (hs : s ∈ Icc u v)
    (ht : collisionTime α β ∉ Icc (u - d) (v + d)) :
    d * ‖α‖ ≤ ‖β + s • α‖ := by
  apply collision_norm_lower_of_closest_time_separation α β hα s d
  have hout : collisionTime α β < u - d ∨ v + d < collisionTime α β := by
    simpa only [mem_Icc, not_and_or, not_le] using ht
  rcases hout with hlo | hhi
  · linarith [neg_le_abs (collisionTime α β - s), hs.1]
  · linarith [le_abs_self (collisionTime α β - s), hs.2]

/-- The closest-time map is measurable, including the harmless totalized
value at `α=0` (which residual content excludes). -/
theorem measurable_collisionTime_comp
    {X : Type*} [MeasurableSpace X] (α β : X → E3)
    (hα : Measurable α) (hβ : Measurable β) :
    Measurable (fun x => collisionTime (α x) (β x)) := by
  unfold collisionTime
  fun_prop

/-- The collision residual is measurable for measurable endpoint data. -/
theorem measurable_collisionResidual_comp
    {X : Type*} [MeasurableSpace X] (α β : X → E3)
    (hα : Measurable α) (hβ : Measurable β) :
    Measurable (fun x => collisionResidual (α x) (β x)) := by
  unfold collisionResidual
  exact hβ.add ((measurable_collisionTime_comp α β hα hβ).smul hα)

/-- The full off-diagonal residual density in Definition 6.26 is measurable. -/
theorem measurable_residualContentWeight
    {X : Type*} [MeasurableSpace X] (α β : X → E3)
    (hα : Measurable α) (hβ : Measurable β)
    (Jplus : Set ℝ) (hJplus : MeasurableSet Jplus) (ρ : ℝ) :
    Measurable (fun x => residualContentWeight Jplus (α x) (β x) ρ) := by
  have hz : MeasurableSet {x | α x ≠ 0} :=
    (measurableSet_eq_fun hα measurable_const).compl
  have hr : MeasurableSet {x | ‖collisionResidual (α x) (β x)‖ ≤ ρ} :=
    measurableSet_le (measurable_collisionResidual_comp α β hα hβ).norm measurable_const
  have ht : MeasurableSet {x | collisionTime (α x) (β x) ∈ Jplus} :=
    hJplus.preimage (measurable_collisionTime_comp α β hα hβ)
  exact Measurable.ite (hz.inter (hr.inter ht)) hα.norm.ennreal_ofReal.inv measurable_const

end StickyKakeya4
