import Theorems.Thm_StickyKakeya4_affine_focus_energy_escape
import Theorems.Thm_StickyKakeya4_hairbrush_compact_decay
import Theorems.Thm_StickyKakeya4_original_residual_criterion

/-!
# Every-reference hairbrush nullity on the original deficient front

Positive exact contact with one reference line allows source-dependent
contact times. The actual affine-focus energy escape handles this geometry
without forcing a common time or passing through a four-cycle argument.
Compact-reference uniformity is qualitative, with no asserted power rate.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology
noncomputable section

namespace StickyKakeya4.NoFrostmanUniformHairbrush

open HairbrushCompactDecay

theorem exact_contact_eq_affine_focus (a b a₀ b₀ : E3) (t : ℝ)
    (ha : a ≠ a₀) (hcontact : ‖(b - b₀) + t • (a - a₀)‖ ≤ 0) :
    b = b₀ - collisionTime (a - a₀) (b - b₀) • (a - a₀) := by
  have hα : a - a₀ ≠ 0 := sub_ne_zero.mpr ha
  have ht := (collision_sublevel_localization (a - a₀) (b - b₀) hα
    0 t le_rfl hcontact).1
  rw [zero_div] at ht
  have heq : collisionTime (a - a₀) (b - b₀) = t :=
    sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm ht (abs_nonneg _)))
  have hzero : (b - b₀) + t • (a - a₀) = 0 :=
    norm_eq_zero.mp (le_antisymm hcontact (norm_nonneg _))
  rw [heq]
  apply eq_sub_iff_add_eq.mpr
  calc
    b + t • (a - a₀) = ((b - b₀) + t • (a - a₀)) + b₀ := by module
    _ = b₀ := by rw [hzero]; simp

/-- Every fixed reference is null. The reference need not be a member of the
source carrier, and its contact-time window need not be the marked slab. -/
theorem exact_hairbrush_null_of_front_dimH_ne_four
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1) (b : E3 → E3) (hb : Measurable b)
    (u v : ℝ) (huv : u < v) (K : Set E4) (hdim : dimH K ≠ 4)
    (hsupport : (((volume.restrict (Icc u v)).prod σ).map
      (slopeSpacetimePoint b)) Kᶜ = 0)
    (I : Set ℝ) (hI : IsCompact I) (z : Phase) :
    σ (hairbrush b I z 0) = 0 := by
  classical
  by_contra hpositive
  have hH : MeasurableSet (hairbrush b I z 0) := measurableSet_hairbrush b hb I hI z 0
  have hpoint : σ {z.1} = 0 := le_antisymm ((hσ _).trans_eq (by simp)) bot_le
  have hremaining : σ (hairbrush b I z 0 \ {z.1}) ≠ 0 := by
    rwa [measure_sdiff_null hpoint]
  let A : ℕ → Set E3 := fun n => hairbrush b I z 0 ∩
    {a | 1 / ((n : ℝ) + 1) ≤ ‖a - z.1‖}
  have hA (n : ℕ) : MeasurableSet (A n) :=
    hH.inter (measurableSet_le measurable_const (by fun_prop))
  have hcover : hairbrush b I z 0 \ {z.1} ⊆ ⋃ n, A n := by
    intro a ha
    have hne : a ≠ z.1 := by simpa only [mem_singleton_iff] using ha.2
    have hnorm : 0 < ‖a - z.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hnorm
    exact mem_iUnion.mpr ⟨n, ha.1, hn.le⟩
  obtain ⟨n, hn⟩ := exists_nonzero_measure_piece_of_countable_cover σ hcover hremaining
  let μ := σ.restrict (A n)
  have hμle : μ ≤ σ := Measure.restrict_le_self
  have hμpos : μ ≠ 0 := by
    intro hz
    have hu : μ univ = 0 := by rw [hz]; simp
    exact hn (by simpa only [μ, Measure.restrict_apply_univ] using hu)
  have hμunit : ∀ᵐ a ∂μ, ‖a‖ ≤ 1 := hunit.filter_mono (ae_mono hμle)
  let τ : E3 → ℝ := fun a => collisionTime (a - z.1) (b a - z.2)
  have hτ : Measurable τ := measurable_collisionTime_comp _ _ (by fun_prop) (by fun_prop)
  have hann : ∀ᵐ a ∂μ, 1 / ((n : ℝ) + 1) ≤ ‖a - z.1‖ :=
    (ae_restrict_mem (hA n)).mono fun a ha => ha.2
  have hrep : ∀ᵐ a ∂μ, b a = z.2 - τ a • (a - z.1) := by
    filter_upwards [ae_restrict_mem (hA n)] with a ha
    obtain ⟨t, _ht, hc⟩ := ha.1
    have hne : a ≠ z.1 := by
      intro heq
      have hbad := ha.2
      change 1 / ((n : ℝ) + 1) ≤ ‖a - z.1‖ at hbad
      rw [heq, sub_self, norm_zero] at hbad
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      exact hpos.not_ge hbad
    exact exact_contact_eq_affine_focus a (b a) z.1 z.2 t hne hc
  have hF := measurable_slopeSpacetimePoint b hb
  have hμsupport : (((volume.restrict (Icc u v)).prod μ).map
      (slopeSpacetimePoint b)) Kᶜ = 0 := by
    apply le_antisymm ?_ bot_le
    exact (((Measure.map_mono (Measure.prod_mono le_rfl hμle) hF) Kᶜ).trans_eq hsupport)
  exact hdim (AffineFocusEnergyEscape.original_front_dimH_eq_four_of_ae_affine_focus
    μ (hμle.trans hσ) hμpos hμunit b z.2 z.1 hτ
    (1 / ((n : ℝ) + 1)) u v (by positivity) huv hann hrep K hμsupport)

/-- The actual no-dimension-four hypothesis now gives maximum-row decay
uniformly over every compact reference family, with variable contact times. -/
theorem uniform_hairbrush_decay_of_front_dimH_ne_four
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1) (b : E3 → E3) (hb : Measurable b)
    (u v : ℝ) (huv : u < v) (K : Set E4) (hdim : dimH K ≠ 4)
    (hsupport : (((volume.restrict (Icc u v)).prod σ).map
      (slopeSpacetimePoint b)) Kᶜ = 0)
    (I : Set ℝ) (hI : IsCompact I) (hIne : I.Nonempty)
    (Z : Set Phase) (hZ : IsCompact Z) (p : ENNReal) (hp : 0 < p) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Z, σ (hairbrush b I z r) < p := by
  obtain ⟨t₀, _ht₀, hmax⟩ := hI.exists_isMaxOn hIne
    (show ContinuousOn (fun t : ℝ => |t|) I from continuous_abs.continuousOn)
  have hT : ∀ t ∈ I, |t| ≤ |t₀| := fun t ht => hmax ht
  exact uniform_small_hairbrush_mass_of_exact_null σ b hb I hI hIne |t₀| hT Z hZ
    (fun z _ => exact_hairbrush_null_of_front_dimH_ne_four σ hσ hunit b hb
      u v huv K hdim hsupport I hI z) p hp

/-- Original-data endpoint with a single fixed source and marked slab.
The compact reference range and compact collision window are chosen only
after the source, and every such choice has qualitative maximum-row decay. -/
theorem sticky_datum_exists_actual_uniform_hairbrush_decay
    (ambient : Set MarkedLine) (hsticky : IsStickyDatum ambient)
    (hdim : dimH (unitFront ambient) ≠ 4) :
    ∃ (σ : Measure E3) (b : E3 → E3) (u v : ℝ),
      IsFiniteMeasure σ ∧ 0 < σ univ ∧ σ ≤ volume ∧ Measurable b ∧
      v - u = 3 / 8 ∧ (∀ᵐ a ∂σ, ‖a‖ ≤ 1) ∧
      (∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
        ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient) ∧
      ∀ (I : Set ℝ), IsCompact I → I.Nonempty →
        ∀ (Z : Set Phase), IsCompact Z → ∀ p : ENNReal, 0 < p →
          ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Z, σ (hairbrush b I z r) < p := by
  obtain ⟨σ, b, u, v, hfinite, hpos, hvol, hb, huv, hunit, hsupport⟩ :=
    ActualSlopeSource.compact_full_direction_actual_slope_source
      ambient hsticky.1 hsticky.2.1 hsticky.2.2.1
  let : IsFiniteMeasure σ := hfinite
  have hfront : (((volume.restrict (Icc u v)).prod σ).map
      (slopeSpacetimePoint b)) (unitFront ambient)ᶜ = 0 :=
    OriginalResidualCriterion.sourceFrontMeasure_supported σ b hb u v
      (unitFront ambient) (StickyKakeya4.IsCompact.unitFront hsticky.1).measurableSet hsupport
  refine ⟨σ, b, u, v, hfinite, hpos, hvol, hb, huv, hunit, hsupport, ?_⟩
  intro I hI hIne Z hZ p hp
  exact uniform_hairbrush_decay_of_front_dimH_ne_four σ hvol hunit b hb
    u v (by linarith) (unitFront ambient) hdim hfront I hI hIne Z hZ p hp

end StickyKakeya4.NoFrostmanUniformHairbrush
