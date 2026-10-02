import Theorems.Thm_StickyKakeya4_borel_selector_foundations
import Theorems.Thm_StickyKakeya4_measurable_selector_parametrization
import Theorems.Thm_StickyKakeya4_vector_center_carleson
import Theorems.Thm_StickyKakeya4_wz_common_slab

/-!
# An actual bounded-density slope source inside the original marked front

Pull the Borel selector back along `a ↦ normalize (a,1)`. Restrict ordinary
three-dimensional Lebesgue measure to the unit slope ball and one positive
marked-centre bin. No comparison of spherical and slope Jacobians is needed.
The selected segments contain a common height interval of length `3/8`.
The final theorem constructs the measure, intercept, and support directly
from a compact valid full-direction marked datum; it has no residual estimate
or assumed source-support certificate among its hypotheses.
-/

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace StickyKakeya4.ActualSlopeSource

/-- The literal point `(x,s)` in the repository's four-dimensional space. -/
def heightPoint (x : E3) (s : ℝ) : E4 :=
  WithLp.toLp 2 (Fin.lastCases s (fun i : Fin 3 => x i))

@[simp] theorem heightPoint_castSucc (x : E3) (s : ℝ) (i : Fin 3) :
    heightPoint x s i.castSucc = x i := by simp [heightPoint]

@[simp] theorem heightPoint_last (x : E3) (s : ℝ) :
    heightPoint x s (Fin.last 3) = s := by
  simpa [heightPoint] using
    (Fin.lastCases_last (motive := fun _ : Fin 4 => ℝ)
      (last := s) (cast := fun i : Fin 3 => x i))

theorem measurable_northSlopeLift : Measurable northSlopeLift := by
  apply (WithLp.measurable_toLp 2 (Fin 4 → ℝ)).comp
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change Measurable (fun a : E3 => northSlopeLift a (Fin.last 3))
    simp_rw [northSlopeLift_last]
    exact measurable_const
  · change Measurable (fun a : E3 => northSlopeLift a j.castSucc)
    simp_rw [northSlopeLift_castSucc]
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).measurable

theorem measurable_northSlopeDirection : Measurable northSlopeDirection := by
  apply Measurable.subtype_mk
  change Measurable (fun a : E3 => ‖northSlopeLift a‖⁻¹ • northSlopeLift a)
  exact measurable_northSlopeLift.norm.inv.smul measurable_northSlopeLift

theorem northSlopeDirection_fourth (a : E3) :
    (northSlopeDirection a : E4) (3 : Fin 4) = ‖northSlopeLift a‖⁻¹ := by
  change ‖northSlopeLift a‖⁻¹ * northSlopeLift a (Fin.last 3) = _
  rw [northSlopeLift_last, mul_one]

theorem northSlopeLift_zero_norm : ‖northSlopeLift (0 : E3)‖ = 1 := by
  have heq : northSlopeLift (0 : E3) = EuclideanSpace.single (Fin.last 3) (1 : ℝ) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [northSlopeLift_last]
      simp
    · rw [northSlopeLift_castSucc]
      simp only [PiLp.zero_apply, EuclideanSpace.single_apply,
        Fin.castSucc_ne_last, if_false]
  rw [heq]
  simp

theorem northSlopeDirection_fourth_ge_half {a : E3}
    (ha : a ∈ Metric.ball (0 : E3) 1) :
    (1 / 2 : ℝ) ≤ (northSlopeDirection a : E4) (3 : Fin 4) := by
  have hanorm : ‖a‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using ha
  have hnpos : 0 < ‖northSlopeLift a‖ :=
    zero_lt_one.trans_le (northSlopeLift_norm_ge_one a)
  have hnupper : ‖northSlopeLift a‖ ≤ 2 := by
    have htriangle := norm_add_le (northSlopeLift a - northSlopeLift 0) (northSlopeLift 0)
    rw [sub_add_cancel, northSlopeLift_sub_norm, sub_zero, northSlopeLift_zero_norm]
      at htriangle
    linarith
  rw [northSlopeDirection_fourth, inv_eq_one_div]
  exact (le_div_iff₀ hnpos).2 (by linarith)

theorem measurable_northGraphIntercept : Measurable northGraphIntercept := by
  unfold northGraphIntercept northGraphSlope horizontalProjection direction offset
  fun_prop

section Selector

variable (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
  (hvalid : ∀ line ∈ selector, IsValidLine line)
  (hselector : IsDirectionSelector selector)

/-- The actual marked line chosen in slope direction `a`. -/
def slopeLine (a : E3) : MarkedLine :=
  selectorLine selector hmeas hvalid hselector (northSlopeDirection a)

theorem measurable_slopeLine :
    Measurable (slopeLine selector hmeas hvalid hselector) :=
  measurable_subtype_coe.comp
    ((measurable_selectorLine selector hmeas hvalid hselector).comp
      measurable_northSlopeDirection)

theorem slopeLine_mem (a : E3) :
    slopeLine selector hmeas hvalid hselector a ∈ selector :=
  (selectorLine selector hmeas hvalid hselector (northSlopeDirection a)).property

theorem direction_slopeLine (a : E3) :
    direction (slopeLine selector hmeas hvalid hselector a) = northSlopeDirection a :=
  direction_selectorLine selector hmeas hvalid hselector (northSlopeDirection a)

theorem slope_slopeLine (a : E3) :
    northGraphSlope (slopeLine selector hmeas hvalid hselector a) = a := by
  have hn : ‖northSlopeLift a‖ ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (northSlopeLift_norm_ge_one a))
  unfold northGraphSlope
  rw [direction_slopeLine]
  ext i
  change (‖northSlopeLift a‖⁻¹ * northSlopeLift a (Fin.last 3))⁻¹ *
      (‖northSlopeLift a‖⁻¹ * northSlopeLift a i.castSucc) = a i
  rw [northSlopeLift_last, northSlopeLift_castSucc, mul_one, inv_inv,
    ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

/-- Fixed-width centre bins in ordinary slope coordinates. -/
def sourceSet (k : ℤ) : Set E3 :=
  Metric.ball 0 1 ∩
    (wzMarkedCenterHeight ∘ slopeLine selector hmeas hvalid hselector) ⁻¹'
      Ico ((k : ℝ) / 8) (((k : ℝ) + 1) / 8)

theorem measurableSet_sourceSet (k : ℤ) :
    MeasurableSet (sourceSet selector hmeas hvalid hselector k) :=
  measurableSet_ball.inter
    (measurableSet_Ico.preimage
      (measurable_wzMarkedCenterHeight.comp
        (measurable_slopeLine selector hmeas hvalid hselector)))

theorem exists_positive_sourceSet :
    ∃ k : ℤ, (volume : Measure E3) (sourceSet selector hmeas hvalid hselector k) ≠ 0 := by
  have hcover : Metric.ball (0 : E3) 1 ⊆
      ⋃ k : ℤ, sourceSet selector hmeas hvalid hselector k := by
    intro a ha
    let z := wzMarkedCenterHeight (slopeLine selector hmeas hvalid hselector a)
    refine mem_iUnion.2 ⟨⌊8 * z⌋, ha, ?_⟩
    have hlo := Int.floor_le (8 * z)
    have hhi := Int.lt_floor_add_one (8 * z)
    change ((⌊8 * z⌋ : ℤ) : ℝ) / 8 ≤ z ∧
      z < (((⌊8 * z⌋ : ℤ) : ℝ) + 1) / 8
    constructor <;> linarith
  by_contra h
  push Not at h
  have hz : (volume : Measure E3)
      (⋃ k : ℤ, sourceSet selector hmeas hvalid hselector k) = 0 := measure_iUnion_null h
  exact (Metric.measure_ball_pos (volume : Measure E3) (0 : E3) (by norm_num : (0 : ℝ) < 1)).ne'
    (measure_mono_null hcover hz)

/-- Lebesgue restriction is the desired density-at-most-one source. -/
def sourceMeasure (k : ℤ) : Measure E3 :=
  volume.restrict (sourceSet selector hmeas hvalid hselector k)

instance sourceMeasure_isFinite (k : ℤ) :
    IsFiniteMeasure (sourceMeasure selector hmeas hvalid hselector k) := by
  constructor
  rw [sourceMeasure, Measure.restrict_apply_univ]
  exact (measure_mono inter_subset_left).trans_lt measure_ball_lt_top

theorem sourceMeasure_le_volume (k : ℤ) :
    sourceMeasure selector hmeas hvalid hselector k ≤ volume :=
  Measure.restrict_le_self

theorem sourceMeasure_slope_norm_le_one (k : ℤ) :
    ∀ᵐ a ∂sourceMeasure selector hmeas hvalid hselector k, ‖a‖ ≤ 1 := by
  filter_upwards [ae_restrict_mem (measurableSet_sourceSet selector hmeas hvalid hselector k)]
    with a ha
  exact (show ‖a‖ < 1 by simpa [Metric.mem_ball, dist_zero_right] using ha.1).le

theorem sourceMeasure_mass_pos (k : ℤ)
    (hk : (volume : Measure E3) (sourceSet selector hmeas hvalid hselector k) ≠ 0) :
    0 < sourceMeasure selector hmeas hvalid hselector k univ := by
  simpa [sourceMeasure] using (pos_iff_ne_zero.mpr hk)

/-- The intercept is inherited from the chosen marked line. -/
def intercept (a : E3) : E3 :=
  northGraphIntercept (slopeLine selector hmeas hvalid hselector a)

theorem measurable_intercept :
    Measurable (intercept selector hmeas hvalid hselector) :=
  measurable_northGraphIntercept.comp (measurable_slopeLine selector hmeas hvalid hselector)

theorem sourceSet_contains_slab (k : ℤ) {a : E3}
    (ha : a ∈ sourceSet selector hmeas hvalid hselector k) :
    ContainsWZHeightSlab (slopeLine selector hmeas hvalid hselector a)
      (Icc ((k : ℝ) / 8 - 1 / 8) ((k : ℝ) / 8 + 1 / 4)) := by
  have hdir : (1 / 2 : ℝ) ≤
      direction (slopeLine selector hmeas hvalid hselector a) (3 : Fin 4) := by
    rw [direction_slopeLine]
    exact northSlopeDirection_fourth_ge_half ha.1
  have hcenter := ha.2
  change (k : ℝ) / 8 ≤ wzMarkedCenterHeight (slopeLine selector hmeas hvalid hselector a) ∧
    wzMarkedCenterHeight (slopeLine selector hmeas hvalid hselector a) <
      ((k : ℝ) + 1) / 8 at hcenter
  convert containsWZHeightSlab_of_center_bin
      (slopeLine selector hmeas hvalid hselector a)
      (c := (1 / 2 : ℝ)) (u := (k : ℝ) / 8) (h := (1 / 8 : ℝ))
      (by norm_num) hdir hcenter.1 (by linarith [hcenter.2]) using 1 <;> congr 1 <;> ring

theorem graph_eq_wzGraphPoint (a : E3) (s : ℝ) :
    heightPoint (intercept selector hmeas hvalid hselector a + s • a) s =
      wzGraphPoint (slopeLine selector hmeas hvalid hselector a) s := by
  have hchart : direction (slopeLine selector hmeas hvalid hselector a) (3 : Fin 4) ≠ 0 := by
    rw [direction_slopeLine, northSlopeDirection_fourth]
    exact inv_ne_zero (ne_of_gt (zero_lt_one.trans_le (northSlopeLift_norm_ge_one a)))
  have hh := horizontalProjection_fixedHeightPoint
    (slopeLine selector hmeas hvalid hselector a) s hchart
  rw [northGraphEvaluation, slope_slopeLine] at hh
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [heightPoint_last]
    exact (wzGraphPoint_fourth_coordinate _ s hchart).symm
  · rw [heightPoint_castSucc]
    exact (congrArg (fun x : E3 => x j) hh).symm

theorem source_graph_mem_unitFront (k : ℤ) :
    ∀ᵐ a ∂sourceMeasure selector hmeas hvalid hselector k,
      ∀ s ∈ Icc ((k : ℝ) / 8 - 1 / 8) ((k : ℝ) / 8 + 1 / 4),
        heightPoint (intercept selector hmeas hvalid hselector a + s • a) s ∈
          unitFront selector := by
  filter_upwards [ae_restrict_mem (measurableSet_sourceSet selector hmeas hvalid hselector k)]
    with a ha
  intro s hs
  rw [graph_eq_wzGraphPoint]
  have hpoint := wzGraphPoint_mem_unitFront_singleton
    (slopeLine selector hmeas hvalid hselector a) _
    (sourceSet_contains_slab selector hmeas hvalid hselector k ha) hs
  rcases hpoint with ⟨line, hline, t, ht, heq⟩
  rw [mem_singleton_iff] at hline
  subst line
  exact ⟨_, slopeLine_mem selector hmeas hvalid hselector a, t, ht, heq⟩

end Selector

/-- An actual positive finite bounded-density slope source for every compact
valid full-direction datum. The common interval has the fixed length `3/8`.
The support conclusion is uniform in height outside one source-null set. -/
theorem compact_full_direction_actual_slope_source
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (hvalid : ∀ line ∈ ambient, IsValidLine line) (hfull : FullDirection ambient) :
    ∃ (σ : Measure E3) (b : E3 → E3) (u v : ℝ),
      IsFiniteMeasure σ ∧ 0 < σ univ ∧ σ ≤ volume ∧ Measurable b ∧
      v - u = 3 / 8 ∧
      (∀ᵐ a ∂σ, ‖a‖ ≤ 1) ∧
      ∀ᵐ a ∂σ, ∀ s ∈ Icc u v, heightPoint (b a + s • a) s ∈ unitFront ambient := by
  obtain ⟨selector, hmeas, hsubset, hselector⟩ :=
    compact_full_direction_borel_selector ambient hcompact hfull
  have hselvalid : ∀ line ∈ selector, IsValidLine line :=
    fun line hline => hvalid line (hsubset hline)
  obtain ⟨k, hk⟩ := exists_positive_sourceSet selector hmeas hselvalid hselector
  refine ⟨sourceMeasure selector hmeas hselvalid hselector k,
    intercept selector hmeas hselvalid hselector,
    (k : ℝ) / 8 - 1 / 8, (k : ℝ) / 8 + 1 / 4,
    inferInstance, sourceMeasure_mass_pos selector hmeas hselvalid hselector k hk,
    sourceMeasure_le_volume selector hmeas hselvalid hselector k,
    measurable_intercept selector hmeas hselvalid hselector, by ring,
    sourceMeasure_slope_norm_le_one selector hmeas hselvalid hselector k, ?_⟩
  filter_upwards [source_graph_mem_unitFront selector hmeas hselvalid hselector k]
    with a ha
  intro s hs
  rcases ha s hs with ⟨line, hline, t, ht, heq⟩
  exact ⟨line, hsubset hline, t, ht, heq⟩

end StickyKakeya4.ActualSlopeSource
