import Theorems.Thm_StickyKakeya4_canonical_sphere_measure

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- Normalized Lebesgue probability on the retained affine-fibre interval. -/
noncomputable def realFibreIntervalProbability : ProbabilityMeasure ℝ :=
  FiniteMeasure.normalize
    (⟨volume.restrict (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)), inferInstance⟩ :
      FiniteMeasure ℝ)

theorem realFibreIntervalProbability_toMeasure :
    (realFibreIntervalProbability : Measure ℝ) =
      volume.restrict (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
  let m : FiniteMeasure ℝ :=
    ⟨volume.restrict (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)), inferInstance⟩
  have hmass : m.mass = 1 := by
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_mass]
    simp [m, Measure.restrict_apply, Real.volume_Icc]
    norm_num
  have hm : m ≠ 0 := by
    intro hzero
    have := congrArg FiniteMeasure.mass hzero
    rw [hmass] at this
    simpa using this
  change (m.normalize : Measure ℝ) = _
  rw [m.toMeasure_normalize_eq_of_nonzero hm, hmass]
  simp [m]

/-- The same probability, now typed by the interval itself.  The projection is
the identity on the restricted measure's support, while the subtype makes it
impossible for later source constructions to forget the fibre restriction. -/
noncomputable def fibreIntervalProbability :
    ProbabilityMeasure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
  ProbabilityMeasure.map realFibreIntervalProbability
    ((continuous_projIcc
      (a := -(1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (h := by norm_num)).measurable.aemeasurable)

/-- The typed fibre probability is exactly restricted Lebesgue measure read
through the subtype coercion. -/
theorem fibreIntervalProbability_apply
    (A : Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (hA : MeasurableSet A) :
    (fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) A =
      volume ((fun t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) =>
        (t : ℝ)) '' A) := by
  let p : ℝ → Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    Set.projIcc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) (by norm_num)
  rw [fibreIntervalProbability, ProbabilityMeasure.toMeasure_map]
  change (Measure.map p (realFibreIntervalProbability : Measure ℝ)) A = _
  rw [Measure.map_apply
    ((continuous_projIcc
      (a := -(1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (h := by norm_num)).measurable) hA]
  rw [realFibreIntervalProbability_toMeasure,
    Measure.restrict_apply
      (hA.preimage ((continuous_projIcc
        (a := -(1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
        (h := by norm_num)).measurable))]
  congr 1
  ext t
  constructor
  · rintro ⟨hpt, ht⟩
    refine ⟨⟨t, ht⟩, ?_, rfl⟩
    simpa [p, Set.projIcc_of_mem (h := by norm_num) ht] using hpt
  · rintro ⟨s, hsA, hst⟩
    subst t
    refine ⟨?_, s.property⟩
    simpa [p, Set.projIcc_of_mem (h := by norm_num) s.property] using hsA

theorem fibreIntervalProbability_apply_le_Ioo
    (A : Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (hA : MeasurableSet A) {a delta : ℝ} (hdelta : 0 ≤ delta)
    (hsub : ∀ t ∈ A, (t : ℝ) ∈ Set.Ioo (a - delta) (a + delta)) :
    (fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) A ≤
      ENNReal.ofReal (2 * delta) := by
  rw [fibreIntervalProbability_apply A hA]
  calc
    volume ((fun t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) =>
        (t : ℝ)) '' A) ≤ volume (Set.Ioo (a - delta) (a + delta)) := by
      apply measure_mono
      rintro _ ⟨t, ht, rfl⟩
      exact hsub t ht
    _ = ENNReal.ofReal ((a + delta) - (a - delta)) := Real.volume_Ioo
    _ = ENNReal.ofReal (2 * delta) := by congr 1 <;> ring

def fibreProjectionCenter (line : MarkedLine) (x : E4) : ℝ :=
  inner ℝ (x - offset line) (direction line) - mark line

theorem fibre_parameter_sub_projectionCenter
    {line : MarkedLine} (hvalid : IsValidLine line) (x : E4) (t : ℝ) :
    t - fibreProjectionCenter line x =
      inner ℝ (rawFrontParam (line, t) - x) (direction line) := by
  simp [fibreProjectionCenter, rawFrontParam, inner_add_left,
    inner_sub_left, inner_smul_left, hvalid.2]
  rw [hvalid.1]
  ring

def markedLineBallFibreSet (line : MarkedLine) (x : E4) (delta : ℝ) :
    Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
  {t | rawFrontParam (line, (t : ℝ)) ∈ Metric.ball x delta}

theorem measurableSet_markedLineBallFibreSet
    (line : MarkedLine) (x : E4) (delta : ℝ) :
    MeasurableSet (markedLineBallFibreSet line x delta) := by
  apply Metric.isOpen_ball.measurableSet.preimage
  exact continuous_rawFrontParam.measurable.comp
    (measurable_const.prodMk measurable_subtype_coe)

/-- A unit-speed valid marked line spends at most `2 * delta` of normalized
fibre time in any physical radius-`delta` ball. -/
theorem fibreIntervalProbability_markedLineBallFibreSet_le
    {line : MarkedLine} (hvalid : IsValidLine line)
    (x : E4) {delta : ℝ} (hdelta : 0 ≤ delta) :
    (fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
        (markedLineBallFibreSet line x delta) ≤
      ENNReal.ofReal (2 * delta) := by
  apply fibreIntervalProbability_apply_le_Ioo
    (markedLineBallFibreSet line x delta)
    (measurableSet_markedLineBallFibreSet line x delta)
    hdelta
  intro t ht
  change dist (rawFrontParam (line, (t : ℝ))) x < delta at ht
  have hinner := abs_real_inner_le_norm
    (rawFrontParam (line, (t : ℝ)) - x) (direction line)
  rw [hvalid.1, mul_one] at hinner
  have habs :
      |(t : ℝ) - fibreProjectionCenter line x| < delta := by
    rw [fibre_parameter_sub_projectionCenter hvalid x (t : ℝ)]
    exact hinner.trans_lt (by simpa [dist_eq_norm] using ht)
  rw [Set.mem_Ioo]
  rw [abs_lt] at habs
  constructor <;> linarith

/-- Canonical probability on direction--fibre coordinates.  Its second
coordinate is the displacement from the retained affine mark, not an
unmarked line parameter. -/
noncomputable def frontParameterProbability :
    ProbabilityMeasure
      ({theta : E4 // ‖theta‖ = 1} × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
  ProbabilityMeasure.prod normSphereProbability fibreIntervalProbability

/-- Push the canonical direction--fibre probability through the exact front
parametrization.  No measurability of the image set is assumed here. -/
noncomputable def selectorFrontProbability
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) : ProbabilityMeasure E4 :=
  ProbabilityMeasure.map frontParameterProbability
    (measurable_frontParametrization selector hmeasurable hvalid hselector).aemeasurable

/-- Every parameter point lands in the physical front.  This pointwise
statement avoids silently asserting that an arbitrary Borel selector has a
Borel image under the collision-prone front map. -/
theorem frontParametrization_mem_unitFront
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (z : {theta : E4 // ‖theta‖ = 1} ×
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    frontParametrization selector hmeasurable hvalid hselector z ∈
      unitFront selector := by
  rw [← range_frontParametrization selector hmeasurable hvalid hselector]
  exact ⟨z, rfl⟩

end StickyKakeya4
