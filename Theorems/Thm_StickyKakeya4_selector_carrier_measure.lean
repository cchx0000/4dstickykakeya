import Theorems.Thm_StickyKakeya4_canonical_sphere_measure

open MeasureTheory Set

noncomputable section

namespace StickyKakeya4

/-- Carrier coordinates of the unique marked selector line with direction
`theta`.  The mark is retained by `selectorLine`; only the carrier projection
is taken here because packing dimension is imposed on that projection. -/
noncomputable def selectorCarrierParam
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    {theta : E4 // ‖theta‖ = 1} → E4 × E4 :=
  fun theta =>
    let line := selectorLine selector hmeasurable hvalid hselector theta
    (direction line, offset line)

theorem measurable_selectorCarrierParam
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Measurable (selectorCarrierParam selector hmeasurable hvalid hselector) := by
  have hline : Measurable (fun theta : {theta : E4 // ‖theta‖ = 1} =>
      ((selectorLine selector hmeasurable hvalid hselector theta : selector) : MarkedLine)) :=
    measurable_subtype_coe.comp
      (measurable_selectorLine selector hmeasurable hvalid hselector)
  exact Measurable.prodMk hline.fst.fst hline.fst.snd

theorem injective_selectorCarrierParam
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Function.Injective
      (selectorCarrierParam selector hmeasurable hvalid hselector) := by
  intro theta phi h
  apply Subtype.ext
  have hfst := congrArg Prod.fst h
  simpa [selectorCarrierParam,
    direction_selectorLine selector hmeasurable hvalid hselector] using hfst

theorem selector_carrierProjection_measurableEmbedding
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    MeasurableEmbedding
      (selector.domRestrict (fun line => (direction line, offset line))) := by
  apply ContinuousOn.measurableEmbedding hmeasurable
  · exact
      (Continuous.prodMk (continuous_fst.comp continuous_fst)
        (continuous_snd.comp continuous_fst)).continuousOn
  · intro line₁ hline₁ line₂ hline₂ hcarrier
    have hdir : direction line₁ = direction line₂ := congrArg Prod.fst hcarrier
    obtain ⟨line, hline, hunique⟩ :=
      hselector (direction line₁) (hvalid line₁ hline₁).1
    exact (hunique line₁ ⟨hline₁, rfl⟩).trans
      (hunique line₂ ⟨hline₂, hdir.symm⟩).symm

theorem range_selectorCarrierParam
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Set.range (selectorCarrierParam selector hmeasurable hvalid hselector) =
      lineCarrier selector := by
  ext carrier
  constructor
  · rintro ⟨theta, rfl⟩
    exact ⟨(selectorLine selector hmeasurable hvalid hselector theta : selector),
      (selectorLine selector hmeasurable hvalid hselector theta).property, rfl⟩
  · rintro ⟨line, hline, rfl⟩
    let theta : {theta : E4 // ‖theta‖ = 1} :=
      ⟨direction line, (hvalid line hline).1⟩
    obtain ⟨chosen, hchosen, hunique⟩ :=
      hselector (direction line) (hvalid line hline).1
    have hsame :
        (selectorLine selector hmeasurable hvalid hselector theta : MarkedLine) = line :=
      (hunique _ ⟨(selectorLine selector hmeasurable hvalid hselector theta).property,
        direction_selectorLine selector hmeasurable hvalid hselector theta⟩).trans
        (hunique line ⟨hline, rfl⟩).symm
    refine ⟨theta, ?_⟩
    simp [selectorCarrierParam, hsame]

theorem measurableSet_lineCarrier_of_selector
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    MeasurableSet (lineCarrier selector) := by
  have hrange :
      Set.range (selector.domRestrict (fun line => (direction line, offset line))) =
        lineCarrier selector := by
    ext carrier
    constructor
    · rintro ⟨line, rfl⟩
      exact ⟨line.1, line.2, rfl⟩
    · rintro ⟨line, hline, rfl⟩
      exact ⟨⟨line, hline⟩, rfl⟩
  rw [← hrange]
  exact
    (selector_carrierProjection_measurableEmbedding selector hmeasurable hvalid hselector).measurableSet_range

/-- Canonical directional probability measure transported to the carrier of
the measurable selector. -/
noncomputable def selectorCarrierProbability
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    ProbabilityMeasure (E4 × E4) :=
  ProbabilityMeasure.map normSphereProbability
    (measurable_selectorCarrierParam selector hmeasurable hvalid hselector).aemeasurable

/-- The transported probability has total mass one on the whole selector
carrier.  This is the nonvanishing input needed to select a positive-mass
member from any packing-dimension countable cover. -/
theorem selectorCarrierProbability_apply_lineCarrier
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) (lineCarrier selector) = 1 := by
  have hpre :
      selectorCarrierParam selector hmeasurable hvalid hselector ⁻¹'
          lineCarrier selector = Set.univ := by
    ext theta
    constructor
    · intro _
      exact Set.mem_univ theta
    · intro _
      rw [← range_selectorCarrierParam selector hmeasurable hvalid hselector]
      exact ⟨theta, rfl⟩
  rw [selectorCarrierProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply
    (measurable_selectorCarrierParam selector hmeasurable hvalid hselector)
    (measurableSet_lineCarrier_of_selector selector hmeasurable hvalid hselector)]
  rw [hpre]
  exact IsProbabilityMeasure.measure_univ

theorem selectorCarrierProbability_apply_compl_lineCarrier
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) (lineCarrier selector)ᶜ = 0 := by
  rw [measure_compl
    (measurableSet_lineCarrier_of_selector selector hmeasurable hvalid hselector)]
  · rw [selectorCarrierProbability_apply_lineCarrier selector hmeasurable hvalid hselector]
    simp
  · rw [selectorCarrierProbability_apply_lineCarrier selector hmeasurable hvalid hselector]
    norm_num

/-- Carrier points whose direction lies in an ambient Euclidean ball. -/
def carrierDirectionBall (theta : E4) (r : ℝ) : Set (E4 × E4) :=
  Prod.fst ⁻¹' Metric.ball theta r

theorem measurableSet_carrierDirectionBall (theta : E4) (r : ℝ) :
    MeasurableSet (carrierDirectionBall theta r) :=
  Metric.isOpen_ball.measurableSet.preimage measurable_fst

/-- The carrier pushforward preserves the direction coordinate exactly, so
direction-ball mass is the canonical norm-sphere cap mass. -/
theorem selectorCarrierProbability_apply_carrierDirectionBall
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (theta : {theta : E4 // ‖theta‖ = 1}) (r : ℝ) :
    (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) (carrierDirectionBall (theta : E4) r) =
      (normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1})
        (Metric.ball theta r) := by
  rw [selectorCarrierProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply
    (measurable_selectorCarrierParam selector hmeasurable hvalid hselector)
    (measurableSet_carrierDirectionBall (theta : E4) r)]
  congr 1
  ext phi
  change dist (direction
      (selectorLine selector hmeasurable hvalid hselector phi))
      (theta : E4) < r ↔ dist (phi : E4) (theta : E4) < r
  rw [direction_selectorLine selector hmeasurable hvalid hselector]

theorem selectorCarrierProbability_carrierDirectionBall_ne_zero
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (theta : {theta : E4 // ‖theta‖ = 1}) {r : ℝ} (hr : 0 < r) :
    (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) (carrierDirectionBall (theta : E4) r) ≠ 0 := by
  rw [selectorCarrierProbability_apply_carrierDirectionBall
    selector hmeasurable hvalid hselector theta r]
  exact normSphereProbability_ball_ne_zero theta hr

/-- Uniform cubic direction-cap estimate for the canonical selector-carrier
probability. -/
theorem selectorCarrierProbability_carrierDirectionBall_upper_bound
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (theta : {theta : E4 // ‖theta‖ = 1}) {r : ℝ}
    (hr : 0 < r) (hrone : r ≤ 1) :
    (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) (carrierDirectionBall (theta : E4) r) ≤
      metricSphereCapConstant * (ENNReal.ofReal r) ^ 3 := by
  rw [selectorCarrierProbability_apply_carrierDirectionBall
    selector hmeasurable hvalid hselector theta r]
  exact normSphereProbability_ball_upper_bound theta hr hrone

end StickyKakeya4
