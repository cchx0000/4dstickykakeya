import Theorems.Thm_StickyKakeya4_selector_carrier_measure

open MeasureTheory Set

noncomputable section

namespace StickyKakeya4

/-!
Covering-number lower bounds supplied by the canonical direction measure.

This is the quantitative core of the previously external assertion that a
full-direction selector carrier has packing dimension at least three.  It is
proved directly from the cubic cap estimate, and does not assume any
dimension theorem.
-/

/-- A finite radius-`r` cover of a set carrying mass `mu s` has cardinality
at least `mu s / B` whenever every radius-`2r` ball centered on the set has
mass at most `B`.  The factor two moves an arbitrary cover center to a point
of the covered set. -/
theorem measure_div_ballBound_le_card_of_coversAtRadius
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (mu : Measure X) (s : Set X) {r : ℝ} (hr : 0 < r)
    (centers : Finset X) (hcover : coversAtRadius s r centers)
    (B : ENNReal) (hB0 : B ≠ 0) (hBtop : B ≠ ⊤)
    (hball : ∀ x ∈ s, mu (Metric.ball x (2 * r)) ≤ B) :
    mu s / B ≤ (centers.card : ENNReal) := by
  have hmass : mu s ≤ (centers.card : ENNReal) * B := by
    calc
      mu s ≤ mu (⋃ c ∈ (centers : Set X), s ∩ Metric.ball c r) := by
        apply measure_mono
        intro x hx
        obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcover hx)
        obtain ⟨hcfin, hxc⟩ := Set.mem_iUnion.mp hc
        exact Set.mem_iUnion.mpr ⟨c,
          Set.mem_iUnion.mpr ⟨hcfin, ⟨hx, hxc⟩⟩⟩
      _ ≤ ∑ c ∈ centers, mu (s ∩ Metric.ball c r) :=
        measure_biUnion_finset_le centers (fun c => s ∩ Metric.ball c r)
      _ ≤ ∑ _c ∈ centers, B := by
        apply Finset.sum_le_sum
        intro c hc
        by_cases hex : ∃ x ∈ s, x ∈ Metric.ball c r
        · obtain ⟨x, hxs, hxc⟩ := hex
          calc
            mu (s ∩ Metric.ball c r) ≤ mu (Metric.ball x (2 * r)) := by
              apply measure_mono
              rintro y ⟨hys, hyc⟩
              rw [Metric.mem_ball] at hyc hxc ⊢
              calc
                dist y x ≤ dist y c + dist c x := dist_triangle y c x
                _ < r + r := add_lt_add hyc (by simpa [dist_comm] using hxc)
                _ = 2 * r := by ring
            _ ≤ B := hball x hxs
        · have hempty : s ∩ Metric.ball c r = ∅ := by
            ext y
            constructor
            · rintro ⟨hys, hyc⟩
              exact (hex ⟨y, hys, hyc⟩).elim
            · intro hy
              exact hy.elim
          rw [hempty]
          simp
      _ = (centers.card : ENNReal) * B := by
        simp
  exact (ENNReal.div_le_iff hB0 hBtop).2 (by simpa [mul_comm] using hmass)

/-- The preceding estimate descends from every concrete finite cover to the
infimum defining `coveringNumber`. -/
theorem measure_div_ballBound_le_coveringNumber
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (mu : Measure X) (s : Set X) {r : ℝ} (hr : 0 < r)
    (B : ENNReal) (hB0 : B ≠ 0) (hBtop : B ≠ ⊤)
    (hball : ∀ x ∈ s, mu (Metric.ball x (2 * r)) ≤ B) :
    mu s / B ≤ coveringNumber s r := by
  rw [coveringNumber]
  apply le_sInf
  intro n hn
  obtain ⟨centers, hcover, rfl⟩ := hn
  exact measure_div_ballBound_le_card_of_coversAtRadius
    mu s hr centers hcover B hB0 hBtop hball

/-- A metric ball in carrier space projects into the direction cap with the
same radius. -/
theorem carrier_ball_subset_directionBall (center : E4 × E4) (r : ℝ) :
    Metric.ball center r ⊆ carrierDirectionBall center.1 r := by
  intro y hy
  rw [Metric.mem_ball] at hy
  change dist y.1 center.1 < r
  rw [Prod.dist_eq] at hy
  exact lt_of_le_of_lt (le_max_left _ _) hy

/-- The selector carrier probability satisfies a cubic bound on ordinary
carrier-space balls centered on the carrier. -/
theorem selectorCarrierProbability_ball_upper_bound
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (center : E4 × E4) (hcenter : center ∈ lineCarrier selector)
    {r : ℝ} (hr : 0 < r) (hrone : r ≤ 1) :
    (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) (Metric.ball center r) ≤
      metricSphereCapConstant * (ENNReal.ofReal r) ^ 3 := by
  obtain ⟨line, hline, hlineCenter⟩ := hcenter
  have hnorm : ‖center.1‖ = 1 := by
    rw [← hlineCenter]
    exact (hvalid line hline).1
  let theta : {theta : E4 // ‖theta‖ = 1} := ⟨center.1, hnorm⟩
  calc
    (selectorCarrierProbability selector hmeasurable hvalid hselector :
        Measure (E4 × E4)) (Metric.ball center r) ≤
        (selectorCarrierProbability selector hmeasurable hvalid hselector :
          Measure (E4 × E4)) (carrierDirectionBall center.1 r) :=
      measure_mono (carrier_ball_subset_directionBall center r)
    _ ≤ metricSphereCapConstant * (ENNReal.ofReal r) ^ 3 := by
      simpa [theta] using
        selectorCarrierProbability_carrierDirectionBall_upper_bound
          selector hmeasurable hvalid hselector theta hr hrone

/-- Concrete cubic lower bound for every sufficiently small covering number
of a measurable full-direction selector carrier. -/
theorem selectorCarrier_coveringNumber_lower_bound
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    {r : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2) :
    (1 : ENNReal) /
        (metricSphereCapConstant * (ENNReal.ofReal (2 * r)) ^ 3) ≤
      coveringNumber (lineCarrier selector) r := by
  let B : ENNReal :=
    metricSphereCapConstant * (ENNReal.ofReal (2 * r)) ^ 3
  have h2r : 0 < 2 * r := by positivity
  have h2rone : 2 * r ≤ 1 := by linarith
  have hB0 : B ≠ 0 := by
    unfold B
    exact mul_ne_zero metricSphereCapConstant_ne_zero
      (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr h2r)))
  have hBtop : B ≠ ⊤ := by
    unfold B
    exact ENNReal.mul_ne_top metricSphereCapConstant_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hmass :
      (selectorCarrierProbability selector hmeasurable hvalid hselector :
        Measure (E4 × E4)) (lineCarrier selector) = 1 :=
    selectorCarrierProbability_apply_lineCarrier
      selector hmeasurable hvalid hselector
  rw [← hmass]
  apply measure_div_ballBound_le_coveringNumber
    (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) (lineCarrier selector) hr B hB0 hBtop
  intro center hcenter
  exact selectorCarrierProbability_ball_upper_bound
    selector hmeasurable hvalid hselector center hcenter h2r h2rone

end StickyKakeya4
