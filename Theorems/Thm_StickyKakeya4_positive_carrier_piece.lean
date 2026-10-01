import Theorems.Thm_StickyKakeya4_dimension_witness_extraction
import Theorems.Thm_StickyKakeya4_selector_carrier_measure

open Filter MeasureTheory Set

noncomputable section

namespace StickyKakeya4

/-- A packing-dimension-three measurable direction selector has a carrier
piece of positive canonical directional mass with a genuine small-scale
covering estimate.  Thus the countable-cover witness supplied by packing
dimension is now tied to the actual selector, rather than to an arbitrary
auxiliary measure. -/
theorem packing_selector_extract_positive_carrier_piece
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3)
    {slack : ENNReal} (hslack : 0 < slack) :
    ∃ piece : Set (E4 × E4),
      (selectorCarrierProbability selector hmeasurable hvalid hselector :
        Measure (E4 × E4)) piece ≠ 0 ∧
      ∃ d : ENNReal, d < 3 + slack ∧ d ≠ ⊤ ∧
        ∃ C : ENNReal, C ≠ ⊤ ∧
          ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            coveringNumber piece r ≤
              C * (ENNReal.ofReal r).rpow (-d.toReal) := by
  apply packingDim_eq_three_extract_nonzero_measure_power_piece
    (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4))
    (lineCarrier selector) hpacking
  · rw [selectorCarrierProbability_apply_lineCarrier selector hmeasurable hvalid hselector]
    norm_num
  · exact hslack

/-- The positive packing piece may be cut back to the actual selector carrier
without losing mass or its finite-scale covering bound.  In particular every
point retained for the later inverse parametrization represents a genuine
selector line. -/
theorem packing_selector_extract_positive_internal_carrier_piece
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3)
    {slack : ENNReal} (hslack : 0 < slack) :
    ∃ piece : Set (E4 × E4),
      piece ⊆ lineCarrier selector ∧
      (selectorCarrierProbability selector hmeasurable hvalid hselector :
        Measure (E4 × E4)) piece ≠ 0 ∧
      ∃ d : ENNReal, d < 3 + slack ∧ d ≠ ⊤ ∧
        ∃ C : ENNReal, C ≠ ⊤ ∧
          ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            coveringNumber piece r ≤
              C * (ENNReal.ofReal r).rpow (-d.toReal) := by
  obtain ⟨piece, hpiece, d, hd, hdtop, C, hCtop, hcover⟩ :=
    packing_selector_extract_positive_carrier_piece selector hmeasurable
      hvalid hselector hpacking hslack
  let mu : Measure (E4 × E4) :=
    selectorCarrierProbability selector hmeasurable hvalid hselector
  have hae : ∀ᵐ x ∂mu, x ∈ lineCarrier selector := by
    rw [ae_iff]
    exact selectorCarrierProbability_apply_compl_lineCarrier
      selector hmeasurable hvalid hselector
  refine ⟨piece ∩ lineCarrier selector, Set.inter_subset_right, ?_, d, hd,
    hdtop, C, hCtop, ?_⟩
  · rw [Set.inter_comm, Measure.measure_inter_eq_of_ae hae]
    exact hpiece
  · filter_upwards [hcover] with r hr
    exact (coveringNumber_mono Set.inter_subset_left r).trans hr

/-- A measurable positive-mass carrier piece.  Closing the internal packing
piece makes it Borel; intersecting again with the measurable carrier keeps
every point genuine.  The harmless radius loss `r ↦ r / 2` is recorded
explicitly instead of being hidden in an unspecified constant. -/
theorem packing_selector_extract_positive_measurable_carrier_piece
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3)
    {slack : ENNReal} (hslack : 0 < slack) :
    ∃ piece : Set (E4 × E4),
      MeasurableSet piece ∧
      piece ⊆ lineCarrier selector ∧
      (selectorCarrierProbability selector hmeasurable hvalid hselector :
        Measure (E4 × E4)) piece ≠ 0 ∧
      ∃ d : ENNReal, d < 3 + slack ∧ d ≠ ⊤ ∧
        ∃ C : ENNReal, C ≠ ⊤ ∧
          ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            coveringNumber piece r ≤
              C * (ENNReal.ofReal (r / 2)).rpow (-d.toReal) := by
  obtain ⟨internal, hinternal, hmass, d, hd, hdtop, C, hCtop, hcover⟩ :=
    packing_selector_extract_positive_internal_carrier_piece selector hmeasurable
      hvalid hselector hpacking hslack
  let piece := closure internal ∩ lineCarrier selector
  have hpiece_meas : MeasurableSet piece :=
    isClosed_closure.measurableSet.inter
      (measurableSet_lineCarrier_of_selector selector hmeasurable hvalid hselector)
  have hpiece_sub : piece ⊆ lineCarrier selector := Set.inter_subset_right
  have hinternal_piece : internal ⊆ piece := by
    intro x hx
    exact ⟨subset_closure hx, hinternal hx⟩
  have hpiece_mass :
      (selectorCarrierProbability selector hmeasurable hvalid hselector :
        Measure (E4 × E4)) piece ≠ 0 := by
    intro hz
    exact hmass (measure_mono_null hinternal_piece hz)
  have hhalf :
      Tendsto (fun r : ℝ => r / 2) (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht : Tendsto (fun r : ℝ => r / 2) (nhds 0) (nhds 0) := by
        have hc : ContinuousAt (fun r : ℝ => r / 2) 0 :=
          (continuous_id.div_const (2 : ℝ)).continuousAt
        simpa using hc.tendsto
      exact ht.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with r hr
      show 0 < r / (2 : ℝ)
      exact div_pos hr (by norm_num)
  have hcover_half := hhalf.eventually hcover
  refine ⟨piece, hpiece_meas, hpiece_sub, hpiece_mass, d, hd, hdtop, C, hCtop, ?_⟩
  filter_upwards [hcover_half, self_mem_nhdsWithin] with r hr hrpos
  exact (coveringNumber_mono Set.inter_subset_left r).trans
    ((coveringNumber_closure_le internal hrpos).trans hr)

end StickyKakeya4
