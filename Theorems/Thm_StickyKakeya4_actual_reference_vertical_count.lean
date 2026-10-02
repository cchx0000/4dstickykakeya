import Theorems.Thm_StickyKakeya4_actual_packing_reference_source
import Theorems.Thm_StickyKakeya4_packing_vertical_count
import Theorems.Thm_StickyKakeya4_north_slope_direction_density

open Filter MeasureTheory Set Metric
open scoped ENNReal

namespace StickyKakeya4.ActualSlopeSource

open PositiveCellRegularization PackingReferenceSource
attribute [local instance] Classical.propDecidable

/-- The actual phase reference source has one uniform vertical counting
constant. The direction bound is derived from slope volume domination and
the unit-slope support, not assumed as an extra density certificate. -/
theorem actual_source_dyadic_vertical_count
    (σ : Measure E3) (hσ : σ ≤ volume)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (f : E3 → E4 × E4) (hf : Measurable f)
    (hfst : ∀ a, (f a).1 = (northSlopeDirection a : E4))
    (c : ENNReal) (hc : 0 < c) (hc1 : c ≤ 1) (ζ : ℝ)
    (nets : ℕ → Finset (E4 × E4))
    (hsep : ∀ n, ∀ y ∈ nets n, ∀ z ∈ nets n, y ≠ z →
      dyadicRadius n / 2 ≤ dist y z)
    (hlower : ∀ n, ∀ y ∈ nets n, c * (dyadicScale n) ^ (3 + ζ) ≤
      (Measure.map f σ) (Metric.ball y (dyadicRadius n))) :
    ∃ A : ENNReal, A ≠ ⊤ ∧ ∀ n (theta : E4),
      (((nets n).filter fun y => y.1 ∈ Metric.ball theta (dyadicRadius n)).card : ENNReal) ≤
        A * (dyadicScale n) ^ (-ζ) := by
  have hmap : (Measure.map f σ).map (Prod.fst : E4 × E4 → E4) =
      σ.map (fun a => (northSlopeDirection a : E4)) := by
    rw [Measure.map_map measurable_fst hf]
    congr 1
    funext a
    exact hfst a
  obtain ⟨D, hD, hdensity⟩ := exists_northSlopeDirection_cubic_density σ hσ hunit
  have hdirection : ∀ (theta : E4) (r : ℝ), 0 < r →
      (Measure.map f σ).map (Prod.fst : E4 × E4 → E4) (Metric.ball theta r) ≤
        D * (ENNReal.ofReal r) ^ (3 : ℕ) := by
    simpa only [hmap] using hdensity
  obtain ⟨A, hA, hcount⟩ := exists_uniform_vertical_reference_count_bound
    (Measure.map f σ) (Prod.fst : E4 × E4 → E4) measurable_fst LipschitzWith.prod_fst
    c D hc (ne_top_of_le_ne_top ENNReal.one_ne_top hc1) hD ζ hdirection
  refine ⟨A, hA, ?_⟩
  intro n theta
  have hlower' : ∀ y ∈ nets n,
      c * (ENNReal.ofReal (dyadicRadius n)).rpow (3 + ζ) ≤
        (Measure.map f σ) (Metric.ball y (dyadicRadius n)) := by
    simpa only [ofReal_dyadicRadius, ENNReal.rpow_eq_pow] using hlower n
  simpa only [ofReal_dyadicRadius, ENNReal.rpow_eq_pow] using
    hcount (dyadicRadius n) (dyadicRadius_pos n) (nets n) (hsep n) hlower' theta

/-- A support restriction uses a subfamily of the fixed actual references.
The vertical count survives on every such subset; no lower-mass assertion
for the thinned source is made. -/
theorem actual_reference_cover_is_hereditary
    (f : E3 → E4 × E4) (B T : Set E3) (hTB : T ⊆ B)
    (n : ℕ) (centers : Finset (E4 × E4))
    (hcover : coversAtRadius (f '' B) (dyadicRadius n) centers)
    (A : ENNReal) (ζ : ℝ)
    (hcount : ∀ theta : E4,
      ((centers.filter fun y => y.1 ∈ Metric.ball theta (dyadicRadius n)).card : ENNReal) ≤
        A * (dyadicScale n) ^ (-ζ)) :
    ∃ kept : Finset (E4 × E4), kept ⊆ centers ∧
      coversAtRadius (f '' T) (dyadicRadius n) kept ∧
      (∀ y ∈ kept, ∃ a ∈ T, f a ∈ Metric.ball y (dyadicRadius n)) ∧
      ∀ theta : E4,
        ((kept.filter fun y => y.1 ∈ Metric.ball theta (dyadicRadius n)).card : ENNReal) ≤
          A * (dyadicScale n) ^ (-ζ) := by
  obtain ⟨kept, hkept, hcoverKept, hlive, hcountKept⟩ :=
    exists_hereditary_reference_subfamily_with_vertical_count
      (f '' B) (f '' T) (Set.image_mono hTB) (dyadicRadius n) centers hcover
      (Prod.fst : E4 × E4 → E4) A ζ (by simpa only [ofReal_dyadicRadius, ENNReal.rpow_eq_pow] using hcount)
  refine ⟨kept, hkept, hcoverKept, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, ⟨a, ha, rfl⟩, hz⟩ := hlive y hy
    exact ⟨a, ha, hz⟩
  · simpa only [ofReal_dyadicRadius, ENNReal.rpow_eq_pow] using hcountKept

/-- Original-data, no-density-certificate endpoint. A sticky marked datum
produces a fixed positive source and occupied dyadic reference nets whose
vertical direction-ball counts are bounded by `A τ^(-ζ)` uniformly in scale.
The source, original carrier map, and literal common-height front support
are the ones constructed before the later finite graph. -/
theorem sticky_datum_exists_actual_vertical_reference_source
    (ambient : Set MarkedLine) (hsticky : IsStickyDatum ambient)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
      (hvalid : ∀ line ∈ selector, IsValidLine line)
      (hselector : IsDirectionSelector selector), selector ⊆ ambient ∧
      ∃ (k : ℤ) (B : Set E3) (K : Set (E4 × E4)) (c A : ENNReal),
        MeasurableSet B ∧ B ⊆ sourceSet selector hmeas hvalid hselector k ∧
        0 < (volume : Measure E3) B ∧ IsFiniteMeasure ((volume : Measure E3).restrict B) ∧
        K ⊆ lineCarrier ambient ∧ IsCompact K ∧
        B ⊆ (slopeCarrierMap selector hmeas hvalid hselector) ⁻¹' K ∧
        0 < c ∧ c ≤ 1 ∧ A ≠ ⊤ ∧
        (∀ a ∈ B, ‖a‖ ≤ 1) ∧
        (∀ a ∈ B, ∀ s ∈ Icc ((k : ℝ) / 8 - 1 / 8) ((k : ℝ) / 8 + 1 / 4),
          heightPoint (intercept selector hmeas hvalid hselector a + s • a) s ∈
            unitFront ambient) ∧
        ∃ nets : ℕ → Finset (E4 × E4), ∀ n,
          (∀ y ∈ nets n, y ∈ K) ∧
          (∀ y ∈ nets n, ∀ z ∈ nets n, y ≠ z → dyadicRadius n / 2 ≤ dist y z) ∧
          coversAtRadius ((slopeCarrierMap selector hmeas hvalid hselector) '' B)
            (dyadicRadius n) (nets n) ∧
          (∀ y ∈ nets n, c * (dyadicScale n) ^ (3 + ζ) ≤
            (Measure.map (slopeCarrierMap selector hmeas hvalid hselector)
              ((volume : Measure E3).restrict B)) (Metric.ball y (dyadicRadius n))) ∧
          ∀ theta : E4,
            (((nets n).filter fun y => y.1 ∈ Metric.ball theta (dyadicRadius n)).card : ENNReal) ≤
              A * (dyadicScale n) ^ (-ζ) := by
  obtain ⟨selector, hmeas, hvalid, hselector, hsubset, k, B, K, c, D,
      hB, hBsource, hBpos, hfinite, hKsubset, hKcompact, hBsupport, hc, hc1, _hD,
      hunit, hfront, nets, hnets⟩ :=
    sticky_datum_exists_actual_reference_restriction ambient hsticky ζ hζ
  let σ : Measure E3 := (volume : Measure E3).restrict B
  let f := slopeCarrierMap selector hmeas hvalid hselector
  have hσ : σ ≤ volume := Measure.restrict_le_self
  have hunitAE : ∀ᵐ a ∂σ, ‖a‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem hB] with a ha
    exact hunit a ha
  have hf : Measurable f := measurable_slopeCarrierMap selector hmeas hvalid hselector
  have hfst : ∀ a, (f a).1 = (northSlopeDirection a : E4) :=
    direction_slopeLine selector hmeas hvalid hselector
  obtain ⟨A, hA, hcount⟩ := actual_source_dyadic_vertical_count σ hσ hunitAE f hf hfst
    c hc hc1 ζ nets (fun n => (hnets n).2.1) (fun n => (hnets n).2.2.2.2)
  refine ⟨selector, hmeas, hvalid, hselector, hsubset, k, B, K, c, A,
    hB, hBsource, hBpos, hfinite, hKsubset, hKcompact, hBsupport,
    hc, hc1, hA, hunit, hfront, nets, ?_⟩
  intro n
  exact ⟨(hnets n).1, (hnets n).2.1, (hnets n).2.2.1, (hnets n).2.2.2.2, hcount n⟩

end StickyKakeya4.ActualSlopeSource
