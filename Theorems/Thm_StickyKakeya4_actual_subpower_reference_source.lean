import Theorems.Thm_StickyKakeya4_exact_packing_reference_piece
import Theorems.Thm_StickyKakeya4_subpower_reference_nets
import Theorems.Thm_StickyKakeya4_actual_reference_vertical_count

/-!
# One actual reference source for every positive exponent slack

The original compact packing-three datum supplies one positive literal
restriction of slope volume, one compact critical-box-dimension carrier,
and one separated dyadic reference family. Only the finite constants depend
on the requested positive slack. The source and nets do not change with it.

This strengthens the earlier per-slack construction. Lower reference masses
are not asserted for arbitrary later source restrictions. Hereditary upper
support counts are available from the existing live-subfamily theorem.
-/

open Filter MeasureTheory Set
open scoped ENNReal
noncomputable section

namespace StickyKakeya4.ActualSubpowerReferenceSource

open ActualSlopeSource PositiveCellRegularization PackingReferenceSource
attribute [local instance] Classical.propDecidable

/-- The original sticky hypotheses construct a single source and reference
sequence with simultaneous subpower vertical counts. The quantifier over
the exponent is after the source, carrier, and nets have been selected. -/
theorem sticky_datum_exists_actual_subpower_reference_source
    (ambient : Set MarkedLine) (hsticky : IsStickyDatum ambient) :
    ∃ (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
      (hvalid : ∀ line ∈ selector, IsValidLine line)
      (hselector : IsDirectionSelector selector), selector ⊆ ambient ∧
      ∃ (k : ℤ) (B : Set E3) (K : Set (E4 × E4))
        (nets : ℕ → Finset (E4 × E4)),
        MeasurableSet B ∧ B ⊆ sourceSet selector hmeas hvalid hselector k ∧
        0 < (volume : Measure E3) B ∧
        IsFiniteMeasure ((volume : Measure E3).restrict B) ∧
        K ⊆ lineCarrier ambient ∧ IsCompact K ∧ upperMinkowskiDim K ≤ 3 ∧
        B ⊆ (slopeCarrierMap selector hmeas hvalid hselector) ⁻¹' K ∧
        (∀ a ∈ B, ‖a‖ ≤ 1) ∧
        (∀ a ∈ B, ∀ s ∈ Icc ((k : ℝ) / 8 - 1 / 8) ((k : ℝ) / 8 + 1 / 4),
          heightPoint (intercept selector hmeas hvalid hselector a + s • a) s ∈
            unitFront ambient) ∧
        (∀ n,
          (∀ y ∈ nets n, y ∈ K) ∧
          (∀ y ∈ nets n, ∀ z ∈ nets n, y ≠ z →
            dyadicRadius n / 2 ≤ dist y z) ∧
          coversAtRadius ((slopeCarrierMap selector hmeas hvalid hselector) '' B)
            (dyadicRadius n) (nets n)) ∧
        ∀ ζ : ℝ, 0 < ζ → ∃ c D A : ENNReal,
          0 < c ∧ c ≤ 1 ∧ D ≠ ⊤ ∧ A ≠ ⊤ ∧ ∀ n,
            ((nets n).card : ENNReal) ≤ D * (dyadicScale n) ^ (-(3 + ζ)) ∧
            (∀ y ∈ nets n, c * (dyadicScale n) ^ (3 + ζ) ≤
              (Measure.map (slopeCarrierMap selector hmeas hvalid hselector)
                ((volume : Measure E3).restrict B)) (Metric.ball y (dyadicRadius n))) ∧
            ∀ theta : E4,
              (((nets n).filter fun (y : E4 × E4) => y.1 ∈ Metric.ball theta (dyadicRadius n)).card :
                ENNReal) ≤ A * (dyadicScale n) ^ (-ζ) := by
  classical
  obtain ⟨selector, hmeas, hsubset, hselector⟩ :=
    compact_full_direction_borel_selector ambient hsticky.1 hsticky.2.2.1
  have hvalid : ∀ line ∈ selector, IsValidLine line :=
    fun line hline => hsticky.2.1 line (hsubset hline)
  obtain ⟨k, hk⟩ := exists_positive_sourceSet selector hmeas hvalid hselector
  let μ := sourceMeasure selector hmeas hvalid hselector k
  let f := slopeCarrierMap selector hmeas hvalid hselector
  have hf : Measurable f := measurable_slopeCarrierMap selector hmeas hvalid hselector
  have hcarrierCompact : IsCompact (lineCarrier ambient) := by
    exact hsticky.1.image (show Continuous (fun line : MarkedLine =>
      (direction line, offset line)) by unfold direction offset; fun_prop)
  have hmass : 0 < (Measure.map f μ) (lineCarrier ambient) := by
    rw [Measure.map_apply hf hcarrierCompact.isClosed.measurableSet]
    have hpre : f ⁻¹' lineCarrier ambient = Set.univ := by
      apply Set.eq_univ_of_forall
      intro a
      exact slopeCarrierMap_mem_lineCarrier ambient selector hmeas hvalid hselector hsubset a
    rw [hpre]
    exact sourceMeasure_mass_pos selector hmeas hvalid hselector k hk
  obtain ⟨K, hKsubset, hKcompact, hKmass, hKdim⟩ :=
    compact_packingDim_le_three_extract_positive_exact_piece
      (Measure.map f μ) (lineCarrier ambient) hcarrierCompact hmass hsticky.2.2.2
  obtain ⟨B₀, hB₀, hB₀support, hB₀pos, nets, hnets, hpower⟩ :=
    SubpowerReferenceNets.exists_upperMinkowskiDim_le_three_reference_source
      μ f hf K hKcompact hKmass hKdim
  let B := B₀ ∩ sourceSet selector hmeas hvalid hselector k
  have hB : MeasurableSet B :=
    hB₀.inter (measurableSet_sourceSet selector hmeas hvalid hselector k)
  have hBpos : 0 < (volume : Measure E3) B := by
    simpa only [μ, sourceMeasure, Measure.restrict_apply hB₀] using hB₀pos
  have heq : μ.restrict B₀ = (volume : Measure E3).restrict B := by
    exact Measure.restrict_restrict hB₀
  have hfinite : IsFiniteMeasure ((volume : Measure E3).restrict B) := by
    rw [← heq]
    infer_instance
  have hunit : ∀ a ∈ B, ‖a‖ ≤ 1 := by
    intro a ha
    exact (show ‖a‖ < 1 by simpa only [Metric.mem_ball, dist_zero_right] using ha.2.1).le
  refine ⟨selector, hmeas, hvalid, hselector, hsubset, k, B, K, nets,
    hB, Set.inter_subset_right, hBpos, hfinite, hKsubset, hKcompact, hKdim,
    fun a ha => hB₀support ha.1, hunit, ?_, ?_, ?_⟩
  · intro a ha s hs
    rw [graph_eq_wzGraphPoint]
    have hp := wzGraphPoint_mem_unitFront_singleton
      (slopeLine selector hmeas hvalid hselector a) _
      (sourceSet_contains_slab selector hmeas hvalid hselector k ha.2) hs
    obtain ⟨line, hline, t, ht, heqline⟩ := hp
    rw [Set.mem_singleton_iff] at hline
    subst line
    exact ⟨_, hsubset (slopeLine_mem selector hmeas hvalid hselector a), t, ht, heqline⟩
  · intro n
    exact ⟨(hnets n).1, (hnets n).2.1,
      fun y hy => (hnets n).2.2 (Set.image_mono Set.inter_subset_left hy)⟩
  · intro ζ hζ
    obtain ⟨c, D, hc, hc1, hD, hbound⟩ := hpower ζ hζ
    have hlower : ∀ n, ∀ y ∈ nets n, c * (dyadicScale n) ^ (3 + ζ) ≤
        (Measure.map f ((volume : Measure E3).restrict B))
          (Metric.ball y (dyadicRadius n)) := by
      intro n y hy
      rw [← heq]
      exact (hbound n).2 y hy
    have hunitAE : ∀ᵐ a ∂((volume : Measure E3).restrict B), ‖a‖ ≤ 1 := by
      filter_upwards [ae_restrict_mem hB] with a ha
      exact hunit a ha
    have hfst : ∀ a, (f a).1 = (northSlopeDirection a : E4) :=
      direction_slopeLine selector hmeas hvalid hselector
    obtain ⟨A, hA, hcount⟩ := actual_source_dyadic_vertical_count
      ((volume : Measure E3).restrict B) Measure.restrict_le_self hunitAE f hf hfst
      c hc hc1 ζ nets (fun n => (hnets n).2.1) hlower
    exact ⟨c, D, A, hc, hc1, hD, hA, fun n =>
      ⟨(hbound n).1, hlower n, hcount n⟩⟩

end StickyKakeya4.ActualSubpowerReferenceSource
