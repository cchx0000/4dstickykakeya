import Theorems.Thm_StickyKakeya4_packing_reference_source
import Theorems.Thm_StickyKakeya4_actual_slope_source

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.ActualSlopeSource

open PositiveCellRegularization PackingReferenceSource

/-- The actual original direction--offset carrier point of a selected slope. -/
def slopeCarrierMap
    (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) (a : E3) : E4 × E4 :=
  (direction (slopeLine selector hmeas hvalid hselector a),
    offset (slopeLine selector hmeas hvalid hselector a))

theorem measurable_slopeCarrierMap
    (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Measurable (slopeCarrierMap selector hmeas hvalid hselector) := by
  exact (measurable_slopeLine selector hmeas hvalid hselector).fst

/-- This phase parametrization stays in the compact original line carrier,
including at slope parameters outside the final measure's support. -/
theorem slopeCarrierMap_mem_lineCarrier
    (ambient selector : Set MarkedLine) (hmeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) (hsubset : selector ⊆ ambient) (a : E3) :
    slopeCarrierMap selector hmeas hvalid hselector a ∈ lineCarrier ambient :=
  ⟨slopeLine selector hmeas hvalid hselector a,
    hsubset (slopeLine_mem selector hmeas hvalid hselector a), rfl⟩

/-- Direct original-data entrypoint. Construct the bounded-density slope
source, then select and regularize a positive packing piece before any fine
graph is chosen. All front/slab information is inherited by genuine measure
restriction. The actual original direction--offset pushforward has occupied
separated dyadic nets with lower mass `c τ^(3+ζ)`.

This does not assert that lower cell masses survive arbitrary later thinning,
or that the root-fiber paid estimates or a moving-blowup Frostman limit have
been proved. -/
theorem compact_full_direction_actual_reference_source
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (hvalid : ∀ line ∈ ambient, IsValidLine line) (hfull : FullDirection ambient)
    (hpacking : packingDim (lineCarrier ambient) ≤ 3)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (σ : Measure E3) (b : E3 → E3) (f : E3 → E4 × E4)
      (u v : ℝ) (B : Set E3) (K : Set (E4 × E4)),
      IsFiniteMeasure σ ∧ 0 < σ Set.univ ∧ σ ≤ volume ∧
      Measurable b ∧ Measurable f ∧ MeasurableSet B ∧
      B ⊆ f ⁻¹' K ∧ σ Bᶜ = 0 ∧ K ⊆ lineCarrier ambient ∧ IsCompact K ∧
      (∀ a, (f a).1 = (northSlopeDirection a : E4)) ∧ v - u = 3 / 8 ∧
      (∀ᵐ a ∂σ, ‖a‖ ≤ 1) ∧
      (∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
        heightPoint (b a + s • a) s ∈ unitFront ambient) ∧
      ∃ c D : ENNReal, 0 < c ∧ c ≤ 1 ∧ D ≠ ⊤ ∧
        ∃ nets : ℕ → Finset (E4 × E4), ∀ n,
          (∀ y ∈ nets n, y ∈ K) ∧
          (∀ y ∈ nets n, ∀ z ∈ nets n, y ≠ z → dyadicRadius n / 2 ≤ dist y z) ∧
          coversAtRadius (f '' B) (dyadicRadius n) (nets n) ∧
          ((nets n).card : ENNReal) ≤ D * (dyadicScale n) ^ (-(3 + ζ / 2)) ∧
          ∀ y ∈ nets n, c * (dyadicScale n) ^ (3 + ζ) ≤
            (Measure.map f σ) (Metric.ball y (dyadicRadius n)) := by
  obtain ⟨selector, hmeas, hsubset, hselector⟩ :=
    compact_full_direction_borel_selector ambient hcompact hfull
  have hselvalid : ∀ line ∈ selector, IsValidLine line :=
    fun line hline => hvalid line (hsubset hline)
  obtain ⟨k, hk⟩ := exists_positive_sourceSet selector hmeas hselvalid hselector
  let μ := sourceMeasure selector hmeas hselvalid hselector k
  let f := slopeCarrierMap selector hmeas hselvalid hselector
  have hf : Measurable f := measurable_slopeCarrierMap selector hmeas hselvalid hselector
  have hcarrierCompact : IsCompact (lineCarrier ambient) := by
    exact hcompact.image (show Continuous (fun line : MarkedLine =>
      (direction line, offset line)) by unfold direction offset; fun_prop)
  have hmass : 0 < (Measure.map f μ) (lineCarrier ambient) := by
    rw [Measure.map_apply hf hcarrierCompact.isClosed.measurableSet]
    have hpre : f ⁻¹' lineCarrier ambient = Set.univ := by
      apply Set.eq_univ_of_forall
      intro a
      exact slopeCarrierMap_mem_lineCarrier ambient selector hmeas hselvalid hselector hsubset a
    rw [hpre]
    exact sourceMeasure_mass_pos selector hmeas hselvalid hselector k hk
  obtain ⟨K, hKsubset, hKcompact, c, D, hc, hc1, hD, B, hB, hBsupport, hBpos,
      nets, hnets⟩ :=
    exists_packingDim_le_three_reference_source μ f hf (lineCarrier ambient)
      hcarrierCompact hmass hpacking ζ hζ
  let σ := μ.restrict B
  have hσle : σ ≤ μ := Measure.restrict_le_self
  have hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1 :=
    (sourceMeasure_slope_norm_le_one selector hmeas hselvalid hselector k).filter_mono
      (ae_mono hσle)
  have hfront : ∀ᵐ a ∂σ,
      ∀ s ∈ Icc ((k : ℝ) / 8 - 1 / 8) ((k : ℝ) / 8 + 1 / 4),
        heightPoint (intercept selector hmeas hselvalid hselector a + s • a) s ∈
          unitFront ambient := by
    filter_upwards [(source_graph_mem_unitFront selector hmeas hselvalid hselector k).filter_mono
      (ae_mono hσle)] with a ha
    intro s hs
    obtain ⟨line, hline, t, ht, heq⟩ := ha s hs
    exact ⟨line, hsubset hline, t, ht, heq⟩
  refine ⟨σ, intercept selector hmeas hselvalid hselector, f,
    (k : ℝ) / 8 - 1 / 8, (k : ℝ) / 8 + 1 / 4, B, K,
    inferInstance, ?_, hσle.trans (sourceMeasure_le_volume selector hmeas hselvalid hselector k),
    measurable_intercept selector hmeas hselvalid hselector, hf, hB, hBsupport, ?_,
    hKsubset, hKcompact, ?_, by ring, hslopes, hfront,
    c, D, hc, hc1, hD, nets, hnets⟩
  · simpa only [σ, Measure.restrict_apply_univ] using hBpos
  · rw [show σ = μ.restrict B from rfl, Measure.restrict_apply hB.compl]
    simp
  · intro a
    exact direction_slopeLine selector hmeas hselvalid hselector a

/-- Exact-source form for the original sticky datum. The returned source is
literally `volume.restrict B`, with `B` contained in one constructed marked
center bin. Its original slope-selected carrier map remains visible in every
net and pushforward assertion, and the entire common slab lies in the
original front pointwise on `B`. -/
theorem sticky_datum_exists_actual_reference_restriction
    (ambient : Set MarkedLine) (hsticky : IsStickyDatum ambient)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
      (hvalid : ∀ line ∈ selector, IsValidLine line)
      (hselector : IsDirectionSelector selector), selector ⊆ ambient ∧
      ∃ (k : ℤ) (B : Set E3) (K : Set (E4 × E4)) (c D : ENNReal),
        MeasurableSet B ∧ B ⊆ sourceSet selector hmeas hvalid hselector k ∧
        0 < (volume : Measure E3) B ∧ IsFiniteMeasure ((volume : Measure E3).restrict B) ∧
        K ⊆ lineCarrier ambient ∧ IsCompact K ∧
        B ⊆ (slopeCarrierMap selector hmeas hvalid hselector) ⁻¹' K ∧
        0 < c ∧ c ≤ 1 ∧ D ≠ ⊤ ∧
        (∀ a ∈ B, ‖a‖ ≤ 1) ∧
        (∀ a ∈ B, ∀ s ∈ Icc ((k : ℝ) / 8 - 1 / 8) ((k : ℝ) / 8 + 1 / 4),
          heightPoint (intercept selector hmeas hvalid hselector a + s • a) s ∈
            unitFront ambient) ∧
        ∃ nets : ℕ → Finset (E4 × E4), ∀ n,
          (∀ y ∈ nets n, y ∈ K) ∧
          (∀ y ∈ nets n, ∀ z ∈ nets n, y ≠ z → dyadicRadius n / 2 ≤ dist y z) ∧
          coversAtRadius ((slopeCarrierMap selector hmeas hvalid hselector) '' B)
            (dyadicRadius n) (nets n) ∧
          ((nets n).card : ENNReal) ≤ D * (dyadicScale n) ^ (-(3 + ζ / 2)) ∧
          ∀ y ∈ nets n, c * (dyadicScale n) ^ (3 + ζ) ≤
            (Measure.map (slopeCarrierMap selector hmeas hvalid hselector)
              ((volume : Measure E3).restrict B)) (Metric.ball y (dyadicRadius n)) := by
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
  obtain ⟨K, hKsubset, hKcompact, c, D, hc, hc1, hD, B₀, hB₀, hB₀support, hB₀pos,
      nets, hnets⟩ :=
    exists_packingDim_le_three_reference_source μ f hf (lineCarrier ambient)
      hcarrierCompact hmass hsticky.2.2.2 ζ hζ
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
  refine ⟨selector, hmeas, hvalid, hselector, hsubset, k, B, K, c, D,
    hB, Set.inter_subset_right, hBpos, hfinite, hKsubset, hKcompact,
    fun a ha => hB₀support ha.1, hc, hc1, hD, ?_, ?_, nets, ?_⟩
  · intro a ha
    exact (show ‖a‖ < 1 by simpa only [Metric.mem_ball, dist_zero_right] using ha.2.1).le
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
    obtain ⟨hsupported, hsep, hcover, hcard, hlower⟩ := hnets n
    refine ⟨hsupported, hsep, ?_, hcard, ?_⟩
    · exact fun y hy => hcover (Set.image_mono Set.inter_subset_left hy)
    · intro y hy
      rw [← heq]
      exact hlower y hy

end StickyKakeya4.ActualSlopeSource
