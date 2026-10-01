import Definitions.Def_sticky_kakeya4_core
import Theorems.Thm_StickyKakeya4_dimension_witness_extraction
import Theorems.Thm_StickyKakeya4_carrier_piece_probability
import Theorems.Thm_StickyKakeya4_compact_front
import Theorems.Thm_StickyKakeya4_retained_source_readback
import Theorems.Thm_StickyKakeya4_retained_parameter_cell_source
import Theorems.Thm_StickyKakeya4_packing_piece_two_probe_firewall
import Theorems.Thm_StickyKakeya4_wz_common_slab_localization

open MeasureTheory Set

namespace StickyKakeya4

/-- Strengthened coherent-source interface retaining the parameter probability
whose physical pushforward is the source readback measure.  This is the exact
interface needed by the no-Wang--Zakharov concentration boundary, which may
be specialized to any probability law on direction--fibre space. -/
def HasParametrizedCoherentFiniteScaleSources
    (selector ambient : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
    ∃ μ : Measure E4,
      IsProbabilityMeasure μ ∧
      μ (unitFront ambient)ᶜ = 0 ∧
      ∃ ν : Measure
          ({theta : E4 // ‖theta‖ = 1} ×
            Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)),
        IsProbabilityMeasure ν ∧
        Measure.map
            (frontParametrization selector hmeasurable hvalid hselector) ν = μ ∧
        ν contactNorthParameterCapᶜ = 0 ∧
        ∃ Cfront : ENNReal, Cfront ≠ 0 ∧ Cfront ≠ ⊤ ∧
        HasFrontDirectionFibreBound selector hmeasurable hvalid hselector
          ν Cfront ∧
        ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∃ n : ℕ, ∃ D : FiniteScaleSource n,
            D.thickness = δ ∧
            ComesFromSelector D selector ∧
            (∀ i, (1 / 2 : ℝ) ≤ direction (D.line i) (3 : Fin 4)) ∧
            IsAdmissibleStickySource D ε C ∧
            C⁻¹ ≤ sourceMass D ∧ sourceMass D ≤ C ∧
            (∀ x : E4, ∃ R : FiniteScaleSource n,
              IsFractionalSourceRestriction R D ∧
              sourceUnion R ⊆ Metric.closedBall x (2 * δ) ∧
              μ (Metric.ball x δ) ≤ C * sourceMass R) ∧
            ∃ cell : Fin n → Set MarkedLine, ∃ Ccell : ENNReal,
              Ccell ≠ 0 ∧ Ccell ≠ ⊤ ∧
              (∀ i, MeasurableSet (cell i)) ∧
              Pairwise (fun i j ↦ Disjoint (cell i) (cell j)) ∧
              (∀ i, ∀ line ∈ cell i,
                ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
                  dist (rawFrontParam (line, t))
                    (rawFrontParam (D.line i, t)) < δ / 4) ∧
              ∀ source : Set
                  ({theta : E4 // ‖theta‖ = 1} ×
                    Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)),
                MeasurableSet source →
                IsFractionalSourceRestriction
                    (retainedParameterFullTubeSource selector hmeasurable
                      hvalid hselector ν source δ D.line D.line_injective
                        cell Ccell) D ∧
                  (∑ i, retainedParameterCellMass selector hmeasurable hvalid
                      hselector ν source (cell i)) = ν source ∧
                  ∀ i, 0 < retainedParameterCellMass selector hmeasurable
                      hvalid hselector ν source (cell i) →
                    ∃ z, z ∈ source ∧
                      frontParameterSelectedLine selector hmeasurable hvalid
                        hselector z ∈ cell i

/-- Source-hereditary strengthening of the parametrized construction.  The
same root finite source works for every positive measurable retained parameter
source.  Its normalized child law is explicit, and its physical ball mass is
paid by a fractional restriction of the same `D`; the sole normalization cost
is the exact coefficient `ν source` inverse. -/
def HasConditionedParametrizedCoherentFiniteScaleSources
    (selector ambient : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
    ∃ μ : Measure E4,
      IsProbabilityMeasure μ ∧
      μ (unitFront ambient)ᶜ = 0 ∧
      ∃ ν : Measure
          ({theta : E4 // ‖theta‖ = 1} ×
            Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)),
        IsProbabilityMeasure ν ∧
        Measure.map
            (frontParametrization selector hmeasurable hvalid hselector) ν = μ ∧
        ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∃ n : ℕ, ∃ D : FiniteScaleSource n,
            D.thickness = δ ∧
            ComesFromSelector D selector ∧
            (∀ i, (1 / 2 : ℝ) ≤ direction (D.line i) (3 : Fin 4)) ∧
            IsAdmissibleStickySource D ε C ∧
            C⁻¹ ≤ sourceMass D ∧ sourceMass D ≤ C ∧
            ∀ source : Set
                ({theta : E4 // ‖theta‖ = 1} ×
                  Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)),
              MeasurableSet source → 0 < ν source →
              IsProbabilityMeasure (normalizedRestrictionMeasure ν source) ∧
              ∀ x : E4, ∃ R : FiniteScaleSource n,
                IsFractionalSourceRestriction R D ∧
                sourceUnion R ⊆ Metric.closedBall x (2 * δ) ∧
                Measure.map
                    (frontParametrization selector hmeasurable hvalid hselector)
                    (ν.restrict source) (Metric.ball x δ) ≤
                  C * sourceMass R ∧
                Measure.map
                    (frontParametrization selector hmeasurable hvalid hselector)
                    (normalizedRestrictionMeasure ν source)
                    (Metric.ball x δ) ≤
                  (ν source)⁻¹ * C * sourceMass R

/-- Forgetting the parameter law recovers the original coherent finite-scale
source interface without weakening any source estimate. -/
theorem HasParametrizedCoherentFiniteScaleSources.toCoherent
    {selector ambient : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (hsources : HasParametrizedCoherentFiniteScaleSources selector ambient
      hmeasurable hvalid hselector) :
    HasCoherentFiniteScaleSources selector ambient := by
  intro ε hε
  obtain ⟨C, hC0, hCTop, μ, hμprob, hμsupport,
      ν, hνprob, hmap, _hnorthSupport,
      _Cfront, _hCfront0, _hCfrontTop, _hfront,
      δ₀, hδ₀, hsourcesδ⟩ := hsources ε hε
  refine ⟨C, hC0, hCTop, μ, hμprob, hμsupport, δ₀, hδ₀, ?_⟩
  intro δ hδ hδ₀
  obtain ⟨n, D, hDδ, hDselector, _hDnorth, hDadmissible,
      hDmassLower, hDmassUpper, hlocal, _haligned⟩ := hsourcesδ δ hδ hδ₀
  exact ⟨n, D, hDδ, hDselector, hDadmissible,
    hDmassLower, hDmassUpper, hlocal⟩

/-- The original parametrized construction already contains the full
conditioned descendant interface once normalized-restriction domination is
read explicitly.  No new measure or scale-wise source is selected here. -/
theorem HasParametrizedCoherentFiniteScaleSources.toConditioned
    {selector ambient : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (hsources : HasParametrizedCoherentFiniteScaleSources selector ambient
      hmeasurable hvalid hselector) :
    HasConditionedParametrizedCoherentFiniteScaleSources selector ambient
      hmeasurable hvalid hselector := by
  intro ε hε
  obtain ⟨C, hC0, hCTop, μ, hμprob, hμsupport,
      ν, hνprob, hmap, _hnorthSupport,
      _Cfront, _hCfront0, _hCfrontTop, _hfront,
      δ₀, hδ₀, hsourcesδ⟩ := hsources ε hε
  refine ⟨C, hC0, hCTop, μ, hμprob, hμsupport,
    ν, hνprob, hmap, δ₀, hδ₀, ?_⟩
  intro δ hδ hδ₀
  obtain ⟨n, D, hDδ, hDselector, hDnorth, hDadmissible,
      hDmassLower, hDmassUpper, hlocal, _haligned⟩ := hsourcesδ δ hδ hδ₀
  refine ⟨n, D, hDδ, hDselector, hDnorth, hDadmissible,
    hDmassLower, hDmassUpper, ?_⟩
  intro source hsource hsourcePos
  have hsourceZero : ν source ≠ 0 := ne_of_gt hsourcePos
  have hsourceTop : ν source ≠ ⊤ := by
    letI : IsProbabilityMeasure ν := hνprob
    exact measure_ne_top ν source
  refine ⟨normalizedRestrictionMeasure_isProbabilityMeasure ν hsource
    hsourceZero hsourceTop, ?_⟩
  intro x
  obtain ⟨R, hR, hRunion, hread⟩ := hlocal x
  have hrootReadback :
      Measure.map
          (frontParametrization selector hmeasurable hvalid hselector) ν
          (Metric.ball x δ) ≤ C * sourceMass R := by
    rw [hmap]
    exact hread
  refine ⟨R, hR, hRunion, ?_, ?_⟩
  · exact map_restrict_apply_le_sourceMass ν source
      (frontParametrization selector hmeasurable hvalid hselector)
      (measurable_frontParametrization selector hmeasurable hvalid hselector)
      Metric.isOpen_ball.measurableSet R C hrootReadback
  · exact map_normalizedRestrictionMeasure_apply_le_scaled_sourceMass
      ν hsource
      (frontParametrization selector hmeasurable hvalid hselector)
      (measurable_frontParametrization selector hmeasurable hvalid hselector)
      Metric.isOpen_ball.measurableSet R C hrootReadback

theorem packing_selector_to_parametrized_finite_scale_sources
    (selector : Set MarkedLine)
    (ambient : Set MarkedLine)
    (hambientCompact : IsCompact ambient)
    (hselectorAmbient : selector ⊆ ambient)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3) :
    HasParametrizedCoherentFiniteScaleSources selector ambient
      hmeasurable hvalid hselector := by
  intro ε hε
  have hslack : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  obtain ⟨δTube, hδTube, hTubeAdmissible⟩ :=
    exists_markedUnitTube_admissible_scale hε
  obtain ⟨centerBin, piece, hpieceMeasurable, hpieceCarrier,
      hpieceLocalized, hpieceMass,
      d, hd, hdtop, Ccover, hCcoverTop, hcover⟩ :=
    packing_selector_extract_positive_measurable_north_center_piece
      selector hmeasurable hvalid hselector hpacking hslack
  let μ : Measure E4 :=
    markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece
  have hμprob : IsProbabilityMeasure μ := by infer_instance
  have hμsupport : μ (unitFront ambient)ᶜ = 0 :=
    markedCarrierPieceFrontProbability_compl_unitFront_eq_zero
      selector ambient hmeasurable hvalid hselector piece hselectorAmbient
      (StickyKakeya4.IsCompact.unitFront hambientCompact).measurableSet
  let νparam : Measure
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    markedCarrierPieceFrontParameterProbability selector hmeasurable
      hvalid hselector piece
  have hνparamProb : IsProbabilityMeasure νparam := by infer_instance
  have hνparamMap :
      Measure.map
          (frontParametrization selector hmeasurable hvalid hselector) νparam = μ := by
    exact map_frontParametrization_markedCarrierPieceFrontParameterProbability
      selector hmeasurable hvalid hselector piece
  have hcarrierSupport :
      (normalizedCarrierPieceProbability selector hmeasurable hvalid hselector piece :
        Measure (E4 × E4)) pieceᶜ = 0 :=
    normalizedCarrierPieceProbability_apply_compl_eq_zero selector hmeasurable
      hvalid hselector piece hpieceMeasurable hpieceMass
  have hparameterSupport :
      (markedCarrierPieceParameterProbability selector hmeasurable hvalid hselector piece :
        Measure ((E4 × E4) × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
          (Prod.fst ⁻¹' pieceᶜ) = 0 :=
    markedCarrierPieceParameterProbability_apply_fst_preimage_compl_eq_zero
      selector hmeasurable hvalid hselector piece hpieceMeasurable hpieceMass
  let ν : Measure MarkedLine :=
    markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece
  have hνprob : IsProbabilityMeasure ν := by infer_instance
  have hlineSupport :
      ν (selectorLinesOverCarrierPiece selector piece)ᶜ = 0 :=
    markedCarrierPieceLineProbability_apply_compl_eq_zero selector hmeasurable
      hvalid hselector piece hpieceMeasurable hpieceCarrier hpieceMass
  let Cdir : ENNReal :=
    carrierPieceDirectionCapConstant selector hmeasurable hvalid
      hselector piece
  have hCdirNe : Cdir ≠ 0 := by
    exact carrierPieceDirectionCapConstant_ne_zero selector hmeasurable hvalid
      hselector piece hpieceMass
  have hCdirTop : Cdir ≠ ⊤ := by
    exact carrierPieceDirectionCapConstant_ne_top selector hmeasurable hvalid
      hselector piece
  have hretainedDirectionCap :
      ∀ (theta : {theta : E4 // ‖theta‖ = 1}), ∀ r : ℝ,
        0 < r → r ≤ 1 →
        ν (lineDirectionBall (theta : E4) r) ≤
          Cdir * (ENNReal.ofReal r) ^ 3 := by
    intro theta r hr hrone
    exact markedCarrierPieceLineProbability_lineDirectionBall_upper_bound
      selector hmeasurable hvalid hselector piece hpieceMeasurable
      hpieceCarrier hpieceMass theta hr hrone
  obtain ⟨δcover, hδcover, hcoverSmall⟩ :=
    eventually_nhdsGT_extract_cutoff hcover
  let pieceLines : Set MarkedLine := selectorLinesOverCarrierPiece selector piece
  have hpieceLinesMeasurable : MeasurableSet pieceLines := by
    exact measurable_selectorLinesOverCarrierPiece selector piece
      hmeasurable hpieceMeasurable
  have hpieceLinesAmbient : pieceLines ⊆ ambient := by
    intro line hline
    exact hselectorAmbient hline.1
  have hfiniteMarkedNet :
      ∀ δ : ℝ, 0 < δ →
        ∃ centers : Set MarkedLine,
          centers ⊆ pieceLines ∧ centers.Finite ∧
            pieceLines ⊆ ⋃ line ∈ centers, Metric.ball line δ := by
    intro δ hδ
    exact StickyKakeya4.IsCompact.exists_finite_marked_net
      hambientCompact hpieceLinesAmbient hδ
  have hfiniteMarkedFrontApproximation :
      ∀ δ : ℝ, 0 < δ →
        ∃ ρ : ℝ, 0 < ρ ∧
          ∃ centers : Set MarkedLine,
            centers ⊆ pieceLines ∧ centers.Finite ∧
              ∀ line ∈ pieceLines,
                ∃ center ∈ centers,
                  dist line center < ρ ∧
                    ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
                      dist (rawFrontParam (line, t))
                        (rawFrontParam (center, t)) < δ := by
    intro δ hδ
    obtain ⟨ρ, hρ, hfront⟩ :=
      StickyKakeya4.IsCompact.exists_marked_radius_for_front
        hambientCompact hδ
    obtain ⟨centers, hcentersPiece, hcentersFinite, hnet⟩ :=
      hfiniteMarkedNet ρ hρ
    refine ⟨ρ, hρ, centers, hcentersPiece, hcentersFinite, ?_⟩
    intro line hline
    have hcovered := hnet hline
    simp only [Set.mem_iUnion, Metric.mem_ball] at hcovered
    obtain ⟨center, hcenter, hdist⟩ := hcovered
    refine ⟨center, hcenter, hdist, ?_⟩
    exact hfront line (hpieceLinesAmbient hline) center
      (hpieceLinesAmbient (hcentersPiece hcenter)) hdist
  have hfiniteWeightedMarkedPartition :
      ∀ eta delta : ℝ, 0 < eta → 0 < delta → delta ≤ 1 →
        ∃ ρ : ℝ, 0 < ρ ∧
          ∃ n : ℕ, ∃ center : Fin n → MarkedLine,
            ∃ cell : Fin n → Set MarkedLine,
              (∀ i, center i ∈ pieceLines) ∧
              Function.Injective center ∧
              (∀ i, MeasurableSet (cell i)) ∧
              Pairwise (fun i j => Disjoint (cell i) (cell j)) ∧
              (∀ i, cell i ⊆ pieceLines ∩ Metric.ball (center i) ρ) ∧
              pieceLines ⊆ ⋃ i, cell i ∧
              (∑' i, ν (cell i)) = 1 ∧
              (∀ i, ∀ line ∈ cell i,
                ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
                  dist (rawFrontParam (line, t))
                    (rawFrontParam (center i, t)) < eta) ∧
              (∀ i, ∀ line ∈ cell i,
                dist (direction line) (direction (center i)) < delta) ∧
              (∀ i, ν (cell i) ≤
                Cdir * (ENNReal.ofReal delta) ^ 3) := by
    intro eta delta heta hdelta hdelta1
    obtain ⟨ρ, hρ, hfront⟩ :=
      StickyKakeya4.IsCompact.exists_marked_radius_for_front
        hambientCompact heta
    let ρsmall : ℝ := min ρ delta
    have hρsmall : 0 < ρsmall := lt_min hρ hdelta
    obtain ⟨centers, hcentersPiece, hcentersFinite, hnet⟩ :=
      hfiniteMarkedNet ρsmall hρsmall
    letI : Fintype centers := hcentersFinite.fintype
    let e : Fin (Fintype.card centers) ≃ centers :=
      (Fintype.equivFin centers).symm
    let center : Fin (Fintype.card centers) → MarkedLine :=
      fun i => (e i).1
    let ballPiece : Fin (Fintype.card centers) → Set MarkedLine :=
      fun i => pieceLines ∩ Metric.ball (center i) ρsmall
    let cell : Fin (Fintype.card centers) → Set MarkedLine :=
      fun i => orderedMeasurableCell ballPiece i
    have hballMeasurable : ∀ i, MeasurableSet (ballPiece i) := by
      intro i
      exact hpieceLinesMeasurable.inter Metric.isOpen_ball.measurableSet
    have hballsCover : pieceLines ⊆ ⋃ i, ballPiece i := by
      intro line hline
      have hcovered := hnet hline
      simp only [Set.mem_iUnion, Metric.mem_ball] at hcovered
      obtain ⟨c, hc, hdist⟩ := hcovered
      let sc : centers := ⟨c, hc⟩
      obtain ⟨i, hi⟩ := e.surjective sc
      refine Set.mem_iUnion.2 ⟨i, hline, ?_⟩
      have hcenter : center i = c := congrArg Subtype.val hi
      simpa [hcenter] using hdist
    have hcellsCover : pieceLines ⊆ ⋃ i, cell i := by
      rw [show (⋃ i, cell i) = ⋃ i, ballPiece i by
        simpa [cell] using iUnion_orderedMeasurableCell ballPiece]
      exact hballsCover
    have hνballs : ν ((⋃ i, ballPiece i)ᶜ) = 0 := by
      apply measure_mono_null (Set.compl_subset_compl.mpr hballsCover)
      exact hlineSupport
    refine ⟨ρsmall, hρsmall, Fintype.card centers, center, cell, ?_, ?_, ?_, ?_, ?_,
      hcellsCover, ?_, ?_, ?_, ?_⟩
    · intro i
      exact hcentersPiece (e i).property
    · intro i j hij
      apply e.injective
      apply Subtype.ext
      exact hij
    · intro i
      exact measurableSet_orderedMeasurableCell ballPiece hballMeasurable i
    · exact orderedMeasurableCell_pairwise_disjoint ballPiece
    · intro i
      exact orderedMeasurableCell_subset ballPiece i
    · simpa [cell] using
        (tsum_measure_orderedMeasurableCell_eq_one ν ballPiece
          hballMeasurable hνballs)
    · intro i line hline t ht
      have hlinePiece : line ∈ pieceLines :=
        (orderedMeasurableCell_subset ballPiece i hline).1
      have hdistSmall : dist line (center i) < ρsmall :=
        (orderedMeasurableCell_subset ballPiece i hline).2
      have hdist : dist line (center i) < ρ :=
        hdistSmall.trans_le (min_le_left _ _)
      exact hfront line (hpieceLinesAmbient hlinePiece) (center i)
        (hpieceLinesAmbient (hcentersPiece (e i).property)) hdist t ht
    · intro i line hline
      have hdistSmall : dist line (center i) < ρsmall :=
        (orderedMeasurableCell_subset ballPiece i hline).2
      have hdir : dist (direction line) (direction (center i)) ≤
          dist line (center i) := by
        simp only [direction, Prod.dist_eq]
        exact le_max_of_le_left (le_max_left _ _)
      exact (hdir.trans_lt hdistSmall).trans_le (min_le_right _ _)
    · intro i
      let theta : {theta : E4 // ‖theta‖ = 1} :=
        ⟨direction (center i), (hvalid (center i) (hcentersPiece (e i).property).1).1⟩
      have hcellSubset : cell i ⊆
          lineDirectionBall (theta : E4) delta := by
        intro line hline
        exact (by
          change dist (direction line) (direction (center i)) < delta
          have hdistSmall : dist line (center i) < ρsmall :=
            (orderedMeasurableCell_subset ballPiece i hline).2
          have hdir : dist (direction line) (direction (center i)) ≤
              dist line (center i) := by
            simp only [direction, Prod.dist_eq]
            exact le_max_of_le_left (le_max_left _ _)
          exact (hdir.trans_lt hdistSmall).trans_le (min_le_right _ _))
      calc
        ν (cell i) ≤ ν (lineDirectionBall (theta : E4) delta) :=
          measure_mono hcellSubset
        _ ≤ Cdir * (ENNReal.ofReal delta) ^ 3 :=
          hretainedDirectionCap theta delta hdelta hdelta1
  have hmarkedTubeAdmissibleCore :
      ∀ line ∈ pieceLines, ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 8 →
        MeasurableSet (markedUnitTube line delta) ∧
        (∀ x ∈ markedUnitTube line delta,
          Metric.infDist x (unitFront {line}) ≤ delta) ∧
        ENNReal.ofReal (1 / 8 : ℝ) * (ENNReal.ofReal delta) ^ 3 *
            ENNReal.ofReal (Real.pi ^ 2 / 2) ≤
          volume (markedUnitTube line delta) := by
    intro line hline delta hdelta hsmall
    refine ⟨measurableSet_markedUnitTube line delta, ?_, ?_⟩
    · intro x hx
      exact hx
    · exact volume_markedUnitTube_lower_bound
        (hvalid line hline.1) hdelta hsmall
  have hmarkedTubeAdmissibleAtEpsilon :
      ∀ line ∈ pieceLines, ∀ delta : ℝ,
        0 < delta → delta ≤ δTube →
          (ENNReal.ofReal delta).rpow (3 + ε) ≤
            volume (markedUnitTube line delta) := by
    intro line hline delta hdelta hsmall
    exact hTubeAdmissible line (hvalid line hline.1) delta hdelta hsmall
  have hfiniteSourceCore :
      ∀ delta : ℝ, 0 < delta → delta ≤ min δTube (1 / 8 : ℝ) →
        ∃ n : ℕ, ∃ D : FiniteScaleSource n,
          D.thickness = delta ∧
          ComesFromSelector D selector ∧
          (∀ i, D.weight i ≤ 1) ∧
          (∀ i, D.fibreMark i = mark (D.line i)) ∧
          (∀ i, IsValidLine (D.line i)) ∧
          (∀ i, MeasurableSet (D.shading i)) ∧
          (∀ i, 0 < D.weight i →
            (ENNReal.ofReal D.thickness).rpow (3 + ε) ≤
              volume (D.shading i)) ∧
          (∀ i x, x ∈ D.shading i →
            Metric.infDist x (unitFront {D.line i}) ≤ D.thickness) := by
    intro delta hdelta hsmall
    have hdeltaEight : delta ≤ (1 / 8 : ℝ) := hsmall.trans (min_le_right _ _)
    have hdeltaOne : delta ≤ 1 := by linarith
    have heta : 0 < delta / 4 := by linarith
    obtain ⟨rho, hrho, n, center, cell, hcenterPiece, hcenterInjective,
        hcellMeasurable, hcellDisjoint, hcellSubordinate, hcellsCover,
        hcellMass, hfrontCell, hdirectionCell, hcellCap⟩ :=
      hfiniteWeightedMarkedPartition (delta / 4) delta heta hdelta hdeltaOne
    let q : Fin n → ENNReal := fun i => ν (cell i)
    let D : FiniteScaleSource n :=
      fullMarkedTubeSource delta center hcenterInjective q Cdir
    have hdenZero : Cdir * (ENNReal.ofReal delta) ^ 3 ≠ 0 := by
      apply mul_ne_zero hCdirNe
      exact pow_ne_zero 3 (ENNReal.ofReal_ne_zero_iff.mpr hdelta)
    have hdenTop : Cdir * (ENNReal.ofReal delta) ^ 3 ≠ ⊤ := by
      exact ENNReal.mul_ne_top hCdirTop
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    refine ⟨n, D, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (hcenterPiece i).1
    · intro i
      exact normalizedPartitionWeight_le_one hdenZero hdenTop (hcellCap i)
    · intro i
      rfl
    · intro i
      exact hvalid (center i) (hcenterPiece i).1
    · intro i
      exact measurableSet_markedUnitTube (center i) delta
    · intro i hi
      exact hmarkedTubeAdmissibleAtEpsilon (center i) (hcenterPiece i)
        delta hdelta (hsmall.trans (min_le_left _ _))
    · intro i x hx
      exact (hmarkedTubeAdmissibleCore (center i) (hcenterPiece i)
        delta hdelta hdeltaEight).2.1 x hx
  have hfiniteSourceMassBounds :
      ∀ delta : ℝ, 0 < delta → delta ≤ (1 / 8 : ℝ) →
        ∃ n : ℕ, ∃ D : FiniteScaleSource n,
          D.thickness = delta ∧ ComesFromSelector D selector ∧
          Cdir⁻¹ *
              (ENNReal.ofReal (1 / 8 : ℝ) *
                ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤ sourceMass D ∧
          sourceMass D ≤ Cdir⁻¹ *
              (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)) := by
    intro delta hdelta hdeltaEight
    have hdeltaOne : delta ≤ 1 := by linarith
    have heta : 0 < delta / 4 := by linarith
    obtain ⟨rho, hrho, n, center, cell, hcenterPiece, hcenterInjective,
        hcellMeasurable, hcellDisjoint, hcellSubordinate, hcellsCover,
        hcellMass, hfrontCell, hdirectionCell, hcellCap⟩ :=
      hfiniteWeightedMarkedPartition (delta / 4) delta heta hdelta hdeltaOne
    let q : Fin n → ENNReal := fun i => ν (cell i)
    let D : FiniteScaleSource n :=
      fullMarkedTubeSource delta center hcenterInjective q Cdir
    have hq : ∑ i, q i = 1 := by
      simpa only [q, tsum_fintype] using hcellMass
    have hlower : ∀ i,
        (ENNReal.ofReal (1 / 8 : ℝ) *
            ENNReal.ofReal (Real.pi ^ 2 / 2)) *
            (ENNReal.ofReal delta) ^ 3 ≤
          volume (markedUnitTube (center i) delta) := by
      intro i
      calc
        (ENNReal.ofReal (1 / 8 : ℝ) *
            ENNReal.ofReal (Real.pi ^ 2 / 2)) *
            (ENNReal.ofReal delta) ^ 3 =
          ENNReal.ofReal (1 / 8 : ℝ) *
            (ENNReal.ofReal delta) ^ 3 *
              ENNReal.ofReal (Real.pi ^ 2 / 2) := by ac_rfl
        _ ≤ volume (markedUnitTube (center i) delta) :=
          (hmarkedTubeAdmissibleCore (center i) (hcenterPiece i)
            delta hdelta hdeltaEight).2.2
    have hupper : ∀ i,
        volume (markedUnitTube (center i) delta) ≤
          (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)) *
            (ENNReal.ofReal delta) ^ 3 := by
      intro i
      calc
        volume (markedUnitTube (center i) delta) ≤
            32 * (ENNReal.ofReal delta) ^ 3 *
              ENNReal.ofReal (Real.pi ^ 2 / 2) :=
          volume_markedUnitTube_upper_bound
            (hvalid (center i) (hcenterPiece i).1) hdelta hdeltaOne
        _ = (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)) *
            (ENNReal.ofReal delta) ^ 3 := by ac_rfl
    have hmassBounds := sourceMass_fullMarkedTubeSource_normalized_bounds
      delta center hcenterInjective q Cdir
      (ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal (Real.pi ^ 2 / 2))
      (32 * ENNReal.ofReal (Real.pi ^ 2 / 2))
      hCdirNe hCdirTop hdelta hq hlower hupper
    exact ⟨n, D, rfl, fun i => (hcenterPiece i).1,
      hmassBounds.1, hmassBounds.2⟩
  have hsmallRadiusDirectionCarlesonData :
      ∀ {n : ℕ} (delta : ℝ) (center : Fin n → MarkedLine)
        (hcenterInjective : Function.Injective center)
        (cell : Fin n → Set MarkedLine),
        0 < delta →
        (∀ i, MeasurableSet (cell i)) →
        Pairwise (fun i j => Disjoint (cell i) (cell j)) →
        (∀ i, ∀ line ∈ cell i,
          dist (direction line) (direction (center i)) < delta) →
        ∀ theta : E4, ∀ r : ℝ, delta ≤ r → r ≤ 1 / 4 →
          directionWeightInBall
              (fullMarkedTubeSource delta center hcenterInjective
                (fun i => ν (cell i)) Cdir) theta r ≤
            (ENNReal.ofReal (2 * (r + delta))) ^ 3 /
              (ENNReal.ofReal delta) ^ 3 := by
    intro n delta center hcenterInjective cell hdelta hcellMeasurable
      hcellDisjoint hdirectionCell theta r hdeltar hrquarter
    let J : Finset (Fin n) :=
      Finset.univ.filter fun i => dist (direction (center i)) theta < r
    let U : Set MarkedLine := ⋃ i ∈ J, cell i
    have hJdisjoint : PairwiseDisjoint (↑J) cell := by
      intro i hi j hj hij
      exact hcellDisjoint hij
    have hmeasureU : ν U = ∑ i ∈ J, ν (cell i) := by
      exact measure_biUnion_finset hJdisjoint
        (fun i hi => hcellMeasurable i)
    have hUsubset : U ⊆ lineDirectionBall theta (r + delta) := by
      intro line hline
      simp only [U, Set.mem_iUnion] at hline
      obtain ⟨i, hiJ, hlineCell⟩ := hline
      have hcenterTheta : dist (direction (center i)) theta < r := by
        simpa [J] using hiJ
      change dist (direction line) theta < r + delta
      calc
        dist (direction line) theta ≤
            dist (direction line) (direction (center i)) +
              dist (direction (center i)) theta := dist_triangle _ _ _
        _ < delta + r := add_lt_add (hdirectionCell i line hlineCell) hcenterTheta
        _ = r + delta := by ring
    have hradiusPos : 0 < r + delta := by linarith
    have hradiusHalf : r + delta ≤ 1 / 2 := by linarith
    have hcellMassBound :
        ∑ i ∈ J, ν (cell i) ≤
          Cdir * (ENNReal.ofReal (2 * (r + delta))) ^ 3 := by
      rw [← hmeasureU]
      exact (measure_mono hUsubset).trans
        (markedCarrierPieceLineProbability_arbitrary_directionBall_upper_bound
          selector hmeasurable hvalid hselector piece hpieceMeasurable
          hpieceCarrier hpieceMass theta hradiusPos hradiusHalf)
    have hratio := sum_normalizedPartitionWeight_le_ratio
      Cdir delta (fun i => ν (cell i)) J
      ((ENNReal.ofReal (2 * (r + delta))) ^ 3)
      hCdirNe hCdirTop hdelta hcellMassBound
    change (∑ i, if dist (direction (center i)) theta < r then
        normalizedPartitionWeight Cdir delta (ν (cell i)) else 0) ≤ _
    rw [← Finset.sum_filter]
    simpa [J] using hratio
  have hdirectionRatioNumeric :
      ∀ delta r : ℝ, 0 < delta → delta ≤ r →
        (ENNReal.ofReal (2 * (r + delta))) ^ 3 /
            (ENNReal.ofReal delta) ^ 3 ≤
          64 * (ENNReal.ofReal (r / delta)) ^ 3 := by
    intro delta r hdelta hdeltar
    have hnum : ENNReal.ofReal (2 * (r + delta)) ≤
        ENNReal.ofReal (4 * r) := by
      exact ENNReal.ofReal_le_ofReal (by linarith)
    calc
      (ENNReal.ofReal (2 * (r + delta))) ^ 3 /
          (ENNReal.ofReal delta) ^ 3 ≤
        (ENNReal.ofReal (4 * r)) ^ 3 /
          (ENNReal.ofReal delta) ^ 3 := by
        apply ENNReal.div_le_div_right
        exact pow_le_pow_left' hnum 3
      _ = (ENNReal.ofReal ((4 * r) / delta)) ^ 3 := by
        rw [ENNReal.ofReal_div_of_pos hdelta]
        simp only [div_eq_mul_inv, mul_pow]
        rw [ENNReal.inv_pow]
      _ = (4 * ENNReal.ofReal (r / delta)) ^ 3 := by
        congr 1
        rw [show (4 * r) / delta = 4 * (r / delta) by ring]
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ = 64 * (ENNReal.ofReal (r / delta)) ^ 3 := by ring
  have hinvScaleDirectionRatio :
      ∀ delta r : ℝ, 0 < delta → 1 / 4 ≤ r →
        ((ENNReal.ofReal delta) ^ 3)⁻¹ ≤
          64 * (ENNReal.ofReal (r / delta)) ^ 3 := by
    intro delta r hdelta hrquarter
    have hreal : 1 / delta ≤ 4 * (r / delta) := by
      rw [show 4 * (r / delta) = (4 * r) / delta by ring]
      exact (div_le_div_iff_of_pos_right hdelta).2 (by linarith)
    have hbase : ENNReal.ofReal (1 / delta) ≤
        ENNReal.ofReal (4 * (r / delta)) :=
      ENNReal.ofReal_le_ofReal hreal
    calc
      ((ENNReal.ofReal delta) ^ 3)⁻¹ =
          (ENNReal.ofReal delta)⁻¹ ^ 3 :=
        ENNReal.inv_pow
      _ = (ENNReal.ofReal (1 / delta)) ^ 3 := by
        rw [show 1 / delta = delta⁻¹ by ring,
          ENNReal.ofReal_inv_of_pos hdelta]
      _ ≤ (ENNReal.ofReal (4 * (r / delta))) ^ 3 :=
        pow_le_pow_left' hbase 3
      _ = (4 * ENNReal.ofReal (r / delta)) ^ 3 := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ = 64 * (ENNReal.ofReal (r / delta)) ^ 3 := by ring
  have hlargeRadiusDirectionCarlesonData :
      ∀ {n : ℕ} (delta : ℝ) (center : Fin n → MarkedLine)
        (hcenterInjective : Function.Injective center)
        (cell : Fin n → Set MarkedLine),
        0 < delta →
        (∑' i, ν (cell i)) = 1 →
        ∀ theta : E4, ∀ r : ℝ, 1 / 4 ≤ r →
          directionWeightInBall
              (fullMarkedTubeSource delta center hcenterInjective
                (fun i => ν (cell i)) Cdir) theta r ≤
            (64 * Cdir⁻¹) * (ENNReal.ofReal (r / delta)) ^ 3 := by
    intro n delta center hcenterInjective cell hdelta hcellMass
      theta r hrquarter
    have hq : ∑ i, ν (cell i) = 1 := by
      simpa only [tsum_fintype] using hcellMass
    have htotal := sum_normalizedPartitionWeight
      Cdir delta (fun i => ν (cell i)) hq
    calc
      directionWeightInBall
          (fullMarkedTubeSource delta center hcenterInjective
            (fun i => ν (cell i)) Cdir) theta r ≤
        ∑ i, normalizedPartitionWeight Cdir delta (ν (cell i)) := by
          unfold directionWeightInBall
          apply Finset.sum_le_sum
          intro i hi
          split <;> simp
      _ = (Cdir * (ENNReal.ofReal delta) ^ 3)⁻¹ := htotal
      _ = Cdir⁻¹ * ((ENNReal.ofReal delta) ^ 3)⁻¹ := by
        rw [ENNReal.mul_inv (Or.inl hCdirNe) (Or.inl hCdirTop)]
      _ ≤ Cdir⁻¹ *
          (64 * (ENNReal.ofReal (r / delta)) ^ 3) :=
        mul_le_mul_right (hinvScaleDirectionRatio delta r hdelta hrquarter) Cdir⁻¹
      _ = (64 * Cdir⁻¹) * (ENNReal.ofReal (r / delta)) ^ 3 := by ac_rfl
  have hdirectionPowerUpgrade :
      ∀ delta r : ℝ, 0 < delta → delta ≤ r →
        (ENNReal.ofReal (r / delta)) ^ 3 ≤
          (ENNReal.ofReal (r / delta)).rpow (3 + ε) := by
    intro delta r hdelta hdeltar
    have hreal : 1 ≤ r / delta :=
      (le_div_iff₀ hdelta).2 (by simpa using hdeltar)
    have hbase : (1 : ENNReal) ≤ ENNReal.ofReal (r / delta) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hreal
    have hexponent : (3 : ℝ) ≤ 3 + ε := by linarith
    simpa using ENNReal.rpow_le_rpow_of_exponent_le hbase hexponent
  have hdirectionCarlesonData :
      ∀ {n : ℕ} (delta : ℝ) (center : Fin n → MarkedLine)
        (hcenterInjective : Function.Injective center)
        (cell : Fin n → Set MarkedLine),
        0 < delta →
        (∀ i, MeasurableSet (cell i)) →
        Pairwise (fun i j => Disjoint (cell i) (cell j)) →
        (∀ i, ∀ line ∈ cell i,
          dist (direction line) (direction (center i)) < delta) →
        (∑' i, ν (cell i)) = 1 →
        ∀ theta : E4, ∀ r : ℝ, delta ≤ r → r ≤ 1 →
          directionWeightInBall
              (fullMarkedTubeSource delta center hcenterInjective
                (fun i => ν (cell i)) Cdir) theta r ≤
            (64 + 64 * Cdir⁻¹) *
              (ENNReal.ofReal (r / delta)).rpow (3 + ε) := by
    intro n delta center hcenterInjective cell hdelta hcellMeasurable
      hcellDisjoint hdirectionCell hcellMass theta r hdeltar hrone
    rcases le_total r (1 / 4 : ℝ) with hrquarter | hquarterr
    · calc
        directionWeightInBall
            (fullMarkedTubeSource delta center hcenterInjective
              (fun i => ν (cell i)) Cdir) theta r ≤
          (ENNReal.ofReal (2 * (r + delta))) ^ 3 /
            (ENNReal.ofReal delta) ^ 3 :=
              hsmallRadiusDirectionCarlesonData delta center hcenterInjective
                cell hdelta hcellMeasurable hcellDisjoint hdirectionCell
                theta r hdeltar hrquarter
        _ ≤ 64 * (ENNReal.ofReal (r / delta)) ^ 3 :=
          hdirectionRatioNumeric delta r hdelta hdeltar
        _ ≤ 64 * (ENNReal.ofReal (r / delta)).rpow (3 + ε) :=
          mul_le_mul_right (hdirectionPowerUpgrade delta r hdelta hdeltar) 64
        _ ≤ (64 + 64 * Cdir⁻¹) *
            (ENNReal.ofReal (r / delta)).rpow (3 + ε) :=
          by
            gcongr
            exact le_add_right le_rfl
    · calc
        directionWeightInBall
            (fullMarkedTubeSource delta center hcenterInjective
              (fun i => ν (cell i)) Cdir) theta r ≤
          (64 * Cdir⁻¹) * (ENNReal.ofReal (r / delta)) ^ 3 :=
            hlargeRadiusDirectionCarlesonData delta center hcenterInjective
              cell hdelta hcellMass theta r hquarterr
        _ ≤ (64 * Cdir⁻¹) *
            (ENNReal.ofReal (r / delta)).rpow (3 + ε) :=
          mul_le_mul_right (hdirectionPowerUpgrade delta r hdelta hdeltar) _
        _ ≤ (64 + 64 * Cdir⁻¹) *
            (ENNReal.ofReal (r / delta)).rpow (3 + ε) :=
          by
            gcongr
            exact le_add_left le_rfl
  have hdReal : d.toReal < 3 + ε := by
    have hrightTop : (3 + ENNReal.ofReal ε : ENNReal) ≠ ⊤ := by
      finiteness
    have h := (ENNReal.toReal_lt_toReal hdtop hrightTop).2 hd
    rw [ENNReal.toReal_add (by norm_num) ENNReal.ofReal_ne_top] at h
    simpa [hε.le] using h
  let Ccarrier : ENNReal :=
    Ccover * (ENNReal.ofReal (1 / 2 : ℝ)).rpow (-d.toReal)
  have hCcarrierTop : Ccarrier ≠ ⊤ := by
    dsimp [Ccarrier]
    apply ENNReal.mul_ne_top hCcoverTop
    exact ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)) ENNReal.ofReal_ne_top
  have hcarrierCoveringData :
      ∀ {n : ℕ} (center : Fin n → MarkedLine),
        (∀ i, center i ∈ pieceLines) →
        ∀ r : ℝ, 0 < r → r ≤ δcover → r ≤ 1 →
          coveringNumber (lineCarrier (Set.range center)) r ≤
            Ccarrier * (ENNReal.ofReal r).rpow (-(3 + ε)) := by
    intro n center hcenterPiece r hr hrcover hrone
    have hcarrierSubset : lineCarrier (Set.range center) ⊆ piece := by
      rintro z ⟨line, ⟨i, rfl⟩, rfl⟩
      exact (hcenterPiece i).2
    have hpieceBound := hcoverSmall r hr hrcover
    have hbase : ENNReal.ofReal r ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hrone
    have hexponent :
        (ENNReal.ofReal r).rpow (-d.toReal) ≤
          (ENNReal.ofReal r).rpow (-(3 + ε)) := by
      exact ENNReal.rpow_le_rpow_of_exponent_ge hbase (by linarith [hdReal])
    have hhalf : ENNReal.ofReal (r / 2) =
        ENNReal.ofReal r * ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [show r / 2 = r * (1 / 2 : ℝ) by ring]
      exact ENNReal.ofReal_mul hr.le
    calc
      coveringNumber (lineCarrier (Set.range center)) r ≤
          coveringNumber piece r := coveringNumber_mono hcarrierSubset r
      _ ≤ Ccover * (ENNReal.ofReal (r / 2)).rpow (-d.toReal) :=
        hpieceBound
      _ = Ccover * ((ENNReal.ofReal r).rpow (-d.toReal) *
            (ENNReal.ofReal (1 / 2 : ℝ)).rpow (-d.toReal)) := by
        rw [hhalf]
        congr 1
        exact ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top
          ENNReal.ofReal_ne_top _
      _ = Ccarrier * (ENNReal.ofReal r).rpow (-d.toReal) := by
        simp only [Ccarrier]
        ac_rfl
      _ ≤ Ccarrier * (ENNReal.ofReal r).rpow (-(3 + ε)) :=
        mul_le_mul_right hexponent Ccarrier
  let ClargeCover : ENNReal :=
    Ccover * (ENNReal.ofReal (δcover / 2)).rpow (-d.toReal)
  let CcarrierAll : ENNReal := max Ccarrier ClargeCover
  have hcarrierCoveringAllScales :
      ∀ {n : ℕ} (delta : ℝ) (center : Fin n → MarkedLine),
        (∀ i, center i ∈ pieceLines) →
        0 < delta → delta ≤ δcover →
        ∀ r : ℝ, delta ≤ r → r ≤ 1 →
          coveringNumber (lineCarrier (Set.range center)) r ≤
            CcarrierAll * (ENNReal.ofReal r).rpow (-(3 + ε)) := by
    intro n delta center hcenterPiece hdelta hdeltaCover r hdeltar hrone
    rcases le_total r δcover with hrcover | hcoverr
    · calc
        coveringNumber (lineCarrier (Set.range center)) r ≤
            Ccarrier * (ENNReal.ofReal r).rpow (-(3 + ε)) :=
          hcarrierCoveringData center hcenterPiece r
            (lt_of_lt_of_le hdelta hdeltar) hrcover hrone
        _ ≤ CcarrierAll * (ENNReal.ofReal r).rpow (-(3 + ε)) := by
          dsimp [CcarrierAll]
          gcongr
          exact le_max_left Ccarrier ClargeCover
    · have hcarrierSubset : lineCarrier (Set.range center) ⊆ piece := by
        rintro z ⟨line, ⟨i, rfl⟩, rfl⟩
        exact (hcenterPiece i).2
      have hrpos : 0 < r := lt_of_lt_of_le hdelta hdeltar
      have hrbasePos : 0 < ENNReal.ofReal r := ENNReal.ofReal_pos.mpr hrpos
      have hrbaseOne : ENNReal.ofReal r ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hrone
      have hpowOne : (1 : ENNReal) ≤
          (ENNReal.ofReal r).rpow (-(3 + ε)) := by
        exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg hrbasePos hrbaseOne
          (by linarith)
      calc
        coveringNumber (lineCarrier (Set.range center)) r ≤
            coveringNumber piece r := coveringNumber_mono hcarrierSubset r
        _ ≤ coveringNumber piece δcover :=
          coveringNumber_anti_radius piece hcoverr
        _ ≤ ClargeCover := by
          simpa [ClargeCover] using hcoverSmall δcover hδcover le_rfl
        _ ≤ CcarrierAll := le_max_right Ccarrier ClargeCover
        _ = CcarrierAll * 1 := (mul_one CcarrierAll).symm
        _ ≤ CcarrierAll * (ENNReal.ofReal r).rpow (-(3 + ε)) :=
          mul_le_mul_right hpowOne CcarrierAll
  let Cread : ENNReal :=
    2 * Cdir *
      ((ENNReal.ofReal (1 / 4 : ℝ)) ^ 4 *
        ENNReal.ofReal (Real.pi ^ 2 / 2))⁻¹
  have hactiveCellLocalVolume :
      ∀ {n : ℕ} (delta : ℝ) (center : Fin n → MarkedLine)
        (cell : Fin n → Set MarkedLine),
        0 < delta →
        (∀ i, ∀ line ∈ cell i,
          ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
            dist (rawFrontParam (line, t))
              (rawFrontParam (center i, t)) < delta / 4) →
        ∀ x : E4, ∀ i,
          (∃ line ∈ cell i,
            (markedLineBallFibreSet line x delta).Nonempty) →
          (ENNReal.ofReal (delta / 4)) ^ 4 *
              ENNReal.ofReal (Real.pi ^ 2 / 2) ≤
            volume (markedUnitTube (center i) delta ∩
              Metric.closedBall x (2 * delta)) := by
    intro n delta center cell hdelta hfront x i hactive
    obtain ⟨line, hlineCell, t, htball⟩ := hactive
    have happrox := hfront i line hlineCell (t : ℝ) t.property
    have hball : dist (rawFrontParam (line, (t : ℝ))) x < delta := htball
    have hnear :
        dist (rawFrontParam (center i, (t : ℝ))) x < 3 * delta / 2 := by
      calc
        dist (rawFrontParam (center i, (t : ℝ))) x ≤
            dist (rawFrontParam (center i, (t : ℝ)))
                (rawFrontParam (line, (t : ℝ))) +
              dist (rawFrontParam (line, (t : ℝ))) x := dist_triangle _ _ _
        _ < delta / 4 + delta :=
          add_lt_add (by simpa [dist_comm] using happrox) hball
        _ < 3 * delta / 2 := by linarith
    exact volume_quarterBall_le_markedUnitTube_inter_closedBall
      (center i) t.property hdelta x hnear
  have hlocalReadbackData :
      ∀ {n : ℕ} (delta : ℝ) (center : Fin n → MarkedLine)
        (hcenterInjective : Function.Injective center)
        (cell : Fin n → Set MarkedLine),
        0 < delta →
        (∀ i, MeasurableSet (cell i)) →
        Pairwise (fun i j => Disjoint (cell i) (cell j)) →
        pieceLines ⊆ ⋃ i, cell i →
        (∀ i, ∀ line ∈ cell i,
          ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
            dist (rawFrontParam (line, t))
              (rawFrontParam (center i, t)) < delta / 4) →
        ∀ x : E4,
          ∃ active : Set (Fin n), ∃ R : FiniteScaleSource n,
            IsFractionalSourceRestriction R
              (fullMarkedTubeSource delta center hcenterInjective
                (fun i => ν (cell i)) Cdir) ∧
            sourceUnion R ⊆ Metric.closedBall x (2 * delta) ∧
            μ (Metric.ball x delta) ≤
              ENNReal.ofReal (2 * delta) *
                ν (⋃ i : {i // i ∈ active}, cell i.1) ∧
            (∀ i, i ∈ active →
              (ENNReal.ofReal (delta / 4)) ^ 4 *
                  ENNReal.ofReal (Real.pi ^ 2 / 2) ≤
                volume (R.shading i)) ∧
            μ (Metric.ball x delta) ≤ Cread * sourceMass R := by
    classical
    intro n delta center hcenterInjective cell hdelta hcellMeasurable
      hcellDisjoint hcellsCover hfront x
    let active : Set (Fin n) :=
      {i | ∃ line ∈ cell i,
        (markedLineBallFibreSet line x delta).Nonempty}
    let q : Fin n → ENNReal := fun i => ν (cell i)
    let R : FiniteScaleSource n :=
      activeBallRestriction delta center hcenterInjective q Cdir active x (2 * delta)
    have hcaptures : ∀ line ∈ pieceLines,
        (markedLineBallFibreSet line x delta).Nonempty →
          ∃ i, i ∈ active ∧ line ∈ cell i := by
      intro line hline hmeet
      have hcovered := hcellsCover hline
      simp only [Set.mem_iUnion] at hcovered
      obtain ⟨i, hicell⟩ := hcovered
      exact ⟨i, ⟨line, hicell, hmeet⟩, hicell⟩
    have hfrontBound := markedCarrierPieceFrontProbability_ball_le_active_cells
      selector hmeasurable hvalid hselector piece hpieceMeasurable
      hpieceCarrier hpieceMass cell hcellMeasurable active x hdelta.le hcaptures
    have hactiveMeasure :
        ν (⋃ i : {i // i ∈ active}, cell i.1) =
          ∑ i, if i ∈ active then ν (cell i) else 0 := by
      let J : Finset (Fin n) := Finset.univ.filter fun i => i ∈ active
      have hJdisjoint : PairwiseDisjoint (↑J) cell := by
        intro i hi j hj hij
        exact hcellDisjoint hij
      calc
        ν (⋃ i : {i // i ∈ active}, cell i.1) =
            ν (⋃ i ∈ J, cell i) := by
              congr 1
              ext line
              simp [J]
        _ = ∑ i ∈ J, ν (cell i) :=
          measure_biUnion_finset hJdisjoint (fun i hi => hcellMeasurable i)
        _ = ∑ i, if i ∈ active then ν (cell i) else 0 := by
          simp [J, Finset.sum_filter]
    have hvol : ∀ i, i ∈ active →
        (ENNReal.ofReal (delta / 4)) ^ 4 *
            ENNReal.ofReal (Real.pi ^ 2 / 2) ≤
          volume (R.shading i) := by
      intro i hiactive
      have hv := hactiveCellLocalVolume delta center cell hdelta hfront x i hiactive
      simpa [R, activeBallRestriction, hiactive] using hv
    have hpayment :=
      two_delta_mul_active_mass_le_readback_constant_mul_sourceMass
        delta center hcenterInjective (fun i => ν (cell i)) Cdir active x
        hdelta hCdirNe hCdirTop
        (by
          intro i hiactive
          have hv := hactiveCellLocalVolume delta center cell hdelta hfront x i hiactive
          simpa using hv)
    refine ⟨active, R, ?_, ?_, hfrontBound, hvol, ?_⟩
    · exact activeBallRestriction_isFractionalSourceRestriction
        delta center hcenterInjective q Cdir active x (2 * delta)
    · exact sourceUnion_activeBallRestriction_subset
        delta center hcenterInjective q Cdir active x (2 * delta)
    · calc
        μ (Metric.ball x delta) ≤
            ENNReal.ofReal (2 * delta) *
              ν (⋃ i : {i // i ∈ active}, cell i.1) := hfrontBound
        _ = ENNReal.ofReal (2 * delta) *
            (∑ i, if i ∈ active then ν (cell i) else 0) := by
          rw [hactiveMeasure]
        _ ≤ Cread * sourceMass R := by
          simpa [Cread, R, q] using hpayment
  let Mlo : ENNReal := Cdir⁻¹ *
    (ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal (Real.pi ^ 2 / 2))
  let Mhi : ENNReal := Cdir⁻¹ *
    (32 * ENNReal.ofReal (Real.pi ^ 2 / 2))
  let Cdirection : ENNReal := 64 + 64 * Cdir⁻¹
  have hMloPos : 0 < Mlo := by
    dsimp [Mlo]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hCdirTop)
      (mul_ne_zero
        (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num))
        (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)))
  have hMloTop : Mlo ≠ ⊤ := by
    dsimp [Mlo]
    finiteness
  have hMhiTop : Mhi ≠ ⊤ := by
    dsimp [Mhi]
    finiteness
  have hCdirectionTop : Cdirection ≠ ⊤ := by
    dsimp [Cdirection]
    finiteness
  have hClargeCoverTop : ClargeCover ≠ ⊤ := by
    dsimp [ClargeCover]
    apply ENNReal.mul_ne_top hCcoverTop
    exact ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.ofReal_ne_zero_iff.mpr (by linarith)) ENNReal.ofReal_ne_top
  have hCcarrierAllTop : CcarrierAll ≠ ⊤ := by
    apply ne_of_lt
    dsimp [CcarrierAll]
    exact max_lt (lt_top_iff_ne_top.mpr hCcarrierTop)
      (lt_top_iff_ne_top.mpr hClargeCoverTop)
  have hCreadTop : Cread ≠ ⊤ := by
    dsimp [Cread]
    have haZero :
        (ENNReal.ofReal (1 / 4 : ℝ)) ^ 4 *
            ENNReal.ofReal (Real.pi ^ 2 / 2) ≠ 0 := by
      apply mul_ne_zero
      · exact pow_ne_zero 4 (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num))
      · exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
    finiteness
  let Cglobal : ENNReal :=
    max Cdirection
      (max CcarrierAll (max Mlo⁻¹ (max Mhi (max Cread 1))))
  have hCglobalNe : Cglobal ≠ 0 := by
    have hone : (1 : ENNReal) ≤ Cglobal := by simp [Cglobal]
    exact ne_of_gt (zero_lt_one.trans_le hone)
  have hCglobalTop : Cglobal ≠ ⊤ := by
    apply ne_of_lt
    dsimp [Cglobal]
    exact max_lt (lt_top_iff_ne_top.mpr hCdirectionTop)
      (max_lt (lt_top_iff_ne_top.mpr hCcarrierAllTop)
        (max_lt (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hMloPos.ne'))
          (max_lt (lt_top_iff_ne_top.mpr hMhiTop)
            (max_lt (lt_top_iff_ne_top.mpr hCreadTop) ENNReal.coe_lt_top))))
  /-
  The positive packing piece is now measurable, lies in the genuine selector
  carrier, has nonzero canonical directional mass, and carries an eventually
  uniform covering estimate.  Its normalized marked-fibre pushforward `μ`
  is the single physical probability to be discretized at every later scale.
  The physical support statement is now discharged on the compact ambient
  front.  Moreover the normalized carrier law and the full carrier--fibre
  product law have zero mass off the retained packing piece.  The corresponding
  marked-line pushforward is likewise supported on the actual selector lines
  over that piece, so later Voronoi weights are honest probabilities on lines
  retaining their affine marks.  The eventual
  covering bound has also been converted to one uniform interval
  `(0, δcover]`.  Finally, compactness of the ambient marked family gives a
  finite net of the actual retained marked lines at every positive radius.
  Heine--Cantor on the compact marked family upgrades that net to a finite
  front approximation: one marked radius works simultaneously for every
  segment parameter, and every retained segment is pointwise within the
  prescribed physical error of its marked center segment.  The centers retain
  the affine mark, so the construction never assumes the mark is continuous
  in the carrier coordinates.  Thus the later finite partition may use
  `carrierPiece_selectorLine_exact` almost everywhere and the marked net
  pointwise.  The retained marked-line law has now also been disjointified
  into finitely many measurable cells subordinate to the marked balls.  Their
  masses sum exactly to one, every cell retains the selector and affine-mark
  data, and the center segment approximates every line in its cell uniformly
  in the fibre parameter.  Every resulting actual marked tube is now also
  measurable, satisfies the physical tube condition pointwise, and has the
  sharp uniform transverse-volume lower bound of order `delta^3`, obtained
  from a longitudinally packed disjoint ball family.  After shrinking to the
  single cutoff `δTube(ε)`, this already gives exactly the ambient-source
  lower bound `delta^(3+ε)` in `IsAdmissibleStickySource`.  The retained
  marked-line probability now also obeys one cubic direction-cap estimate
  with a finite nonzero constant `Cdir`; it is the exact pushforward of the
  normalized sphere-cap estimate through the conditioned carrier piece and
  the marked-line inverse.  The two-scale probability cells, normalized
  weights, one-level source tree, exact scale-free source-mass bounds, and
  active-cell local readback data are now constructed above.  What remains in
  the final assembly is the arbitrary-center direction--Carleson comparison,
  the retained carrier covering exponent comparison, and the finite maximum
  of their constants.  No endpoint attainment or scale-dependent change of
  measure remains in this interface.
  -/
  have hνparamFront :
      HasFrontDirectionFibreBound selector hmeasurable hvalid hselector
        νparam Cdir := by
    simpa [νparam, Cdir] using
      (markedCarrierPieceFrontParameterProbability_hasFrontDirectionFibreBound
        selector hmeasurable hvalid hselector piece hpieceMeasurable
          hpieceCarrier hpieceMass)
  have hνparamNorth : νparam contactNorthParameterCapᶜ = 0 := by
    have hpieceNorth : ∀ q ∈ piece,
        dist q.1 contactNorthPole < (1 / 4 : ℝ) := by
      intro q hq
      have hqNorth := (hpieceLocalized hq).1.2
      simpa [northCarrierRegion, carrierDirectionBall, wzNorthPole,
        contactNorthPole, Metric.mem_ball] using hqNorth
    simpa [νparam] using
      (markedCarrierPieceFrontParameterProbability_contactNorthSupport
        hpieceMeasurable hpieceCarrier hpieceMass hpieceNorth)
  refine ⟨Cglobal, hCglobalNe, hCglobalTop, μ, hμprob, hμsupport,
    νparam, hνparamProb, hνparamMap, hνparamNorth,
      Cdir, hCdirNe, hCdirTop,
      hνparamFront, ?_⟩
  let δ₀ : ℝ := min δTube (min (1 / 8 : ℝ) δcover)
  have hδ₀ : 0 < δ₀ := by
    dsimp [δ₀]
    exact lt_min hδTube (lt_min (by norm_num) hδcover)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro delta hdelta hdelta₀
  have hdeltaTube : delta ≤ δTube :=
    hdelta₀.trans (min_le_left _ _)
  have hdeltaEight : delta ≤ (1 / 8 : ℝ) :=
    hdelta₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaCover : delta ≤ δcover :=
    hdelta₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdeltaOne : delta ≤ 1 := by linarith
  have heta : 0 < delta / 4 := by linarith
  obtain ⟨rho, hrho, n, center, cell, hcenterPiece, hcenterInjective,
      hcellMeasurable, hcellDisjoint, hcellSubordinate, hcellsCover,
      hcellMass, hfrontCell, hdirectionCell, hcellCap⟩ :=
    hfiniteWeightedMarkedPartition (delta / 4) delta heta hdelta hdeltaOne
  let q : Fin n → ENNReal := fun i => ν (cell i)
  let D : FiniteScaleSource n :=
    fullMarkedTubeSource delta center hcenterInjective q Cdir
  have hq : ∑ i, q i = 1 := by
    simpa only [q, tsum_fintype] using hcellMass
  have hdenZero : Cdir * (ENNReal.ofReal delta) ^ 3 ≠ 0 := by
    exact mul_ne_zero hCdirNe
      (pow_ne_zero 3 (ENNReal.ofReal_ne_zero_iff.mpr hdelta))
  have hdenTop : Cdir * (ENNReal.ofReal delta) ^ 3 ≠ ⊤ := by
    exact ENNReal.mul_ne_top hCdirTop
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hlower : ∀ i,
      (ENNReal.ofReal (1 / 8 : ℝ) *
          ENNReal.ofReal (Real.pi ^ 2 / 2)) *
          (ENNReal.ofReal delta) ^ 3 ≤
        volume (markedUnitTube (center i) delta) := by
    intro i
    calc
      (ENNReal.ofReal (1 / 8 : ℝ) *
          ENNReal.ofReal (Real.pi ^ 2 / 2)) *
          (ENNReal.ofReal delta) ^ 3 =
        ENNReal.ofReal (1 / 8 : ℝ) *
          (ENNReal.ofReal delta) ^ 3 *
            ENNReal.ofReal (Real.pi ^ 2 / 2) := by ac_rfl
      _ ≤ volume (markedUnitTube (center i) delta) :=
        (hmarkedTubeAdmissibleCore (center i) (hcenterPiece i)
          delta hdelta hdeltaEight).2.2
  have hupper : ∀ i,
      volume (markedUnitTube (center i) delta) ≤
        (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)) *
          (ENNReal.ofReal delta) ^ 3 := by
    intro i
    calc
      volume (markedUnitTube (center i) delta) ≤
          32 * (ENNReal.ofReal delta) ^ 3 *
            ENNReal.ofReal (Real.pi ^ 2 / 2) :=
        volume_markedUnitTube_upper_bound
          (hvalid (center i) (hcenterPiece i).1) hdelta hdeltaOne
      _ = (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)) *
          (ENNReal.ofReal delta) ^ 3 := by ac_rfl
  have hmassBounds := sourceMass_fullMarkedTubeSource_normalized_bounds
    delta center hcenterInjective q Cdir
    (ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal (Real.pi ^ 2 / 2))
    (32 * ENNReal.ofReal (Real.pi ^ 2 / 2))
    hCdirNe hCdirTop hdelta hq hlower hupper
  refine ⟨n, D, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hcenterPiece i).1
  · intro i
    exact northCarrierRegion_direction_ge_half selector
      (direction (center i), offset (center i))
      (hpieceLocalized (hcenterPiece i).2).1
  · refine ⟨hdelta, (lt_of_le_of_lt hdeltaEight (by norm_num)), ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact normalizedPartitionWeight_le_one hdenZero hdenTop (hcellCap i)
    · intro i
      rfl
    · intro i
      exact hvalid (center i) (hcenterPiece i).1
    · intro i
      exact measurableSet_markedUnitTube (center i) delta
    · intro i hi
      exact hmarkedTubeAdmissibleAtEpsilon (center i) (hcenterPiece i)
        delta hdelta hdeltaTube
    · intro i x hx
      exact (hmarkedTubeAdmissibleCore (center i) (hcenterPiece i)
        delta hdelta hdeltaEight).2.1 x hx
    · intro theta r hdeltar hrone
      have hdir := hdirectionCarlesonData delta center hcenterInjective cell
        hdelta hcellMeasurable hcellDisjoint hdirectionCell hcellMass
        theta r hdeltar hrone
      calc
        directionWeightInBall D theta r ≤
            Cdirection * (ENNReal.ofReal (r / delta)).rpow (3 + ε) := by
          simpa [D, q, Cdirection] using hdir
        _ ≤ Cglobal * (ENNReal.ofReal (r / delta)).rpow (3 + ε) := by
          simpa [mul_comm] using mul_le_mul_right
            (by simp [Cglobal] : Cdirection ≤ Cglobal)
            ((ENNReal.ofReal (r / delta)).rpow (3 + ε))
    · intro r hdeltar hrone
      have hcov := hcarrierCoveringAllScales delta center hcenterPiece
        hdelta hdeltaCover r hdeltar hrone
      calc
        coveringNumber (lineCarrier (Set.range D.line)) r ≤
            CcarrierAll * (ENNReal.ofReal r).rpow (-(3 + ε)) := by
          change coveringNumber (lineCarrier (Set.range center)) r ≤ _
          exact hcov
        _ ≤ Cglobal * (ENNReal.ofReal r).rpow (-(3 + ε)) := by
          simpa [mul_comm] using mul_le_mul_right
            (by simp [Cglobal] : CcarrierAll ≤ Cglobal)
            ((ENNReal.ofReal r).rpow (-(3 + ε)))
  · calc
      Cglobal⁻¹ ≤ Mlo := by
        have hdom : Mlo⁻¹ ≤ Cglobal := by simp [Cglobal]
        simpa using ENNReal.inv_le_inv' hdom
      _ ≤ sourceMass D := by
        simpa [D, Mlo] using hmassBounds.1
  · calc
      sourceMass D ≤ Mhi := by
        simpa [D, Mhi] using hmassBounds.2
      _ ≤ Cglobal := by simp [Cglobal]
  · constructor
    · intro x
      obtain ⟨active, R, hrestriction, hsupport, hfrontBound, hvolume, hread⟩ :=
        hlocalReadbackData delta center hcenterInjective cell hdelta
          hcellMeasurable hcellDisjoint hcellsCover hfrontCell x
      refine ⟨R, ?_, hsupport, ?_⟩
      · simpa [D, q] using hrestriction
      · calc
          μ (Metric.ball x delta) ≤ Cread * sourceMass R := hread
          _ ≤ Cglobal * sourceMass R := by
            simpa [mul_comm] using mul_le_mul_right
              (by simp [Cglobal] : Cread ≤ Cglobal) (sourceMass R)
    · refine ⟨cell, Cdir, hCdirNe, hCdirTop,
        hcellMeasurable, hcellDisjoint, ?_, ?_⟩
      · intro i line hline t ht
        simpa [D] using hfrontCell i line hline t ht
      · intro source hsource
        refine ⟨?_, ?_, ?_⟩
        · have hrestriction :=
            retainedParameterFullTubeSource_isFractionalSourceRestriction_of_packingPiece
              selector hmeasurable hvalid hselector piece source delta D.line
                D.line_injective cell hcellMeasurable Cdir
          have hroot :
              fullMarkedTubeSource delta D.line D.line_injective
                  (fun i ↦ ν (cell i)) Cdir = D := by
            rfl
          rw [hroot] at hrestriction
          simpa [νparam] using hrestriction
        · have hsum :=
            sum_packingPiece_retainedParameterCellMass_eq_sourceMass
              selector hmeasurable hvalid hselector piece hpieceMeasurable
                hpieceCarrier hpieceMass source hsource cell hcellMeasurable
                  hcellDisjoint hcellsCover
          simpa [νparam] using hsum
        · intro i hpos
          exact retainedParameterCellMass_pos_has_witness selector hmeasurable
            hvalid hselector νparam source (cell i) hpos

/-- Public backward-compatible projection of the strengthened construction. -/
theorem packing_selector_to_finite_scale_sources
    (selector : Set MarkedLine)
    (ambient : Set MarkedLine)
    (hambientCompact : IsCompact ambient)
    (hselectorAmbient : selector ⊆ ambient)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3) :
    HasCoherentFiniteScaleSources selector ambient :=
  (packing_selector_to_parametrized_finite_scale_sources selector ambient
    hambientCompact hselectorAmbient hmeasurable hvalid hselector hpacking).toCoherent

end StickyKakeya4
