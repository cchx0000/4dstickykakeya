import Theorems.Thm_StickyKakeya4_retained_source_readback
import Theorems.Thm_StickyKakeya4_front_parametrization
import Theorems.Thm_StickyKakeya4_carrier_piece_probability

open MeasureTheory Set

noncomputable section

namespace StickyKakeya4

/-- Forget only the fibre coordinate of a canonical front parameter and keep
the actual selected marked line.  In particular the affine mark is not
reconstructed from an unmarked carrier. -/
def frontParameterSelectedLine
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    ({theta : E4 // ‖theta‖ = 1} ×
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) → MarkedLine :=
  fun z ↦ selectorLine selector hmeasurable hvalid hselector z.1

theorem measurable_frontParameterSelectedLine
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Measurable
      (frontParameterSelectedLine selector hmeasurable hvalid hselector) := by
  exact measurable_subtype_coe.comp
    ((measurable_selectorLine selector hmeasurable hvalid hselector).comp
      measurable_fst)

/-- The parameter cell lying over one measurable cell of actual marked
selector lines. -/
def frontParameterLineCell
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (cell : Set MarkedLine) :
    Set ({theta : E4 // ‖theta‖ = 1} ×
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
  (frontParameterSelectedLine selector hmeasurable hvalid hselector) ⁻¹' cell

/-- The canonical direction--fibre law attached to a retained packing piece
has exactly the marked-line marginal already used in the finite packing
construction.  This identity is the bridge which lets retained parameter
cell masses replace the former root-law domination argument without changing
the root finite source. -/
theorem map_frontParameterSelectedLine_markedCarrierPieceFrontParameterProbability
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) :
    Measure.map
        (frontParameterSelectedLine selector hmeasurable hvalid hselector)
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure
            ({theta : E4 // ‖theta‖ = 1} ×
              Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) =
      (markedCarrierPieceLineProbability selector hmeasurable hvalid
        hselector piece : Measure MarkedLine) := by
  let P : Measure (E4 × E4) :=
    normalizedCarrierPieceProbability selector hmeasurable hvalid hselector piece
  let I : Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    fibreIntervalProbability
  let G : E4 × E4 → MarkedLine := fun carrier ↦
    (selectorLineFromCarrier selector hmeasurable hvalid hselector carrier :
      MarkedLine)
  have hG : Measurable G :=
    measurable_subtype_coe.comp
      (measurable_selectorLineFromCarrier selector hmeasurable hvalid hselector)
  have hcompose :
      (frontParameterSelectedLine selector hmeasurable hvalid hselector) ∘
          (markedCarrierPieceFrontParameterMap selector hmeasurable hvalid
            hselector) = G ∘ Prod.fst := by
    funext z
    let line :=
      selectorLineFromCarrier selector hmeasurable hvalid hselector z.1
    let theta : {theta : E4 // ‖theta‖ = 1} :=
      ⟨direction line, (hvalid line line.property).1⟩
    obtain ⟨chosen, _hchosen, hunique⟩ :=
      hselector (direction line) (hvalid line line.property).1
    have hsame :
        (selectorLine selector hmeasurable hvalid hselector theta : MarkedLine) =
          (line : MarkedLine) :=
      (hunique _ ⟨(selectorLine selector hmeasurable hvalid hselector theta).property,
        direction_selectorLine selector hmeasurable hvalid hselector theta⟩).trans
        (hunique line ⟨line.property, rfl⟩).symm
    simpa [Function.comp_def, frontParameterSelectedLine,
      markedCarrierPieceFrontParameterMap, G, line, theta] using hsame
  rw [markedCarrierPieceFrontParameterProbability,
    ProbabilityMeasure.toMeasure_map,
    markedCarrierPieceLineProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
    (measurable_frontParameterSelectedLine selector hmeasurable hvalid hselector)
    (measurable_markedCarrierPieceFrontParameterMap selector hmeasurable
      hvalid hselector)]
  change Measure.map
      ((frontParameterSelectedLine selector hmeasurable hvalid hselector) ∘
        markedCarrierPieceFrontParameterMap selector hmeasurable hvalid hselector)
      (P.prod I) = Measure.map G P
  rw [hcompose]
  rw [← Measure.map_map hG measurable_fst]
  rw [Measure.map_fst_prod]
  simp [I]

/-- Keep both the actual selected marked line and the affine-fibre coordinate.
For a retained packing piece this coordinate change sends its canonical
direction--fibre law exactly to the product of the retained marked-line law
and the uniform fibre law. -/
def frontParameterSelectedLineFibre
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    ({theta : E4 // ‖theta‖ = 1} ×
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) →
      MarkedLine × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
  fun z ↦
    (frontParameterSelectedLine selector hmeasurable hvalid hselector z, z.2)

theorem measurable_frontParameterSelectedLineFibre
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Measurable
      (frontParameterSelectedLineFibre selector hmeasurable hvalid
        hselector) := by
  exact
    (measurable_frontParameterSelectedLine selector hmeasurable hvalid
      hselector).prodMk measurable_snd

theorem map_frontParameterSelectedLineFibre_markedCarrierPieceFrontParameterProbability
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) :
    Measure.map
        (frontParameterSelectedLineFibre selector hmeasurable hvalid hselector)
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece : Measure
            ({theta : E4 // ‖theta‖ = 1} ×
              Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) =
      (markedCarrierPieceLineProbability selector hmeasurable hvalid
        hselector piece : Measure MarkedLine).prod
          (fibreIntervalProbability : Measure
            (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) := by
  let P : Measure (E4 × E4) :=
    normalizedCarrierPieceProbability selector hmeasurable hvalid hselector piece
  let I : Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    fibreIntervalProbability
  let G : E4 × E4 → MarkedLine := fun carrier ↦
    (selectorLineFromCarrier selector hmeasurable hvalid hselector carrier :
      MarkedLine)
  have hG : Measurable G :=
    measurable_subtype_coe.comp
      (measurable_selectorLineFromCarrier selector hmeasurable hvalid hselector)
  have hcompose :
      (frontParameterSelectedLineFibre selector hmeasurable hvalid hselector) ∘
          (markedCarrierPieceFrontParameterMap selector hmeasurable hvalid
            hselector) = Prod.map G id := by
    funext z
    apply Prod.ext
    · let line :=
        selectorLineFromCarrier selector hmeasurable hvalid hselector z.1
      let theta : {theta : E4 // ‖theta‖ = 1} :=
        ⟨direction line, (hvalid line line.property).1⟩
      obtain ⟨chosen, _hchosen, hunique⟩ :=
        hselector (direction line) (hvalid line line.property).1
      have hsame :
          (selectorLine selector hmeasurable hvalid hselector theta :
              MarkedLine) = (line : MarkedLine) :=
        (hunique _
          ⟨(selectorLine selector hmeasurable hvalid hselector theta).property,
            direction_selectorLine selector hmeasurable hvalid hselector theta⟩).trans
          (hunique line ⟨line.property, rfl⟩).symm
      simpa [Function.comp_def, frontParameterSelectedLineFibre,
        frontParameterSelectedLine, markedCarrierPieceFrontParameterMap,
        G, line, theta] using hsame
    · rfl
  rw [markedCarrierPieceFrontParameterProbability,
    ProbabilityMeasure.toMeasure_map,
    markedCarrierPieceLineProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
    (measurable_frontParameterSelectedLineFibre selector hmeasurable hvalid
      hselector)
    (measurable_markedCarrierPieceFrontParameterMap selector hmeasurable
      hvalid hselector)]
  change Measure.map
      ((frontParameterSelectedLineFibre selector hmeasurable hvalid hselector) ∘
        markedCarrierPieceFrontParameterMap selector hmeasurable hvalid hselector)
      (P.prod I) = (Measure.map G P).prod I
  rw [hcompose]
  have hmapId : Measure.map id I = I := Measure.map_id
  calc
    Measure.map (Prod.map G id) (P.prod I) =
        (Measure.map G P).prod (Measure.map id I) := by
      exact (Measure.map_prod_map P I hG measurable_id).symm
    _ = (Measure.map G P).prod I := by rw [hmapId]

/-- Cellwise form of the marked-line marginal identity. -/
theorem markedCarrierPieceFrontParameterProbability_frontParameterLineCell
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) {cell : Set MarkedLine}
    (hcell : MeasurableSet cell) :
    (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure
          ({theta : E4 // ‖theta‖ = 1} ×
            Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
        (frontParameterLineCell selector hmeasurable hvalid hselector cell) =
      (markedCarrierPieceLineProbability selector hmeasurable hvalid
        hselector piece : Measure MarkedLine) cell := by
  calc
    (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure
          ({theta : E4 // ‖theta‖ = 1} ×
            Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
        (frontParameterLineCell selector hmeasurable hvalid hselector cell) =
      Measure.map
          (frontParameterSelectedLine selector hmeasurable hvalid hselector)
          (markedCarrierPieceFrontParameterProbability selector hmeasurable
            hvalid hselector piece : Measure
              ({theta : E4 // ‖theta‖ = 1} ×
                Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) cell := by
        rw [Measure.map_apply
          (measurable_frontParameterSelectedLine selector hmeasurable hvalid
            hselector) hcell]
        rfl
    _ = (markedCarrierPieceLineProbability selector hmeasurable hvalid
        hselector piece : Measure MarkedLine) cell := by
      rw [map_frontParameterSelectedLine_markedCarrierPieceFrontParameterProbability]

theorem measurableSet_frontParameterLineCell
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    {cell : Set MarkedLine} (hcell : MeasurableSet cell) :
    MeasurableSet
      (frontParameterLineCell selector hmeasurable hvalid hselector cell) :=
  hcell.preimage
    (measurable_frontParameterSelectedLine selector hmeasurable hvalid hselector)

/-- The coefficient assigned to one finite marked-line cell by an actual
retained parameter source.  This is deliberately unnormalized: descendants
therefore add with coefficient one. -/
def retainedParameterCellMass
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (nu : Measure
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (source : Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (cell : Set MarkedLine) : ENNReal :=
  nu (source ∩
    frontParameterLineCell selector hmeasurable hvalid hselector cell)

/-- Retaining a parameter source can only decrease each marked-line cell
mass. -/
theorem retainedParameterCellMass_le_root
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (nu : Measure
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (source : Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (cell : Set MarkedLine) :
    retainedParameterCellMass selector hmeasurable hvalid hselector
        nu source cell ≤
      nu (frontParameterLineCell selector hmeasurable hvalid hselector cell) := by
  exact measure_mono Set.inter_subset_right

/-- The full-tube source whose row coefficients are the actual masses of a
retained parameter source in the marked-line cells. -/
noncomputable def retainedParameterFullTubeSource {n : ℕ}
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (nu : Measure
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (source : Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (cell : Fin n → Set MarkedLine)
    (C : ENNReal) : FiniteScaleSource n :=
  fullMarkedTubeSource delta line hline
    (fun i ↦ retainedParameterCellMass selector hmeasurable hvalid hselector
      nu source (cell i)) C

/-- Exact source-coherence bridge.  The retained finite source is a
coefficient-one fractional restriction of the root source formed from the
same parameter cells.  Lines, affine marks, shadings, and the carrier tree
are definitionally unchanged. -/
theorem retainedParameterFullTubeSource_isFractionalSourceRestriction
    {n : ℕ}
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (nu : Measure
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (source : Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (cell : Fin n → Set MarkedLine)
    (C : ENNReal) :
    IsFractionalSourceRestriction
      (retainedParameterFullTubeSource selector hmeasurable hvalid hselector
        nu source delta line hline cell C)
      (fullMarkedTubeSource delta line hline
        (fun i ↦ nu (frontParameterLineCell selector hmeasurable hvalid
          hselector (cell i))) C) := by
  apply fullMarkedTubeSource_isFractionalSourceRestriction_of_cellMass_le
  intro i
  exact retainedParameterCellMass_le_root selector hmeasurable hvalid hselector
    nu source (cell i)

/-- Packing-piece specialization of the exact source-coherence bridge.  Its
root is literally the pre-existing full-tube source whose cell masses are
computed with `markedCarrierPieceLineProbability`; hence it can replace the
former root-law-only `toConditioned` readback without altering `D`. -/
theorem retainedParameterFullTubeSource_isFractionalSourceRestriction_of_packingPiece
    {n : ℕ}
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (source : Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (cell : Fin n → Set MarkedLine)
    (hcell : ∀ i, MeasurableSet (cell i)) (C : ENNReal) :
    IsFractionalSourceRestriction
      (retainedParameterFullTubeSource selector hmeasurable hvalid hselector
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece)
        source delta line hline cell C)
      (fullMarkedTubeSource delta line hline
        (fun i ↦
          (markedCarrierPieceLineProbability selector hmeasurable hvalid
            hselector piece : Measure MarkedLine) (cell i)) C) := by
  apply fullMarkedTubeSource_isFractionalSourceRestriction_of_cellMass_le
  intro i
  calc
    retainedParameterCellMass selector hmeasurable hvalid hselector
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece) source (cell i) ≤
      (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure
          ({theta : E4 // ‖theta‖ = 1} ×
            Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
        (frontParameterLineCell selector hmeasurable hvalid hselector
          (cell i)) :=
      retainedParameterCellMass_le_root selector hmeasurable hvalid hselector
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece) source (cell i)
    _ = (markedCarrierPieceLineProbability selector hmeasurable hvalid
          hselector piece : Measure MarkedLine) (cell i) :=
      markedCarrierPieceFrontParameterProbability_frontParameterLineCell
        selector hmeasurable hvalid hselector piece (hcell i)

/-- A positive retained row has a literal parameter witness in the retained
source and its actual selected marked line lies in the corresponding cell.
This prevents later collision rows from being imported from the root law. -/
theorem retainedParameterCellMass_pos_has_witness
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (nu : Measure
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (source : Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (cell : Set MarkedLine)
    (hpos : 0 < retainedParameterCellMass selector hmeasurable hvalid
      hselector nu source cell) :
    ∃ z, z ∈ source ∧
      frontParameterSelectedLine selector hmeasurable hvalid hselector z ∈
        cell := by
  by_contra hnone
  push_neg at hnone
  have hempty : source ∩
      frontParameterLineCell selector hmeasurable hvalid hselector cell = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage,
      frontParameterLineCell, Set.mem_empty_iff_false, iff_false]
    exact fun hz ↦ hnone z hz.1 hz.2
  rw [retainedParameterCellMass, hempty, measure_empty] at hpos
  exact (lt_irrefl 0) hpos

/-- A positive retained row is geometrically attached to the conditioned
packet.  At the witness's actual affine-fibre height, the row centre passes
within the cell approximation error plus the packet radius of the packet
centre. -/
theorem retainedParameterCellMass_pos_center_near_packet
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (nu : Measure
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (source : Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (cell : Set MarkedLine) (center : MarkedLine)
    (x : E4) (radius eta : ℝ)
    (hsourceBall : source ⊆
      (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
        Metric.ball x radius)
    (hcellApprox : ∀ line ∈ cell,
      ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        dist (rawFrontParam (line, t)) (rawFrontParam (center, t)) < eta)
    (hpos : 0 < retainedParameterCellMass selector hmeasurable hvalid
      hselector nu source cell) :
    ∃ z, z ∈ source ∧
      frontParameterSelectedLine selector hmeasurable hvalid hselector z ∈
        cell ∧
      dist (rawFrontParam (center, (z.2 : ℝ))) x < eta + radius := by
  obtain ⟨z, hzsource, hzcell⟩ :=
    retainedParameterCellMass_pos_has_witness selector hmeasurable hvalid
      hselector nu source cell hpos
  refine ⟨z, hzsource, hzcell, ?_⟩
  have happrox := hcellApprox
    (frontParameterSelectedLine selector hmeasurable hvalid hselector z)
    hzcell (z.2 : ℝ) z.2.property
  have hball := hsourceBall hzsource
  change dist
      (rawFrontParam
        (frontParameterSelectedLine selector hmeasurable hvalid hselector z,
          (z.2 : ℝ))) x < radius at hball
  calc
    dist (rawFrontParam (center, (z.2 : ℝ))) x ≤
        dist (rawFrontParam (center, (z.2 : ℝ)))
            (rawFrontParam
              (frontParameterSelectedLine selector hmeasurable hvalid hselector z,
                (z.2 : ℝ))) +
          dist
            (rawFrontParam
              (frontParameterSelectedLine selector hmeasurable hvalid hselector z,
                (z.2 : ℝ))) x := dist_triangle _ _ _
    _ < eta + radius := add_lt_add (by simpa [dist_comm] using happrox) hball

/-- A measurable disjoint marked-line partition covering the retained source
conserves its complete unnormalized mass.  This is the finite source version
of source heredity: no normalization factor and no root-law mass enter the
identity. -/
theorem sum_retainedParameterCellMass_eq_sourceMass
    {n : ℕ}
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (nu : Measure
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (source : Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (cell : Fin n → Set MarkedLine)
    (hsource : MeasurableSet source)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j)))
    (hcover : source ⊆ ⋃ i,
      frontParameterLineCell selector hmeasurable hvalid hselector (cell i)) :
    ∑ i, retainedParameterCellMass selector hmeasurable hvalid hselector
        nu source (cell i) = nu source := by
  classical
  let retainedCell : Fin n → Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    fun i ↦ source ∩
      frontParameterLineCell selector hmeasurable hvalid hselector (cell i)
  have hretainedMeasurable : ∀ i, MeasurableSet (retainedCell i) := by
    intro i
    exact hsource.inter
      (measurableSet_frontParameterLineCell selector hmeasurable hvalid
        hselector (hcell i))
  have hretainedDisjoint :
      Pairwise (fun i j ↦ Disjoint (retainedCell i) (retainedCell j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    exact Set.disjoint_left.mp (hdisjoint hij) hzi.2 hzj.2
  have hunion : (⋃ i, retainedCell i) = source := by
    apply Set.Subset.antisymm
    · intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨i, hzi⟩ := hz
      exact hzi.1
    · intro z hz
      have hzcover := hcover hz
      simp only [Set.mem_iUnion] at hzcover ⊢
      obtain ⟨i, hzi⟩ := hzcover
      exact ⟨i, hz, hzi⟩
  have hfinsetDisjoint : PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin n))) retainedCell := by
    intro i _hi j _hj hij
    exact hretainedDisjoint hij
  calc
    ∑ i, retainedParameterCellMass selector hmeasurable hvalid hselector
        nu source (cell i) = ∑ i ∈ (Finset.univ : Finset (Fin n)),
          nu (retainedCell i) := by
            simp [retainedParameterCellMass, retainedCell]
    _ = nu (⋃ i ∈ (Finset.univ : Finset (Fin n)), retainedCell i) := by
      rw [measure_biUnion_finset hfinsetDisjoint
        (fun i _hi ↦ hretainedMeasurable i)]
    _ = nu source := by simpa [hunion]

/-- Null-complement form of the preceding identity.  This is the form used
for packing-piece laws: their marked-line cells cover the law almost surely,
which is the exact measure-theoretic condition needed for arbitrary retained
measurable sources. -/
theorem sum_retainedParameterCellMass_eq_sourceMass_of_compl_null
    {n : ℕ}
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (nu : Measure
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (source : Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (cell : Fin n → Set MarkedLine)
    (hsource : MeasurableSet source)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j)))
    (hcompl : nu
      (⋃ i, frontParameterLineCell selector hmeasurable hvalid hselector
        (cell i))ᶜ = 0) :
    ∑ i, retainedParameterCellMass selector hmeasurable hvalid hselector
        nu source (cell i) = nu source := by
  classical
  let covered : Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    ⋃ i, frontParameterLineCell selector hmeasurable hvalid hselector
      (cell i)
  let retainedCell : Fin n → Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    fun i ↦ source ∩
      frontParameterLineCell selector hmeasurable hvalid hselector (cell i)
  have hretainedMeasurable : ∀ i, MeasurableSet (retainedCell i) := by
    intro i
    exact hsource.inter
      (measurableSet_frontParameterLineCell selector hmeasurable hvalid
        hselector (hcell i))
  have hretainedDisjoint :
      Pairwise (fun i j ↦ Disjoint (retainedCell i) (retainedCell j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    exact Set.disjoint_left.mp (hdisjoint hij) hzi.2 hzj.2
  have hunion : (⋃ i, retainedCell i) = source ∩ covered := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, covered, retainedCell]
    constructor
    · rintro ⟨i, hzsource, hzcell⟩
      exact ⟨hzsource, i, hzcell⟩
    · rintro ⟨hzsource, i, hzcell⟩
      exact ⟨i, hzsource, hzcell⟩
  have hfinsetDisjoint : PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin n))) retainedCell := by
    intro i _hi j _hj hij
    exact hretainedDisjoint hij
  have hcoveredMass : nu (source ∩ covered) = nu source := by
    have hdiff := measure_sdiff_null (s := source) (t := coveredᶜ) (by
      simpa [covered] using hcompl)
    simpa [sdiff_eq, compl_compl] using hdiff
  calc
    ∑ i, retainedParameterCellMass selector hmeasurable hvalid hselector
        nu source (cell i) = ∑ i ∈ (Finset.univ : Finset (Fin n)),
          nu (retainedCell i) := by
            simp [retainedParameterCellMass, retainedCell]
    _ = nu (⋃ i ∈ (Finset.univ : Finset (Fin n)), retainedCell i) := by
      rw [measure_biUnion_finset hfinsetDisjoint
        (fun i _hi ↦ hretainedMeasurable i)]
    _ = nu (source ∩ covered) := by simpa [hunion]
    _ = nu source := hcoveredMass

/-- The marked-line cells produced from a retained packing piece cover its
canonical direction--fibre law almost surely. -/
theorem markedCarrierPieceFrontParameterProbability_compl_cells_eq_zero
    {n : ℕ}
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass :
      (selectorCarrierProbability selector hmeasurable hvalid hselector :
        Measure (E4 × E4)) piece ≠ 0)
    (cell : Fin n → Set MarkedLine)
    (hcover : selectorLinesOverCarrierPiece selector piece ⊆ ⋃ i, cell i) :
    (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure
          ({theta : E4 // ‖theta‖ = 1} ×
            Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
      (⋃ i, frontParameterLineCell selector hmeasurable hvalid hselector
        (cell i))ᶜ = 0 := by
  let F := frontParameterSelectedLine selector hmeasurable hvalid hselector
  let coveredLines : Set MarkedLine := ⋃ i, cell i
  have hpreimage :
      (⋃ i, frontParameterLineCell selector hmeasurable hvalid hselector
        (cell i)) = F ⁻¹' coveredLines := by
    ext z
    simp [F, coveredLines, frontParameterLineCell]
  have hsubset : (F ⁻¹' coveredLines)ᶜ ⊆
      F ⁻¹' (selectorLinesOverCarrierPiece selector piece)ᶜ := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_preimage] at hz ⊢
    exact fun hzpiece ↦ hz (hcover hzpiece)
  have hlineNull :
      (markedCarrierPieceLineProbability selector hmeasurable hvalid
        hselector piece : Measure MarkedLine)
          (selectorLinesOverCarrierPiece selector piece)ᶜ = 0 :=
    markedCarrierPieceLineProbability_apply_compl_eq_zero selector hmeasurable
      hvalid hselector piece hpieceMeasurable hpieceCarrier hpieceMass
  have hparameterNull :
      (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure
          ({theta : E4 // ‖theta‖ = 1} ×
            Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
        (F ⁻¹' (selectorLinesOverCarrierPiece selector piece)ᶜ) = 0 := by
    rw [← Measure.map_apply
      (measurable_frontParameterSelectedLine selector hmeasurable hvalid
        hselector)
      ((measurable_selectorLinesOverCarrierPiece selector piece hmeasurable
        hpieceMeasurable).compl)]
    rw [map_frontParameterSelectedLine_markedCarrierPieceFrontParameterProbability]
    exact hlineNull
  rw [hpreimage]
  exact measure_mono_null hsubset hparameterNull

/-- Every measurable retained source has total finite-cell mass exactly equal
to its parameter mass in the packing-piece law. -/
theorem sum_packingPiece_retainedParameterCellMass_eq_sourceMass
    {n : ℕ}
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass :
      (selectorCarrierProbability selector hmeasurable hvalid hselector :
        Measure (E4 × E4)) piece ≠ 0)
    (source : Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (hsource : MeasurableSet source)
    (cell : Fin n → Set MarkedLine)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j)))
    (hcover : selectorLinesOverCarrierPiece selector piece ⊆ ⋃ i, cell i) :
    ∑ i, retainedParameterCellMass selector hmeasurable hvalid hselector
        (markedCarrierPieceFrontParameterProbability selector hmeasurable
          hvalid hselector piece) source (cell i) =
      (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece : Measure
          ({theta : E4 // ‖theta‖ = 1} ×
            Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) source := by
  apply sum_retainedParameterCellMass_eq_sourceMass_of_compl_null
    selector hmeasurable hvalid hselector
      (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece) source cell hsource hcell hdisjoint
  exact markedCarrierPieceFrontParameterProbability_compl_cells_eq_zero
    selector hmeasurable hvalid hselector piece hpieceMeasurable hpieceCarrier
      hpieceMass cell hcover

/-- Coefficient-one event readback for an actual retained source.  If the
retained parameters reaching a measurable physical target are covered by a
chosen set of marked-line cells, then their pushforward mass is paid by the
sum of the corresponding retained row masses.  No root source occurs in the
conclusion. -/
theorem map_restrict_apply_le_sum_retainedParameterCellMass
    {n : ℕ}
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (nu : Measure
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (source : Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (cell : Fin n → Set MarkedLine) (active : Finset (Fin n))
    (target : Set E4)
    (hsource : MeasurableSet source)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j)))
    (htarget : MeasurableSet target)
    (hcover :
      (frontParametrization selector hmeasurable hvalid hselector) ⁻¹' target ∩
          source ⊆
        ⋃ i : {i // i ∈ active},
          source ∩ frontParameterLineCell selector hmeasurable hvalid
            hselector (cell i.1)) :
    Measure.map
        (frontParametrization selector hmeasurable hvalid hselector)
        (nu.restrict source) target ≤
      ∑ i ∈ active,
        retainedParameterCellMass selector hmeasurable hvalid hselector
          nu source (cell i) := by
  classical
  let retainedCell : Fin n → Set
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    fun i ↦ source ∩
      frontParameterLineCell selector hmeasurable hvalid hselector (cell i)
  have hretainedMeasurable : ∀ i, MeasurableSet (retainedCell i) := by
    intro i
    exact hsource.inter
      (measurableSet_frontParameterLineCell selector hmeasurable hvalid
        hselector (hcell i))
  have hJdisjoint : PairwiseDisjoint (↑active) retainedCell := by
    intro i _hi j _hj hij
    change Disjoint (retainedCell i) (retainedCell j)
    rw [Set.disjoint_left]
    intro z hzi hzj
    exact Set.disjoint_left.mp (hdisjoint hij) hzi.2 hzj.2
  have hcoverJ :
      (frontParametrization selector hmeasurable hvalid hselector) ⁻¹' target ∩
          source ⊆ ⋃ i ∈ active, retainedCell i := by
    intro z hz
    have hz' := hcover hz
    simp only [Set.mem_iUnion] at hz' ⊢
    obtain ⟨i, hzi⟩ := hz'
    exact ⟨i.1, i.2, hzi⟩
  rw [Measure.map_apply
    (measurable_frontParametrization selector hmeasurable hvalid hselector)
    htarget]
  rw [Measure.restrict_apply
    (htarget.preimage
      (measurable_frontParametrization selector hmeasurable hvalid hselector))]
  calc
    nu ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹' target ∩
        source) ≤ nu (⋃ i ∈ active, retainedCell i) := measure_mono hcoverJ
    _ = ∑ i ∈ active, nu (retainedCell i) :=
      measure_biUnion_finset hJdisjoint
        (fun i _hi ↦ hretainedMeasurable i)
    _ = ∑ i ∈ active,
        retainedParameterCellMass selector hmeasurable hvalid hselector
          nu source (cell i) := by
      simp [retainedCell, retainedParameterCellMass]

end StickyKakeya4
