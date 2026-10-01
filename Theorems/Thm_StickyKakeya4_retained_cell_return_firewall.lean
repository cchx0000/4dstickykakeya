import Theorems.Thm_StickyKakeya4_law_level_return_budget
import Theorems.Thm_StickyKakeya4_collision_flow_overlap_witness
import Theorems.Thm_StickyKakeya4_collision_heavy_edge_decomposition
import Theorems.Thm_StickyKakeya4_front_fibre_lower_bound

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace StickyKakeya4

/-- If the representative tube of one retained parameter cell contains a
point `y`, then every actual north-chart line from that cell passes close to
the horizontal part of `y` at the common height `y₃`.  The estimate uses the
literal affine-marked cell approximation, not an unmarked carrier surrogate. -/
theorem retained_parameter_cell_common_probe_of_tube_point
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {nu : Measure FrontParameterSpace}
    {n : ℕ} (D : FiniteScaleSource n)
    (cell : Fin n → Set MarkedLine) (Ccell : ENNReal)
    (source : Set FrontParameterSpace)
    (hsourceNorth : source ⊆ contactNorthParameterCap)
    (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 < eta)
    (hcellApprox : ∀ i, ∀ line ∈ cell i,
      ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        dist (rawFrontParam (line, t))
          (rawFrontParam (D.line i, t)) < delta / 4)
    (i : Fin n) (y : E4)
    (hy : y ∈
      (retainedParameterFullTubeSource selector hmeasurable hvalid hselector
        nu source delta D.line D.line_injective cell Ccell).shading i) :
    ∀ z ∈ source,
      frontParameterSelectedLine selector hmeasurable hvalid hselector z ∈
          cell i →
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            (y (3 : Fin 4)) -
        horizontalProjection y‖ <
          3 * (delta + eta + delta / 4) := by
  intro z hzsource hzcell
  let line := selectorLine selector hmeasurable hvalid hselector z.1
  have hlineValid : IsValidLine line := hvalid line line.property
  have hhalf : (1 / 2 : ℝ) ≤ direction line (3 : Fin 4) := by
    rw [direction_selectorLine selector hmeasurable hvalid hselector z.1]
    exact contactNorthParameterCap_direction_ge_half z (hsourceNorth hzsource)
  have hlinePos : 0 < direction line (3 : Fin 4) :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hhalf
  have hyTube : y ∈ markedUnitTube (D.line i) delta := by
    simpa [retainedParameterFullTubeSource] using hy
  have hinf : Metric.infDist y (unitFront {D.line i}) ≤ delta :=
    (mem_markedUnitTube_iff (D.line i) delta y).mp hyTube
  obtain ⟨t, ht, hrepresentative⟩ :=
    exists_rawFrontParam_dist_lt_of_infDist_le (D.line i) y hinf heta
  have hactualApprox :
      dist (rawFrontParam (line, t)) (rawFrontParam (D.line i, t)) <
        delta / 4 := by
    apply hcellApprox i line
    · simpa [line, frontParameterSelectedLine] using hzcell
    · exact ht
  have hnearActual :
      dist y (rawFrontParam (line, t)) < delta + eta + delta / 4 := by
    calc
      dist y (rawFrontParam (line, t)) ≤
          dist y (rawFrontParam (D.line i, t)) +
            dist (rawFrontParam (D.line i, t))
              (rawFrontParam (line, t)) := dist_triangle _ _ _
      _ < (delta + eta) + delta / 4 := by
        exact add_lt_add hrepresentative (by simpa [dist_comm] using hactualApprox)
  have hfixed :=
    dist_fixedHeightPoint_lt_chartAmplification_mul_of_rawFrontParam_near
      line hlineValid hlinePos.ne' y t (delta + eta + delta / 4)
        hnearActual
  have hradiusNonneg : 0 ≤ delta + eta + delta / 4 := by
    positivity
  have hfixedThree :
      dist (fixedHeightPoint line (y (3 : Fin 4))) y <
        3 * (delta + eta + delta / 4) := by
    refine hfixed.trans_le ?_
    exact mul_le_mul_of_nonneg_right
      (north_chartAmplification_le_three line hhalf) hradiusNonneg
  calc
    ‖northGraphEvaluation line (y (3 : Fin 4)) -
        horizontalProjection y‖ =
        ‖horizontalProjection
          (fixedHeightPoint line (y (3 : Fin 4)) - y)‖ := by
      rw [horizontalProjection_sub,
        horizontalProjection_fixedHeightPoint line
          (y (3 : Fin 4)) hlinePos.ne']
    _ ≤ ‖fixedHeightPoint line (y (3 : Fin 4)) - y‖ :=
      norm_horizontalProjection_le _
    _ = dist (fixedHeightPoint line (y (3 : Fin 4))) y := by
      rw [dist_eq_norm]
    _ < 3 * (delta + eta + delta / 4) := hfixedThree

/-- The actual marked-line masses of all retained cells whose representative
tubes contain one point are charged together to a single ball of the marked
front.  The cells may have unrelated affine centers.  Pairwise disjointness
gives coefficient-one summation, while the endpoint-robust fibre estimate
supplies the single transverse factor `delta + eta + delta / 4` without an
interior-fibre hypothesis. -/
theorem marked_cell_mass_active_at_point_mul_tube_radius_le_front_ball
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass :
      (selectorCarrierProbability selector hmeasurable hvalid hselector :
        Measure (E4 × E4)) piece ≠ 0)
    {nu : Measure FrontParameterSpace} (source : Set FrontParameterSpace)
    {n : ℕ} (D : FiniteScaleSource n)
    (cell : Fin n → Set MarkedLine) (Ccell : ENNReal)
    (hcellMeasurable : ∀ i, MeasurableSet (cell i))
    (hcellDisjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j)))
    (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 < eta)
    (hcellApprox : ∀ i, ∀ line ∈ cell i,
      ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        dist (rawFrontParam (line, t))
          (rawFrontParam (D.line i, t)) < delta / 4)
    (y : E4)
    (houterRadiusOne :
      2 * (delta + eta + delta / 4) ≤ 1) :
    ENNReal.ofReal (delta + eta + delta / 4) *
        (∑ i ∈ sourceActiveIndicesAtPoint
          (retainedParameterFullTubeSource selector hmeasurable hvalid
            hselector nu source delta D.line D.line_injective cell Ccell) y,
          (markedCarrierPieceLineProbability selector hmeasurable hvalid
            hselector piece : Measure MarkedLine) (cell i)) ≤
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4)
          (Metric.ball y (2 * (delta + eta + delta / 4))) := by
  classical
  let R : FiniteScaleSource n :=
    retainedParameterFullTubeSource selector hmeasurable hvalid hselector
      nu source delta D.line D.line_injective cell Ccell
  let active : Finset (Fin n) := sourceActiveIndicesAtPoint R y
  let activeLines : Set MarkedLine := ⋃ i ∈ active, cell i
  let mu : Measure MarkedLine :=
    markedCarrierPieceLineProbability selector hmeasurable hvalid
      hselector piece
  have hactiveLinesMeasurable : MeasurableSet activeLines := by
    exact Finset.measurableSet_biUnion active
      (fun i _hi ↦ hcellMeasurable i)
  have hactiveDisjoint : PairwiseDisjoint (↑active) cell := by
    intro i _hi j _hj hij
    exact hcellDisjoint hij
  have hsum : (∑ i ∈ active, mu (cell i)) = mu activeLines := by
    exact (measure_biUnion_finset hactiveDisjoint
      (fun i _hi ↦ hcellMeasurable i)).symm
  change ENNReal.ofReal (delta + eta + delta / 4) *
      (∑ i ∈ active, mu (cell i)) ≤ _
  rw [hsum]
  have hcharge :=
    markedCarrierPieceLineProbability_mul_half_of_exists_crossing_le_front_ball
      selector hmeasurable hvalid hselector piece hpieceMeasurable
        hpieceCarrier hpieceMass activeLines hactiveLinesMeasurable y
          (2 * (delta + eta + delta / 4)) (by positivity)
            houterRadiusOne
          (by
            intro line hlinePiece hlineActive
            change line ∈ ⋃ i ∈ active, cell i at hlineActive
            simp only [Set.mem_iUnion] at hlineActive
            obtain ⟨i, hiActive, hlineCell⟩ := hlineActive
            have hiActive' := hiActive
            simp only [active, sourceActiveIndicesAtPoint,
              Finset.mem_filter, Finset.mem_univ, true_and] at hiActive'
            have hyTube : y ∈ markedUnitTube (D.line i) delta := by
              simpa [R, retainedParameterFullTubeSource] using hiActive'.1
            have hinf : Metric.infDist y (unitFront {D.line i}) ≤ delta :=
              (mem_markedUnitTube_iff (D.line i) delta y).mp hyTube
            obtain ⟨t, ht, hrepresentative⟩ :=
              exists_rawFrontParam_dist_lt_of_infDist_le
                (D.line i) y hinf heta
            have hactualApprox :
                dist (rawFrontParam (line, t))
                    (rawFrontParam (D.line i, t)) < delta / 4 :=
              hcellApprox i line hlineCell t ht
            have hnearActual :
                dist y (rawFrontParam (line, t)) <
                  delta + eta + delta / 4 := by
              calc
                dist y (rawFrontParam (line, t)) ≤
                    dist y (rawFrontParam (D.line i, t)) +
                      dist (rawFrontParam (D.line i, t))
                        (rawFrontParam (line, t)) := dist_triangle _ _ _
                _ < (delta + eta) + delta / 4 := by
                  exact add_lt_add hrepresentative
                    (by simpa [dist_comm] using hactualApprox)
            refine ⟨t, ht, ?_⟩
            have hhalf :
                2 * (delta + eta + delta / 4) / 2 =
                  delta + eta + delta / 4 := by ring
            simpa [hhalf, dist_comm] using hnearActual)
  have hhalf :
      2 * (delta + eta + delta / 4) / 2 =
        delta + eta + delta / 4 := by ring
  simpa [hhalf] using hcharge

/-- Source-hereditary form of the preceding physical-ball charge.  It uses
the actual mass left in `source ∩ lineCell`; no root-law mass is substituted
for a retained descendant. -/
theorem retained_cell_mass_active_at_point_mul_tube_radius_le_front_ball
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass :
      (selectorCarrierProbability selector hmeasurable hvalid hselector :
        Measure (E4 × E4)) piece ≠ 0)
    (source : Set FrontParameterSpace)
    {n : ℕ} (D : FiniteScaleSource n)
    (cell : Fin n → Set MarkedLine) (Ccell : ENNReal)
    (hcellMeasurable : ∀ i, MeasurableSet (cell i))
    (hcellDisjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j)))
    (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 < eta)
    (hcellApprox : ∀ i, ∀ line ∈ cell i,
      ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        dist (rawFrontParam (line, t))
          (rawFrontParam (D.line i, t)) < delta / 4)
    (y : E4)
    (houterRadiusOne :
      2 * (delta + eta + delta / 4) ≤ 1) :
    ENNReal.ofReal (delta + eta + delta / 4) *
        (∑ i ∈ sourceActiveIndicesAtPoint
          (retainedParameterFullTubeSource selector hmeasurable hvalid
            hselector
              (markedCarrierPieceFrontParameterProbability selector
                hmeasurable hvalid hselector piece)
              source delta D.line D.line_injective cell Ccell) y,
          retainedParameterCellMass selector hmeasurable hvalid hselector
            (markedCarrierPieceFrontParameterProbability selector hmeasurable
              hvalid hselector piece) source (cell i)) ≤
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4)
          (Metric.ball y (2 * (delta + eta + delta / 4))) := by
  let nu : Measure FrontParameterSpace :=
    markedCarrierPieceFrontParameterProbability selector hmeasurable
      hvalid hselector piece
  let R : FiniteScaleSource n :=
    retainedParameterFullTubeSource selector hmeasurable hvalid hselector
      nu source delta D.line D.line_injective cell Ccell
  let active : Finset (Fin n) := sourceActiveIndicesAtPoint R y
  have hcellBound : ∀ i,
      retainedParameterCellMass selector hmeasurable hvalid hselector
          nu source (cell i) ≤
        (markedCarrierPieceLineProbability selector hmeasurable hvalid
          hselector piece : Measure MarkedLine) (cell i) := by
    intro i
    calc
      retainedParameterCellMass selector hmeasurable hvalid hselector
          nu source (cell i) ≤
        nu (frontParameterLineCell selector hmeasurable hvalid hselector
          (cell i)) :=
        retainedParameterCellMass_le_root selector hmeasurable hvalid
          hselector nu source (cell i)
      _ = (markedCarrierPieceLineProbability selector hmeasurable hvalid
          hselector piece : Measure MarkedLine) (cell i) := by
        exact markedCarrierPieceFrontParameterProbability_frontParameterLineCell
          selector hmeasurable hvalid hselector piece (hcellMeasurable i)
  have hroot :=
    marked_cell_mass_active_at_point_mul_tube_radius_le_front_ball
      piece hpieceMeasurable hpieceCarrier hpieceMass (nu := nu) source D cell Ccell
        hcellMeasurable hcellDisjoint delta eta hdelta heta hcellApprox y
          houterRadiusOne
  change ENNReal.ofReal (delta + eta + delta / 4) *
      (∑ i ∈ active,
        retainedParameterCellMass selector hmeasurable hvalid hselector
          nu source (cell i)) ≤ _
  calc
    ENNReal.ofReal (delta + eta + delta / 4) *
        (∑ i ∈ active,
          retainedParameterCellMass selector hmeasurable hvalid hselector
            nu source (cell i)) ≤
      ENNReal.ofReal (delta + eta + delta / 4) *
        (∑ i ∈ active,
          (markedCarrierPieceLineProbability selector hmeasurable hvalid
            hselector piece : Measure MarkedLine) (cell i)) := by
        gcongr with i hi
        exact hcellBound i
    _ ≤ (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4)
          (Metric.ball y (2 * (delta + eta + delta / 4))) := by
      simpa [nu, R, active] using hroot

/-- A positive retained row through a physical point has two genuine common
probes: the packet-center probe and the collision-height probe.  The public
cap--fibre certificate therefore gives an explicit upper bound for that
row's actual retained mass. -/
theorem retained_parameter_cell_mass_le_of_tube_point_and_height_separation
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {nu : Measure FrontParameterSpace} {Cfront : ENNReal}
    (hfront : HasFrontDirectionFibreBound selector hmeasurable hvalid
      hselector nu Cfront)
    (child : MeasuredConditionedBoundaryPacketState nu selector
      hmeasurable hvalid hselector)
    (hchildNorth : child.source ⊆ contactNorthParameterCap)
    {n : ℕ} (D : FiniteScaleSource n)
    (cell : Fin n → Set MarkedLine) (Ccell : ENNReal)
    (delta tubeSlack g directionSlack : ℝ)
    (hdelta : 0 < delta) (htubeSlack : 0 < tubeSlack)
    (hg : 0 < g) (hdirectionSlack : 0 < directionSlack)
    (hcellApprox : ∀ i, ∀ line ∈ cell i,
      ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        dist (rawFrontParam (line, t))
          (rawFrontParam (D.line i, t)) < delta / 4)
    (i : Fin n) (y : E4)
    (hy : y ∈
      (retainedParameterFullTubeSource selector hmeasurable hvalid hselector
        nu child.source delta D.line D.line_injective cell Ccell).shading i)
    (hcellMass : 0 < retainedParameterCellMass selector hmeasurable hvalid
      hselector nu child.source (cell i))
    (hsep : g ≤ |y (3 : Fin 4) - child.center (3 : Fin 4)|)
    (hradiusOne :
      2 * ((6 * child.radius +
          2 * (3 * (delta + tubeSlack + delta / 4))) / g) +
        directionSlack ≤ 1) :
    retainedParameterCellMass selector hmeasurable hvalid hselector
        nu child.source (cell i) ≤
      ENNReal.ofReal (2 * child.radius) *
        (Cfront *
          (ENNReal.ofReal
            (2 * ((6 * child.radius +
                2 * (3 * (delta + tubeSlack + delta / 4))) / g) +
              directionSlack)) ^ 3) := by
  let cellSource : Set FrontParameterSpace :=
    child.source ∩
      frontParameterLineCell selector hmeasurable hvalid hselector (cell i)
  obtain ⟨referenceParameter, hrefSource, hrefCell⟩ :=
    retainedParameterCellMass_pos_has_witness selector hmeasurable hvalid
      hselector nu child.source (cell i) hcellMass
  let reference : MarkedLine :=
    selectorLine selector hmeasurable hvalid hselector referenceParameter.1
  have href : reference ∈ selector :=
    (selectorLine selector hmeasurable hvalid hselector
      referenceParameter.1).property
  have hsourcePos : ∀ z ∈ cellSource,
      0 < direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4) := by
    intro z hz
    have hhalf : (1 / 2 : ℝ) ≤ direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4) := by
      rw [direction_selectorLine selector hmeasurable hvalid hselector z.1]
      exact contactNorthParameterCap_direction_ge_half z
        (hchildNorth hz.1)
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le hhalf
  have hrefPos : 0 < direction reference (3 : Fin 4) := by
    have hhalf : (1 / 2 : ℝ) ≤ direction reference (3 : Fin 4) := by
      dsimp [reference]
      rw [direction_selectorLine selector hmeasurable hvalid hselector
        referenceParameter.1]
      exact contactNorthParameterCap_direction_ge_half referenceParameter
        (hchildNorth hrefSource)
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le hhalf
  have hfirst : ∀ z ∈ cellSource,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            (child.center (3 : Fin 4)) -
        northGraphEvaluation reference (child.center (3 : Fin 4))‖ ≤
          6 * child.radius := by
    intro z hz
    exact le_of_lt
      (child.source_pair_common_probe_of_north hchildNorth z
        referenceParameter hz.1 hrefSource)
  have hprobe :=
    retained_parameter_cell_common_probe_of_tube_point D cell Ccell
      child.source hchildNorth delta tubeSlack hdelta htubeSlack
        hcellApprox i y hy
  have hsecond : ∀ z ∈ cellSource,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            (y (3 : Fin 4)) -
        northGraphEvaluation reference (y (3 : Fin 4))‖ ≤
          2 * (3 * (delta + tubeSlack + delta / 4)) := by
    intro z hz
    let u := northGraphEvaluation
      (selectorLine selector hmeasurable hvalid hselector z.1)
        (y (3 : Fin 4))
    let v := northGraphEvaluation reference (y (3 : Fin 4))
    let c := horizontalProjection y
    have hu : ‖u - c‖ < 3 * (delta + tubeSlack + delta / 4) := by
      exact hprobe z hz.1 hz.2
    have hv : ‖v - c‖ < 3 * (delta + tubeSlack + delta / 4) := by
      exact hprobe referenceParameter hrefSource hrefCell
    apply le_of_lt
    calc
      ‖u - v‖ = ‖(u - c) + (c - v)‖ := by congr 1 <;> abel
      _ ≤ ‖u - c‖ + ‖c - v‖ := norm_add_le _ _
      _ = ‖u - c‖ + ‖v - c‖ := by rw [norm_sub_rev c v]
      _ < 3 * (delta + tubeSlack + delta / 4) +
          3 * (delta + tubeSlack + delta / 4) := add_lt_add hu hv
      _ = 2 * (3 * (delta + tubeSlack + delta / 4)) := by ring
  have hsourceBall : cellSource ⊆
      (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
        Metric.ball child.center child.radius := by
    intro z hz
    exact child.source_subset_ball hz.1
  have hbound := hfront.source_le_of_two_probe_and_ball
    cellSource reference href hsourcePos hrefPos
      (child.center (3 : Fin 4)) (y (3 : Fin 4))
      (6 * child.radius) (2 * (3 * (delta + tubeSlack + delta / 4)))
      g directionSlack hfirst hsecond child.center child.radius hsourceBall
      (mul_nonneg (by norm_num) child.radius_pos.le)
      (mul_nonneg (by norm_num) (by positivity)) hg hsep
      hdirectionSlack hradiusOne child.radius_pos.le
  simpa [cellSource, retainedParameterCellMass] using hbound

/-- All retained parameter cells meeting one separated physical outer point
may be charged together, with coefficient one and with no factor equal to the
number of active rows.  Disjointness of the marked cells identifies the sum
of their actual retained masses with the measure of their union.  The union
has the packet-center probe and the common outer probe, so the public
cap--fibre certificate applies once to the whole union.  This is the local
weighted vector-center Carleson estimate needed before summing distinct outer
centers. -/
theorem sum_active_retained_parameter_cell_mass_le_of_common_outer_point
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {nu : Measure FrontParameterSpace} {Cfront : ENNReal}
    (hfront : HasFrontDirectionFibreBound selector hmeasurable hvalid
      hselector nu Cfront)
    (child : MeasuredConditionedBoundaryPacketState nu selector
      hmeasurable hvalid hselector)
    (hchildNorth : child.source ⊆ contactNorthParameterCap)
    {n : ℕ} (D : FiniteScaleSource n)
    (cell : Fin n → Set MarkedLine) (Ccell : ENNReal)
    (hcellMeasurable : ∀ i, MeasurableSet (cell i))
    (hcellDisjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j)))
    (delta tubeSlack g directionSlack : ℝ)
    (hdelta : 0 < delta) (htubeSlack : 0 < tubeSlack)
    (hg : 0 < g) (hdirectionSlack : 0 < directionSlack)
    (hcellApprox : ∀ i, ∀ line ∈ cell i,
      ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        dist (rawFrontParam (line, t))
          (rawFrontParam (D.line i, t)) < delta / 4)
    (y : E4)
    (hsep : g ≤ |y (3 : Fin 4) - child.center (3 : Fin 4)|)
    (hradiusOne :
      2 * ((6 * child.radius +
          2 * (3 * (delta + tubeSlack + delta / 4))) / g) +
        directionSlack ≤ 1) :
    (∑ i ∈ sourceActiveIndicesAtPoint
        (retainedParameterFullTubeSource selector hmeasurable hvalid
          hselector nu child.source delta D.line D.line_injective cell Ccell) y,
      retainedParameterCellMass selector hmeasurable hvalid hselector
        nu child.source (cell i)) ≤
      ENNReal.ofReal (2 * child.radius) *
        (Cfront *
          (ENNReal.ofReal
            (2 * ((6 * child.radius +
                2 * (3 * (delta + tubeSlack + delta / 4))) / g) +
              directionSlack)) ^ 3) := by
  classical
  let R : FiniteScaleSource n :=
    retainedParameterFullTubeSource selector hmeasurable hvalid hselector
      nu child.source delta D.line D.line_injective cell Ccell
  let active : Finset (Fin n) := sourceActiveIndicesAtPoint R y
  let activeSource : Set FrontParameterSpace :=
    ⋃ i ∈ active,
      child.source ∩
        frontParameterLineCell selector hmeasurable hvalid hselector (cell i)
  let retainedCell : Fin n → Set FrontParameterSpace := fun i ↦
    child.source ∩
      frontParameterLineCell selector hmeasurable hvalid hselector (cell i)
  have hretainedMeasurable : ∀ i, MeasurableSet (retainedCell i) := by
    intro i
    exact child.source_measurable.inter
      (measurableSet_frontParameterLineCell selector hmeasurable hvalid
        hselector (hcellMeasurable i))
  have hretainedDisjoint : PairwiseDisjoint (↑active) retainedCell := by
    intro i _hi j _hj hij
    change Disjoint (retainedCell i) (retainedCell j)
    rw [Set.disjoint_left]
    intro z hzi hzj
    exact Set.disjoint_left.mp (hcellDisjoint hij) hzi.2 hzj.2
  have hsumMeasure :
      (∑ i ∈ active,
        retainedParameterCellMass selector hmeasurable hvalid hselector
          nu child.source (cell i)) = nu activeSource := by
    calc
      (∑ i ∈ active,
          retainedParameterCellMass selector hmeasurable hvalid hselector
            nu child.source (cell i)) =
          ∑ i ∈ active, nu (retainedCell i) := by
            simp [retainedCell, retainedParameterCellMass]
      _ = nu (⋃ i ∈ active, retainedCell i) :=
        (measure_biUnion_finset hretainedDisjoint
          (fun i _hi ↦ hretainedMeasurable i)).symm
      _ = nu activeSource := by rfl
  change (∑ i ∈ active,
      retainedParameterCellMass selector hmeasurable hvalid hselector
        nu child.source (cell i)) ≤ _
  rw [hsumMeasure]
  by_cases hactiveZero : nu activeSource = 0
  · simp [hactiveZero]
  have hactiveNonempty : activeSource.Nonempty :=
    nonempty_of_measure_ne_zero hactiveZero
  obtain ⟨referenceParameter, hrefActive⟩ := hactiveNonempty
  have activeSource_witness : ∀ z ∈ activeSource,
      ∃ i ∈ active, z ∈ child.source ∧
        frontParameterSelectedLine selector hmeasurable hvalid hselector z ∈
          cell i := by
    intro z hz
    change z ∈ ⋃ i ∈ active,
      child.source ∩
        frontParameterLineCell selector hmeasurable hvalid hselector
          (cell i) at hz
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      frontParameterLineCell] at hz
    obtain ⟨i, hi, hzSource, hzCell⟩ := hz
    exact ⟨i, hi, hzSource, hzCell⟩
  obtain ⟨referenceIndex, hrefIndexActive, hrefSource, hrefCell⟩ :=
    activeSource_witness referenceParameter hrefActive
  let reference : MarkedLine :=
    selectorLine selector hmeasurable hvalid hselector referenceParameter.1
  have href : reference ∈ selector :=
    (selectorLine selector hmeasurable hvalid hselector
      referenceParameter.1).property
  have hsourcePos : ∀ z ∈ activeSource,
      0 < direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4) := by
    intro z hz
    obtain ⟨_i, _hi, hzSource, _hzCell⟩ := activeSource_witness z hz
    have hhalf : (1 / 2 : ℝ) ≤ direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4) := by
      rw [direction_selectorLine selector hmeasurable hvalid hselector z.1]
      exact contactNorthParameterCap_direction_ge_half z
        (hchildNorth hzSource)
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le hhalf
  have hrefPos : 0 < direction reference (3 : Fin 4) := by
    have hhalf : (1 / 2 : ℝ) ≤ direction reference (3 : Fin 4) := by
      dsimp [reference]
      rw [direction_selectorLine selector hmeasurable hvalid hselector
        referenceParameter.1]
      exact contactNorthParameterCap_direction_ge_half referenceParameter
        (hchildNorth hrefSource)
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le hhalf
  have hfirst : ∀ z ∈ activeSource,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            (child.center (3 : Fin 4)) -
        northGraphEvaluation reference (child.center (3 : Fin 4))‖ ≤
          6 * child.radius := by
    intro z hz
    obtain ⟨_i, _hi, hzSource, _hzCell⟩ := activeSource_witness z hz
    exact le_of_lt
      (child.source_pair_common_probe_of_north hchildNorth z
        referenceParameter hzSource hrefSource)
  have common_outer_probe : ∀ z ∈ activeSource,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            (y (3 : Fin 4)) - horizontalProjection y‖ <
        3 * (delta + tubeSlack + delta / 4) := by
    intro z hz
    obtain ⟨i, hiActive, hzSource, hzCell⟩ := activeSource_witness z hz
    have hiActive' := hiActive
    simp only [active, sourceActiveIndicesAtPoint, Finset.mem_filter,
      Finset.mem_univ, true_and] at hiActive'
    apply retained_parameter_cell_common_probe_of_tube_point
      D cell Ccell child.source hchildNorth delta tubeSlack hdelta
        htubeSlack hcellApprox i y
    · simpa [R] using hiActive'.1
    · exact hzSource
    · exact hzCell
  have hrefOuter :
      ‖northGraphEvaluation reference (y (3 : Fin 4)) -
          horizontalProjection y‖ <
        3 * (delta + tubeSlack + delta / 4) :=
    common_outer_probe referenceParameter hrefActive
  have hsecond : ∀ z ∈ activeSource,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            (y (3 : Fin 4)) -
        northGraphEvaluation reference (y (3 : Fin 4))‖ ≤
          2 * (3 * (delta + tubeSlack + delta / 4)) := by
    intro z hz
    let u := northGraphEvaluation
      (selectorLine selector hmeasurable hvalid hselector z.1)
        (y (3 : Fin 4))
    let v := northGraphEvaluation reference (y (3 : Fin 4))
    let c := horizontalProjection y
    have hu : ‖u - c‖ < 3 * (delta + tubeSlack + delta / 4) := by
      exact common_outer_probe z hz
    have hv : ‖v - c‖ < 3 * (delta + tubeSlack + delta / 4) := by
      exact hrefOuter
    apply le_of_lt
    calc
      ‖u - v‖ = ‖(u - c) + (c - v)‖ := by congr 1 <;> abel
      _ ≤ ‖u - c‖ + ‖c - v‖ := norm_add_le _ _
      _ = ‖u - c‖ + ‖v - c‖ := by rw [norm_sub_rev c v]
      _ < 3 * (delta + tubeSlack + delta / 4) +
          3 * (delta + tubeSlack + delta / 4) := add_lt_add hu hv
      _ = 2 * (3 * (delta + tubeSlack + delta / 4)) := by ring
  have hsourceBall : activeSource ⊆
      (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
        Metric.ball child.center child.radius := by
    intro z hz
    obtain ⟨_i, _hi, hzSource, _hzCell⟩ := activeSource_witness z hz
    exact child.source_subset_ball hzSource
  exact hfront.source_le_of_two_probe_and_ball
    activeSource reference href hsourcePos hrefPos
      (child.center (3 : Fin 4)) (y (3 : Fin 4))
      (6 * child.radius) (2 * (3 * (delta + tubeSlack + delta / 4)))
      g directionSlack hfirst hsecond child.center child.radius hsourceBall
      (mul_nonneg (by norm_num) child.radius_pos.le)
      (mul_nonneg (by norm_num) (by positivity)) hg hsep
      hdirectionSlack hradiusOne child.radius_pos.le

/-- Exact conversion between the unnormalized retained parameter mass active
at one physical point and the normalized finite-source multiplicity there.
The factor is precisely the single source normalization
`Ccell * delta^3`; hence the preceding coefficient-one outer-point estimate
can be combined directly with collision multiplicity lower bounds. -/
theorem sum_active_retained_parameter_cell_mass_eq_normalization_mul_sourceFunction
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (nu : Measure FrontParameterSpace) (source : Set FrontParameterSpace)
    {n : ℕ} (D : FiniteScaleSource n)
    (cell : Fin n → Set MarkedLine) (Ccell : ENNReal)
    (hCcellZero : Ccell ≠ 0) (hCcellTop : Ccell ≠ ⊤)
    (delta : ℝ) (hdelta : 0 < delta) (y : E4) :
    (∑ i ∈ sourceActiveIndicesAtPoint
        (retainedParameterFullTubeSource selector hmeasurable hvalid
          hselector nu source delta D.line D.line_injective cell Ccell) y,
      retainedParameterCellMass selector hmeasurable hvalid hselector
        nu source (cell i)) =
      (Ccell * (ENNReal.ofReal delta) ^ 3) *
        sourceFunction
          (retainedParameterFullTubeSource selector hmeasurable hvalid
            hselector nu source delta D.line D.line_injective cell Ccell) y := by
  classical
  let q : Fin n → ENNReal := fun i ↦
    retainedParameterCellMass selector hmeasurable hvalid hselector
      nu source (cell i)
  let R : FiniteScaleSource n :=
    retainedParameterFullTubeSource selector hmeasurable hvalid hselector
      nu source delta D.line D.line_injective cell Ccell
  let active : Finset (Fin n) := sourceActiveIndicesAtPoint R y
  let scale : ENNReal := (ENNReal.ofReal delta) ^ 3
  have hscaleZero : scale ≠ 0 :=
    pow_ne_zero 3 (ENNReal.ofReal_ne_zero_iff.mpr hdelta)
  have hscaleTop : scale ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hdenZero : Ccell * scale ≠ 0 :=
    mul_ne_zero hCcellZero hscaleZero
  have hdenTop : Ccell * scale ≠ ⊤ :=
    ENNReal.mul_ne_top hCcellTop hscaleTop
  have hnormalized :
      (∑ i ∈ active, normalizedPartitionWeight Ccell delta (q i)) =
        (∑ i ∈ active, q i) / (Ccell * scale) := by
    unfold normalizedPartitionWeight
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul active]
  have hsourceFunction : sourceFunction R y =
      ∑ i ∈ active, normalizedPartitionWeight Ccell delta (q i) := by
    rw [sourceFunction_eq_sum_activeWeights]
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  change (∑ i ∈ active, q i) =
    (Ccell * scale) * sourceFunction R y
  rw [hsourceFunction, hnormalized]
  rw [div_eq_mul_inv]
  calc
    (∑ i ∈ active, q i) =
        (∑ i ∈ active, q i) * 1 := by rw [mul_one]
    _ = (∑ i ∈ active, q i) *
          ((Ccell * scale) * (Ccell * scale)⁻¹) := by
        rw [ENNReal.mul_inv_cancel hdenZero hdenTop]
    _ = (Ccell * scale) *
          ((∑ i ∈ active, q i) * (Ccell * scale)⁻¹) := by
        ac_rfl

/-- Pointwise multiplicity form of the marked-front ball charge.  This is
the collision-ledger interface: the actual normalized multiplicity of the
retained source is paid by one ball of the physical front, with exactly the
single source normalization and the single affine-fibre factor. -/
theorem normalized_sourceFunction_mul_tube_radius_le_front_ball
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass :
      (selectorCarrierProbability selector hmeasurable hvalid hselector :
        Measure (E4 × E4)) piece ≠ 0)
    (source : Set FrontParameterSpace)
    {n : ℕ} (D : FiniteScaleSource n)
    (cell : Fin n → Set MarkedLine) (Ccell : ENNReal)
    (hCcellZero : Ccell ≠ 0) (hCcellTop : Ccell ≠ ⊤)
    (hcellMeasurable : ∀ i, MeasurableSet (cell i))
    (hcellDisjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j)))
    (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 < eta)
    (hcellApprox : ∀ i, ∀ line ∈ cell i,
      ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        dist (rawFrontParam (line, t))
          (rawFrontParam (D.line i, t)) < delta / 4)
    (y : E4)
    (houterRadiusOne :
      2 * (delta + eta + delta / 4) ≤ 1) :
    ENNReal.ofReal (delta + eta + delta / 4) *
        ((Ccell * (ENNReal.ofReal delta) ^ 3) *
          sourceFunction
            (retainedParameterFullTubeSource selector hmeasurable hvalid
              hselector
                (markedCarrierPieceFrontParameterProbability selector
                  hmeasurable hvalid hselector piece)
                source delta D.line D.line_injective cell Ccell) y) ≤
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4)
          (Metric.ball y (2 * (delta + eta + delta / 4))) := by
  let nu : Measure FrontParameterSpace :=
    markedCarrierPieceFrontParameterProbability selector hmeasurable
      hvalid hselector piece
  rw [← sum_active_retained_parameter_cell_mass_eq_normalization_mul_sourceFunction
    nu source D cell Ccell hCcellZero hCcellTop delta hdelta y]
  exact retained_cell_mass_active_at_point_mul_tube_radius_le_front_ball
    piece hpieceMeasurable hpieceCarrier hpieceMass source D cell Ccell
      hcellMeasurable hcellDisjoint delta eta hdelta heta hcellApprox y
        houterRadiusOne

/-- Fully source-hereditary physical-ball charge.  Arbitrary measurable
shading and weight restrictions only lower pointwise multiplicity, so the
same marked-front ball pays every retained descendant with the original
normalization and no new constant. -/
theorem normalized_restricted_sourceFunction_mul_tube_radius_le_front_ball
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass :
      (selectorCarrierProbability selector hmeasurable hvalid hselector :
        Measure (E4 × E4)) piece ≠ 0)
    (source : Set FrontParameterSpace)
    {n : ℕ} (D Rloc : FiniteScaleSource n)
    (cell : Fin n → Set MarkedLine) (Ccell : ENNReal)
    (hCcellZero : Ccell ≠ 0) (hCcellTop : Ccell ≠ ⊤)
    (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 < eta)
    (hRloc : IsFractionalSourceRestriction Rloc
      (retainedParameterFullTubeSource selector hmeasurable hvalid
        hselector
          (markedCarrierPieceFrontParameterProbability selector hmeasurable
            hvalid hselector piece)
          source delta D.line D.line_injective cell Ccell))
    (hcellMeasurable : ∀ i, MeasurableSet (cell i))
    (hcellDisjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j)))
    (hcellApprox : ∀ i, ∀ line ∈ cell i,
      ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        dist (rawFrontParam (line, t))
          (rawFrontParam (D.line i, t)) < delta / 4)
    (y : E4)
    (houterRadiusOne :
      2 * (delta + eta + delta / 4) ≤ 1) :
    ENNReal.ofReal (delta + eta + delta / 4) *
        ((Ccell * (ENNReal.ofReal delta) ^ 3) * sourceFunction Rloc y) ≤
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4)
          (Metric.ball y (2 * (delta + eta + delta / 4))) := by
  let R : FiniteScaleSource n :=
    retainedParameterFullTubeSource selector hmeasurable hvalid hselector
      (markedCarrierPieceFrontParameterProbability selector hmeasurable
        hvalid hselector piece)
      source delta D.line D.line_injective cell Ccell
  calc
    ENNReal.ofReal (delta + eta + delta / 4) *
        ((Ccell * (ENNReal.ofReal delta) ^ 3) * sourceFunction Rloc y) ≤
      ENNReal.ofReal (delta + eta + delta / 4) *
        ((Ccell * (ENNReal.ofReal delta) ^ 3) * sourceFunction R y) := by
          gcongr
          exact sourceFunction_le_of_fractionalSourceRestriction hRloc y
    _ ≤ (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4)
          (Metric.ball y (2 * (delta + eta + delta / 4))) := by
      simpa [R] using
        (normalized_sourceFunction_mul_tube_radius_le_front_ball
          piece hpieceMeasurable hpieceCarrier hpieceMass source D cell Ccell
            hCcellZero hCcellTop hcellMeasurable hcellDisjoint delta eta
              hdelta heta hcellApprox y houterRadiusOne)

/-- Collision-facing form of the local vector-center estimate.  It bounds
the true weighted multiplicity at the common outer point after restoring the
single finite-source normalization factor. -/
theorem normalized_sourceFunction_le_of_common_outer_point
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {nu : Measure FrontParameterSpace} {Cfront : ENNReal}
    (hfront : HasFrontDirectionFibreBound selector hmeasurable hvalid
      hselector nu Cfront)
    (child : MeasuredConditionedBoundaryPacketState nu selector
      hmeasurable hvalid hselector)
    (hchildNorth : child.source ⊆ contactNorthParameterCap)
    {n : ℕ} (D : FiniteScaleSource n)
    (cell : Fin n → Set MarkedLine) (Ccell : ENNReal)
    (hCcellZero : Ccell ≠ 0) (hCcellTop : Ccell ≠ ⊤)
    (hcellMeasurable : ∀ i, MeasurableSet (cell i))
    (hcellDisjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j)))
    (delta tubeSlack g directionSlack : ℝ)
    (hdelta : 0 < delta) (htubeSlack : 0 < tubeSlack)
    (hg : 0 < g) (hdirectionSlack : 0 < directionSlack)
    (hcellApprox : ∀ i, ∀ line ∈ cell i,
      ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        dist (rawFrontParam (line, t))
          (rawFrontParam (D.line i, t)) < delta / 4)
    (y : E4)
    (hsep : g ≤ |y (3 : Fin 4) - child.center (3 : Fin 4)|)
    (hradiusOne :
      2 * ((6 * child.radius +
          2 * (3 * (delta + tubeSlack + delta / 4))) / g) +
        directionSlack ≤ 1) :
    (Ccell * (ENNReal.ofReal delta) ^ 3) *
        sourceFunction
          (retainedParameterFullTubeSource selector hmeasurable hvalid
            hselector nu child.source delta D.line D.line_injective
              cell Ccell) y ≤
      ENNReal.ofReal (2 * child.radius) *
        (Cfront *
          (ENNReal.ofReal
            (2 * ((6 * child.radius +
                2 * (3 * (delta + tubeSlack + delta / 4))) / g) +
              directionSlack)) ^ 3) := by
  rw [← sum_active_retained_parameter_cell_mass_eq_normalization_mul_sourceFunction
    nu child.source D cell Ccell hCcellZero hCcellTop delta hdelta y]
  exact sum_active_retained_parameter_cell_mass_le_of_common_outer_point
    hfront child hchildNorth D cell Ccell hcellMeasurable hcellDisjoint
      delta tubeSlack g directionSlack hdelta htubeSlack hg hdirectionSlack
      hcellApprox y hsep hradiusOne

/-- The same outer-point estimate is hereditary under an arbitrary fractional
shading/weight restriction of the aligned retained source.  This is the form
consumed by the localized collision source produced by a bad physical ball. -/
theorem normalized_restricted_sourceFunction_le_of_common_outer_point
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {nu : Measure FrontParameterSpace} {Cfront : ENNReal}
    (hfront : HasFrontDirectionFibreBound selector hmeasurable hvalid
      hselector nu Cfront)
    (child : MeasuredConditionedBoundaryPacketState nu selector
      hmeasurable hvalid hselector)
    (hchildNorth : child.source ⊆ contactNorthParameterCap)
    {n : ℕ} (D Rloc : FiniteScaleSource n)
    (cell : Fin n → Set MarkedLine) (Ccell : ENNReal)
    (hCcellZero : Ccell ≠ 0) (hCcellTop : Ccell ≠ ⊤)
    (hRloc : IsFractionalSourceRestriction Rloc
      (retainedParameterFullTubeSource selector hmeasurable hvalid
        hselector nu child.source D.thickness D.line D.line_injective
          cell Ccell))
    (hcellMeasurable : ∀ i, MeasurableSet (cell i))
    (hcellDisjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j)))
    (tubeSlack g directionSlack : ℝ)
    (hdelta : 0 < D.thickness) (htubeSlack : 0 < tubeSlack)
    (hg : 0 < g) (hdirectionSlack : 0 < directionSlack)
    (hcellApprox : ∀ i, ∀ line ∈ cell i,
      ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        dist (rawFrontParam (line, t))
          (rawFrontParam (D.line i, t)) < D.thickness / 4)
    (y : E4)
    (hsep : g ≤ |y (3 : Fin 4) - child.center (3 : Fin 4)|)
    (hradiusOne :
      2 * ((6 * child.radius +
          2 * (3 * (D.thickness + tubeSlack + D.thickness / 4))) / g) +
        directionSlack ≤ 1) :
    (Ccell * (ENNReal.ofReal D.thickness) ^ 3) *
        sourceFunction Rloc y ≤
      ENNReal.ofReal (2 * child.radius) *
        (Cfront *
          (ENNReal.ofReal
            (2 * ((6 * child.radius +
                2 * (3 * (D.thickness + tubeSlack + D.thickness / 4))) / g) +
              directionSlack)) ^ 3) := by
  calc
    (Ccell * (ENNReal.ofReal D.thickness) ^ 3) *
        sourceFunction Rloc y ≤
      (Ccell * (ENNReal.ofReal D.thickness) ^ 3) *
        sourceFunction
          (retainedParameterFullTubeSource selector hmeasurable hvalid
            hselector nu child.source D.thickness D.line D.line_injective
              cell Ccell) y := by
        gcongr
        exact sourceFunction_le_of_fractionalSourceRestriction hRloc y
    _ ≤ ENNReal.ofReal (2 * child.radius) *
        (Cfront *
          (ENNReal.ofReal
            (2 * ((6 * child.radius +
                2 * (3 * (D.thickness + tubeSlack + D.thickness / 4))) / g) +
              directionSlack)) ^ 3) :=
      normalized_sourceFunction_le_of_common_outer_point
        hfront child hchildNorth D cell Ccell hCcellZero hCcellTop
          hcellMeasurable hcellDisjoint D.thickness tubeSlack g
          directionSlack hdelta htubeSlack hg hdirectionSlack hcellApprox
          y hsep hradiusOne

/-- A localized scaled-union failure cannot live entirely in a height slab
separated from its retained boundary packet once its multiplicity gain
exceeds the coefficient-one cap--fibre budget.  The lower multiplicity comes
from the collision ledger, while the upper multiplicity is the preceding
weighted common-outer-point estimate. -/
theorem no_scaled_union_failure_on_separated_retained_slab
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {nu : Measure FrontParameterSpace} {Cfront : ENNReal}
    (hfront : HasFrontDirectionFibreBound selector hmeasurable hvalid
      hselector nu Cfront)
    (child : MeasuredConditionedBoundaryPacketState nu selector
      hmeasurable hvalid hselector)
    (hchildNorth : child.source ⊆ contactNorthParameterCap)
    {n : ℕ} (D Rloc : FiniteScaleSource n)
    (cell : Fin n → Set MarkedLine) (Ccell : ENNReal)
    (hCcellZero : Ccell ≠ 0) (hCcellTop : Ccell ≠ ⊤)
    {epsilon : ℝ} {C gain : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hRlocD : IsFractionalSourceRestriction Rloc D)
    (hRlocAligned : IsFractionalSourceRestriction Rloc
      (retainedParameterFullTubeSource selector hmeasurable hvalid
        hselector nu child.source D.thickness D.line D.line_injective
          cell Ccell))
    (hmass0 : sourceMass Rloc ≠ 0) (hgainTop : gain ≠ ⊤)
    (hfailure : (gain + 1) * volume (sourceUnion Rloc) ≤
      sourceMass Rloc)
    (hcellMeasurable : ∀ i, MeasurableSet (cell i))
    (hcellDisjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j)))
    (tubeSlack g directionSlack : ℝ)
    (hdelta : 0 < D.thickness) (htubeSlack : 0 < tubeSlack)
    (hg : 0 < g) (hdirectionSlack : 0 < directionSlack)
    (hcellApprox : ∀ i, ∀ line ∈ cell i,
      ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        dist (rawFrontParam (line, t))
          (rawFrontParam (D.line i, t)) < D.thickness / 4)
    (hseparated : ∀ y ∈ sourceUnion Rloc,
      g ≤ |y (3 : Fin 4) - child.center (3 : Fin 4)|)
    (hradiusOne :
      2 * ((6 * child.radius +
          2 * (3 * (D.thickness + tubeSlack + D.thickness / 4))) / g) +
        directionSlack ≤ 1)
    (hbudget :
      ENNReal.ofReal (2 * child.radius) *
          (Cfront *
            (ENNReal.ofReal
              (2 * ((6 * child.radius +
                  2 * (3 * (D.thickness + tubeSlack + D.thickness / 4))) / g) +
                directionSlack)) ^ 3) ≤
        (Ccell * (ENNReal.ofReal D.thickness) ^ 3) * gain) : False := by
  obtain ⟨y, hyUnion, hyGain⟩ :=
    scaled_union_failure_has_pointwise_multiplicity_gt_gain
      hD hRlocD hmass0 hgainTop hfailure
  have hupper :=
    normalized_restricted_sourceFunction_le_of_common_outer_point
      hfront child hchildNorth D Rloc cell Ccell hCcellZero hCcellTop
        hRlocAligned hcellMeasurable hcellDisjoint tubeSlack g
        directionSlack hdelta htubeSlack hg hdirectionSlack hcellApprox
        y (hseparated y hyUnion) hradiusOne
  have hscaleZero : (ENNReal.ofReal D.thickness) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (ENNReal.ofReal_ne_zero_iff.mpr hdelta)
  have hscaleTop : (ENNReal.ofReal D.thickness) ^ 3 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hdenZero : Ccell * (ENNReal.ofReal D.thickness) ^ 3 ≠ 0 :=
    mul_ne_zero hCcellZero hscaleZero
  have hdenTop : Ccell * (ENNReal.ofReal D.thickness) ^ 3 ≠ ⊤ :=
    ENNReal.mul_ne_top hCcellTop hscaleTop
  have hlower :
      (Ccell * (ENNReal.ofReal D.thickness) ^ 3) * gain <
        (Ccell * (ENNReal.ofReal D.thickness) ^ 3) *
          sourceFunction Rloc y :=
    by
      simpa [mul_comm] using
        (ENNReal.mul_lt_mul_left hdenZero hdenTop hyGain)
  exact (not_lt_of_ge hupper) (hbudget.trans_lt hlower)

/-- Every scaled-union failure in an aligned retained source has a genuine
weighted high-multiplicity point inside the prescribed height window around
the child packet.  Thus the separated-return firewall does not merely rule
out a prelocalized bad slab: it sends the actual collision witness into the
near-height continuation branch. -/
theorem scaled_union_failure_has_near_child_weighted_witness
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {nu : Measure FrontParameterSpace} {Cfront : ENNReal}
    (hfront : HasFrontDirectionFibreBound selector hmeasurable hvalid
      hselector nu Cfront)
    (child : MeasuredConditionedBoundaryPacketState nu selector
      hmeasurable hvalid hselector)
    (hchildNorth : child.source ⊆ contactNorthParameterCap)
    {n : ℕ} (D Rloc : FiniteScaleSource n)
    (cell : Fin n → Set MarkedLine) (Ccell : ENNReal)
    (hCcellZero : Ccell ≠ 0) (hCcellTop : Ccell ≠ ⊤)
    {epsilon : ℝ} {C gain : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hRlocD : IsFractionalSourceRestriction Rloc D)
    (hRlocAligned : IsFractionalSourceRestriction Rloc
      (retainedParameterFullTubeSource selector hmeasurable hvalid
        hselector nu child.source D.thickness D.line D.line_injective
          cell Ccell))
    (hmass0 : sourceMass Rloc ≠ 0) (hgainTop : gain ≠ ⊤)
    (hfailure : (gain + 1) * volume (sourceUnion Rloc) ≤
      sourceMass Rloc)
    (hcellMeasurable : ∀ i, MeasurableSet (cell i))
    (hcellDisjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j)))
    (tubeSlack g directionSlack : ℝ)
    (hdelta : 0 < D.thickness) (htubeSlack : 0 < tubeSlack)
    (hg : 0 < g) (hdirectionSlack : 0 < directionSlack)
    (hcellApprox : ∀ i, ∀ line ∈ cell i,
      ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        dist (rawFrontParam (line, t))
          (rawFrontParam (D.line i, t)) < D.thickness / 4)
    (hradiusOne :
      2 * ((6 * child.radius +
          2 * (3 * (D.thickness + tubeSlack + D.thickness / 4))) / g) +
        directionSlack ≤ 1)
    (hbudget :
      ENNReal.ofReal (2 * child.radius) *
          (Cfront *
            (ENNReal.ofReal
              (2 * ((6 * child.radius +
                  2 * (3 * (D.thickness + tubeSlack + D.thickness / 4))) / g) +
                directionSlack)) ^ 3) ≤
        (Ccell * (ENNReal.ofReal D.thickness) ^ 3) * gain) :
    ∃ y : E4, y ∈ sourceUnion Rloc ∧
      |y (3 : Fin 4) - child.center (3 : Fin 4)| < g ∧
      gain < sourceFunction Rloc y := by
  obtain ⟨y, hyUnion, hyGain⟩ :=
    scaled_union_failure_has_pointwise_multiplicity_gt_gain
      hD hRlocD hmass0 hgainTop hfailure
  refine ⟨y, hyUnion, ?_, hyGain⟩
  by_contra hnear
  have hsep : g ≤ |y (3 : Fin 4) - child.center (3 : Fin 4)| :=
    not_lt.mp hnear
  have hupper :=
    normalized_restricted_sourceFunction_le_of_common_outer_point
      hfront child hchildNorth D Rloc cell Ccell hCcellZero hCcellTop
        hRlocAligned hcellMeasurable hcellDisjoint tubeSlack g
        directionSlack hdelta htubeSlack hg hdirectionSlack hcellApprox
        y hsep hradiusOne
  have hscaleZero : (ENNReal.ofReal D.thickness) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (ENNReal.ofReal_ne_zero_iff.mpr hdelta)
  have hscaleTop : (ENNReal.ofReal D.thickness) ^ 3 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hdenZero : Ccell * (ENNReal.ofReal D.thickness) ^ 3 ≠ 0 :=
    mul_ne_zero hCcellZero hscaleZero
  have hdenTop : Ccell * (ENNReal.ofReal D.thickness) ^ 3 ≠ ⊤ :=
    ENNReal.mul_ne_top hCcellTop hscaleTop
  have hlower :
      (Ccell * (ENNReal.ofReal D.thickness) ^ 3) * gain <
        (Ccell * (ENNReal.ofReal D.thickness) ^ 3) *
          sourceFunction Rloc y := by
    simpa [mul_comm] using
      (ENNReal.mul_lt_mul_left hdenZero hdenTop hyGain)
  exact (not_lt_of_ge hupper) (hbudget.trans_lt hlower)

end StickyKakeya4
