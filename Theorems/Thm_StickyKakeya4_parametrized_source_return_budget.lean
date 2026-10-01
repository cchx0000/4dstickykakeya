import Theorems.Thm_StickyKakeya4_packing_selector_to_finite_scale_sources
import Theorems.Thm_StickyKakeya4_law_level_return_budget
import Theorems.Thm_StickyKakeya4_retained_cell_return_firewall
import Theorems.Thm_StickyKakeya4_collision_time_coherent_motion

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- Fractional source restriction is transitive: restricting an already
retained source again preserves the original marked lines, affine marks,
carrier tree, and only decreases shadings and weights. -/
theorem fractionalSourceRestriction_trans {n : ℕ}
    {R S D : FiniteScaleSource n}
    (hRS : IsFractionalSourceRestriction R S)
    (hSD : IsFractionalSourceRestriction S D) :
    IsFractionalSourceRestriction R D := by
  rcases hRS with ⟨hthickRS, hlineRS, hmarkRS, htreeRS,
    hmeasR, hshadeRS, hweightRS⟩
  rcases hSD with ⟨hthickSD, hlineSD, hmarkSD, htreeSD,
    _hmeasS, hshadeSD, hweightSD⟩
  exact ⟨hthickRS.trans hthickSD, hlineRS.trans hlineSD,
    hmarkRS.trans hmarkSD, htreeRS.trans htreeSD, hmeasR,
    fun i ↦ (hshadeRS i).trans (hshadeSD i),
    fun i ↦ (hweightRS i).trans (hweightSD i)⟩

/-- Public milestone-4-to-boundary bridge.  The parameter law exposed by the
finite-scale source construction supplies the north support and cap--fibre
certificate needed by the law-level return budget.  The retained child is
then discretized by the same finite source at every sufficiently small scale:
its row masses add exactly to the child mass, and every positive row has a
literal marked parameter witness in the child. -/
theorem parametrizedCoherentSources_produce_budget_adapted_retained_source
    (selector ambient : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hsources : HasParametrizedCoherentFiniteScaleSources selector ambient
      hmeasurable hvalid hselector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (sourceEpsilon : ℝ) (hsourceEpsilon : 0 < sourceEpsilon)
    (g K : ℝ) (hg : 0 < g) (hK : 0 ≤ K) :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
    ∃ nu : Measure FrontParameterSpace,
      IsProbabilityMeasure nu ∧
      nu contactNorthParameterCapᶜ = 0 ∧
      ∃ Cfront : ENNReal, Cfront ≠ 0 ∧ Cfront ≠ ⊤ ∧
      HasFrontDirectionFibreBound selector hmeasurable hvalid hselector
        nu Cfront ∧
      ∃ (epsilon : ℝ)
        (parent child : MeasuredConditionedBoundaryPacketState nu selector
          hmeasurable hvalid hselector)
        (rho delta0 : ℝ),
        0 < epsilon ∧ epsilon < 4 ∧
        parent.source ⊆ contactNorthParameterCap ∧
        0 < rho ∧ rho ≤ parent.radius / 4 ∧ rho ≤ 1 ∧
        IsMeasuredConditionedBoundaryPacketChild parent child ∧
        child.radius < rho ∧
        nu parent.source *
            (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
              (ENNReal.ofReal child.radius).rpow (4 - epsilon)) <
          nu child.source ∧
        child.source ⊆ contactNorthParameterCap ∧
        (∀ (t E : ℝ) (outerCenter : E3),
          0 ≤ E → E ≤ K * child.radius →
          g ≤ |t - child.center (3 : Fin 4)| →
          ¬ (∀ z ∈ child.source,
            ‖northGraphEvaluation
                (selectorLine selector hmeasurable hvalid hselector z.1) t -
              outerCenter‖ ≤ E)) ∧
        0 < delta0 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
          ∃ n : ℕ, ∃ D R : FiniteScaleSource n,
            D.thickness = delta ∧
            ComesFromSelector D selector ∧
            (∀ i, (1 / 2 : ℝ) ≤ direction (D.line i) (3 : Fin 4)) ∧
            IsAdmissibleStickySource D sourceEpsilon C ∧
            C⁻¹ ≤ sourceMass D ∧ sourceMass D ≤ C ∧
            IsFractionalSourceRestriction R D ∧
            ∃ cell : Fin n → Set MarkedLine, ∃ Ccell : ENNReal,
              Ccell ≠ 0 ∧ Ccell ≠ ⊤ ∧
              R = retainedParameterFullTubeSource selector hmeasurable
                hvalid hselector nu child.source delta D.line
                  D.line_injective cell Ccell ∧
              (∀ i, MeasurableSet (cell i)) ∧
              Pairwise (fun i j ↦ Disjoint (cell i) (cell j)) ∧
              (∀ i, ∀ line ∈ cell i,
                ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
                  dist (rawFrontParam (line, t))
                    (rawFrontParam (D.line i, t)) < delta / 4) ∧
              (∑ i, retainedParameterCellMass selector hmeasurable hvalid
                  hselector nu child.source (cell i)) = nu child.source ∧
              (∀ i, 0 < retainedParameterCellMass selector hmeasurable
                    hvalid hselector nu child.source (cell i) →
                  ∃ z, z ∈ child.source ∧
                    frontParameterSelectedLine selector hmeasurable hvalid
                      hselector z ∈ cell i) ∧
              ∀ (Rloc : FiniteScaleSource n) (gain : ENNReal)
                  (tubeSlack directionSlack timeGap eta : ℝ)
                  (current : ENNReal),
                IsFractionalSourceRestriction Rloc R →
                sourceMass Rloc ≠ 0 → gain ≠ ⊤ →
                (gain + 1) * volume (sourceUnion Rloc) ≤ sourceMass Rloc →
                0 < tubeSlack → 0 < directionSlack →
                0 ≤ timeGap → 0 < eta →
                2 * ((6 * child.radius +
                      2 * (3 * (delta + tubeSlack + delta / 4))) / g) +
                    directionSlack ≤ 1 →
                ENNReal.ofReal (2 * child.radius) *
                    (Cfront *
                      (ENNReal.ofReal
                        (2 * ((6 * child.radius +
                            2 * (3 * (delta + tubeSlack + delta / 4))) / g) +
                          directionSlack)) ^ 3) ≤
                  (Ccell * (ENNReal.ofReal delta) ^ 3) * gain →
                ∃ y : E4, y ∈ sourceUnion Rloc ∧
                  |y (3 : Fin 4) - child.center (3 : Fin 4)| < g ∧
                  gain < sourceFunction Rloc y ∧
                  SourcePointCoherentCollisionTimeOrAffineThreePacketAlternative
                    Rloc y selector timeGap eta current := by
  obtain ⟨C, hC0, hCTop, _mu, _hmuProbability, _hmuSupport,
      nu, hnuProbability, _hmap, hnorth, Cfront, hCfront0,
      hCfrontTop, hfront, delta0, hdelta0, hsourcesDelta⟩ :=
    hsources sourceEpsilon hsourceEpsilon
  obtain ⟨epsilon, parent, child, rho, hepsilon, hepsilonFour,
      hparentNorth, hrho, hrhoQuarter, hrhoOne, hchild, hchildRho,
      hmassLower, hchildNorth, hnoReturn⟩ :=
    coherentBoundary_produces_budget_adapted_north_child_for_measure
      hboundary nu hnuProbability hnorth hCfrontTop hfront g K hg hK
  refine ⟨C, hC0, hCTop, nu, hnuProbability, hnorth,
    Cfront, hCfront0, hCfrontTop, hfront,
    epsilon, parent, child, rho, delta0, hepsilon, hepsilonFour,
    hparentNorth, hrho, hrhoQuarter, hrhoOne, hchild, hchildRho,
    hmassLower, hchildNorth, hnoReturn, hdelta0, ?_⟩
  intro delta hdelta hdelta0
  obtain ⟨n, D, hDdelta, hDselector, hDnorth, hDadmissible,
      hDmassLower, hDmassUpper, _hlocal, cell, Ccell,
      hCcellZero, hCcellTop, hcellMeasurable, hcellDisjoint,
      hcellApprox, haligned⟩ :=
    hsourcesDelta delta hdelta hdelta0
  obtain ⟨hR, hmassSum, hwitness⟩ :=
    haligned child.source child.source_measurable
  let R : FiniteScaleSource n :=
    retainedParameterFullTubeSource selector hmeasurable hvalid hselector
      nu child.source delta D.line D.line_injective cell Ccell
  refine ⟨n, D, R, hDdelta, hDselector, hDnorth, hDadmissible,
    hDmassLower, hDmassUpper, ?_, cell, Ccell,
    hCcellZero, hCcellTop, rfl, hcellMeasurable, hcellDisjoint,
    hcellApprox, hmassSum, hwitness, ?_⟩
  · simpa [R] using hR
  · intro Rloc gain tubeSlack directionSlack timeGap eta current hRlocR hmass0
      hgainTop hfailure htubeSlack hdirectionSlack htimeGap heta
      hradiusOne hbudget
    have hRlocD : IsFractionalSourceRestriction Rloc D :=
      fractionalSourceRestriction_trans hRlocR (by simpa [R] using hR)
    have hRlocAligned : IsFractionalSourceRestriction Rloc
        (retainedParameterFullTubeSource selector hmeasurable hvalid
          hselector nu child.source D.thickness D.line D.line_injective
            cell Ccell) := by
      rw [hDdelta]
      simpa [R] using hRlocR
    have hdeltaD : 0 < D.thickness := by simpa [hDdelta] using hdelta
    have hcellApproxD : ∀ i, ∀ line ∈ cell i,
        ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
          dist (rawFrontParam (line, t))
            (rawFrontParam (D.line i, t)) < D.thickness / 4 := by
      simpa [hDdelta] using hcellApprox
    have hradiusOneD :
        2 * ((6 * child.radius +
            2 * (3 * (D.thickness + tubeSlack + D.thickness / 4))) / g) +
          directionSlack ≤ 1 := by
      simpa [hDdelta] using hradiusOne
    have hbudgetD :
        ENNReal.ofReal (2 * child.radius) *
            (Cfront *
              (ENNReal.ofReal
                (2 * ((6 * child.radius +
                    2 * (3 * (D.thickness + tubeSlack + D.thickness / 4))) / g) +
                  directionSlack)) ^ 3) ≤
          (Ccell * (ENNReal.ofReal D.thickness) ^ 3) * gain := by
      simpa [hDdelta] using hbudget
    obtain ⟨y, hyUnion, hyNear, hyGain⟩ :=
      scaled_union_failure_has_near_child_weighted_witness
        hfront child hchildNorth D Rloc cell Ccell hCcellZero hCcellTop
        hDadmissible hRlocD hRlocAligned hmass0 hgainTop hfailure
        hcellMeasurable hcellDisjoint tubeSlack g directionSlack hdeltaD
        htubeSlack hg hdirectionSlack hcellApproxD hradiusOneD hbudgetD
    have hweightTop : ∀ i, Rloc.weight i ≠ ⊤ := by
      intro i
      exact ne_of_lt ((hRlocD.2.2.2.2.2.2 i).trans_lt
        ((hDadmissible.2.2.1 i).trans_lt ENNReal.one_lt_top))
    have hsourceZero : sourceFunction Rloc y ≠ 0 := by
      change 0 < sourceFunction Rloc y at hyUnion
      exact ne_of_gt hyUnion
    have hRlocSelector : ∀ i, Rloc.line i ∈ selector := by
      intro i
      rw [congrFun hRlocD.2.1 i]
      exact hDselector i
    have hRlocChart : ∀ i,
        direction (Rloc.line i) (3 : Fin 4) ≠ 0 := by
      intro i
      rw [congrFun hRlocD.2.1 i]
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) (hDnorth i))
    have hRlocNorth : ∀ i, (1 / 2 : ℝ) ≤
        direction (Rloc.line i) (3 : Fin 4) := by
      intro i
      rw [congrFun hRlocD.2.1 i]
      exact hDnorth i
    have hscale : 0 ≤ Rloc.thickness + eta := by
      rw [hRlocD.1]
      nlinarith [hDadmissible.1]
    refine ⟨y, hyUnion, hyNear, hyGain, ?_⟩
    have hroute :=
      sourcePoint_commonHeight_contactCycle_or_three_packet_half_removal
      hDadmissible hRlocD selector hRlocSelector hRlocChart y
      hweightTop hsourceZero timeGap eta htimeGap heta current
    exact
      sourcePointContactCycleOrThreePacket_to_coherentCollisionTime_or_affineThreePacket
        hvalid hselector hRlocNorth hscale hroute

end StickyKakeya4
