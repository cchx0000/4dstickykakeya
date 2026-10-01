import Theorems.Thm_StickyKakeya4_contact_symplectic_edge_flow_certificate_existence
import Theorems.Thm_StickyKakeya4_front_parameter_probability
import Theorems.Thm_StickyKakeya4_carrier_piece_probability
import Theorems.Thm_StickyKakeya4_wang_zakharov_finite_interface

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- Specialize the failed vector-Frostman alternative to the canonical
direction--fibre probability.  The returned ball is the first actual packet
in the coherent-concentration branch: it carries more canonical marked mass
than any prescribed finite four-dimensional Frostman allowance at the
selected exponent. -/
theorem coherentBoundary_has_canonical_concentration_packet
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
      ∀ C : ENNReal, C ≠ ⊤ →
        ∃ (x : E4) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
          C * (ENNReal.ofReal r).rpow (4 - epsilon) <
            (frontParameterProbability : Measure FrontParameterSpace)
              ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
                Metric.ball x r) := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hfailure⟩ :=
    coherentConcentrationBoundary_extracts_failed_frostman_scale
      selector hmeasurable hvalid hselector hboundary
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_⟩
  intro C hCtop
  let nu : Measure FrontParameterSpace := frontParameterProbability
  have hnu : IsProbabilityMeasure nu := by infer_instance
  simpa [nu] using hfailure nu hnu C hCtop

/-- Specialize the failed vector-Frostman alternative to the normalized law
on one retained carrier piece.  The boundary theorem quantifies over every
probability on the canonical direction--fibre space, so the carrier-piece
law is first transported there and then read back in physical space.  This
keeps the concentration ball and the later packing cover on the same piece. -/
theorem coherentBoundary_has_carrierPiece_concentration_packet
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (piece : Set (E4 × E4)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
      ∀ C : ENNReal, C ≠ ⊤ →
        ∃ (x : E4) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
          C * (ENNReal.ofReal r).rpow (4 - epsilon) <
            (markedCarrierPieceFrontProbability selector hmeasurable hvalid
              hselector piece : Measure E4) (Metric.ball x r) := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hfailure⟩ :=
    coherentConcentrationBoundary_extracts_failed_frostman_scale
      selector hmeasurable hvalid hselector hboundary
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_⟩
  intro C hCtop
  let nu : Measure FrontParameterSpace :=
    markedCarrierPieceFrontParameterProbability selector hmeasurable hvalid
      hselector piece
  have hnu : IsProbabilityMeasure nu := by infer_instance
  obtain ⟨x, r, hr, hrOne, hlarge⟩ := hfailure nu hnu C hCtop
  refine ⟨x, r, hr, hrOne, ?_⟩
  change C * (ENNReal.ofReal r).rpow (4 - epsilon) <
    (markedCarrierPieceFrontParameterProbability selector hmeasurable hvalid
      hselector piece : Measure FrontParameterSpace)
      ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
        Metric.ball x r) at hlarge
  rw [← Measure.map_apply
      (measurable_frontParametrization selector hmeasurable hvalid hselector)
      Metric.isOpen_ball.measurableSet,
    map_frontParametrization_markedCarrierPieceFrontParameterProbability]
    at hlarge
  exact hlarge

/-- The concentration packets for a fixed normalized carrier piece occur
below every prescribed positive scale.  The proof is the probability
normalization argument on the piece law itself: a violating ball with radius
at least `rho` would have mass strictly larger than one. -/
theorem coherentBoundary_has_arbitrarily_small_carrierPiece_concentration_packet
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (piece : Set (E4 × E4)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        ∃ (x : E4) (r : ℝ), 0 < r ∧ r < rho ∧
          ((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
              (ENNReal.ofReal r).rpow (4 - epsilon) <
            (markedCarrierPieceFrontProbability selector hmeasurable hvalid
              hselector piece : Measure E4) (Metric.ball x r) := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hpacket⟩ :=
    coherentBoundary_has_carrierPiece_concentration_packet
      selector hmeasurable hvalid hselector hboundary piece
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_⟩
  intro rho hrho hrhoOne
  let q : ℝ := 4 - epsilon
  have hq : 0 < q := by dsimp [q]; linarith
  let base : ENNReal := (ENNReal.ofReal rho).rpow q
  have hbase0 : base ≠ 0 := by
    exact ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hrho)
      ENNReal.ofReal_ne_top)
  have hbaseTop : base ≠ ⊤ := by
    exact ne_of_lt
      (ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
  have hCtop : base⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hbase0
  obtain ⟨x, r, hr, hrOne, hlarge⟩ := hpacket base⁻¹ hCtop
  have hrSmall : r < rho := by
    by_contra hnot
    have hrhoLe : rho ≤ r := le_of_not_gt hnot
    have hpowMono : base ≤ (ENNReal.ofReal r).rpow q := by
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hrhoLe) hq.le
    have hone : 1 ≤ base⁻¹ * (ENNReal.ofReal r).rpow q := by
      calc
        1 = base⁻¹ * base := (ENNReal.inv_mul_cancel hbase0 hbaseTop).symm
        _ ≤ base⁻¹ * (ENNReal.ofReal r).rpow q := by gcongr
    let mu : Measure E4 :=
      markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece
    have hmu : IsProbabilityMeasure mu := by infer_instance
    have hprobability : mu (Metric.ball x r) ≤ 1 := by
      calc
        mu (Metric.ball x r) ≤ mu Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := hmu.measure_univ
    have hnotLarge :
        ¬ base⁻¹ * (ENNReal.ofReal r).rpow q < mu (Metric.ball x r) :=
      not_lt_of_ge (hprobability.trans hone)
    exact hnotLarge (by simpa [mu, base, q] using hlarge)
  exact ⟨x, r, hr, hrSmall, by simpa [base, q] using hlarge⟩

/-- The canonical concentration packets occur below every prescribed positive
scale.  The normalization constant is the reciprocal of the candidate
`(4-epsilon)` mass at `rho`.  A violating ball of radius at least `rho` would
then have mass strictly larger than one, contradicting probability
normalization.  This supplies the genuinely vanishing scales required by the
finite WZ readback. -/
theorem coherentBoundary_has_arbitrarily_small_canonical_concentration_packet
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        ∃ (x : E4) (r : ℝ), 0 < r ∧ r < rho ∧
          ((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
              (ENNReal.ofReal r).rpow (4 - epsilon) <
            (frontParameterProbability : Measure FrontParameterSpace)
              ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
                Metric.ball x r) := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hpacket⟩ :=
    coherentBoundary_has_canonical_concentration_packet
      selector hmeasurable hvalid hselector hboundary
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_⟩
  intro rho hrho hrhoOne
  let q : ℝ := 4 - epsilon
  have hq : 0 < q := by dsimp [q]; linarith
  let base : ENNReal := (ENNReal.ofReal rho).rpow q
  have hbase0 : base ≠ 0 := by
    exact ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hrho)
      ENNReal.ofReal_ne_top)
  have hbaseTop : base ≠ ⊤ := by
    exact ne_of_lt
      (ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
  have hCtop : base⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hbase0
  obtain ⟨x, r, hr, hrOne, hlarge⟩ := hpacket base⁻¹ hCtop
  have hrSmall : r < rho := by
    by_contra hnot
    have hrhoLe : rho ≤ r := le_of_not_gt hnot
    have hpowMono : base ≤ (ENNReal.ofReal r).rpow q := by
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hrhoLe) hq.le
    have hone : 1 ≤ base⁻¹ * (ENNReal.ofReal r).rpow q := by
      calc
        1 = base⁻¹ * base := (ENNReal.inv_mul_cancel hbase0 hbaseTop).symm
        _ ≤ base⁻¹ * (ENNReal.ofReal r).rpow q := by gcongr
    let nu : Measure FrontParameterSpace := frontParameterProbability
    have hnu : IsProbabilityMeasure nu := by infer_instance
    have hprobability :
        nu ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
            Metric.ball x r) ≤ 1 := by
      calc
        nu ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
            Metric.ball x r) ≤ nu Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := hnu.measure_univ
    have hnotLarge :
        ¬ base⁻¹ * (ENNReal.ofReal r).rpow q <
          nu ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
            Metric.ball x r) :=
      not_lt_of_ge (hprobability.trans hone)
    exact hnotLarge (by simpa [nu, base, q] using hlarge)
  exact ⟨x, r, hr, hrSmall, by simpa [base, q] using hlarge⟩

/-- Every positive radius admits a strictly smaller dyadic WZ scale. -/
theorem exists_wz_dyadic_scale_lt {rho : ℝ} (hrho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧ delta < rho ∧ IsWZDyadicScale delta := by
  obtain ⟨level, hlevel⟩ :=
    exists_pow_lt_of_lt_one hrho (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨(2 : ℝ)⁻¹ ^ level, pow_pos (by norm_num) level, hlevel, ?_⟩
  exact ⟨level, rfl⟩

/-- A coherent boundary packet can be resolved by a dyadic WZ scale strictly
below its physical concentration radius.  Thus the later cubical source may
be constructed at `delta` while its active restriction is read back inside
the larger ball of radius `r`; no comparison of mass at two radii is used. -/
theorem coherentBoundary_has_dyadically_resolved_concentration_packet
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        ∃ (x : E4) (r delta : ℝ),
          0 < delta ∧ delta < r ∧ r < rho ∧
          IsWZDyadicScale delta ∧
          ((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
              (ENNReal.ofReal r).rpow (4 - epsilon) <
            (frontParameterProbability : Measure FrontParameterSpace)
              ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
                Metric.ball x r) := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hpacket⟩ :=
    coherentBoundary_has_arbitrarily_small_canonical_concentration_packet
      selector hmeasurable hvalid hselector hboundary
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_⟩
  intro rho hrho hrhoOne
  obtain ⟨x, r, hr, hrho', hmass⟩ := hpacket rho hrho hrhoOne
  obtain ⟨delta, hdelta, hdr, hdyadic⟩ := exists_wz_dyadic_scale_lt hr
  exact ⟨x, r, delta, hdelta, hdr, hrho', hdyadic, hmass⟩

end StickyKakeya4
