import Theorems.Thm_StickyKakeya4_contact_symplectic_edge_flow_certificate_existence

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- Intrinsic no-Wang--Zakharov output of a coherent concentration boundary.
For one exponent below four, the canonical marked direction--fibre law has a
Frostman-violating packet below every prescribed positive radius. -/
structure ShrinkingCanonicalConcentrationPackets
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_four : epsilon < 4
  packet : ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
    ∃ (x : E4) (r : ℝ), 0 < r ∧ r < rho ∧
      ((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
          (ENNReal.ofReal r).rpow (4 - epsilon) <
        (frontParameterProbability : Measure FrontParameterSpace)
          ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
            Metric.ball x r)

/-- The positive boundary certificate itself supplies shrinking canonical
packets.  The proof uses only probability normalization and monotonicity of
`rpow`; no Kakeya estimate, WZ theorem, or finite tube input is invoked. -/
theorem shrinkingCanonicalConcentrationPackets_of_coherentBoundary
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    Nonempty (ShrinkingCanonicalConcentrationPackets selector
      hmeasurable hvalid hselector) := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hfailure⟩ :=
    coherentConcentrationBoundary_extracts_failed_frostman_scale
      selector hmeasurable hvalid hselector hboundary
  refine ⟨⟨epsilon, hepsilon, hepsilonFour, ?_⟩⟩
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
  let nu : Measure FrontParameterSpace := frontParameterProbability
  have hnu : IsProbabilityMeasure nu := by infer_instance
  obtain ⟨x, r, hr, hrOne, hlarge⟩ :=
    hfailure nu hnu base⁻¹ hCtop
  have hrSmall : r < rho := by
    by_contra hnot
    have hrhoLe : rho ≤ r := le_of_not_gt hnot
    have hpowMono : base ≤ (ENNReal.ofReal r).rpow q := by
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hrhoLe) hq.le
    have hone : 1 ≤ base⁻¹ * (ENNReal.ofReal r).rpow q := by
      calc
        1 = base⁻¹ * base := (ENNReal.inv_mul_cancel hbase0 hbaseTop).symm
        _ ≤ base⁻¹ * (ENNReal.ofReal r).rpow q := by gcongr
    have hprobability :
        nu ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
            Metric.ball x r) ≤ 1 := by
      calc
        nu ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
            Metric.ball x r) ≤ nu Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := hnu.measure_univ
    exact (not_lt_of_ge (hprobability.trans hone))
      (by simpa [nu, base, q] using hlarge)
  exact ⟨x, r, hr, hrSmall, by simpa [nu, base, q] using hlarge⟩

/-- A canonical geometric schedule of requested packet radii. -/
def canonicalPacketRequestRadius (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ (n + 1)

theorem canonicalPacketRequestRadius_pos (n : ℕ) :
    0 < canonicalPacketRequestRadius n := by
  exact pow_pos (by norm_num) _

theorem canonicalPacketRequestRadius_le_one (n : ℕ) :
    canonicalPacketRequestRadius n ≤ 1 := by
  unfold canonicalPacketRequestRadius
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- Concrete countable readback used by the fresh-return construction: one
strictly smaller positive concentration packet is selected at every geometric
request scale. -/
theorem ShrinkingCanonicalConcentrationPackets.exists_geometric_packet_sequence
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (packets : ShrinkingCanonicalConcentrationPackets selector
      hmeasurable hvalid hselector) :
    ∃ center : ℕ → E4, ∃ radius : ℕ → ℝ,
      (∀ n, 0 < radius n) ∧
      (∀ n, radius n < canonicalPacketRequestRadius n) ∧
      ∀ n,
        ((ENNReal.ofReal (canonicalPacketRequestRadius n)).rpow
          (4 - packets.epsilon))⁻¹ *
            (ENNReal.ofReal (radius n)).rpow (4 - packets.epsilon) <
          (frontParameterProbability : Measure FrontParameterSpace)
            ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
              Metric.ball (center n) (radius n)) := by
  have hexists : ∀ n : ℕ, ∃ (x : E4) (r : ℝ),
      0 < r ∧ r < canonicalPacketRequestRadius n ∧
        ((ENNReal.ofReal (canonicalPacketRequestRadius n)).rpow
          (4 - packets.epsilon))⁻¹ *
            (ENNReal.ofReal r).rpow (4 - packets.epsilon) <
          (frontParameterProbability : Measure FrontParameterSpace)
            ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
              Metric.ball x r) := by
    intro n
    exact packets.packet (canonicalPacketRequestRadius n)
      (canonicalPacketRequestRadius_pos n)
      (canonicalPacketRequestRadius_le_one n)
  choose center radius hproperties using hexists
  exact ⟨center, radius,
    (fun n ↦ (hproperties n).1),
    (fun n ↦ (hproperties n).2.1),
    (fun n ↦ (hproperties n).2.2)⟩

end StickyKakeya4
