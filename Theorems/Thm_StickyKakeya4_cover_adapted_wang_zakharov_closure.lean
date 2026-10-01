import Theorems.Thm_StickyKakeya4_contact_symplectic_edge_flow_certificate_existence
import Theorems.Thm_StickyKakeya4_wang_zakharov_finite_interface
import Theorems.Thm_StickyKakeya4_wz_carrier_pruning
import Theorems.Thm_StickyKakeya4_wz_readback_bookkeeping
import Theorems.Thm_StickyKakeya4_wz_boundary_concentration_packet
import Theorems.Thm_StickyKakeya4_wz_common_slab_localization

open Filter MeasureTheory Set
open scoped ENNReal Topology Pointwise RealInnerProductSpace

namespace StickyKakeya4

/-!
The external Wang--Zakharov theorem and the internal cover-adapted reduction
are kept as two separately typed interfaces.  This prevents the published
finite estimate from being conflated with the manuscript's source
construction and Hausdorff-cover readback.
-/

/-- Exact finite packet at one fixed Hausdorff exponent gap.  The packet
contains a literal finite WZ input, its physical cover target, and the strict
coefficient absorption needed for the terminal comparison. -/
def HasCoverAdaptedWZContradictionPacketsAtExponent
    (ambient selector : Set MarkedLine) (chi : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta →
  ∀ A : ENNReal, A ≠ 0 → A ≠ ⊤ →
  ∀ deltaZero : ℝ, 0 < deltaZero →
    ∃ (n : ℕ) (D : FiniteScaleSource n) (target : Set E4)
      (upperConstant : ENNReal),
      0 < D.thickness ∧
      D.thickness ≤ deltaZero ∧
      IsWangZakharovNativeFiniteInput D eta ∧
      (⋃ i, D.shading i) ⊆ target ∧
      upperConstant *
          (ENNReal.ofReal D.thickness).rpow (chi / 2) < A⁻¹ ∧
      coveringNumber target D.thickness ≤
        upperConstant *
          (ENNReal.ofReal D.thickness).rpow (-4 + chi)

/-- Cover-adapted packets with the exponent gap selected from the hypothetical
sub-four-dimensional ambient front. -/
def HasCoverAdaptedWZContradictionPackets
    (ambient selector : Set MarkedLine) : Prop :=
  dimH (unitFront ambient) < 4 →
    ∃ chi : ℝ, 0 < chi ∧ chi < 4 ∧
      HasCoverAdaptedWZContradictionPacketsAtExponent ambient selector chi

/-- Positive concentration data extracted from the boundary branch.  For the
canonical marked direction--fibre law, every finite Frostman coefficient is
violated by a physical ball, and at least half of that ball mass survives on
directions whose selected marked fibre is active in the same ball. -/
def HasCanonicalSelectorFrontConcentration
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) : Prop :=
  ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
    ∀ C : ENNReal, C ≠ ⊤ →
      ∃ (x : E4) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
        C * (ENNReal.ofReal r).rpow (4 - epsilon) <
          (selectorFrontProbability selector hmeasurable hvalid hselector :
            Measure E4) (Metric.ball x r) ∧
        (selectorFrontProbability selector hmeasurable hvalid hselector :
            Measure E4) (Metric.ball x r) / 2 ≤
          (normSphereProbability :
            Measure {theta : E4 // ‖theta‖ = 1})
            {theta |
              (selectorFrontProbability selector hmeasurable hvalid hselector :
                  Measure E4) (Metric.ball x r) / 2 ≤
                (fibreIntervalProbability :
                  Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
                  (markedLineSetFibreSet
                    ((selectorLine selector hmeasurable hvalid hselector theta :
                      selector) : MarkedLine) (Metric.ball x r))}

/-- The negative boundary alternative has a concrete positive readback in the
canonical physical front probability. -/
theorem hasCanonicalSelectorFrontConcentration_of_boundary
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    HasCanonicalSelectorFrontConcentration selector hmeasurable hvalid
      hselector := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hball⟩ :=
    coherentConcentrationBoundary_extracts_selectorFrontProbability_ball
      selector hmeasurable hvalid hselector hboundary
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_⟩
  intro C hCtop
  obtain ⟨x, r, hr, hrOne, hlarge⟩ := hball C hCtop
  refine ⟨x, r, hr, hrOne, hlarge, ?_⟩
  exact selector_active_directions_half_front_mass
    selector hmeasurable hvalid hselector (Metric.ball x r)
      Metric.isOpen_ball.measurableSet

/-- Strengthened positive boundary data: concentration packets occur below
every prescribed positive radius, while the same ball still supplies the
half-mass active-direction layer. -/
def HasArbitrarilySmallCanonicalSelectorFrontConcentration
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) : Prop :=
  ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
    ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      ∃ (x : E4) (r : ℝ), 0 < r ∧ r < rho ∧
        ((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal r).rpow (4 - epsilon) <
          (selectorFrontProbability selector hmeasurable hvalid hselector :
            Measure E4) (Metric.ball x r) ∧
        (selectorFrontProbability selector hmeasurable hvalid hselector :
            Measure E4) (Metric.ball x r) / 2 ≤
          (normSphereProbability :
            Measure {theta : E4 // ‖theta‖ = 1})
            {theta |
              (selectorFrontProbability selector hmeasurable hvalid hselector :
                  Measure E4) (Metric.ball x r) / 2 ≤
                (fibreIntervalProbability :
                  Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
                  (markedLineSetFibreSet
                    ((selectorLine selector hmeasurable hvalid hselector theta :
                      selector) : MarkedLine) (Metric.ball x r))}

theorem hasArbitrarilySmallCanonicalSelectorFrontConcentration_of_boundary
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    HasArbitrarilySmallCanonicalSelectorFrontConcentration selector
      hmeasurable hvalid hselector := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hpacket⟩ :=
    coherentBoundary_has_arbitrarily_small_canonical_concentration_packet
      selector hmeasurable hvalid hselector hboundary
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_⟩
  intro rho hrho hrhoOne
  obtain ⟨x, r, hr, hrSmall, hlarge⟩ := hpacket rho hrho hrhoOne
  have hphysical :
      (selectorFrontProbability selector hmeasurable hvalid hselector :
          Measure E4) (Metric.ball x r) =
        (frontParameterProbability : Measure FrontParameterSpace)
          ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
            Metric.ball x r) := by
    rw [selectorFrontProbability, ProbabilityMeasure.toMeasure_map]
    exact Measure.map_apply
      (measurable_frontParametrization selector hmeasurable hvalid hselector)
      Metric.isOpen_ball.measurableSet
  refine ⟨x, r, hr, hrSmall, ?_, ?_⟩
  · rwa [hphysical]
  · exact selector_active_directions_half_front_mass
      selector hmeasurable hvalid hselector (Metric.ball x r)
        Metric.isOpen_ball.measurableSet

/-- Arbitrarily small concentration packets with an explicitly smaller dyadic
cell scale.  This is the scale-resolved positive input to carrier pruning. -/
def HasDyadicallyResolvedCanonicalSelectorFrontConcentration
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) : Prop :=
  ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
    ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      ∃ (x : E4) (r delta : ℝ),
        0 < delta ∧ delta < r ∧ r < rho ∧
        IsWZDyadicScale delta ∧
        ((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal r).rpow (4 - epsilon) <
          (selectorFrontProbability selector hmeasurable hvalid hselector :
            Measure E4) (Metric.ball x r) ∧
        (selectorFrontProbability selector hmeasurable hvalid hselector :
            Measure E4) (Metric.ball x r) / 2 ≤
          (normSphereProbability :
            Measure {theta : E4 // ‖theta‖ = 1})
            {theta |
              (selectorFrontProbability selector hmeasurable hvalid hselector :
                  Measure E4) (Metric.ball x r) / 2 ≤
                (fibreIntervalProbability :
                  Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
                  (markedLineSetFibreSet
                    ((selectorLine selector hmeasurable hvalid hselector theta :
                      selector) : MarkedLine) (Metric.ball x r))}

theorem hasDyadicallyResolvedCanonicalSelectorFrontConcentration_of_boundary
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    HasDyadicallyResolvedCanonicalSelectorFrontConcentration selector
      hmeasurable hvalid hselector := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hpacket⟩ :=
    coherentBoundary_has_dyadically_resolved_concentration_packet
      selector hmeasurable hvalid hselector hboundary
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_⟩
  intro rho hrho hrhoOne
  obtain ⟨x, r, delta, hdelta, hdeltaR, hrSmall, hdyadic, hlarge⟩ :=
    hpacket rho hrho hrhoOne
  have hphysical :
      (selectorFrontProbability selector hmeasurable hvalid hselector :
          Measure E4) (Metric.ball x r) =
        (frontParameterProbability : Measure FrontParameterSpace)
          ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
            Metric.ball x r) := by
    rw [selectorFrontProbability, ProbabilityMeasure.toMeasure_map]
    exact Measure.map_apply
      (measurable_frontParametrization selector hmeasurable hvalid hselector)
      Metric.isOpen_ball.measurableSet
  refine ⟨x, r, delta, hdelta, hdeltaR, hrSmall, hdyadic, ?_, ?_⟩
  · rwa [hphysical]
  · exact selector_active_directions_half_front_mass
      selector hmeasurable hvalid hselector (Metric.ball x r)
        Metric.isOpen_ball.measurableSet

/-- A fixed finite coefficient times the positive power of the two-scale
mesh tends to zero.  The cutoff is uniform for every smaller positive mesh. -/
theorem exists_const_mul_two_scale_rpow_threshold
    {eta : ℝ} (heta : 0 < eta)
    (C B : ENNReal) (hCtop : C ≠ ⊤) (hB : 0 < B) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaZero →
        C * (ENNReal.ofReal (2 * delta)).rpow eta ≤ B := by
  have htwo :
      Tendsto (fun delta : ℝ => 2 * delta) (𝓝 0) (𝓝 0) := by
    change Tendsto ((fun _ : ℝ => (2 : ℝ)) * id) (𝓝 0) (𝓝 0)
    simpa only [Pi.mul_apply, id_eq, mul_zero] using
      ((continuous_const.mul continuous_id).continuousAt.tendsto :
        Tendsto ((fun _ : ℝ => (2 : ℝ)) * id) (𝓝 0) (𝓝 (2 * 0)))
  have hofReal :
      Tendsto (fun r : ℝ => ENNReal.ofReal r) (𝓝 0) (𝓝 0) := by
    simpa using (ENNReal.continuous_ofReal.tendsto 0)
  have hlimit :
      Tendsto (fun delta : ℝ =>
          C * (ENNReal.ofReal (2 * delta)).rpow eta)
        (𝓝[>] 0) (𝓝 0) :=
    ((ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hCtop heta).comp
      (hofReal.comp htwo)).mono_left inf_le_left
  have hsmall :
      ∀ᶠ delta : ℝ in 𝓝[>] 0,
        C * (ENNReal.ofReal (2 * delta)).rpow eta < B :=
    (tendsto_order.1 hlimit).2 _ hB
  have hrange : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT (by norm_num)
  obtain ⟨deltaZero, hsmallZero, hdeltaZero, hdeltaZeroOne⟩ :=
    (hsmall.and hrange).exists
  refine ⟨deltaZero, hdeltaZero, hdeltaZeroOne, ?_⟩
  intro delta hdelta hdeltaLe
  have hpowMono :
      (ENNReal.ofReal (2 * delta)).rpow eta ≤
        (ENNReal.ofReal (2 * deltaZero)).rpow eta := by
    apply ENNReal.rpow_le_rpow
    · exact ENNReal.ofReal_le_ofReal (by linarith)
    · exact heta.le
  exact (mul_le_mul_right hpowMono C).trans hsmallZero.le

/-- Strict version of the two-scale coefficient cutoff.  This is kept
separate from the non-strict normalization lemma because the terminal WZ
comparison needs a genuinely strict coefficient gap. -/
theorem exists_const_mul_two_scale_rpow_strict_threshold
    {eta : ℝ} (heta : 0 < eta)
    (C B : ENNReal) (hCtop : C ≠ ⊤) (hB : 0 < B) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaZero →
        C * (ENNReal.ofReal (2 * delta)).rpow eta < B := by
  have htwo :
      Tendsto (fun delta : ℝ => 2 * delta) (nhds 0) (nhds 0) := by
    change Tendsto ((fun _ : ℝ => (2 : ℝ)) * id) (nhds 0) (nhds 0)
    simpa only [Pi.mul_apply, id_eq, mul_zero] using
      ((continuous_const.mul continuous_id).continuousAt.tendsto :
        Tendsto ((fun _ : ℝ => (2 : ℝ)) * id) (nhds 0) (nhds (2 * 0)))
  have hofReal :
      Tendsto (fun r : ℝ => ENNReal.ofReal r) (nhds 0) (nhds 0) := by
    simpa using (ENNReal.continuous_ofReal.tendsto 0)
  have hlimit :
      Tendsto (fun delta : ℝ =>
          C * (ENNReal.ofReal (2 * delta)).rpow eta)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    ((ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hCtop heta).comp
      (hofReal.comp htwo)).mono_left inf_le_left
  have hsmall :
      ∀ᶠ delta : ℝ in nhdsWithin 0 (Set.Ioi 0),
        C * (ENNReal.ofReal (2 * delta)).rpow eta < B :=
    (tendsto_order.1 hlimit).2 _ hB
  have hrange : Set.Ioc (0 : ℝ) 1 ∈ nhdsWithin 0 (Set.Ioi 0) :=
    Ioc_mem_nhdsGT (by norm_num)
  obtain ⟨deltaZero, hsmallZero, hdeltaZero, hdeltaZeroOne⟩ :=
    (hsmall.and hrange).exists
  refine ⟨deltaZero, hdeltaZero, hdeltaZeroOne, ?_⟩
  intro delta hdelta hdeltaLe
  have hpowMono :
      (ENNReal.ofReal (2 * delta)).rpow eta ≤
        (ENNReal.ofReal (2 * deltaZero)).rpow eta := by
    apply ENNReal.rpow_le_rpow
    · exact ENNReal.ofReal_le_ofReal (by linarith)
    · exact heta.le
  exact (mul_le_mul_right hpowMono C).trans_lt hsmallZero

/-- A fixed convex-Wolff coefficient with loss `beta` is absorbed by any
strictly larger WZ loss exponent `eta`, uniformly below one positive scale.
This is the exact coefficient conversion used after the John-ellipsoid
direction count. -/
theorem exists_convex_wolff_coefficient_absorption_threshold
    {beta eta : ℝ} (hgap : beta < eta)
    (Ccw : ENNReal) (hCcwTop : Ccw ≠ ⊤) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaZero →
        Ccw * (ENNReal.ofReal delta).rpow (-beta) ≤
          (ENNReal.ofReal delta).rpow (-eta) := by
  have hpower : 0 < eta - beta := sub_pos.mpr hgap
  obtain ⟨deltaZero, hdeltaZero, hdeltaZeroOne, hsmall⟩ :=
    exists_const_mul_two_scale_rpow_threshold
      hpower Ccw 1 hCcwTop (by norm_num)
  refine ⟨deltaZero, hdeltaZero, hdeltaZeroOne, ?_⟩
  intro delta hdelta hdeltaSmall
  have hhalfSmall : delta / 2 ≤ deltaZero :=
    (div_le_self hdelta.le (by norm_num)).trans hdeltaSmall
  have hcoeff :
      Ccw * (ENNReal.ofReal delta).rpow (eta - beta) ≤ 1 := by
    have h := hsmall (delta / 2) (by positivity) hhalfSmall
    simpa only [mul_div_cancel₀ delta (by norm_num : (2 : ℝ) ≠ 0)] using h
  have hbaseZero : ENNReal.ofReal delta ≠ 0 := by positivity
  have hbaseTop : ENNReal.ofReal delta ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrpow :
      (ENNReal.ofReal delta).rpow (eta - beta) *
          (ENNReal.ofReal delta).rpow (-eta) =
        (ENNReal.ofReal delta).rpow (-beta) := by
    calc
      (ENNReal.ofReal delta).rpow (eta - beta) *
          (ENNReal.ofReal delta).rpow (-eta) =
        (ENNReal.ofReal delta).rpow ((eta - beta) + (-eta)) :=
          (ENNReal.rpow_add (eta - beta) (-eta) hbaseZero hbaseTop).symm
      _ = (ENNReal.ofReal delta).rpow (-beta) := by
        congr 1
        ring
  calc
    Ccw * (ENNReal.ofReal delta).rpow (-beta) =
        (Ccw * (ENNReal.ofReal delta).rpow (eta - beta)) *
          (ENNReal.ofReal delta).rpow (-eta) := by
      rw [mul_assoc, hrpow]
    _ ≤ 1 * (ENNReal.ofReal delta).rpow (-eta) := by
      gcongr
    _ = (ENNReal.ofReal delta).rpow (-eta) := one_mul _

/-- A single finite net of the fixed radius-five ball scales and translates
to a uniform cover of every radius-`5 * delta` ball by radius-`delta` balls.
The cardinality of the net is independent of the centre and of `delta`; this
is the finite-dimensional doubling constant needed for target inflation. -/
theorem exists_e4_uniform_five_ball_cover :
    ∃ net : Finset E4,
      ∀ (x : E4) (delta : ℝ), 0 < delta →
        Metric.ball x (5 * delta) ⊆
          ⋃ c ∈ (net : Set E4), Metric.ball (x + delta • c) delta := by
  classical
  let fixedBall : Set E4 := Metric.closedBall 0 5
  have hfixedCompact : IsCompact fixedBall := by
    simpa [fixedBall] using (isCompact_closedBall (0 : E4) 5)
  have hfixedCover : fixedBall ⊆
      ⋃ z : {z // z ∈ fixedBall}, Metric.ball (z : E4) 1 := by
    intro y hy
    simp only [Set.mem_iUnion]
    exact ⟨⟨y, hy⟩, Metric.mem_ball_self (by norm_num)⟩
  obtain ⟨indices, hindices⟩ := hfixedCompact.elim_finite_subcover
    (fun z : {z // z ∈ fixedBall} => Metric.ball (z : E4) 1)
    (fun _ => Metric.isOpen_ball) hfixedCover
  let inclusion : {z // z ∈ fixedBall} ↪ E4 :=
    ⟨fun z => (z : E4), Subtype.val_injective⟩
  let net : Finset E4 := indices.map inclusion
  refine ⟨net, ?_⟩
  intro x delta hdelta y hy
  let z : E4 := delta⁻¹ • (y - x)
  have hzNorm : ‖z‖ < 5 := by
    have hy' : ‖y - x‖ < 5 * delta := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
    dsimp [z]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdelta)]
    have hmul := mul_lt_mul_of_pos_left hy' (inv_pos.mpr hdelta)
    calc
      delta⁻¹ * ‖y - x‖ < delta⁻¹ * (5 * delta) := hmul
      _ = 5 := by field_simp [hdelta.ne']
  have hzFixed : z ∈ fixedBall := by
    change dist z 0 ≤ 5
    simpa [dist_zero_right] using hzNorm.le
  have hzCovered := hindices hzFixed
  simp only [Set.mem_iUnion] at hzCovered
  obtain ⟨q, hqIndex, hzq⟩ := hzCovered
  have hqNet : (q : E4) ∈ net := by
    dsimp [net]
    exact Finset.mem_map.mpr ⟨q, hqIndex, rfl⟩
  simp only [Set.mem_iUnion]
  refine ⟨(q : E4), ⟨hqNet, ?_⟩⟩
  rw [Metric.mem_ball] at hzq ⊢
  have hyScale : y = x + delta • z := by
    dsimp [z]
    rw [smul_smul]
    have hscalar : delta * delta⁻¹ = (1 : ℝ) :=
      mul_inv_cancel₀ hdelta.ne'
    rw [hscalar, one_smul, add_sub_cancel]
  rw [hyScale, dist_eq_norm]
  have hdiff :
      (x + delta • z) - (x + delta • (q : E4)) =
        delta • (z - (q : E4)) := by module
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hdelta]
  have hscaled :=
    mul_lt_mul_of_pos_left (by simpa [dist_eq_norm] using hzq) hdelta
  nlinarith

/-- The fixed net above gives a centre- and scale-independent covering-number
bound for a radius-`5 * delta` ball when it is read at radius `delta`. -/
theorem exists_e4_uniform_five_ball_covering_number :
    ∃ Q : ENNReal, Q ≠ ⊤ ∧
      ∀ (x : E4) (delta : ℝ), 0 < delta →
        coveringNumber (Metric.ball x (5 * delta)) delta ≤ Q := by
  classical
  obtain ⟨net, hnet⟩ := exists_e4_uniform_five_ball_cover
  refine ⟨(net.card : ENNReal), ENNReal.natCast_ne_top net.card, ?_⟩
  intro x delta hdelta
  let centers : Finset E4 :=
    Finset.image (fun c : E4 => x + delta • c) net
  have hcentersCard : centers.card ≤ net.card := by
    dsimp [centers]
    exact Finset.card_image_le
  have hcover : coversAtRadius (Metric.ball x (5 * delta)) delta centers := by
    intro y hy
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hnet x delta hdelta hy)
    obtain ⟨hcNet, hyc⟩ := Set.mem_iUnion.mp hc
    apply Set.mem_iUnion.mpr
    refine ⟨x + delta • c, Set.mem_iUnion.mpr ⟨?_, hyc⟩⟩
    dsimp [centers]
    exact Finset.mem_image.mpr ⟨c, hcNet, rfl⟩
  calc
    coveringNumber (Metric.ball x (5 * delta)) delta ≤
        (centers.card : ENNReal) :=
      coveringNumber_le_card_of_coversAtRadius
        (Metric.ball x (5 * delta)) delta centers hcover
    _ ≤ (net.card : ENNReal) := by exact_mod_cast hcentersCard

/-- Inflating an arbitrary target by one radius-`delta` ball costs only a
fixed four-dimensional doubling constant when the target itself is covered
at radius `4 * delta`.  The added `1` is exactly the endpoint loss in
extracting a finite witness from the infimum defining `coveringNumber`. -/
theorem exists_e4_uniform_inflated_target_covering_bound :
    ∃ Q : ENNReal, Q ≠ ⊤ ∧
      ∀ (target : Set E4) (M : ENNReal) (delta : ℝ),
        0 < delta → M ≠ ⊤ →
        coveringNumber target (4 * delta) ≤ M →
        coveringNumber
            (⋃ y ∈ target, Metric.ball y delta) delta ≤
          Q * (M + 1) := by
  classical
  obtain ⟨net, hnet⟩ := exists_e4_uniform_five_ball_cover
  refine ⟨(net.card : ENNReal), ENNReal.natCast_ne_top net.card, ?_⟩
  intro target M delta hdelta hMTop htarget
  obtain ⟨coarse, hcoarse, hcoarseCard⟩ :=
    coveringNumber_le_extract_finset_cover
      target (4 * delta) hMTop htarget
  let pairs : Finset (E4 × E4) := coarse.product net
  let centers : Finset E4 :=
    Finset.image (fun p : E4 × E4 => p.1 + delta • p.2) pairs
  have hcentersCardNat : centers.card ≤ coarse.card * net.card := by
    calc
      centers.card ≤ pairs.card := by
        dsimp [centers]
        exact Finset.card_image_le
      _ = coarse.card * net.card := by simp [pairs]
  have hcentersCard : (centers.card : ENNReal) ≤
      (coarse.card : ENNReal) * (net.card : ENNReal) := by
    exact_mod_cast hcentersCardNat
  have hinflatedCover : coversAtRadius
      (⋃ y ∈ target, Metric.ball y delta) delta centers := by
    intro z hz
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hyTarget, hzy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hcoarse hyTarget)
    obtain ⟨haCoarse, hya⟩ := Set.mem_iUnion.mp ha
    have hza : z ∈ Metric.ball a (5 * delta) := by
      rw [Metric.mem_ball] at hzy hya ⊢
      calc
        dist z a ≤ dist z y + dist y a := dist_triangle z y a
        _ < delta + 4 * delta := add_lt_add hzy hya
        _ = 5 * delta := by ring
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hnet a delta hdelta hza)
    obtain ⟨hcNet, hzc⟩ := Set.mem_iUnion.mp hc
    apply Set.mem_iUnion.mpr
    refine ⟨a + delta • c, Set.mem_iUnion.mpr ⟨?_, hzc⟩⟩
    dsimp [centers]
    apply Finset.mem_image.mpr
    refine ⟨(a, c), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨haCoarse, hcNet⟩
  calc
    coveringNumber (⋃ y ∈ target, Metric.ball y delta) delta ≤
        (centers.card : ENNReal) :=
      coveringNumber_le_card_of_coversAtRadius
        (⋃ y ∈ target, Metric.ball y delta) delta centers hinflatedCover
    _ ≤ (coarse.card : ENNReal) * (net.card : ENNReal) := hcentersCard
    _ = (net.card : ENNReal) * (coarse.card : ENNReal) := mul_comm _ _
    _ ≤ (net.card : ENNReal) * (M + 1) := by
      gcongr

/-- Repackage the preceding fixed-count estimate in the exact power-law form
required by `HasCoverAdaptedWZContradictionPacketsAtExponent`.  No estimate is
lost here: the compensating positive power is put into `upperConstant` and
cancels the requested negative power exactly. -/
theorem inflated_target_covering_bound_as_power
    (target : Set E4) (Q M : ENNReal) (delta chi : ℝ)
    (hdelta : 0 < delta)
    (hbound : coveringNumber
        (⋃ y ∈ target, Metric.ball y delta) delta ≤ Q * (M + 1)) :
    let upperConstant :=
      Q * (M + 1) * (ENNReal.ofReal delta).rpow (4 - chi)
    coveringNumber (⋃ y ∈ target, Metric.ball y delta) delta ≤
      upperConstant * (ENNReal.ofReal delta).rpow (-4 + chi) := by
  dsimp only
  let x : ENNReal := ENNReal.ofReal delta
  have hx0 : x ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hdelta
  have hxtop : x ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcancel :
      x.rpow (4 - chi) * x.rpow (-4 + chi) = 1 := by
    calc
      x.rpow (4 - chi) * x.rpow (-4 + chi) =
          x.rpow ((4 - chi) + (-4 + chi)) :=
        (ENNReal.rpow_add (4 - chi) (-4 + chi) hx0 hxtop).symm
      _ = 1 := by
        have hzero : (4 - chi) + (-4 + chi) = 0 := by ring
        rw [hzero]
        simp
  calc
    coveringNumber (⋃ y ∈ target, Metric.ball y delta) delta ≤
        Q * (M + 1) := hbound
    _ = (Q * (M + 1) * x.rpow (4 - chi)) *
          x.rpow (-4 + chi) := by
      rw [mul_assoc, hcancel, mul_one]

/-- A unit-cost Hausdorff layer is already sufficient for the terminal
coefficient gap.  The layer estimate controls the `M` contribution after
rescaling from `delta / 2` to `delta`; the extra witness-cardinality unit is
absorbed by the positive power `delta^(chi/2)`. -/
theorem exists_inflated_target_coefficient_gap_threshold
    (Q A : ENNReal) (hQTop : Q ≠ ⊤) (hAZero : A ≠ 0) (hATop : A ≠ ⊤)
    (d chi : ℝ) (hd : 0 < d) (hchi : 0 < chi) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
      ∀ (delta : ℝ) (M : ENNReal),
        0 < delta → delta ≤ deltaZero →
        M * (ENNReal.ofReal (delta / 2)).rpow d < 1 →
        (Q * (M + 1) * (ENNReal.ofReal delta).rpow d) *
            (ENNReal.ofReal delta).rpow (chi / 2) < A⁻¹ := by
  let twoPower : ENNReal := (2 : ENNReal).rpow d
  let C : ENNReal := Q * (twoPower + 1)
  have hTwoPowerTop : twoPower ≠ ⊤ := by
    dsimp [twoPower]
    exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  have hCTop : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.mul_ne_top hQTop (ENNReal.add_ne_top.mpr ⟨hTwoPowerTop, by norm_num⟩)
  have hAInvPos : 0 < A⁻¹ := ENNReal.inv_pos.mpr hATop
  obtain ⟨deltaZero, hdeltaZero, hdeltaZeroOne, hsmall⟩ :=
    exists_const_mul_two_scale_rpow_strict_threshold
      (eta := chi / 2) (by positivity) C A⁻¹ hCTop hAInvPos
  refine ⟨deltaZero, hdeltaZero, hdeltaZeroOne, ?_⟩
  intro delta M hdelta hdeltaSmall hcost
  let x : ENNReal := ENNReal.ofReal delta
  let y : ENNReal := ENNReal.ofReal (delta / 2)
  have hxEq : x = 2 * y := by
    dsimp [x, y]
    calc
      ENNReal.ofReal delta = ENNReal.ofReal (2 * (delta / 2)) := by
        congr 1
        ring
      _ = ENNReal.ofReal 2 * ENNReal.ofReal (delta / 2) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = 2 * ENNReal.ofReal (delta / 2) := by norm_num
  have hxOne : x ≤ 1 := by
    dsimp [x]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (hdeltaSmall.trans hdeltaZeroOne)
  have hxPowerOne : x.rpow d ≤ 1 := by
    calc
      x.rpow d ≤ (1 : ENNReal).rpow d :=
        ENNReal.rpow_le_rpow hxOne hd.le
      _ = 1 := by simp
  have hMPower : M * x.rpow d ≤ twoPower := by
    rw [hxEq]
    change M * (2 * y).rpow d ≤ twoPower
    change M * ((2 * y) ^ d) ≤ twoPower
    rw [ENNReal.mul_rpow_of_nonneg _ _ hd.le]
    calc
      M * ((2 : ENNReal).rpow d * y.rpow d) =
          twoPower * (M * y.rpow d) := by
        dsimp [twoPower]
        ac_rfl
      _ ≤ twoPower * 1 := by
        gcongr
      _ = twoPower := mul_one _
  have hcoefficient : Q * (M + 1) * x.rpow d ≤ C := by
    calc
      Q * (M + 1) * x.rpow d =
          Q * (M * x.rpow d + x.rpow d) := by
        ring
      _ ≤ Q * (twoPower + 1) := by
        gcongr
      _ = C := rfl
  have hhalfSmall : delta / 2 ≤ deltaZero :=
    (div_le_self hdelta.le (by norm_num)).trans hdeltaSmall
  have hstrict : C * x.rpow (chi / 2) < A⁻¹ := by
    have h := hsmall (delta / 2) (by positivity) hhalfSmall
    simpa only [mul_div_cancel₀ delta (by norm_num : (2 : ℝ) ≠ 0)] using h
  calc
    (Q * (M + 1) * x.rpow d) * x.rpow (chi / 2) ≤
        C * x.rpow (chi / 2) := by gcongr
    _ < A⁻¹ := hstrict

/-- Concentration after the continuous active-direction layer has been
discretized into actual marked selector lines.  After the physical ball is
chosen, the dyadic mesh may still be taken below an arbitrary positive
cutoff.  The retained family is nonempty, active in the same ball, separated
at the tube scale, and satisfies the cubic cap count. -/
def HasFiniteDyadicSelectorConcentrationPackets
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) : Prop :=
  ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
    ∀ rho : ℝ, 0 < rho → rho ≤ 1 / 4 →
      ∃ (x : E4) (r : ℝ),
        0 < r ∧ r < rho ∧
        ((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal r).rpow (4 - epsilon) <
          (selectorFrontProbability selector hmeasurable hvalid hselector :
            Measure E4) (Metric.ball x r) ∧
        ∀ eta : ℝ, 0 < eta → ∀ deltaZero : ℝ, 0 < deltaZero →
          ∃ (delta : ℝ) (retained : Finset MarkedLine) (levelZero : ℕ),
            0 < delta ∧ delta < r ∧ delta < deltaZero ∧
            IsWZDyadicScale delta ∧
            2 * delta = (2 : ℝ)⁻¹ ^ levelZero ∧
            2 * delta ≤ 1 ∧
            (125 : ENNReal) ≤
              (ENNReal.ofReal (2 * delta)).rpow (-eta) ∧
            retained.Nonempty ∧
            (↑retained : Set MarkedLine) ⊆
              selector ∩
                {line |
                  (selectorFrontProbability selector hmeasurable hvalid hselector :
                      Measure E4) (Metric.ball x r) / 2 ≤
                    (fibreIntervalProbability :
                      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
                      (markedLineSetFibreSet line (Metric.ball x r))} ∧
            (∀ line ∈ retained,
              (4 : ENNReal) *
                  (8 * ((ENNReal.ofReal (2 * delta)).rpow eta *
                    (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤
                (fibreIntervalProbability :
                  Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
                  (markedLineSetFibreSet line (Metric.ball x r))) ∧
            (∀ line ∈ retained, ∀ line' ∈ retained, line ≠ line' →
              2 * delta ≤ dist (direction line) (direction line')) ∧
            (selectorFrontProbability selector hmeasurable hvalid hselector :
                Measure E4) (Metric.ball x r) / 2 ≤
              (retained.card : ENNReal) *
                (metricSphereCapConstant * (ENNReal.ofReal (4 * delta)) ^ 3)

/-- Arbitrarily small canonical concentration contains enough mass to choose
the cubical scale after seeing the physical packet and then produce a
nonempty finite active marked-line family.  Thus scale choice, selector
discretization, and the cardinality estimate are not assumptions of the
remaining cover-adapted packet gate. -/
theorem hasFiniteDyadicSelectorConcentrationPackets_of_arbitrarilySmall
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hconcentration : HasArbitrarilySmallCanonicalSelectorFrontConcentration
      selector hmeasurable hvalid hselector) :
    HasFiniteDyadicSelectorConcentrationPackets selector hmeasurable hvalid
      hselector := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hpacket⟩ := hconcentration
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_⟩
  intro rho hrho hrhoQuarter
  have hrhoOne : rho ≤ 1 := by linarith
  obtain ⟨x, r, hr, hrSmall, hlarge, _hactiveMass⟩ :=
    hpacket rho hrho hrhoOne
  refine ⟨x, r, hr, hrSmall, hlarge, ?_⟩
  have hmassPos : 0 <
      (selectorFrontProbability selector hmeasurable hvalid hselector :
        Measure E4) (Metric.ball x r) :=
    lt_of_le_of_lt bot_le hlarge
  have hhalfPos : 0 <
      (selectorFrontProbability selector hmeasurable hvalid hselector :
        Measure E4) (Metric.ball x r) / 2 :=
    ENNReal.div_pos hmassPos.ne' (by norm_num)
  intro eta heta deltaZero hdeltaZero
  let Cactive : ENNReal :=
    4 * (8 * (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))
  have hCactiveTop : Cactive ≠ ⊤ := by
    dsimp [Cactive]
    apply ENNReal.mul_ne_top
    · norm_num
    · apply ENNReal.mul_ne_top
      · norm_num
      · apply ENNReal.mul_ne_top
        · norm_num
        · exact ENNReal.ofReal_ne_top
  obtain ⟨activeZero, hactiveZero, _hactiveZeroOne, hactiveBound⟩ :=
    exists_const_mul_two_scale_rpow_threshold heta Cactive
      ((selectorFrontProbability selector hmeasurable hvalid hselector :
        Measure E4) (Metric.ball x r) / 2) hCactiveTop hhalfPos
  obtain ⟨absorbZero, habsorbZero, _habsorbZeroOne, habsorbBound⟩ :=
    exists_subpower_absorption_threshold heta
  let meshZero : ℝ := min deltaZero (min activeZero (absorbZero / 2))
  have hmeshZero : 0 < meshZero := by
    dsimp [meshZero]
    exact lt_min hdeltaZero (lt_min hactiveZero (by positivity))
  obtain ⟨delta, hdelta, hdeltaMin, hdyadic⟩ :=
    exists_wz_dyadic_scale_lt (lt_min hr hmeshZero)
  have hdeltaR : delta < r := hdeltaMin.trans_le (min_le_left _ _)
  have hdeltaMesh : delta < meshZero :=
    hdeltaMin.trans_le (min_le_right _ _)
  have hdeltaZero' : delta < deltaZero := by
    exact hdeltaMesh.trans_le (by
      dsimp [meshZero]
      exact min_le_left _ _)
  have hdeltaActive : delta ≤ activeZero := by
    exact hdeltaMesh.le.trans (by
      dsimp [meshZero]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have htubeAbsorb : 2 * delta ≤ absorbZero := by
    have hhalf : delta ≤ absorbZero / 2 :=
      hdeltaMesh.le.trans (by
        dsimp [meshZero]
        exact (min_le_right _ _).trans (min_le_right _ _))
    linarith
  have htubeOne : 2 * delta ≤ 1 := by linarith
  have habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal (2 * delta)).rpow (-eta) :=
    habsorbBound (2 * delta) (by positivity) htubeAbsorb
  have hactiveBase :
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal (2 * delta)).rpow eta *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤
        (selectorFrontProbability selector hmeasurable hvalid hselector :
          Measure E4) (Metric.ball x r) / 2 := by
    calc
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal (2 * delta)).rpow eta *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) =
          Cactive * (ENNReal.ofReal (2 * delta)).rpow eta := by
            dsimp [Cactive]
            ac_rfl
      _ ≤ (selectorFrontProbability selector hmeasurable hvalid hselector :
          Measure E4) (Metric.ball x r) / 2 :=
        hactiveBound delta hdelta hdeltaActive
  have hcellDyadic : IsWZDyadicScale delta := hdyadic
  obtain ⟨level, hdeltaLevel⟩ := hdyadic
  have hlevel : level ≠ 0 := by
    intro hzero
    subst level
    norm_num at hdeltaLevel
    linarith
  obtain ⟨levelZero, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hlevel
  have htubeDyadic : 2 * delta = (2 : ℝ)⁻¹ ^ levelZero := by
    rw [hdeltaLevel, pow_succ]
    ring
  obtain ⟨retained, hretained, hseparated, hcount⟩ :=
    selector_exists_separated_active_family_with_count
      selector hmeasurable hvalid hselector (Metric.ball x r)
        Metric.isOpen_ball.measurableSet hdelta (by linarith)
  have hretainedNonempty : retained.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hcardNot
    have hcardZero : retained.card = 0 := Nat.eq_zero_of_not_pos hcardNot
    have hcountZero :
        (selectorFrontProbability selector hmeasurable hvalid hselector :
          Measure E4) (Metric.ball x r) / 2 ≤ 0 := by
      simpa [hcardZero] using hcount
    exact (not_lt_of_ge hcountZero) hhalfPos
  exact ⟨delta, retained, levelZero, hdelta, hdeltaR, hdeltaZero',
    hcellDyadic, htubeDyadic, htubeOne, habsorb, hretainedNonempty, hretained,
    (by
      intro line hline
      exact hactiveBase.trans (hretained hline).2),
    hseparated, hcount⟩

/-- Finite concentration packet supported on one measurable positive carrier
piece.  Unlike the canonical-selector packet, every retained line belongs to
the same packing piece whose normalized law produced the concentration ball;
the cap constant is consequently the carrier-piece direction constant. -/
def HasFiniteDyadicCarrierPieceConcentrationPackets
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) : Prop :=
  ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
    ∀ rho : ℝ, 0 < rho → rho ≤ 1 / 4 →
      ∃ (x : E4) (r : ℝ),
        0 < r ∧ r < rho ∧
        ((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal r).rpow (4 - epsilon) <
          (markedCarrierPieceFrontProbability selector hmeasurable hvalid
            hselector piece : Measure E4) (Metric.ball x r) ∧
        ∀ eta : ℝ, 0 < eta → ∀ deltaZero : ℝ, 0 < deltaZero →
          ∃ (delta : ℝ) (retained : Finset MarkedLine) (levelZero : ℕ),
            0 < delta ∧ delta < r ∧ delta < deltaZero ∧
            IsWZDyadicScale delta ∧
            2 * delta = (2 : ℝ)⁻¹ ^ levelZero ∧
            2 * delta ≤ 1 ∧
            (125 : ENNReal) ≤
              (ENNReal.ofReal (2 * delta)).rpow (-eta) ∧
            retained.Nonempty ∧
            (↑retained : Set MarkedLine) ⊆
              selectorLinesOverCarrierPiece selector piece ∩
                {line |
                  (markedCarrierPieceFrontProbability selector hmeasurable hvalid
                      hselector piece : Measure E4) (Metric.ball x r) / 2 ≤
                    (fibreIntervalProbability :
                      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
                      (markedLineSetFibreSet line (Metric.ball x r))} ∧
            (∀ line ∈ retained,
              (4 : ENNReal) *
                  (8 * ((ENNReal.ofReal (2 * delta)).rpow eta *
                    (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤
                (fibreIntervalProbability :
                  Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
                  (markedLineSetFibreSet line (Metric.ball x r))) ∧
            (∀ line ∈ retained, ∀ line' ∈ retained, line ≠ line' →
              2 * delta ≤ dist (direction line) (direction line')) ∧
            (markedCarrierPieceFrontProbability selector hmeasurable hvalid
                hselector piece : Measure E4) (Metric.ball x r) / 2 ≤
              (retained.card : ENNReal) *
                (carrierPieceDirectionCapConstant selector hmeasurable hvalid
                    hselector piece * (ENNReal.ofReal (4 * delta)) ^ 3)

/-- The coherent boundary supplies a complete active-ready finite packet on
any fixed measurable positive carrier piece.  Scale choice occurs after the
piece-specific concentration ball is known, so no uniform Minkowski cover of
the full selector is asserted or used. -/
theorem hasFiniteDyadicCarrierPieceConcentrationPackets_of_boundary
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0) :
    HasFiniteDyadicCarrierPieceConcentrationPackets selector hmeasurable hvalid
      hselector piece := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hpacket⟩ :=
    coherentBoundary_has_arbitrarily_small_carrierPiece_concentration_packet
      selector hmeasurable hvalid hselector hboundary piece
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_⟩
  intro rho hrho hrhoQuarter
  have hrhoOne : rho ≤ 1 := by linarith
  obtain ⟨x, r, hr, hrSmall, hlarge⟩ := hpacket rho hrho hrhoOne
  refine ⟨x, r, hr, hrSmall, hlarge, ?_⟩
  have hmassPos : 0 <
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball x r) :=
    lt_of_le_of_lt bot_le hlarge
  have hhalfPos : 0 <
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball x r) / 2 :=
    ENNReal.div_pos hmassPos.ne' (by norm_num)
  intro eta heta deltaZero hdeltaZero
  let Cactive : ENNReal :=
    4 * (8 * (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))
  have hCactiveTop : Cactive ≠ ⊤ := by
    dsimp [Cactive]
    apply ENNReal.mul_ne_top
    · norm_num
    · apply ENNReal.mul_ne_top
      · norm_num
      · apply ENNReal.mul_ne_top
        · norm_num
        · exact ENNReal.ofReal_ne_top
  obtain ⟨activeZero, hactiveZero, _hactiveZeroOne, hactiveBound⟩ :=
    exists_const_mul_two_scale_rpow_threshold heta Cactive
      ((markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) (Metric.ball x r) / 2)
      hCactiveTop hhalfPos
  obtain ⟨absorbZero, habsorbZero, _habsorbZeroOne, habsorbBound⟩ :=
    exists_subpower_absorption_threshold heta
  let meshZero : ℝ := min deltaZero (min activeZero (absorbZero / 2))
  have hmeshZero : 0 < meshZero := by
    dsimp [meshZero]
    exact lt_min hdeltaZero (lt_min hactiveZero (by positivity))
  obtain ⟨delta, hdelta, hdeltaMin, hdyadic⟩ :=
    exists_wz_dyadic_scale_lt (lt_min hr hmeshZero)
  have hdeltaR : delta < r := hdeltaMin.trans_le (min_le_left _ _)
  have hdeltaMesh : delta < meshZero :=
    hdeltaMin.trans_le (min_le_right _ _)
  have hdeltaZero' : delta < deltaZero := by
    exact hdeltaMesh.trans_le (by
      dsimp [meshZero]
      exact min_le_left _ _)
  have hdeltaActive : delta ≤ activeZero := by
    exact hdeltaMesh.le.trans (by
      dsimp [meshZero]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have htubeAbsorb : 2 * delta ≤ absorbZero := by
    have hhalf : delta ≤ absorbZero / 2 :=
      hdeltaMesh.le.trans (by
        dsimp [meshZero]
        exact (min_le_right _ _).trans (min_le_right _ _))
    linarith
  have htubeOne : 2 * delta ≤ 1 := by linarith
  have hfourDeltaOne : 2 * (2 * delta) ≤ 1 := by linarith
  have habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal (2 * delta)).rpow (-eta) :=
    habsorbBound (2 * delta) (by positivity) htubeAbsorb
  have hactiveBase :
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal (2 * delta)).rpow eta *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤
        (markedCarrierPieceFrontProbability selector hmeasurable hvalid
          hselector piece : Measure E4) (Metric.ball x r) / 2 := by
    calc
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal (2 * delta)).rpow eta *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) =
          Cactive * (ENNReal.ofReal (2 * delta)).rpow eta := by
            dsimp [Cactive]
            ac_rfl
      _ ≤ (markedCarrierPieceFrontProbability selector hmeasurable hvalid
          hselector piece : Measure E4) (Metric.ball x r) / 2 :=
        hactiveBound delta hdelta hdeltaActive
  have hcellDyadic : IsWZDyadicScale delta := hdyadic
  obtain ⟨level, hdeltaLevel⟩ := hdyadic
  have hlevel : level ≠ 0 := by
    intro hzero
    subst level
    norm_num at hdeltaLevel
    linarith
  obtain ⟨levelZero, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hlevel
  have htubeDyadic : 2 * delta = (2 : ℝ)⁻¹ ^ levelZero := by
    rw [hdeltaLevel, pow_succ]
    ring
  obtain ⟨retained, hretained, hseparated, hcount⟩ :=
    markedCarrierPiece_exists_separated_active_family_with_count
      selector hmeasurable hvalid hselector piece hpieceMeasurable hpieceCarrier
      hmass (Metric.ball x r) Metric.isOpen_ball.measurableSet
      (delta := 2 * delta) (by positivity) hfourDeltaOne
  have hretainedNonempty : retained.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hcardNot
    have hcardZero : retained.card = 0 := Nat.eq_zero_of_not_pos hcardNot
    have hcountZero :
        (markedCarrierPieceFrontProbability selector hmeasurable hvalid
          hselector piece : Measure E4) (Metric.ball x r) / 2 ≤ 0 := by
      simpa [hcardZero] using hcount
    exact (not_lt_of_ge hcountZero) hhalfPos
  refine ⟨delta, retained, levelZero, hdelta, hdeltaR, hdeltaZero', hcellDyadic,
    htubeDyadic, htubeOne, habsorb, hretainedNonempty, hretained, ?_,
    hseparated, ?_⟩
  · intro line hline
    exact hactiveBase.trans (hretained hline).2
  · simpa [show 2 * (2 * delta) = 4 * delta by ring] using hcount

/-- Once the published finite estimate and the cover-adapted packets are
separately available, the qualitative four-dimensional conclusion follows
formally.  This theorem contains the full WZ readback and terminal exponent
contradiction; neither is hidden in an external discharge. -/
theorem dimH_eq_four_of_wz_finite_estimate_and_cover_packets
    (ambient selector : Set MarkedLine)
    (hWZ : HasWangZakharovFiniteEstimate)
    (hpackets : HasCoverAdaptedWZContradictionPackets ambient selector) :
    dimH (unitFront ambient) = 4 := by
  have hdimUpper : dimH (unitFront ambient) ≤ 4 := by
    calc
      dimH (unitFront ambient) ≤ dimH (Set.univ : Set E4) :=
        dimH_mono (Set.subset_univ _)
      _ = 4 := by simp [E4, Real.dimH_univ_eq_finrank]
  apply le_antisymm hdimUpper
  by_contra hnot
  have hdimStrict : dimH (unitFront ambient) < 4 := lt_of_not_ge hnot
  obtain ⟨chi, hchi, hchiFour, hpacket⟩ := hpackets hdimStrict
  obtain ⟨eta, heta, A, hA0, hAtop, deltaZero, hdeltaZero, hlower⟩ :=
    wang_zakharov_finite_readback_to_target hWZ (chi / 2) (by positivity)
  obtain ⟨n, D, target, upperConstant, hthickness, hsmall, hinput,
      htarget, hgap, hupper⟩ :=
    hpacket eta heta A hA0 hAtop deltaZero hdeltaZero
  have hlower' :
      A⁻¹ * (ENNReal.ofReal D.thickness).rpow (-4 + chi / 2) ≤
        coveringNumber target D.thickness :=
    hlower n D target hsmall hinput htarget
  exact wz_covering_bounds_contradiction_ennreal_coefficients
    hthickness hgap hlower' hupper

/-- Sole external analytic input: Wang--Zakharov's published finite theorem
in its native volume normalization. -/
axiom wang_zakharov_published_volume_estimate :
    HasWangZakharovFiniteVolumeEstimate

/-- The covering-number form used below is now an internal consequence of
the published volume theorem, including the complete four-dimensional ball
normalization. -/
theorem wang_zakharov_finite_estimate : HasWangZakharovFiniteEstimate :=
  wang_zakharov_volume_estimate_to_covering
    wang_zakharov_published_volume_estimate

/-- A low-cost Hausdorff cover of the compact ambient front can be replaced
by its measurable closed-diameter thickenings and stripped of all
zero-diameter members without losing any of the normalized packing-piece
front probability.  This closes the measure-theoretic support step before
the dyadic Hausdorff-layer selection. -/
theorem markedCarrierPieceFrontProbability_positive_cover_support
    (ambient selector : Set MarkedLine)
    (hambientCompact : IsCompact ambient)
    (hselectorAmbient : selector ⊆ ambient)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (cover : ℕ → Set E4)
    (hcover : unitFront ambient ⊆ ⋃ i, cover i) :
    (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
      Measure E4)
        ((⋃ i : {i : ℕ // Metric.ediam (cover i) ≠ 0},
          closedDiameterThickening cover i.1)ᶜ) = 0 := by
  apply measure_compl_iUnion_positive_closedDiameterThickening_eq_zero
    (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
      Measure E4)
  · intro x
    exact markedCarrierPieceFrontProbability_singleton_eq_zero
      selector hmeasurable hvalid hselector piece hpieceMeasurable
        hpieceCarrier hpieceMass x
  · exact markedCarrierPieceFrontProbability_compl_unitFront_eq_zero
      selector ambient hmeasurable hvalid hselector piece hselectorAmbient
        (StickyKakeya4.IsCompact.unitFront hambientCompact).measurableSet
  · exact hcover

/-- From the strict Hausdorff-dimension hypothesis, extract the actual
low-cost cover and a measurable first-assigned dyadic target layer carrying
power-scale mass for the normalized packing-piece front law.  This is the
cover-layer construction used in the manuscript before active-direction
selection; no concentration ball is substituted for it. -/
theorem markedCarrierPiece_exists_low_cost_dyadic_target_layer
    (ambient selector : Set MarkedLine)
    (hambientCompact : IsCompact ambient)
    (hselectorAmbient : selector ⊆ ambient)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hpieceMass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (seed : Set E4) (hseedMeasurable : MeasurableSet seed)
    (boundaryLower : ENNReal) (hboundaryLowerPos : 0 < boundaryLower)
    (hboundaryLower : boundaryLower <
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) seed)
    {d : NNReal} (hdim : dimH (unitFront ambient) < (d : ENNReal))
    {rho : ENNReal} (hrho : 0 < rho) (hrhoQuarter : rho ≤ 1 / 4)
    {epsilon : ENNReal} (hepsilon : 0 < epsilon)
    {theta : ℝ} (htheta : 0 < theta) :
    ∃ cover : ℕ → Set E4,
      (∀ i, Metric.ediam (cover i) ≤ rho) ∧
      (∑' i, ⨆ _ : (cover i).Nonempty,
        (Metric.ediam (cover i)).rpow (d : ℝ)) < epsilon ∧
      ∃ (n : ℕ) (target : Set E4),
        target =
          disjointedCoverScaleGroup
              (positiveClosedDiameterCover cover)
              (fun i => dyadicENNRealScale (Metric.ediam (cover i))) n ∩ seed ∧
        MeasurableSet target ∧
        boundaryLower * dyadicMassThreshold theta n <
          (markedCarrierPieceFrontProbability selector hmeasurable hvalid
            hselector piece : Measure E4) target ∧
        0 < (markedCarrierPieceFrontProbability selector hmeasurable hvalid
          hselector piece : Measure E4) target ∧
        (∀ i,
          dyadicENNRealScale (Metric.ediam (cover i)) = n →
          (positiveClosedDiameterCover cover i).Nonempty →
            ((2 : ENNReal)⁻¹) ^ (n + 1) < Metric.ediam (cover i) ∧
            Metric.ediam (cover i) ≤ ((2 : ENNReal)⁻¹) ^ n) ∧
        1 ≤ n ∧
        ((2 : ENNReal)⁻¹) ^ (n + 1) < rho ∧
        0 < ((((2 : ENNReal)⁻¹) ^ n).toReal) ∧
        ((((2 : ENNReal)⁻¹) ^ n).toReal) ≤ 1 / 2 ∧
        IsWZDyadicScale ((((2 : ENNReal)⁻¹) ^ n).toReal) ∧
        IsWZDyadicScale (((((2 : ENNReal)⁻¹) ^ n).toReal) / 2) ∧
        (positiveDyadicCoverLayerIndices cover n).Finite ∧
        ((positiveDyadicCoverLayerIndices cover n).ncard : ENNReal) *
            (((2 : ENNReal)⁻¹) ^ (n + 1)).rpow (d : ℝ) < epsilon ∧
        coveringNumber target
          (4 * ((((2 : ENNReal)⁻¹) ^ n).toReal)) ≤
            ((positiveDyadicCoverLayerIndices cover n).ncard : ENNReal) ∧
        (∃ retained : Finset MarkedLine,
          retained.Nonempty ∧
          (↑retained : Set MarkedLine) ⊆
            selectorLinesOverCarrierPiece selector piece ∩
              {line |
                (markedCarrierPieceFrontProbability selector hmeasurable hvalid
                  hselector piece : Measure E4) target / 2 ≤
                (fibreIntervalProbability :
                  Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
                  (markedLineSetFibreSet line target)} ∧
          (∀ line ∈ retained, ∀ line' ∈ retained,
            line ≠ line' →
              ((((2 : ENNReal)⁻¹) ^ n).toReal) ≤
                dist (direction line) (direction line')) ∧
          (markedCarrierPieceFrontProbability selector hmeasurable hvalid
            hselector piece : Measure E4) target / 2 ≤
              (retained.card : ENNReal) *
                (carrierPieceDirectionCapConstant selector hmeasurable hvalid
                  hselector piece *
                    (ENNReal.ofReal
                      (2 * ((((2 : ENNReal)⁻¹) ^ n).toReal))) ^ 3) ∧
          (((boundaryLower *
              ((1 - dyadicMassRatio theta) * (2 : ENNReal)⁻¹)).toReal) /
              (16 * (carrierPieceDirectionCapConstant selector hmeasurable
                hvalid hselector piece).toReal)) *
            ((((2 : ENNReal)⁻¹) ^ n).toReal) ^ (-3 + theta) ≤
              (retained.card : ℝ)) ∧
        ∀ delta : ℝ, 0 < delta → 2 * delta ≤ 1 →
          ∃ retained : Finset MarkedLine,
            retained.Nonempty ∧
            (↑retained : Set MarkedLine) ⊆
              selectorLinesOverCarrierPiece selector piece ∩
                {line |
                  (markedCarrierPieceFrontProbability selector hmeasurable hvalid
                    hselector piece : Measure E4) target / 2 ≤
                  (fibreIntervalProbability :
                    Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
                    (markedLineSetFibreSet line target)} ∧
            (∀ line ∈ retained, ∀ line' ∈ retained,
              line ≠ line' →
                delta ≤ dist (direction line) (direction line')) ∧
            (markedCarrierPieceFrontProbability selector hmeasurable hvalid
              hselector piece : Measure E4) target / 2 ≤
              (retained.card : ENNReal) *
                (carrierPieceDirectionCapConstant selector hmeasurable hvalid
                  hselector piece * (ENNReal.ofReal (2 * delta)) ^ 3) := by
  let mu : Measure E4 :=
    markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece
  change boundaryLower < mu seed at hboundaryLower
  let conditionedFinite : FiniteMeasure E4 :=
    ⟨mu.restrict seed, inferInstance⟩
  have hseedMassPos : 0 < mu seed := hboundaryLowerPos.trans hboundaryLower
  have hconditionedFiniteNe : conditionedFinite ≠ 0 := by
    intro hzero
    have hzero' : (conditionedFinite : Measure E4) = 0 := by
      rw [hzero]
      rfl
    have hseedZero : mu seed = 0 :=
      Measure.restrict_eq_zero.mp (by simpa [conditionedFinite] using hzero')
    exact hseedMassPos.ne' hseedZero
  let conditioned : ProbabilityMeasure E4 := conditionedFinite.normalize
  letI : IsProbabilityMeasure (conditioned : Measure E4) := by infer_instance
  obtain ⟨cover, hcover, hdiam, hcost⟩ :=
    exists_small_diameter_cover_of_dimH_lt
      (unitFront ambient) hdim (r := rho) (epsilon := epsilon)
        hrho hepsilon
  have hdiamOne : ∀ i, Metric.ediam (cover i) ≤ 1 := by
    intro i
    exact (hdiam i).trans (hrhoQuarter.trans (by norm_num))
  have hdPos : 0 < d := by
    have hdENN : 0 < (d : ENNReal) := (bot_le : 0 ≤ dimH (unitFront ambient)).trans_lt hdim
    exact_mod_cast hdENN
  have hcostFinite :
      (∑' i, ⨆ _ : (cover i).Nonempty,
        (Metric.ediam (cover i)).rpow (d : ℝ)) ≠ ⊤ :=
    ne_of_lt (hcost.trans_le le_top)
  have hmuSupport : mu (unitFront ambient)ᶜ = 0 := by
    exact markedCarrierPieceFrontProbability_compl_unitFront_eq_zero
      selector ambient hmeasurable hvalid hselector piece hselectorAmbient
        (StickyKakeya4.IsCompact.unitFront hambientCompact).measurableSet
  have hmuSingleton : ∀ x, mu {x} = 0 := by
    intro x
    exact markedCarrierPieceFrontProbability_singleton_eq_zero
      selector hmeasurable hvalid hselector piece hpieceMeasurable
        hpieceCarrier hpieceMass x
  have hconditionedSupport :
      (conditioned : Measure E4) (unitFront ambient)ᶜ = 0 := by
    change (conditionedFinite.normalize : Measure E4) (unitFront ambient)ᶜ = 0
    rw [conditionedFinite.toMeasure_normalize_eq_of_nonzero
      hconditionedFiniteNe, Measure.smul_apply]
    have hnull : (conditionedFinite : Measure E4) (unitFront ambient)ᶜ = 0 := by
      change (mu.restrict seed) (unitFront ambient)ᶜ = 0
      rw [Measure.restrict_apply
        (StickyKakeya4.IsCompact.unitFront hambientCompact).measurableSet.compl]
      exact measure_mono_null Set.inter_subset_left hmuSupport
    rw [hnull]
    simp
  have hconditionedSingleton : ∀ x, (conditioned : Measure E4) {x} = 0 := by
    intro x
    change (conditionedFinite.normalize : Measure E4) {x} = 0
    rw [conditionedFinite.toMeasure_normalize_eq_of_nonzero
      hconditionedFiniteNe, Measure.smul_apply]
    have hnull : (conditionedFinite : Measure E4) {x} = 0 := by
      change (mu.restrict seed) {x} = 0
      rw [Measure.restrict_apply (MeasurableSet.singleton x)]
      exact measure_mono_null Set.inter_subset_left (hmuSingleton x)
    rw [hnull]
    simp
  obtain ⟨n, hmass, htargetMeasurable, hscale⟩ :=
    exists_positive_dyadic_cover_scale_group_with_power_mass
      (conditioned : Measure E4) hconditionedSingleton (unitFront ambient)
        hconditionedSupport cover hcover hdiamOne htheta
  let coverLayer : Set E4 :=
    disjointedCoverScaleGroup
      (positiveClosedDiameterCover cover)
      (fun i => dyadicENNRealScale (Metric.ediam (cover i))) n
  let target : Set E4 := coverLayer ∩ seed
  have htargetMeasurable' : MeasurableSet target :=
    htargetMeasurable.inter hseedMeasurable
  have hconditionedMass :
      dyadicMassThreshold theta n <
        (conditioned : Measure E4) coverLayer := by
    simpa [coverLayer] using hmass
  have hconditionedMassValue :
      (↑conditionedFinite.mass : ENNReal) = mu seed := by
    simp [conditionedFinite, FiniteMeasure.mass, hseedMeasurable]
  have hconditionedMassZero :
      (↑conditionedFinite.mass : ENNReal) ≠ 0 := by
    rw [hconditionedMassValue]
    exact hseedMassPos.ne'
  have hconditionedNNMassZero : conditionedFinite.mass ≠ 0 := by
    intro hzero
    apply hconditionedMassZero
    rw [hzero]
    rfl
  have hconditionedMassTop :
      (↑conditionedFinite.mass : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hconditionedMassFormula :
      (conditioned : Measure E4) coverLayer =
        (↑conditionedFinite.mass : ENNReal)⁻¹ * mu target := by
    change (conditionedFinite.normalize : Measure E4) coverLayer = _
    rw [conditionedFinite.toMeasure_normalize_eq_of_nonzero
      hconditionedFiniteNe, Measure.smul_apply]
    change (↑conditionedFinite.mass⁻¹ : ENNReal) *
      (mu.restrict seed) coverLayer = _
    rw [Measure.restrict_apply htargetMeasurable]
    simpa [target, coverLayer, ENNReal.coe_inv hconditionedNNMassZero]
  have hseedTimesThreshold :
      mu seed * dyadicMassThreshold theta n < mu target := by
    have hmul := ENNReal.mul_lt_mul_left hconditionedMassZero
      hconditionedMassTop hconditionedMass
    rw [hconditionedMassFormula] at hmul
    calc
      mu seed * dyadicMassThreshold theta n =
          dyadicMassThreshold theta n *
            (↑conditionedFinite.mass : ENNReal) := by
        rw [hconditionedMassValue]
        ac_rfl
      _ < (((↑conditionedFinite.mass : ENNReal)⁻¹ * mu target)) *
          (↑conditionedFinite.mass : ENNReal) := hmul
      _ = mu target := by
        rw [show (((↑conditionedFinite.mass : ENNReal)⁻¹ * mu target)) *
              (↑conditionedFinite.mass : ENNReal) =
            ((↑conditionedFinite.mass : ENNReal)⁻¹ *
              (↑conditionedFinite.mass : ENNReal)) * mu target by ac_rfl,
          ENNReal.inv_mul_cancel hconditionedMassZero hconditionedMassTop,
          one_mul]
  have hboundaryMass :
      boundaryLower * dyadicMassThreshold theta n < mu target := by
    have hlowerScaled :
        boundaryLower * dyadicMassThreshold theta n ≤
          mu seed * dyadicMassThreshold theta n := by gcongr
    exact hlowerScaled.trans_lt hseedTimesThreshold
  have htargetPos : 0 < mu target :=
    (bot_lt_iff_ne_bot.mpr
      (mul_ne_zero hboundaryLowerPos.ne'
        (dyadicMassThreshold_pos htheta n).ne')).trans hboundaryMass
  have htargetNonempty : target.Nonempty := by
    by_contra htargetEmpty
    have htargetEq : target = ∅ := Set.not_nonempty_iff_eq_empty.mp htargetEmpty
    rw [htargetEq, measure_empty] at htargetPos
    exact (lt_irrefl 0) htargetPos
  have hnPos : 1 ≤ n := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hnZero
    obtain ⟨x, hx⟩ := htargetNonempty
    have hxLayer : x ∈ coverLayer := hx.1
    change x ∈ disjointedCoverScaleGroup
      (positiveClosedDiameterCover cover)
      (fun i => dyadicENNRealScale (Metric.ediam (cover i))) n at hxLayer
    simp only [disjointedCoverScaleGroup, Set.mem_iUnion] at hxLayer
    obtain ⟨i, hxi⟩ := hxLayer
    have hpositiveNonempty :
        (positiveClosedDiameterCover cover i.1).Nonempty :=
      ⟨x, disjointed_subset (positiveClosedDiameterCover cover) i.1 hxi⟩
    have hlower := (hscale i.1 i.property hpositiveNonempty).1
    have hlower' : (2 : ENNReal)⁻¹ < Metric.ediam (cover i.1) := by
      calc
        (2 : ENNReal)⁻¹ = ((2 : ENNReal)⁻¹) ^ (n + 1) := by
          rw [hnZero]
          norm_num
        _ < Metric.ediam (cover i.1) := hlower
    have hupper : Metric.ediam (cover i.1) ≤ (2 : ENNReal)⁻¹ :=
      (hdiam i.1).trans (hrhoQuarter.trans (by norm_num))
    exact (not_lt_of_ge hupper) hlower'
  have hscaleRho : ((2 : ENNReal)⁻¹) ^ (n + 1) < rho := by
    obtain ⟨x, hx⟩ := htargetNonempty
    have hxLayer : x ∈ coverLayer := hx.1
    change x ∈ disjointedCoverScaleGroup
      (positiveClosedDiameterCover cover)
      (fun i => dyadicENNRealScale (Metric.ediam (cover i))) n at hxLayer
    simp only [disjointedCoverScaleGroup, Set.mem_iUnion] at hxLayer
    obtain ⟨i, hxi⟩ := hxLayer
    have hpositiveNonempty :
        (positiveClosedDiameterCover cover i.1).Nonempty :=
      ⟨x, disjointed_subset (positiveClosedDiameterCover cover) i.1 hxi⟩
    exact (hscale i.1 i.property hpositiveNonempty).1.trans_le (hdiam i.1)
  have hscaleToReal : ((((2 : ENNReal)⁻¹) ^ n).toReal) =
      (2 : ℝ)⁻¹ ^ n := by
    rw [ENNReal.toReal_pow]
    norm_num
  have hscaleToRealPos : 0 < ((((2 : ENNReal)⁻¹) ^ n).toReal) := by
    rw [hscaleToReal]
    positivity
  have hscaleToRealHalf : ((((2 : ENNReal)⁻¹) ^ n).toReal) ≤ 1 / 2 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnPos)
    subst n
    rw [hscaleToReal, pow_succ]
    have hkpow : (2 : ℝ)⁻¹ ^ k ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hkpow (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  have htubeDyadic : IsWZDyadicScale
      ((((2 : ENNReal)⁻¹) ^ n).toReal) :=
    ⟨n, hscaleToReal⟩
  have hcellDyadic : IsWZDyadicScale
      (((((2 : ENNReal)⁻¹) ^ n).toReal) / 2) := by
    refine ⟨n + 1, ?_⟩
    rw [hscaleToReal, pow_succ]
    ring
  have hlayerFinite : (positiveDyadicCoverLayerIndices cover n).Finite :=
    finite_positiveDyadicCoverLayerIndices cover hdPos hdiamOne hcostFinite n
  have hlayerCost :
      ((positiveDyadicCoverLayerIndices cover n).ncard : ENNReal) *
          (((2 : ENNReal)⁻¹) ^ (n + 1)).rpow (d : ℝ) < epsilon :=
    positiveDyadicCoverLayerIndices_ncard_mul_rpow_lt
      cover hdPos hdiamOne hcost n
  obtain ⟨centers, hcentersCover, hcentersCard⟩ :=
    exists_finite_centers_cover_disjointed_dyadic_group
      cover hdiamOne n hlayerFinite (fun i hi hnonempty => (hscale i hi hnonempty).2)
  have htargetCovering :
      coveringNumber target
        (4 * ((((2 : ENNReal)⁻¹) ^ n).toReal)) ≤
          ((positiveDyadicCoverLayerIndices cover n).ncard : ENNReal) := by
    calc
      coveringNumber target
          (4 * ((((2 : ENNReal)⁻¹) ^ n).toReal)) ≤
          coveringNumber coverLayer
            (4 * ((((2 : ENNReal)⁻¹) ^ n).toReal)) :=
        coveringNumber_mono Set.inter_subset_left _
      _ ≤ (centers.card : ENNReal) :=
        coveringNumber_le_card_of_coversAtRadius coverLayer
          (4 * ((((2 : ENNReal)⁻¹) ^ n).toReal)) centers
            (by simpa [coverLayer] using hcentersCover)
      _ ≤ ((positiveDyadicCoverLayerIndices cover n).ncard : ENNReal) := by
        exact_mod_cast hcentersCard
  have hactive : ∀ delta : ℝ, 0 < delta → 2 * delta ≤ 1 →
      ∃ retained : Finset MarkedLine,
        retained.Nonempty ∧
        (↑retained : Set MarkedLine) ⊆
          selectorLinesOverCarrierPiece selector piece ∩
            {line | mu target / 2 ≤
              (fibreIntervalProbability :
                Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
                (markedLineSetFibreSet line target)} ∧
        (∀ line ∈ retained, ∀ line' ∈ retained,
          line ≠ line' → delta ≤ dist (direction line) (direction line')) ∧
        mu target / 2 ≤
          (retained.card : ENNReal) *
            (carrierPieceDirectionCapConstant selector hmeasurable hvalid
              hselector piece * (ENNReal.ofReal (2 * delta)) ^ 3) := by
    intro delta hdelta hdeltaOne
    obtain ⟨retained, hretained, hseparated, hcount⟩ :=
      markedCarrierPiece_exists_separated_active_family_with_count
        selector hmeasurable hvalid hselector piece hpieceMeasurable
          hpieceCarrier hpieceMass target htargetMeasurable' hdelta hdeltaOne
    have hhalfPos : 0 < mu target / 2 :=
      ENNReal.div_pos htargetPos.ne' (by norm_num)
    have hretainedNonempty : retained.Nonempty := by
      apply Finset.card_pos.mp
      by_contra hcardNot
      have hcardZero : retained.card = 0 := Nat.eq_zero_of_not_pos hcardNot
      have hcountZero : mu target / 2 ≤ 0 := by
        simpa [hcardZero] using hcount
      exact (not_lt_of_ge hcountZero) hhalfPos
    exact ⟨retained, hretainedNonempty, hretained, hseparated, hcount⟩
  obtain ⟨retained, hretainedNonempty, hretained, hseparated, hcount⟩ :=
    hactive ((((2 : ENNReal)⁻¹) ^ n).toReal)
      hscaleToRealPos (by linarith)
  have hcapZero :
      carrierPieceDirectionCapConstant selector hmeasurable hvalid
        hselector piece ≠ 0 :=
    carrierPieceDirectionCapConstant_ne_zero selector hmeasurable hvalid
      hselector piece hpieceMass
  have hcapTop :
      carrierPieceDirectionCapConstant selector hmeasurable hvalid
        hselector piece ≠ ⊤ :=
    carrierPieceDirectionCapConstant_ne_top selector hmeasurable hvalid
      hselector piece
  let lowerConstant : ENNReal := boundaryLower *
    ((1 - dyadicMassRatio theta) * (2 : ENNReal)⁻¹)
  have hboundaryLowerTop : boundaryLower ≠ ⊤ := by
    have hseedLe : mu seed ≤ 1 := by
      calc
        mu seed ≤ mu Set.univ := measure_mono (Set.subset_univ seed)
        _ = 1 := by simp [mu]
    exact ne_top_of_le_ne_top (by norm_num)
      (hboundaryLower.le.trans hseedLe)
  have hlowerConstantTop : lowerConstant ≠ ⊤ := by
    dsimp [lowerConstant]
    exact ENNReal.mul_ne_top hboundaryLowerTop (by finiteness)
  have hmassPower :
      lowerConstant *
          (ENNReal.ofReal ((((2 : ENNReal)⁻¹) ^ n).toReal)).rpow theta ≤
        mu target := by
    have hscaleOfReal :
        ENNReal.ofReal ((((2 : ENNReal)⁻¹) ^ n).toReal) =
          ((2 : ENNReal)⁻¹) ^ n := ENNReal.ofReal_toReal (by simp)
    rw [hscaleOfReal]
    simpa [lowerConstant, dyadicMassThreshold_eq_prefactor_mul_scale_rpow,
      mul_assoc] using hboundaryMass.le
  have hrealCount :=
    active_family_real_card_lower_bound_with_coefficient retained hscaleToRealPos
      hlowerConstantTop hcapZero hcapTop hmassPower hcount
  exact ⟨cover, hdiam, hcost, n, target, rfl,
    htargetMeasurable', hboundaryMass, htargetPos, hscale, hnPos,
    hscaleRho, hscaleToRealPos, hscaleToRealHalf, htubeDyadic, hcellDyadic, hlayerFinite,
    hlayerCost, htargetCovering,
    ⟨retained, hretainedNonempty, hretained, hseparated, hcount, hrealCount⟩,
    hactive⟩

/-- The retained marked lines of a carrier-piece packet admit one genuine
finite carrier-cell system at all pruning radii.  This is the concrete
bridge from the packing-piece covering estimate to the ambient-domain cell
assignment consumed by the packing-three pruning theorem; the affine mark
is retained in the domain even though the cells depend only on the unmarked
carrier `(direction, offset)`. -/
theorem retained_carrier_piece_has_dyadic_common_cover_cells
    (selector : Set MarkedLine) (piece : Set (E4 × E4))
    (carrierCoverConstant carrierDim : ENNReal)
    (hcarrierCoverConstantTop : carrierCoverConstant ≠ ⊤)
    (hcarrierCover : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      coveringNumber piece r ≤ carrierCoverConstant *
        (ENNReal.ofReal (r / 2)).rpow (-carrierDim.toReal))
    (retained : Finset MarkedLine) (hretainedNonempty : retained.Nonempty)
    (hretained : (↑retained : Set MarkedLine) ⊆
      selectorLinesOverCarrierPiece selector piece)
    (levelZero : ℕ) :
    ∃ CAll : ENNReal, CAll ≠ ⊤ ∧ carrierCoverConstant ≤ CAll ∧
      ∃ allCenters : Finset (E4 × E4),
        ∃ cells : Fin (levelZero + 1) →
            Finset {x // x ∈ allCenters},
          (∀ ell, ((cells ell).card : ENNReal) <
            CAll *
              (ENNReal.ofReal (wzDyadicRadius levelZero ell / 4)).rpow
                (-carrierDim.toReal) + 1) ∧
          ∃ cell : Fin (levelZero + 1) → MarkedLine →
              {x // x ∈ allCenters},
            (∀ ell line, line ∈ retained → cell ell line ∈ cells ell) ∧
            (∀ ell line, line ∈ retained →
              dist (direction line, offset line) (cell ell line : E4 × E4) <
                wzDyadicRadius levelZero ell / 2) ∧
            ∀ ell line, line ∈ retained →
              ∀ line', line' ∈ retained →
                cell ell line = cell ell line' →
                  dist (direction line, offset line)
                    (direction line', offset line') ≤
                      wzDyadicRadius levelZero ell := by
  obtain ⟨_cutoff, _hcutoff, _hcutoffOne, CAll, hCAllTop,
      hconstant, hcoverAll⟩ :=
    eventual_covering_bound_extend_to_unit_interval
      piece hcarrierCoverConstantTop hcarrierCover
  refine ⟨CAll, hCAllTop, hconstant, ?_⟩
  apply exists_dyadic_common_cover_cells_on_ambient
    piece retained (fun line : MarkedLine => (direction line, offset line))
      levelZero CAll carrierDim hretainedNonempty hCAllTop
  · intro line hline
    have hlinePiece := hretained hline
    exact hlinePiece.2
  · exact hcoverAll

/-- Real-cardinality form of the carrier-cell bridge, with the coefficient
needed by the packing-three pruning theorem explicit and uniform in the
terminal dyadic depth.  No affine-fibre mark is discarded: `cell` is still
defined on `MarkedLine`, while only its carrier image is covered. -/
theorem retained_carrier_piece_has_dyadic_common_cover_cells_with_uniform_real_bound
    (selector : Set MarkedLine) (piece : Set (E4 × E4))
    (carrierCoverConstant carrierDim : ENNReal)
    (hcarrierCoverConstantTop : carrierCoverConstant ≠ ⊤)
    (hcarrierCover : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      coveringNumber piece r ≤ carrierCoverConstant *
        (ENNReal.ofReal (r / 2)).rpow (-carrierDim.toReal))
    (retained : Finset MarkedLine) (hretainedNonempty : retained.Nonempty)
    (hretained : (↑retained : Set MarkedLine) ⊆
      selectorLinesOverCarrierPiece selector piece)
    (levelZero : ℕ) (packingSlack : ℝ)
    (hpackingSlack : 0 ≤ packingSlack)
    (hcarrierDim : carrierDim.toReal ≤ 3 + packingSlack) :
    ∃ CAll : ENNReal, CAll ≠ ⊤ ∧ carrierCoverConstant ≤ CAll ∧
      ∃ allCenters : Finset (E4 × E4),
        ∃ cells : Fin (levelZero + 1) →
            Finset {x // x ∈ allCenters},
          (∀ ell, ((cells ell).card : ℝ) ≤
            (CAll.toReal * (4 : ℝ) ^ carrierDim.toReal + 1) *
              ((2 : ℝ) ^ (3 + packingSlack)) ^ ell.val) ∧
          ∃ cell : Fin (levelZero + 1) → MarkedLine →
              {x // x ∈ allCenters},
            (∀ ell line, line ∈ retained → cell ell line ∈ cells ell) ∧
            (∀ ell line, line ∈ retained →
              dist (direction line, offset line) (cell ell line : E4 × E4) <
                wzDyadicRadius levelZero ell / 2) ∧
            ∀ ell line, line ∈ retained →
              ∀ line', line' ∈ retained →
                cell ell line = cell ell line' →
                  dist (direction line, offset line)
                    (direction line', offset line') ≤
                      wzDyadicRadius levelZero ell := by
  obtain ⟨_cutoff, _hcutoff, _hcutoffOne, CAll, hCAllTop,
      hconstant, hcoverAll⟩ :=
    eventual_covering_bound_extend_to_unit_interval
      piece hcarrierCoverConstantTop hcarrierCover
  refine ⟨CAll, hCAllTop, hconstant, ?_⟩
  apply exists_dyadic_common_cover_cells_on_ambient_with_uniform_real_bound
    piece retained (fun line : MarkedLine => (direction line, offset line))
      levelZero CAll carrierDim packingSlack hretainedNonempty hCAllTop
      hpackingSlack hcarrierDim
  · intro line hline
    have hlinePiece := hretained hline
    exact hlinePiece.2
  · exact hcoverAll

/-- The packing-piece cover is first extended to every radius up to one,
and only then is the compensation cutoff chosen.  Thus the cutoff is allowed
to depend on the genuine uniform cover coefficient, but is fixed before the
Hausdorff layer and its finite marked family are selected.  This is the
quantifier order needed to close the manuscript's compensation zone. -/
theorem carrier_piece_has_uniform_cover_and_cover_adapted_compensation_threshold
    (piece : Set (E4 × E4))
    (carrierCoverConstant carrierDim : ENNReal)
    (hcarrierCoverConstantTop : carrierCoverConstant ≠ ⊤)
    (hcarrierCover : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      coveringNumber piece r ≤ carrierCoverConstant *
        (ENNReal.ofReal (r / 2)).rpow (-carrierDim.toReal))
    (theta thresholdConstant pointConstant : ℝ)
    (htheta : 0 < theta)
    (hcarrierDim : carrierDim < 3 + ENNReal.ofReal (theta / 4))
    (hcarrierDimTop : carrierDim ≠ ⊤)
    (hthresholdConstant : 0 ≤ thresholdConstant)
    (hpointConstant : 0 < pointConstant) :
    ∃ CAll : ENNReal, CAll ≠ ⊤ ∧ carrierCoverConstant ≤ CAll ∧
      (∀ r : ℝ, 0 < r → r ≤ 1 →
        coveringNumber piece r ≤
          CAll * (ENNReal.ofReal (r / 2)).rpow (-carrierDim.toReal)) ∧
      carrierDim.toReal ≤ 3 + theta / 4 ∧
      ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ deltaZero →
          (4 * (((CAll.toReal * (4 : ℝ) ^ carrierDim.toReal + 1) *
              thresholdConstant)) * (2 : ℝ) ^ (theta / 4) /
                ((2 : ℝ) ^ (theta / 4) - 1)) *
            delta ^ (3 * theta - theta / 4 - 2 * theta) ≤
              pointConstant := by
  obtain ⟨_cutoff, _hcutoff, _hcutoffOne, CAll, hCAllTop,
      hconstant, hcoverAll⟩ :=
    eventual_covering_bound_extend_to_unit_interval
      piece hcarrierCoverConstantTop hcarrierCover
  have hrightTop :
      (3 + ENNReal.ofReal (theta / 4) : ENNReal) ≠ ⊤ := by
    finiteness
  have hcarrierDimRealLt :
      carrierDim.toReal < (3 + ENNReal.ofReal (theta / 4) : ENNReal).toReal :=
    (ENNReal.toReal_lt_toReal hcarrierDimTop hrightTop).2 hcarrierDim
  have hcarrierDimReal : carrierDim.toReal ≤ 3 + theta / 4 := by
    rw [ENNReal.toReal_add (by norm_num) ENNReal.ofReal_ne_top] at hcarrierDimRealLt
    have hthetaQuarter : 0 ≤ theta / 4 := by positivity
    simpa [hthetaQuarter] using hcarrierDimRealLt.le
  have hcellConstant :
      0 ≤ CAll.toReal * (4 : ℝ) ^ carrierDim.toReal + 1 := by
    positivity
  obtain ⟨deltaZero, hdeltaZero, hdeltaZeroOne, habsorb⟩ :=
    exists_cover_adapted_packing_three_compensation_threshold
      htheta hcellConstant hthresholdConstant hpointConstant
  exact ⟨CAll, hCAllTop, hconstant, hcoverAll, hcarrierDimReal,
    deltaZero, hdeltaZero, hdeltaZeroOne, habsorb⟩

/-- Uniform active-fibre cutoff for the Hausdorff-layer route.  The selected
layer already carries a fixed prefactor times `delta^theta`; below one
uniform scale the extra WZ factor `delta^(2 * theta)` is absorbed into that
prefactor.  Thus the same layer mass supplies the `3 * theta` cubical shading
density required after pruning. -/
theorem exists_dyadic_mass_active_fibre_threshold
    (theta : ℝ) (htheta : 0 < theta) (C : ENNReal) (hCtop : C ≠ ⊤) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
      ∀ (n : ℕ) (delta : ℝ) (mass : ENNReal),
        0 < delta → delta ≤ deltaZero →
        delta = ((((2 : ENNReal)⁻¹) ^ n).toReal) →
        dyadicMassThreshold theta n ≤ mass →
        C * (ENNReal.ofReal delta).rpow (3 * theta) ≤ mass / 2 := by
  let prefactor : ENNReal :=
    (1 - dyadicMassRatio theta) * (2 : ENNReal)⁻¹
  have hprefactor : 0 < prefactor := by
    dsimp [prefactor]
    apply bot_lt_iff_ne_bot.mpr
    exact mul_ne_zero
      (tsub_pos_iff_lt.mpr (dyadicMassRatio_lt_one htheta)).ne'
      (by norm_num)
  have hhalf : 0 < prefactor / 2 :=
    ENNReal.div_pos hprefactor.ne' (by norm_num)
  obtain ⟨deltaZero, hdeltaZero, hdeltaZeroOne, hsmall⟩ :=
    exists_const_mul_two_scale_rpow_threshold
      (eta := 2 * theta) (by positivity) C (prefactor / 2) hCtop hhalf
  refine ⟨deltaZero, hdeltaZero, hdeltaZeroOne, ?_⟩
  intro n delta mass hdelta hdeltaSmall hdyadic hmass
  have hhalfScale : delta / 2 ≤ deltaZero := by
    exact (div_le_self hdelta.le (by norm_num)).trans hdeltaSmall
  have habsorb :
      C * (ENNReal.ofReal delta).rpow (2 * theta) ≤ prefactor / 2 := by
    have h := hsmall (delta / 2) (by positivity) hhalfScale
    simpa only [mul_div_cancel₀ delta (by norm_num : (2 : ℝ) ≠ 0)] using h
  exact dyadicMassThreshold_dominates_active_fibre_requirement
    theta n delta C mass htheta hdyadic (by simpa [prefactor] using habsorb)
      hmass

/-- A selected dyadic Hausdorff layer now feeds the carrier pruning theorem
without an additional cardinality hypothesis.  The layer mass and the cubic
direction-cap estimate first give the common `2 * theta` point loss; the
uniform carrier cover and the already-absorbed compensation inequality then
produce genuine marked carrier cells and a half-sized terminal family. -/
theorem dyadic_cover_layer_has_packing_three_carrier_pruning
    (selector : Set MarkedLine) (piece : Set (E4 × E4))
    (CAll carrierDim : ENNReal)
    (theta delta pointConstant : ℝ) (levelZero : ℕ)
    (retained : Finset MarkedLine)
    (hretainedNonempty : retained.Nonempty)
    (hretained : (↑retained : Set MarkedLine) ⊆
      selectorLinesOverCarrierPiece selector piece)
    (hCAllTop : CAll ≠ ⊤)
    (htheta : 0 < theta)
    (hdelta : delta = ((((2 : ENNReal)⁻¹) ^ levelZero).toReal))
    (hpointLower : pointConstant * delta ^ (-3 + 2 * theta) ≤
      (retained.card : ℝ))
    (hcarrierDim : carrierDim.toReal ≤ 3 + theta / 4)
    (habsorb :
      (4 * (((CAll.toReal * (4 : ℝ) ^ carrierDim.toReal + 1) * 8)) *
          (2 : ℝ) ^ (theta / 4) /
            ((2 : ℝ) ^ (theta / 4) - 1)) *
        delta ^ (3 * theta - theta / 4 - 2 * theta) ≤ pointConstant)
    (hcovering : ∀ r : ℝ, 0 < r → r ≤ 1 →
      coveringNumber piece r ≤
        CAll * (ENNReal.ofReal (r / 2)).rpow (-carrierDim.toReal)) :
    ∃ allCenters : Finset (E4 × E4),
      ∃ cells : Fin (levelZero + 1) → Finset {x // x ∈ allCenters},
        ∃ cell : Fin (levelZero + 1) → MarkedLine →
            {x // x ∈ allCenters},
          (∀ ell, ((cells ell).card : ℝ) ≤
            (CAll.toReal * (4 : ℝ) ^ carrierDim.toReal + 1) *
              ((2 : ℝ) ^ (3 + theta / 4)) ^ ell.val) ∧
          (∀ ell line, line ∈ retained → cell ell line ∈ cells ell) ∧
          (∀ ell line, line ∈ retained → ∀ line', line' ∈ retained →
            cell ell line = cell ell line' →
              dist (direction line, offset line)
                (direction line', offset line') ≤
                  wzDyadicRadius levelZero ell) ∧
          ∃ pruned : Finset MarkedLine,
            pruned ⊆ retained ∧
            retained.card ≤ 2 * pruned.card ∧
            (∀ ell b,
              (pointsInCell pruned (cell ell) b).Nonempty →
                activeCarrierPruningThreshold
                    (fun j =>
                      (8 * delta ^ (3 * theta - 3)) *
                        (1 / 8 : ℝ) ^ j.val) ell ≤
                  (pointsInCell pruned (cell ell) b).card) ∧
            ∀ ell line, line ∈ pruned →
              (8 * delta ^ (3 * theta - 3)) *
                  (1 / 8 : ℝ) ^ ell.val ≤
                ((pointsInMetricClosedBall pruned
                  (fun marked : MarkedLine =>
                    (direction marked, offset marked)) line
                  (wzDyadicRadius levelZero ell)).card : ℝ) := by
  have hdeltaPos : 0 < delta := by
    rw [hdelta]
    exact ENNReal.toReal_pos (by simp) (by simp)
  have hdyadic : delta = (2 : ℝ)⁻¹ ^ levelZero := by
    rw [hdelta, ENNReal.toReal_pow]
    norm_num
  apply exists_packing_three_dyadic_carleson_pruning_from_uniform_cover
    piece retained
      (fun marked : MarkedLine => (direction marked, offset marked))
      levelZero CAll carrierDim delta (theta / 4) (2 * theta)
      (3 * theta) 8 pointConstant hretainedNonempty hCAllTop hdeltaPos
      hdyadic (by positivity) hcarrierDim (by norm_num) hpointLower habsorb
  · intro line hline
    exact (hretained hline).2
  · exact hcovering

/-- Once the cover-adapted packing-three pruning has produced its terminal
cell populations, those very populations assemble the full finite WZ source.
The physical tube thickness is `delta`, the cubical shading scale is
`delta / 2`, and the requested WZ exponent may be any `eta ≥ 3 * theta`.
Consequently no further almost-AD hypothesis remains between pruning and the
finite WZ interface; the only geometric input still exposed here is the
convex-Wolff count and its normalization. -/
theorem packing_three_pruning_assembles_wz_finite_input
    {beta : Type*} (levelZero : ℕ) (theta eta delta : ℝ)
    (pruned : Finset MarkedLine)
    (lowerCell : Fin (levelZero + 1) → MarkedLine → beta)
    (hpruned : pruned.Nonempty)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (heta : 3 * theta ≤ eta)
    (hdyadic : delta = (2 : ℝ)⁻¹ ^ levelZero)
    (hcellDyadic : IsWZDyadicScale (delta / 2))
    (hterminal : ∀ ell b,
      (pointsInCell pruned (lowerCell ell) b).Nonempty →
        activeCarrierPruningThreshold
            (fun j : Fin (levelZero + 1) =>
              (8 * delta ^ (3 * theta - 3)) *
                (1 / 8 : ℝ) ^ j.val) ell ≤
          (pointsInCell pruned (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, a ∈ pruned → ∀ b, b ∈ pruned →
      lowerCell ell b = lowerCell ell a →
        dist (direction b, offset b) (direction a, offset a) ≤
          wzDyadicRadius levelZero ell)
    (hvalid : ∀ line ∈ pruned, IsValidLine line)
    (hseparated : ∀ a ∈ pruned, ∀ b ∈ pruned, a ≠ b →
      delta ≤ dist (direction a) (direction b))
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal delta).rpow (-eta))
    (K : ENNReal)
    (hgeometric : ∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount
        (retainedWZCellSourceAtScales delta (delta / 2) pruned
          (fun _ => ∅) hdelta hseparated) U : ENNReal) ≤
        K * volume U)
    (hnormalize : K ≤
      (ENNReal.ofReal delta).rpow (-eta) * pruned.card)
    (activeTime : Fin pruned.card →
      Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (hactive : ∀ i,
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal delta).rpow eta *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) (activeTime i))
    (target : Set E4)
    (hactiveTarget : ∀ i t, t ∈ activeTime i →
      rawFrontParam (retainedIndex pruned i, (t : ℝ)) ∈ target) :
    ∃ shadingCells : MarkedLine → Finset (Fin 4 → ℤ),
      IsWangZakharovFiniteInput
        (retainedWZCellSourceAtScales delta (delta / 2) pruned shadingCells
          hdelta hseparated) eta ∧
      (⋃ i, (retainedWZCellSourceAtScales delta (delta / 2) pruned
        shadingCells hdelta hseparated).shading i) ⊆
          ⋃ y ∈ target, Metric.ball y delta := by
  have hcellPos : 0 < delta / 2 := by positivity
  have htubeOne : 2 * (delta / 2) ≤ 1 := by linarith
  have htubeDyadic : 2 * (delta / 2) = (2 : ℝ)⁻¹ ^ levelZero := by
    rw [hdyadic]
    ring
  have hbase : ENNReal.ofReal delta ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hdeltaOne
  have hexponent :
      (ENNReal.ofReal delta).rpow eta ≤
        (ENNReal.ofReal delta).rpow (3 * theta) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hbase heta
  have hlowerThreshold : ∀ ell,
      (ENNReal.ofReal (2 * (delta / 2))).rpow eta *
          (ENNReal.ofReal
            ((2 * wzDyadicRadius levelZero ell) / (2 * (delta / 2)))) ^ 3 ≤
        (activeCarrierPruningThreshold
          (fun j : Fin (levelZero + 1) =>
            (8 * delta ^ (3 * theta - 3)) *
              (1 / 8 : ℝ) ^ j.val) ell : ENNReal) := by
    intro ell
    have hthree := cover_adapted_active_threshold_gives_wz_lower
      levelZero ell delta theta hdelta
    have hmono :
        (ENNReal.ofReal delta).rpow eta *
            (ENNReal.ofReal
              ((2 * wzDyadicRadius levelZero ell) / delta)) ^ 3 ≤
          (ENNReal.ofReal delta).rpow (3 * theta) *
            (ENNReal.ofReal
              ((2 * wzDyadicRadius levelZero ell) / delta)) ^ 3 := by
      gcongr
    simpa only [mul_div_cancel₀ delta (by norm_num : (2 : ℝ) ≠ 0)] using
      hmono.trans hthree
  have hseparated' : ∀ a ∈ pruned, ∀ b ∈ pruned, a ≠ b →
      2 * (delta / 2) ≤ dist (direction a) (direction b) := by
    simpa only [mul_div_cancel₀ delta (by norm_num : (2 : ℝ) ≠ 0)] using
      hseparated
  have habsorb' : (125 : ENNReal) ≤
      (ENNReal.ofReal (2 * (delta / 2))).rpow (-eta) := by
    convert habsorb using 1 <;> ring
  have hgeometric' : ∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount
        (retainedWZCellSourceAtScales (2 * (delta / 2)) (delta / 2) pruned
          (fun _ => ∅) (by positivity) hseparated') U : ENNReal) ≤
        K * volume U := by
    simpa only [mul_div_cancel₀ delta (by norm_num : (2 : ℝ) ≠ 0)] using
      hgeometric
  have hnormalize' : K ≤
      (ENNReal.ofReal (2 * (delta / 2))).rpow (-eta) * pruned.card := by
    convert hnormalize using 1 <;> ring
  have hactive' : ∀ i,
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal (2 * (delta / 2))).rpow eta *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) (activeTime i) := by
    intro i
    convert hactive i using 1 <;> ring
  obtain ⟨shadingCells, hinput, hinflation⟩ :=
    exists_retained_wz_two_scale_finite_input_with_target_inflation
      pruned lowerCell
      (activeCarrierPruningThreshold
        (fun j : Fin (levelZero + 1) =>
          (8 * delta ^ (3 * theta - 3)) *
            (1 / 8 : ℝ) ^ j.val))
      eta (delta / 2) hpruned hcellPos htubeOne htubeDyadic
      hcellDyadic hterminal hlowerDiameter hlowerThreshold hvalid hseparated'
      habsorb' K hgeometric' hnormalize' activeTime hactive' target
      hactiveTarget
  refine ⟨shadingCells, ?_, ?_⟩
  · simpa only [mul_div_cancel₀ delta (by norm_num : (2 : ℝ) ≠ 0)] using
      hinput
  · simpa only [mul_div_cancel₀ delta (by norm_num : (2 : ℝ) ≠ 0)] using
      hinflation

/-- The Hausdorff cover layer, packing-three pruning, and the cubical WZ
assembly form one continuous finite-scale implication.  The active fibre is
not reselected after pruning: it is the literal fibre section of the same
physical target, restricted along `pruned ⊆ retained`.  Thus the only
remaining hypotheses in this implication are the convex-Wolff count and its
normalization, stated uniformly for the pruned subfamily produced by the
carrier argument. -/
theorem dyadic_cover_layer_pruning_assembles_wz_finite_input
    (selector : Set MarkedLine) (piece : Set (E4 × E4))
    (CAll carrierDim : ENNReal)
    (theta eta delta pointConstant : ℝ) (levelZero : ℕ)
    (retained : Finset MarkedLine) (target : Set E4)
    {mass : ENNReal}
    (hretainedNonempty : retained.Nonempty)
    (hretained : (↑retained : Set MarkedLine) ⊆
      selectorLinesOverCarrierPiece selector piece)
    (hCAllTop : CAll ≠ ⊤)
    (htheta : 0 < theta)
    (heta : 3 * theta ≤ eta)
    (hdeltaPos : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdelta : delta = ((((2 : ENNReal)⁻¹) ^ levelZero).toReal))
    (hcellDyadic : IsWZDyadicScale (delta / 2))
    (hpointLower : pointConstant * delta ^ (-3 + 2 * theta) ≤
      (retained.card : ℝ))
    (hcarrierDim : carrierDim.toReal ≤ 3 + theta / 4)
    (habsorbPruning :
      (4 * (((CAll.toReal * (4 : ℝ) ^ carrierDim.toReal + 1) * 8)) *
          (2 : ℝ) ^ (theta / 4) /
            ((2 : ℝ) ^ (theta / 4) - 1)) *
        delta ^ (3 * theta - theta / 4 - 2 * theta) ≤ pointConstant)
    (hcovering : ∀ r : ℝ, 0 < r → r ≤ 1 →
      coveringNumber piece r ≤
        CAll * (ENNReal.ofReal (r / 2)).rpow (-carrierDim.toReal))
    (hvalidRetained : ∀ line ∈ retained, IsValidLine line)
    (hseparatedRetained : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      delta ≤ dist (direction a) (direction b))
    (hactiveRetained : ∀ line ∈ retained,
      mass / 2 ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
          (markedLineSetFibreSet line target))
    (hactiveMass :
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal delta).rpow (3 * theta) *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤ mass / 2)
    (habsorbWZ : (125 : ENNReal) ≤
      (ENNReal.ofReal delta).rpow (-eta))
    (K : Finset MarkedLine → ENNReal)
    (hgeometric : ∀ (pruned : Finset MarkedLine),
      pruned.Nonempty → pruned ⊆ retained →
      retained.card ≤ 2 * pruned.card →
      ∀ hsep : ∀ a ∈ pruned, ∀ b ∈ pruned, a ≠ b →
          delta ≤ dist (direction a) (direction b),
        ∀ U : Set E4, Convex ℝ U →
          (wzContainedTubeCount
            (retainedWZCellSourceAtScales delta (delta / 2) pruned
              (fun _ => ∅) hdeltaPos hsep) U : ENNReal) ≤
            K pruned * volume U)
    (hnormalize : ∀ (pruned : Finset MarkedLine),
      pruned.Nonempty → pruned ⊆ retained →
      retained.card ≤ 2 * pruned.card →
        K pruned ≤ (ENNReal.ofReal delta).rpow (-eta) * pruned.card) :
    ∃ pruned : Finset MarkedLine,
      pruned.Nonempty ∧ pruned ⊆ retained ∧
      ∃ hsep : ∀ a ∈ pruned, ∀ b ∈ pruned, a ≠ b →
          delta ≤ dist (direction a) (direction b),
        ∃ shadingCells : MarkedLine → Finset (Fin 4 → ℤ),
          IsWangZakharovFiniteInput
            (retainedWZCellSourceAtScales delta (delta / 2) pruned
              shadingCells hdeltaPos hsep) eta ∧
          (⋃ i, (retainedWZCellSourceAtScales delta (delta / 2) pruned
            shadingCells hdeltaPos hsep).shading i) ⊆
              ⋃ y ∈ target, Metric.ball y delta := by
  obtain ⟨allCenters, cells, lowerCell, _hcellCount, _hcellMem,
      hlowerDiameter, pruned, hprunedSubset, hhalf, hterminal,
      _hmetricPopulation⟩ :=
    dyadic_cover_layer_has_packing_three_carrier_pruning
      selector piece CAll carrierDim theta delta pointConstant levelZero
      retained hretainedNonempty hretained hCAllTop htheta hdelta
      hpointLower hcarrierDim habsorbPruning hcovering
  have hprunedNonempty : pruned.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hprunedEmpty
    rw [hprunedEmpty, Finset.card_empty, Nat.mul_zero] at hhalf
    exact (Nat.not_succ_le_zero _)
      (hretainedNonempty.card_pos.trans_le hhalf)
  have hseparatedPruned : ∀ a ∈ pruned, ∀ b ∈ pruned, a ≠ b →
      delta ≤ dist (direction a) (direction b) := by
    intro a ha b hb hab
    exact hseparatedRetained a (hprunedSubset ha) b (hprunedSubset hb) hab
  have hdyadicReal : delta = (2 : ℝ)⁻¹ ^ levelZero := by
    rw [hdelta, ENNReal.toReal_pow]
    norm_num
  have hbase : ENNReal.ofReal delta ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hdeltaOne
  have hexponent :
      (ENNReal.ofReal delta).rpow eta ≤
        (ENNReal.ofReal delta).rpow (3 * theta) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hbase heta
  let activeTime : Fin pruned.card →
      Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    fun i => markedLineSetFibreSet (retainedIndex pruned i) target
  have hactive : ∀ i,
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal delta).rpow eta *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) (activeTime i) := by
    intro i
    calc
      (4 : ENNReal) *
            (8 * ((ENNReal.ofReal delta).rpow eta *
              (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤
          (4 : ENNReal) *
            (8 * ((ENNReal.ofReal delta).rpow (3 * theta) *
              (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) := by
        gcongr
      _ ≤ mass / 2 := hactiveMass
      _ ≤ (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) (activeTime i) := by
        exact hactiveRetained (retainedIndex pruned i)
          (hprunedSubset (retainedIndex_mem pruned i))
  have hactiveTarget : ∀ i t, t ∈ activeTime i →
      rawFrontParam (retainedIndex pruned i, (t : ℝ)) ∈ target := by
    intro i t ht
    simpa [activeTime, markedLineSetFibreSet, markedLineFibreFrontParam] using ht
  obtain ⟨shadingCells, hinput, hinflation⟩ :=
    packing_three_pruning_assembles_wz_finite_input
      levelZero theta eta delta pruned lowerCell hprunedNonempty hdeltaPos
      hdeltaOne heta hdyadicReal hcellDyadic hterminal
      (by
        intro ell a ha b hb heq
        exact hlowerDiameter ell b (hprunedSubset hb) a
          (hprunedSubset ha) heq)
      (fun line hline => hvalidRetained line (hprunedSubset hline))
      hseparatedPruned habsorbWZ (K pruned)
      (hgeometric pruned hprunedNonempty hprunedSubset hhalf hseparatedPruned)
      (hnormalize pruned hprunedNonempty hprunedSubset hhalf)
      activeTime hactive target hactiveTarget
  refine ⟨pruned, hprunedNonempty, hprunedSubset, hseparatedPruned,
    shadingCells, ?_, ?_⟩
  · simpa only using hinput
  · simpa only using hinflation

/-- Exact normalization bridge for the John-ellipsoid convex estimate.  The
geometric lemma gives the paper's coefficient
`Ccw * delta^(-2 * theta)` relative to the number of retained tubes.  The
Hausdorff layer gives the size exponent `-3 + 2 * theta`, and the pruning
keeps at least half of that family.  Once the fixed coefficient is absorbed
below the chosen cutoff, the result is precisely the convex-Wolff clause in
`IsWangZakharovFiniteInput`. -/
theorem half_pruned_family_has_normalized_convex_wolff_data
    (theta eta delta pointConstant : ℝ) (retained : Finset MarkedLine)
    (hdeltaPos : 0 < delta)
    (hvalidRetained : ∀ line ∈ retained, IsValidLine line)
    (hpointLower :
      pointConstant * delta ^ (-3 + 2 * theta) ≤
        (retained.card : ℝ))
    (Ccw : ENNReal)
    (hCcwAbsorb :
      Ccw * (ENNReal.ofReal delta).rpow (-2 * theta) ≤
        (ENNReal.ofReal delta).rpow (-eta))
    (hconvex : ∀ (pruned : Finset MarkedLine),
      pruned.Nonempty →
      (pointConstant / 2) * delta ^ (-3 + 2 * theta) ≤
        (pruned.card : ℝ) →
      (∀ line ∈ pruned, IsValidLine line) →
      ∀ hsep : ∀ a ∈ pruned, ∀ b ∈ pruned, a ≠ b →
          delta ≤ dist (direction a) (direction b),
        ∀ U : Set E4, Convex ℝ U →
          (wzContainedTubeCount
            (retainedWZCellSourceAtScales delta (delta / 2) pruned
              (fun _ => ∅) hdeltaPos hsep) U : ENNReal) ≤
            ((Ccw * (ENNReal.ofReal delta).rpow (-2 * theta)) *
              pruned.card) * volume U) :
    let K : Finset MarkedLine → ENNReal := fun pruned =>
      (Ccw * (ENNReal.ofReal delta).rpow (-2 * theta)) * pruned.card
    (∀ (pruned : Finset MarkedLine),
      pruned.Nonempty → pruned ⊆ retained →
      retained.card ≤ 2 * pruned.card →
      ∀ hsep : ∀ a ∈ pruned, ∀ b ∈ pruned, a ≠ b →
          delta ≤ dist (direction a) (direction b),
        ∀ U : Set E4, Convex ℝ U →
          (wzContainedTubeCount
            (retainedWZCellSourceAtScales delta (delta / 2) pruned
              (fun _ => ∅) hdeltaPos hsep) U : ENNReal) ≤
            K pruned * volume U) ∧
    (∀ (pruned : Finset MarkedLine),
      pruned.Nonempty → pruned ⊆ retained →
      retained.card ≤ 2 * pruned.card →
        K pruned ≤
          (ENNReal.ofReal delta).rpow (-eta) * pruned.card) := by
  dsimp only
  constructor
  · intro pruned hpruned hsubset hhalf hsep U hU
    have hhalfReal : (retained.card : ℝ) ≤ 2 * (pruned.card : ℝ) := by
      exact_mod_cast hhalf
    have hprunedLower :
        (pointConstant / 2) * delta ^ (-3 + 2 * theta) ≤
          (pruned.card : ℝ) := by
      nlinarith
    exact hconvex pruned hpruned hprunedLower
      (fun line hline => hvalidRetained line (hsubset hline)) hsep U hU
  · intro pruned _hpruned _hsubset _hhalf
    simpa [mul_comm] using
      (mul_le_mul_right hCcwAbsorb (pruned.card : ENNReal))

/-- Correct quantifier order for the packing-three carrier extraction.  The
Wang--Zakharov exponent is fixed first; only then do we choose the bookkeeping
loss and extract a positive carrier piece with the correspondingly smaller
upper-box slack.  In particular no single preselected piece is incorrectly
asked to work for every arbitrarily small WZ exponent. -/
theorem packing_selector_extract_piece_with_wz_compatible_slack
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ theta : ℝ, 0 < theta ∧ 4 * theta < eta ∧
      ∃ (k : ℤ) (piece : Set (E4 × E4)),
        MeasurableSet piece ∧
        piece ⊆ lineCarrier selector ∧
        piece ⊆ northCarrierRegion selector ∩
          carrierMarkedCenterBin selector hmeasurable hvalid hselector k ∧
        (selectorCarrierProbability selector hmeasurable hvalid hselector :
          Measure (E4 × E4)) piece ≠ 0 ∧
        ∃ carrierDim : ENNReal,
          carrierDim < 3 + ENNReal.ofReal (theta / 4) ∧
          carrierDim ≠ ⊤ ∧
          ∃ carrierCoverConstant : ENNReal,
            carrierCoverConstant ≠ ⊤ ∧
            ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              coveringNumber piece r ≤ carrierCoverConstant *
                (ENNReal.ofReal (r / 2)).rpow (-carrierDim.toReal) := by
  let theta : ℝ := eta / 8
  have htheta : 0 < theta := by
    dsimp [theta]
    positivity
  have hthetaEta : 4 * theta < eta := by
    dsimp [theta]
    linarith
  have hslack : 0 < ENNReal.ofReal (theta / 4) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨k, piece, hpieceMeasurable, hpieceCarrier, hpieceLocalized, hpieceMass,
      carrierDim, hcarrierDim, hcarrierDimTop, carrierCoverConstant,
      hcarrierCoverConstantTop, hcarrierCover⟩ :=
    packing_selector_extract_positive_measurable_north_center_piece
      selector hmeasurable hvalid hselector hpacking hslack
  exact ⟨theta, htheta, hthetaEta, k, piece, hpieceMeasurable,
    hpieceCarrier, hpieceLocalized, hpieceMass, carrierDim, hcarrierDim, hcarrierDimTop,
    carrierCoverConstant, hcarrierCoverConstantTop, hcarrierCover⟩

/-- The pure four-dimensional convex-geometric core of the Wolff estimate.
For a `delta`-separated family of marked unit tubes, the number of tubes
contained in a convex set is at most a universal multiple of
`delta⁻³ * volume U`.  No lower cardinality or subpower bookkeeping occurs
here.  This is exactly the output of the John-ellipsoid direction-cone
argument in the paper. -/
def HasSeparatedDirectionsConvexGeometricCount : Prop :=
  ∃ Cgeom : ENNReal, Cgeom ≠ ⊤ ∧
    ∀ (delta : ℝ) (pruned : Finset MarkedLine),
      (hdelta : 0 < delta) → delta ≤ 1 → pruned.Nonempty →
      (∀ line ∈ pruned, IsValidLine line) →
      ∀ hsep : ∀ a ∈ pruned, ∀ b ∈ pruned, a ≠ b →
          delta ≤ dist (direction a) (direction b),
        ∀ U : Set E4, Convex ℝ U →
          (wzContainedTubeCount
            (retainedWZCellSourceAtScales delta (delta / 2) pruned
              (fun _ => ∅) hdelta hsep) U : ENNReal) ≤
            (Cgeom * (ENNReal.ofReal delta).rpow (-3)) * volume U

/-- The ambient radial thickening of the directions of precisely those
source tubes which are contained in `U`.  Its centers stay indexed by the
source, so affine marks and multiplicities are not discarded. -/
noncomputable def wzContainedDirectionBallUnion {n : ℕ}
    (D : FiniteScaleSource n) (U : Set E4) (radius : ℝ) : Set E4 := by
  classical
  exact finiteDirectionBallUnion
    (Finset.univ.filter fun i =>
      markedUnitTube (D.line i) D.thickness ⊆ U)
    (fun i => direction (D.line i)) radius

/-- The affine mark is retained in the convex geometry: subtracting the two
actual marked endpoints realizes the line direction.  Hence a direction
ball of the same radius as a contained marked tube lies in the physical
difference body `U - U`. -/
theorem direction_ball_subset_difference_body_of_markedUnitTube_subset
    (line : MarkedLine) (U : Set E4) {radius : ℝ}
    (htube : markedUnitTube line radius ⊆ U) :
    Metric.ball (direction line) radius ⊆ U - U := by
  intro x hx
  let a : E4 := rawFrontParam (line, -(1 / 2 : ℝ))
  let b : E4 := rawFrontParam (line, 1 / 2)
  have hab : b - a = direction line := by
    rcases line with ⟨⟨theta, omega⟩, tau⟩
    simp [a, b, rawFrontParam]
    module
  have hradius : 0 < radius :=
    lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hx)
  have haTube : a ∈ markedUnitTube line radius := by
    apply ball_rawFrontParam_subset_markedUnitTube line
      (t := -(1 / 2 : ℝ)) (delta := radius) (by norm_num)
    simp [a, hradius]
  have haxBall : a + x ∈ Metric.ball b radius := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : a + x - b = x - direction line := by
      rw [← hab]
      module
    rw [hdiff]
    simpa [dist_eq_norm] using hx
  have haxTube : a + x ∈ markedUnitTube line radius :=
    ball_rawFrontParam_subset_markedUnitTube line
      (t := (1 / 2 : ℝ)) (delta := radius) (by norm_num) haxBall
  have haU : a ∈ U := htube haTube
  have haxU : a + x ∈ U := htube haxTube
  change ∃ y ∈ U, ∃ z ∈ U, y - z = x
  exact ⟨a + x, haxU, a, haU, by module⟩

/-- All contained-tube direction balls of radius no larger than the tube
thickness lie in one common difference body. -/
theorem wzContainedDirectionBallUnion_subset_difference_body
    {n : ℕ} (D : FiniteScaleSource n) (U : Set E4) (radius : ℝ)
    (hradius : radius ≤ D.thickness) :
    wzContainedDirectionBallUnion D U radius ⊆ U - U := by
  classical
  intro x hx
  rw [wzContainedDirectionBallUnion, finiteDirectionBallUnion] at hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hi, hx⟩
  exact direction_ball_subset_difference_body_of_markedUnitTube_subset
    (D.line i) U (Finset.mem_filter.mp hi).2
    (Metric.mem_ball.mpr ((Metric.mem_ball.mp hx).trans_le hradius))

/-- A separated contained-tube family contributes exactly one disjoint
ambient half-scale ball per contained tube.  This is the rigorous
codimension-one packing step behind the John-ellipsoid argument: the later
shell estimate only has to bound the volume of the displayed union. -/
theorem volume_wzContainedDirectionBallUnion_of_separated
    {n : ℕ} (D : FiniteScaleSource n) (U : Set E4)
    {delta : ℝ} (hdelta : 0 < delta)
    (hsep : ∀ i j, i ≠ j →
      delta ≤ dist (direction (D.line i)) (direction (D.line j))) :
    volume (wzContainedDirectionBallUnion D U (delta / 2)) =
      (wzContainedTubeCount D U : ENNReal) *
        ((ENNReal.ofReal delta) ^ 4 *
          volume (Metric.ball (0 : E4) (1 / 2))) := by
  classical
  rw [wzContainedDirectionBallUnion,
    volume_finiteDirectionBallUnion_of_separated]
  · rw [volume_ball_zero_half_scale hdelta]
    rfl
  · intro i hi j hj hij
    simpa only [two_mul, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      hsep i j hij

/-- A finite union of radius-`r` balls centered on the unit sphere lies in
the open radial shell `1-r < ‖x‖ < 1+r`.  This records the radial geometry
that turns repeated homothetic copies into disjoint shells. -/
theorem finiteDirectionBallUnion_norm_bounds
    {alpha : Type*} (s : Finset alpha) (center : alpha → E4)
    (radius : ℝ)
    (hunit : ∀ a ∈ s, ‖center a‖ = 1)
    {x : E4} (hx : x ∈ finiteDirectionBallUnion s center radius) :
    1 - radius < ‖x‖ ∧ ‖x‖ < 1 + radius := by
  classical
  rw [finiteDirectionBallUnion] at hx
  rcases Set.mem_iUnion.mp hx with ⟨a, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨ha, hx⟩
  have hdist : dist x (center a) < radius := Metric.mem_ball.mp hx
  have hlower : 1 - ‖x‖ ≤ dist x (center a) := by
    rw [dist_eq_norm]
    simpa [hunit a ha, norm_sub_rev] using norm_sub_norm_le (center a) x
  have hupper : ‖x‖ - 1 ≤ dist x (center a) := by
    rw [dist_eq_norm]
    simpa [hunit a ha] using norm_sub_norm_le x (center a)
  constructor <;> linarith

/-- Finite ambient direction-ball unions are measurable. -/
theorem measurableSet_finiteDirectionBallUnion
    {alpha : Type*} (s : Finset alpha) (center : alpha → E4)
    (radius : ℝ) :
    MeasurableSet (finiteDirectionBallUnion s center radius) := by
  classical
  unfold finiteDirectionBallUnion
  exact Finset.measurableSet_biUnion s (fun _ _ => measurableSet_ball)

/-- Positive homothetic copies of a radial shell are pairwise disjoint once
the outer radius of each earlier copy is below the inner radius of the next.
This is the exact disjointness mechanism in the radial sweep. -/
theorem pairwiseDisjoint_smul_of_radial_shell
    (A : Set E4) (low high : ℝ)
    (hnorm : ∀ x ∈ A, low < ‖x‖ ∧ ‖x‖ < high)
    (scales : Finset ℝ)
    (hpos : ∀ t ∈ scales, 0 < t)
    (hsep : ∀ a ∈ scales, ∀ b ∈ scales, a < b →
      a * high ≤ b * low) :
    Set.Pairwise (scales : Set ℝ)
      (fun a b => Disjoint (a • A) (b • A)) := by
  intro a ha b hb hab
  rw [Set.disjoint_left]
  intro x hxa hxb
  rcases Set.mem_smul_set.mp hxa with ⟨y, hy, hay⟩
  rcases Set.mem_smul_set.mp hxb with ⟨z, hz, hbz⟩
  have haPos := hpos a ha
  have hbPos := hpos b hb
  have hnormEq : a * ‖y‖ = b * ‖z‖ := by
    calc
      a * ‖y‖ = ‖a • y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos haPos]
      _ = ‖x‖ := congrArg norm hay
      _ = ‖b • z‖ := (congrArg norm hbz).symm
      _ = b * ‖z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hbPos]
  rcases lt_or_gt_of_ne hab with hab' | hba'
  · have hsep' := hsep a ha b hb hab'
    have hayHigh : a * ‖y‖ < a * high :=
      mul_lt_mul_of_pos_left (hnorm y hy).2 haPos
    have hbLow : b * low < b * ‖z‖ :=
      mul_lt_mul_of_pos_left (hnorm z hz).1 hbPos
    linarith
  · have hsep' := hsep b hb a ha hba'
    have hbzHigh : b * ‖z‖ < b * high :=
      mul_lt_mul_of_pos_left (hnorm z hz).2 hbPos
    have haLow : a * low < a * ‖y‖ :=
      mul_lt_mul_of_pos_left (hnorm y hy).1 haPos
    linarith

/-- Exact four-dimensional volume of the finite radial sweep.  No boundary
error is present: the strict radial-shell bounds make the homothetic copies
literally disjoint. -/
theorem volume_biUnion_smul_of_radial_shell
    (A : Set E4) (low high : ℝ)
    (hnorm : ∀ x ∈ A, low < ‖x‖ ∧ ‖x‖ < high)
    (hA : MeasurableSet A)
    (scales : Finset ℝ)
    (hpos : ∀ t ∈ scales, 0 < t)
    (hsep : ∀ a ∈ scales, ∀ b ∈ scales, a < b →
      a * high ≤ b * low) :
    volume (⋃ t ∈ scales, t • A) =
      ∑ t ∈ scales, ENNReal.ofReal (t ^ 4) * volume A := by
  have hdisjoint := pairwiseDisjoint_smul_of_radial_shell
    A low high hnorm scales hpos hsep
  rw [measure_biUnion_finset hdisjoint
    (fun t ht => hA.const_smul_of_ne_zero (hpos t ht).ne')]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Measure.addHaar_smul_of_nonneg volume (hpos t ht).le]
  simp

/-- If `A` lies in a convex body containing the origin, then every radial
copy `t • A`, `0 ≤ t ≤ 1`, remains in that body.  Applied to `U-U`, this
places the whole disjoint radial sweep in one physical difference body. -/
theorem biUnion_smul_subset_convex
    (A B : Set E4) (hA : A ⊆ B) (hB : Convex ℝ B)
    (hzero : (0 : E4) ∈ B) (scales : Finset ℝ)
    (hscale : ∀ t ∈ scales, t ∈ Set.Icc (0 : ℝ) 1) :
    (⋃ t ∈ scales, t • A) ⊆ B := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨t, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨ht, hx⟩
  rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
  exact hB.smul_mem_of_zero_mem hzero (hA hy) (hscale t ht)

/-- Quantitative radial-sweep packing.  Each admissible scale contributes
at least `c^4 * volume A`; pairwise radial separation makes the contributions
disjoint, and convexity keeps their union inside `B`. -/
theorem card_mul_volume_le_of_radial_shell_scales
    (A B : Set E4) (low high c : ℝ)
    (hnorm : ∀ x ∈ A, low < ‖x‖ ∧ ‖x‖ < high)
    (hAmeas : MeasurableSet A) (hAB : A ⊆ B)
    (hB : Convex ℝ B) (hzero : (0 : E4) ∈ B)
    (scales : Finset ℝ)
    (hpos : ∀ t ∈ scales, 0 < t)
    (hleone : ∀ t ∈ scales, t ≤ 1)
    (hc : 0 ≤ c) (hcscale : ∀ t ∈ scales, c ≤ t)
    (hsep : ∀ a ∈ scales, ∀ b ∈ scales, a < b →
      a * high ≤ b * low) :
    (scales.card : ENNReal) *
        (ENNReal.ofReal (c ^ 4) * volume A) ≤ volume B := by
  have hvol := volume_biUnion_smul_of_radial_shell
    A low high hnorm hAmeas scales hpos hsep
  have hsubset := biUnion_smul_subset_convex
    A B hAB hB hzero scales (fun t ht => ⟨(hpos t ht).le, hleone t ht⟩)
  calc
    (scales.card : ENNReal) *
        (ENNReal.ofReal (c ^ 4) * volume A) =
        ∑ _t ∈ scales, ENNReal.ofReal (c ^ 4) * volume A := by simp
    _ ≤ ∑ t ∈ scales, ENNReal.ofReal (t ^ 4) * volume A := by
      apply Finset.sum_le_sum
      intro t ht
      gcongr
      exact hcscale t ht
    _ = volume (⋃ t ∈ scales, t • A) := hvol.symm
    _ ≤ volume B := measure_mono hsubset

/-- The abstract radial sweep applied to the actual marked tubes.  The
affine-fibre endpoint argument places the direction-ball union in `U-U`;
the present theorem then packs every admissible radial copy inside that
single convex difference body. -/
theorem card_mul_contained_direction_volume_le_difference_body
    {n : ℕ} (D : FiniteScaleSource n) (U : Set E4) (radius c : ℝ)
    (hvalid : ∀ i, IsValidLine (D.line i))
    (hU : Convex ℝ U)
    (hradius : radius ≤ D.thickness)
    (scales : Finset ℝ)
    (hpos : ∀ t ∈ scales, 0 < t)
    (hleone : ∀ t ∈ scales, t ≤ 1)
    (hc : 0 ≤ c) (hcscale : ∀ t ∈ scales, c ≤ t)
    (hsep : ∀ a ∈ scales, ∀ b ∈ scales, a < b →
      a * (1 + radius) ≤ b * (1 - radius)) :
    (scales.card : ENNReal) *
        (ENNReal.ofReal (c ^ 4) *
          volume (wzContainedDirectionBallUnion D U radius)) ≤
      volume (U - U) := by
  classical
  let A := wzContainedDirectionBallUnion D U radius
  have hAmeas : MeasurableSet A := by
    dsimp [A, wzContainedDirectionBallUnion]
    exact measurableSet_finiteDirectionBallUnion _ _ _
  have hnorm : ∀ x ∈ A, 1 - radius < ‖x‖ ∧ ‖x‖ < 1 + radius := by
    intro x hx
    apply finiteDirectionBallUnion_norm_bounds
      (Finset.univ.filter fun i =>
        markedUnitTube (D.line i) D.thickness ⊆ U)
      (fun i => direction (D.line i)) radius
    · intro i hi
      exact (hvalid i).1
    · exact hx
  have hAB : A ⊆ U - U :=
    wzContainedDirectionBallUnion_subset_difference_body D U radius hradius
  by_cases hAempty : A = ∅
  · change (scales.card : ENNReal) *
        (ENNReal.ofReal (c ^ 4) * volume A) ≤ volume (U - U)
    rw [hAempty, measure_empty]
    simp
  · have hAnonempty : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hAempty
    rcases hAnonempty with ⟨x, hx⟩
    have hxB := hAB hx
    change ∃ y ∈ U, ∃ z ∈ U, y - z = x at hxB
    rcases hxB with ⟨y, hy, z, hz, hyz⟩
    have hzero : (0 : E4) ∈ U - U := by
      change ∃ y' ∈ U, ∃ z' ∈ U, y' - z' = 0
      exact ⟨y, hy, y, hy, sub_self y⟩
    exact card_mul_volume_le_of_radial_shell_scales
      A (U - U) (1 - radius) (1 + radius) c hnorm hAmeas hAB
      (hU.sub hU) hzero scales hpos hleone hc hcscale hsep

/-- Explicit arithmetic progression of radial scales.  For small `delta`
it contains order `delta⁻¹` points between `1/2` and `1-delta/2`. -/
noncomputable def radialShellScales (delta : ℝ) : Finset ℝ :=
  (Finset.range (⌊(1 / (2 * delta) - 1 / 2 : ℝ)⌋₊ + 1)).image
    (fun k : ℕ => 1 / 2 + (k : ℝ) * delta)

theorem radialShellScales_card (delta : ℝ) (hdelta : 0 < delta) :
    (radialShellScales delta).card =
      ⌊(1 / (2 * delta) - 1 / 2 : ℝ)⌋₊ + 1 := by
  classical
  rw [radialShellScales, Finset.card_image_of_injective]
  · simp
  · intro k l hkl
    have hcast : (k : ℝ) = (l : ℝ) := by
      nlinarith
    exact_mod_cast hcast

theorem radialShellScales_mem_bounds
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    {t : ℝ} (ht : t ∈ radialShellScales delta) :
    0 < t ∧ 1 / 2 ≤ t ∧ t ≤ 1 - delta / 2 := by
  classical
  rw [radialShellScales, Finset.mem_image] at ht
  rcases ht with ⟨k, hk, rfl⟩
  have hklt : k < ⌊(1 / (2 * delta) - 1 / 2 : ℝ)⌋₊ + 1 :=
    Finset.mem_range.mp hk
  have hkfloor : k ≤ ⌊(1 / (2 * delta) - 1 / 2 : ℝ)⌋₊ :=
    Nat.lt_succ_iff.mp hklt
  have htwoDelta : 0 < 2 * delta := by positivity
  have hfrac : 1 ≤ 1 / (2 * delta) := by
    rw [le_div_iff₀ htwoDelta]
    nlinarith
  have hq : 0 ≤ 1 / (2 * delta) - 1 / 2 := by linarith
  have hkcast : (k : ℝ) ≤ 1 / (2 * delta) - 1 / 2 := by
    calc
      (k : ℝ) ≤ (⌊(1 / (2 * delta) - 1 / 2 : ℝ)⌋₊ : ℝ) := by
        exact_mod_cast hkfloor
      _ ≤ 1 / (2 * delta) - 1 / 2 := Nat.floor_le hq
  have hkmul : (k : ℝ) * delta ≤
      (1 / (2 * delta) - 1 / 2) * delta :=
    mul_le_mul_of_nonneg_right hkcast hdelta.le
  constructor
  · positivity
  constructor
  · have hkNonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hmulNonneg : 0 ≤ (k : ℝ) * delta :=
      mul_nonneg hkNonneg hdelta.le
    norm_num
    positivity
  · field_simp [ne_of_gt hdelta] at hkmul ⊢
    nlinarith

theorem radialShellScales_separated
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2) :
    ∀ a ∈ radialShellScales delta,
      ∀ b ∈ radialShellScales delta, a < b →
        a * (1 + delta / 2) ≤ b * (1 - delta / 2) := by
  classical
  intro a ha b hb hab
  rw [radialShellScales, Finset.mem_image] at ha hb
  rcases ha with ⟨k, hk, rfl⟩
  rcases hb with ⟨l, hl, rfl⟩
  have hklCast : (k : ℝ) < (l : ℝ) := by
    nlinarith
  have hkl : k < l := by exact_mod_cast hklCast
  have hklOne : (k : ℝ) + 1 ≤ (l : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hkl)
  have hbge : 1 / 2 + (k : ℝ) * delta + delta ≤
      1 / 2 + (l : ℝ) * delta := by
    have := mul_le_mul_of_nonneg_right hklOne hdelta.le
    nlinarith
  have haupper := radialShellScales_mem_bounds hdelta hdeltaHalf
    (show 1 / 2 + (k : ℝ) * delta ∈ radialShellScales delta by
      rw [radialShellScales, Finset.mem_image]
      exact ⟨k, hk, rfl⟩)
  have hnonneg : 0 ≤ 1 - delta / 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hbge hnonneg
  nlinarith [hmul, haupper.2.2]

theorem radialShellScales_card_lower
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2) :
    ENNReal.ofReal (1 / (4 * delta)) ≤
      ((radialShellScales delta).card : ENNReal) := by
  have htwoDelta : 0 < 2 * delta := by positivity
  have hfrac : 1 ≤ 1 / (2 * delta) := by
    rw [le_div_iff₀ htwoDelta]
    nlinarith
  have hq : 0 ≤ 1 / (2 * delta) - 1 / 2 := by linarith
  have hquarter : 1 / (4 * delta) ≤ 1 / (2 * delta) - 1 / 2 := by
    field_simp [ne_of_gt hdelta]
    nlinarith
  have hlt : 1 / (2 * delta) - 1 / 2 <
      (⌊(1 / (2 * delta) - 1 / 2 : ℝ)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [radialShellScales_card delta hdelta]
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  norm_num at hlt ⊢
  linarith

/-- For `delta ≤ 1/2`, the explicit radial sweep recovers the missing
shell thickness: the contained-direction union has volume at most
`64 * delta` times the volume of the physical difference body. -/
theorem small_delta_contained_direction_volume_le_difference_body
    {n : ℕ} (D : FiniteScaleSource n) (U : Set E4) {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hvalid : ∀ i, IsValidLine (D.line i))
    (hU : Convex ℝ U) (hradius : delta / 2 ≤ D.thickness) :
    volume (wzContainedDirectionBallUnion D U (delta / 2)) ≤
      ENNReal.ofReal (64 * delta) * volume (U - U) := by
  let A : ENNReal :=
    volume (wzContainedDirectionBallUnion D U (delta / 2))
  let B : ENNReal := volume (U - U)
  let alpha : ENNReal := ENNReal.ofReal (1 / (64 * delta))
  have hpack := card_mul_contained_direction_volume_le_difference_body
    D U (delta / 2) (1 / 2) hvalid hU hradius
    (radialShellScales delta)
    (fun t ht => (radialShellScales_mem_bounds hdelta hdeltaHalf ht).1)
    (fun t ht =>
      (radialShellScales_mem_bounds hdelta hdeltaHalf ht).2.2.trans
        (by linarith))
    (by norm_num)
    (fun t ht => (radialShellScales_mem_bounds hdelta hdeltaHalf ht).2.1)
    (radialShellScales_separated hdelta hdeltaHalf)
  have hcard := radialShellScales_card_lower hdelta hdeltaHalf
  have hcoeff : alpha * A ≤ B := by
    calc
      alpha * A =
          ENNReal.ofReal (1 / (4 * delta)) *
            (ENNReal.ofReal ((1 / 2 : ℝ) ^ 4) * A) := by
        dsimp [alpha]
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp [ne_of_gt hdelta]
        ring
      _ ≤ ((radialShellScales delta).card : ENNReal) *
            (ENNReal.ofReal ((1 / 2 : ℝ) ^ 4) * A) := by
        gcongr
      _ ≤ B := by simpa [A, B] using hpack
  have halphaPos : 0 < alpha := by
    dsimp [alpha]
    positivity
  have halphaZero : alpha ≠ 0 := ne_of_gt halphaPos
  have halphaTop : alpha ≠ ⊤ := by
    dsimp [alpha]
    exact ENNReal.ofReal_ne_top
  calc
    volume (wzContainedDirectionBallUnion D U (delta / 2)) = A := rfl
    _ = alpha⁻¹ * (alpha * A) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel halphaZero halphaTop, one_mul]
    _ ≤ alpha⁻¹ * B := by gcongr
    _ = ENNReal.ofReal (64 * delta) * volume (U - U) := by
      congr 1
      dsimp [alpha]
      rw [← ENNReal.ofReal_inv_of_pos
        (show 0 < 1 / (64 * delta) by positivity)]
      congr 1
      field_simp [ne_of_gt hdelta]

/-- Incidence set whose right sections are the covariogram slices
`K ∩ (x +ᵥ K)`. -/
def differenceIncidenceSet (K : Set E4) : Set (E4 × E4) :=
  {p | p.1 ∈ K ∧ p.1 - p.2 ∈ K}

theorem measurableSet_differenceIncidenceSet
    {K : Set E4} (hK : MeasurableSet K) :
    MeasurableSet (differenceIncidenceSet K) := by
  exact (hK.preimage measurable_fst).inter
    (hK.preimage (measurable_fst.sub measurable_snd))

theorem differenceIncidenceSet_rightSection
    (K : Set E4) (x : E4) :
    (fun y => (y, x)) ⁻¹' differenceIncidenceSet K =
      K ∩ (x +ᵥ K) := by
  ext y
  constructor
  · intro hy
    refine ⟨hy.1, ?_⟩
    refine ⟨y - x, hy.2, ?_⟩
    change x + (y - x) = y
    abel
  · rintro ⟨hyK, z, hzK, hzx⟩
    refine ⟨hyK, ?_⟩
    have : y - x = z := by
      change x +ᵥ z = y at hzx
      rw [vadd_eq_add] at hzx
      rw [← hzx]
      abel
    rwa [this]

theorem differenceIncidenceSet_preimage_prod
    (K : Set E4) :
    differenceIncidenceSet K =
      (fun p : E4 × E4 => (p.1, p.2 - p.1)) ⁻¹' (K ×ˢ (-K)) := by
  ext p
  simp only [differenceIncidenceSet, mem_setOf_eq, mem_preimage, mem_prod,
    Prod.fst, Prod.snd]
  constructor
  · rintro ⟨hpK, hdiffK⟩
    refine ⟨hpK, ?_⟩
    rw [Set.mem_neg]
    simpa only [neg_sub] using hdiffK
  · rintro ⟨hpK, hneg⟩
    refine ⟨hpK, ?_⟩
    rw [Set.mem_neg] at hneg
    simpa only [neg_sub] using hneg

theorem volume_neg_eq (K : Set E4) (hK : MeasurableSet K) :
    volume (-K) = volume K := by
  have h := (Measure.measurePreserving_neg volume).measure_preimage
    hK.nullMeasurableSet
  have hpre : Neg.neg ⁻¹' K = -K := by
    ext x
    simp [Set.mem_neg]
  rwa [hpre] at h

theorem volume_differenceIncidenceSet
    (K : Set E4) (hK : MeasurableSet K) :
    (volume.prod volume) (differenceIncidenceSet K) =
      volume K * volume K := by
  rw [differenceIncidenceSet_preimage_prod]
  calc
    (volume.prod volume)
        ((fun p : E4 × E4 => (p.1, p.2 - p.1)) ⁻¹' (K ×ˢ (-K))) =
        (volume.prod volume) (K ×ˢ (-K)) :=
      (measurePreserving_prod_sub volume volume).measure_preimage
        ((hK.prod (hK.neg)).nullMeasurableSet)
    _ = volume K * volume (-K) := Measure.prod_prod K (-K)
    _ = volume K * volume K := by rw [volume_neg_eq K hK]

/-- The integral of the covariogram is the square of the volume. -/
theorem lintegral_convex_covariogram
    (K : Set E4) (hK : MeasurableSet K) :
    (∫⁻ (x : E4), volume (K ∩ (x +ᵥ K))) = volume K * volume K := by
  rw [← volume_differenceIncidenceSet K hK,
    Measure.prod_apply_symm (measurableSet_differenceIncidenceSet hK)]
  apply lintegral_congr
  intro x
  rw [differenceIncidenceSet_rightSection]

/-- If `x` lies in the half difference body, convexity places a half-scale
copy of `K` inside the covariogram slice at `x`. -/
theorem half_differenceBody_covariogram_lower
    (K : Set E4) (hK : Convex ℝ K) {x : E4}
    (hx : x ∈ (1 / 2 : ℝ) • (K - K)) :
    ENNReal.ofReal ((1 / 2 : ℝ) ^ 4) * volume K ≤
      volume (K ∩ (x +ᵥ K)) := by
  rcases Set.mem_smul_set.mp hx with ⟨d, hd, rfl⟩
  change ∃ a ∈ K, ∃ b ∈ K, a - b = d at hd
  obtain ⟨a, ha, b, hb, rfl⟩ := hd
  let A : Set E4 := ((1 / 2 : ℝ) • a) +ᵥ ((1 / 2 : ℝ) • K)
  have hAsub : A ⊆ K ∩ (((1 / 2 : ℝ) • (a - b)) +ᵥ K) := by
    rintro y ⟨w, hw, rfl⟩
    rcases Set.mem_smul_set.mp hw with ⟨z, hz, rfl⟩
    have hay : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • z ∈ K :=
      hK ha hz (by norm_num) (by norm_num) (by norm_num)
    have hby : (1 / 2 : ℝ) • b + (1 / 2 : ℝ) • z ∈ K :=
      hK hb hz (by norm_num) (by norm_num) (by norm_num)
    refine ⟨?_, ?_⟩
    · simpa only [vadd_eq_add] using hay
    · refine ⟨(1 / 2 : ℝ) • b + (1 / 2 : ℝ) • z, hby, ?_⟩
      change (1 / 2 : ℝ) • (a - b) +
          ((1 / 2 : ℝ) • b + (1 / 2 : ℝ) • z) =
        (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • z
      module
  calc
    ENNReal.ofReal ((1 / 2 : ℝ) ^ 4) * volume K = volume A := by
      dsimp [A]
      rw [measure_vadd,
        Measure.addHaar_smul_of_nonneg volume
          (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      simp
    _ ≤ volume (K ∩ (((1 / 2 : ℝ) • (a - b)) +ᵥ K)) :=
      measure_mono hAsub

theorem measurable_convex_covariogram
    (K : Set E4) (hK : MeasurableSet K) :
    Measurable fun x : E4 => volume (K ∩ (x +ᵥ K)) := by
  have h : Measurable fun x : E4 =>
      volume ((fun y : E4 => (y, x)) ⁻¹' differenceIncidenceSet K) :=
    measurable_measure_prodMk_right (measurableSet_differenceIncidenceSet hK)
  convert h using 1
  funext x
  rw [differenceIncidenceSet_rightSection]

/-- A self-contained four-dimensional difference-body bound for compact
positive-volume convex sets.  The constant `256` comes from applying the
half-scale covariogram lower bound on the half difference body. -/
theorem compact_convex_difference_body_volume_le
    (K : Set E4) (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (hvolume : volume K ≠ 0) :
    volume (K - K) ≤ ENNReal.ofReal 256 * volume K := by
  let c : ENNReal := ENNReal.ofReal ((1 / 2 : ℝ) ^ 4)
  let H : Set E4 := (1 / 2 : ℝ) • (K - K)
  have hKmeas : MeasurableSet K := hcompact.measurableSet
  have hHcompact : IsCompact H := by
    have hdiff : IsCompact (K - K) := by
      simpa [sub_eq_add_neg] using hcompact.add hcompact.neg
    exact hdiff.smul (1 / 2 : ℝ)
  have hHmeas : MeasurableSet H := hHcompact.measurableSet
  have hpoint : ∀ x ∈ H,
      c * volume K ≤ volume (K ∩ (x +ᵥ K)) := by
    intro x hx
    exact half_differenceBody_covariogram_lower K hconvex hx
  have hintegral :
      c * volume K * volume H ≤
        ∫⁻ (x : E4), volume (K ∩ (x +ᵥ K)) := by
    calc
      c * volume K * volume H =
          ∫⁻ (x : E4), H.indicator (fun _ => c * volume K) x := by
        rw [lintegral_indicator_const hHmeas]
      _ ≤ ∫⁻ (x : E4), volume (K ∩ (x +ᵥ K)) := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ H
        · simpa [Set.indicator_of_mem hx] using hpoint x hx
        · simp [hx]
  have hHvolume : volume H = c * volume (K - K) := by
    dsimp [H, c]
    rw [Measure.addHaar_smul_of_nonneg volume
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simp
  have hraw :
      ((c * c) * volume (K - K)) * volume K ≤
        volume K * volume K := by
    calc
      ((c * c) * volume (K - K)) * volume K =
          c * volume K * volume H := by
        rw [hHvolume]
        ring
      _ ≤ ∫⁻ (x : E4), volume (K ∩ (x +ᵥ K)) := hintegral
      _ = volume K * volume K := lintegral_convex_covariogram K hKmeas
  have hvolumeTop : volume K ≠ ⊤ := hcompact.measure_lt_top.ne
  have hraw' :
      volume K * ((c * c) * volume (K - K)) ≤ volume K * volume K := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hraw
  have hcancelK : (c * c) * volume (K - K) ≤ volume K :=
    (ENNReal.mul_le_mul_iff_right hvolume hvolumeTop).1 hraw'
  have hcNorm : ENNReal.ofReal 256 * (c * c) = 1 := by
    dsimp [c]
    norm_num
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 16)]
    rw [show (256 : ENNReal) = ENNReal.ofReal (256 : ℝ) by norm_num]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 256)]
    norm_num
  calc
    volume (K - K) = 1 * volume (K - K) := by simp
    _ = ENNReal.ofReal 256 * ((c * c) * volume (K - K)) := by
      rw [← mul_assoc, hcNorm, one_mul]
    _ ≤ ENNReal.ofReal 256 * volume K := by gcongr

/-- The compact bound extends to every positive-volume convex set by
increasing compact convex truncations.  Convex boundaries are Haar-null, so
closing each truncation does not change its volume. -/
theorem convex_difference_body_volume_le
    (U : Set E4) (hconvex : Convex ℝ U) (hvolume : volume U ≠ 0) :
    volume (U - U) ≤ ENNReal.ofReal 256 * volume U := by
  have hinterior : (interior U).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hsubset : U ⊆ frontier U := by
      intro y hy
      rw [frontier, hempty]
      exact ⟨subset_closure hy, by simp⟩
    exact hvolume (measure_mono_null hsubset (hconvex.addHaar_frontier volume))
  obtain ⟨x, hx⟩ := hinterior
  have hnhds : U ∈ nhds x := mem_interior_iff_mem_nhds.mp hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let K : ℕ → Set E4 := fun n =>
    closure (U ∩ Metric.closedBall x (r + n))
  have hKcompact : ∀ n, IsCompact (K n) := by
    intro n
    apply Metric.isCompact_of_isClosed_isBounded isClosed_closure
    exact (Metric.isBounded_closedBall.subset inter_subset_right).closure
  have hKconvex : ∀ n, Convex ℝ (K n) := by
    intro n
    exact (hconvex.inter (convex_closedBall x (r + n))).closure
  have hKmono : Monotone K := by
    intro n m hnm
    apply closure_mono
    have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    exact inter_subset_inter_right _
      (Metric.closedBall_subset_closedBall (add_le_add_right hnm' r))
  have hKvolume : ∀ n, volume (K n) ≤ volume U := by
    intro n
    calc
      volume (K n) = volume (U ∩ Metric.closedBall x (r + n)) := by
        exact measure_closure_of_null_frontier
          ((hconvex.inter (convex_closedBall x (r + n))).addHaar_frontier volume)
      _ ≤ volume U := measure_mono inter_subset_left
  have hKpositive : ∀ n, volume (K n) ≠ 0 := by
    intro n
    have hsmallBall : Metric.ball x (r / 2) ⊆ K n := by
      intro y hy
      apply subset_closure
      constructor
      · exact hball (Metric.ball_subset_ball (by linarith) hy)
      · rw [Metric.mem_closedBall]
        have hyn : dist y x < r / 2 := by simpa [dist_comm] using hy
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
    have hballPos : 0 < volume (Metric.ball x (r / 2)) := by
      rw [InnerProductSpace.volume_ball]
      positivity
    exact ne_of_gt (hballPos.trans_le (measure_mono hsmallBall))
  have hbodyBound : ∀ n,
      volume (K n - K n) ≤ ENNReal.ofReal 256 * volume U := by
    intro n
    exact (compact_convex_difference_body_volume_le
      (K n) (hKcompact n) (hKconvex n) (hKpositive n)).trans
        (mul_le_mul_right (hKvolume n) (ENNReal.ofReal 256))
  have hbodyMono : Monotone (fun n => K n - K n) := by
    intro n m hnm z hz
    rcases hz with ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, hKmono hnm ha, b, hKmono hnm hb, rfl⟩
  have hcover : U - U ⊆ ⋃ n : ℕ, K n - K n := by
    intro z hz
    rcases hz with ⟨a, ha, b, hb, rfl⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (max (dist a x) (dist b x))
    have haBall : a ∈ Metric.closedBall x (r + n) := by
      rw [Metric.mem_closedBall]
      have han : dist a x < (n : ℝ) := (le_max_left _ _).trans_lt hn
      have hnle : (n : ℝ) ≤ r + n := by linarith
      simpa [dist_comm] using han.le.trans hnle
    have hbBall : b ∈ Metric.closedBall x (r + n) := by
      rw [Metric.mem_closedBall]
      have hbn : dist b x < (n : ℝ) := (le_max_right _ _).trans_lt hn
      have hnle : (n : ℝ) ≤ r + n := by linarith
      simpa [dist_comm] using hbn.le.trans hnle
    apply mem_iUnion.2
    exact ⟨n, a, subset_closure ⟨ha, haBall⟩,
      b, subset_closure ⟨hb, hbBall⟩, rfl⟩
  calc
    volume (U - U) ≤ volume (⋃ n : ℕ, K n - K n) := measure_mono hcover
    _ = ⨆ n : ℕ, volume (K n - K n) := hbodyMono.measure_iUnion
    _ ≤ ENNReal.ofReal 256 * volume U := iSup_le hbodyBound

/-- Four-dimensional Rogers--Shephard-type input in the exact form needed
below.  Only the positive-volume case is requested; the empty contained-tube
branch is discharged separately in the shell theorem. -/
def HasConvexDifferenceBodyVolumeEstimate : Prop :=
  ∃ Cdiff : ENNReal, Cdiff ≠ ⊤ ∧
    ∀ U : Set E4, Convex ℝ U → volume U ≠ 0 →
      volume (U - U) ≤ Cdiff * volume U

theorem convex_difference_body_volume_estimate :
    HasConvexDifferenceBodyVolumeEstimate := by
  exact ⟨ENNReal.ofReal 256, ENNReal.ofReal_ne_top,
    convex_difference_body_volume_le⟩

/-- Exact remaining geometric input after the disjoint-ball packing has
been proved: the radial shell swept out by directions of tubes contained in
a convex set has volume `O(delta * volume U)`.  Unlike the earlier Wolff
interface, this statement contains no cardinality conclusion and is thus a
pure convex-geometric target. -/
def HasConvexContainedDirectionShellEstimate : Prop :=
  ∃ Cshell : ENNReal, Cshell ≠ ⊤ ∧
    ∀ (delta : ℝ) (pruned : Finset MarkedLine),
      (hdelta : 0 < delta) → delta ≤ 1 → pruned.Nonempty →
      (∀ line ∈ pruned, IsValidLine line) →
      ∀ hsep : ∀ a ∈ pruned, ∀ b ∈ pruned, a ≠ b →
          delta ≤ dist (direction a) (direction b),
        ∀ U : Set E4, Convex ℝ U →
          volume (wzContainedDirectionBallUnion
            (retainedWZCellSourceAtScales delta (delta / 2) pruned
              (fun _ => ∅) hdelta hsep) U (delta / 2)) ≤
            (Cshell * ENNReal.ofReal delta) * volume U

/-- A uniform Rogers--Shephard difference-body bound supplies the complete
contained-direction shell estimate.  The small-scale branch uses the explicit
radial sweep above; the large-scale branch uses direct containment in `U-U`.
The numerical loss is `64 * Cdiff`. -/
theorem convex_difference_body_estimate_implies_shell
    (hdiff : HasConvexDifferenceBodyVolumeEstimate) :
    HasConvexContainedDirectionShellEstimate := by
  classical
  obtain ⟨Cdiff, hCdiffTop, hdiffBound⟩ := hdiff
  let Cshell : ENNReal := ENNReal.ofReal 64 * Cdiff
  have hCshellTop : Cshell ≠ ⊤ := by
    dsimp [Cshell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCdiffTop
  refine ⟨Cshell, hCshellTop, ?_⟩
  intro delta pruned hdelta hdeltaOne hpruned hvalid hsep U hU
  let D := retainedWZCellSourceAtScales delta (delta / 2) pruned
    (fun _ => ∅) hdelta hsep
  have hvalidD : ∀ i, IsValidLine (D.line i) := by
    intro i
    exact hvalid (retainedIndex pruned i) (retainedIndex_mem pruned i)
  have hradius : delta / 2 ≤ D.thickness := by
    simp [D, retainedWZCellSourceAtScales,
      directionSeparatedWZCellSourceAtScales,
      directionSeparatedMarkedShadingSource,
      unweightedMarkedShadingSource, hdelta.le]
  let contained : Finset (Fin pruned.card) :=
    Finset.univ.filter fun i =>
      markedUnitTube (D.line i) D.thickness ⊆ U
  by_cases hcontained : contained.Nonempty
  · obtain ⟨i, hi⟩ := hcontained
    have hiTube : markedUnitTube (D.line i) D.thickness ⊆ U :=
      (Finset.mem_filter.mp hi).2
    have hthickness : 0 < D.thickness :=
      (half_pos hdelta).trans_le hradius
    have hballU :
        Metric.ball (rawFrontParam (D.line i, (0 : ℝ))) D.thickness ⊆ U :=
      (ball_rawFrontParam_subset_markedUnitTube (D.line i)
        (t := (0 : ℝ)) (delta := D.thickness) (by norm_num)).trans hiTube
    have hvolumeU : volume U ≠ 0 := by
      have hballPos :
          0 < volume (Metric.ball
            (rawFrontParam (D.line i, (0 : ℝ))) D.thickness) := by
        rw [InnerProductSpace.volume_ball]
        positivity
      exact ne_of_gt (hballPos.trans_le (measure_mono hballU))
    by_cases hsmall : delta ≤ 1 / 2
    · have hsweep := small_delta_contained_direction_volume_le_difference_body
        D U hdelta hsmall hvalidD hU hradius
      have hdiffU := hdiffBound U hU hvolumeU
      calc
        volume (wzContainedDirectionBallUnion D U (delta / 2)) ≤
            ENNReal.ofReal (64 * delta) * volume (U - U) := hsweep
        _ ≤ ENNReal.ofReal (64 * delta) * (Cdiff * volume U) := by
          gcongr
        _ = (Cshell * ENNReal.ofReal delta) * volume U := by
          dsimp [Cshell]
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
          ring
    · have hlarge : 1 / 2 < delta := lt_of_not_ge hsmall
      have hsubset := wzContainedDirectionBallUnion_subset_difference_body
        D U (delta / 2) hradius
      have hdeltaFactor : 1 ≤ ENNReal.ofReal 64 * ENNReal.ofReal delta := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64),
          ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      calc
        volume (wzContainedDirectionBallUnion D U (delta / 2)) ≤
            volume (U - U) := measure_mono hsubset
        _ ≤ Cdiff * volume U := hdiffBound U hU hvolumeU
        _ ≤ (Cshell * ENNReal.ofReal delta) * volume U := by
          dsimp [Cshell]
          gcongr
          calc
            Cdiff = 1 * Cdiff := by simp
            _ ≤ (ENNReal.ofReal 64 * ENNReal.ofReal delta) * Cdiff := by
              gcongr
            _ = (ENNReal.ofReal 64 * Cdiff) * ENNReal.ofReal delta := by ring
  · have hcontainedEmpty : contained = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcontained
    have hunionEmpty :
        wzContainedDirectionBallUnion D U (delta / 2) = ∅ := by
      simpa [wzContainedDirectionBallUnion, contained, hcontainedEmpty,
        finiteDirectionBallUnion]
    rw [hunionEmpty, measure_empty]
    exact bot_le

/-- The contained-direction shell estimate is unconditional in four dimensions. -/
theorem convex_contained_direction_shell_estimate :
    HasConvexContainedDirectionShellEstimate :=
  convex_difference_body_estimate_implies_shell
    convex_difference_body_volume_estimate

/-- The shell estimate is exactly equivalent to the missing scale in the
convex count.  Four-dimensional disjoint balls contribute `delta^4`, while
the radial shell has thickness `delta`; cancelling the positive finite
half-unit-ball volume leaves `delta^(-3)`. -/
theorem convex_contained_direction_shell_estimate_implies_geometric_count
    (hshell : HasConvexContainedDirectionShellEstimate) :
    HasSeparatedDirectionsConvexGeometricCount := by
  obtain ⟨Cshell, hCshellTop, hshellBound⟩ := hshell
  let vhalf : ENNReal := volume (Metric.ball (0 : E4) (1 / 2))
  let Cgeom : ENNReal := Cshell * vhalf⁻¹
  have hvhalfPos : 0 < vhalf := by
    dsimp [vhalf]
    rw [InnerProductSpace.volume_ball]
    positivity
  have hvhalfZero : vhalf ≠ 0 := ne_of_gt hvhalfPos
  have hvhalfTop : vhalf ≠ ⊤ := by
    dsimp [vhalf]
    exact ne_of_lt measure_ball_lt_top
  have hCgeomTop : Cgeom ≠ ⊤ := by
    dsimp [Cgeom]
    exact ENNReal.mul_ne_top hCshellTop (ENNReal.inv_ne_top.mpr hvhalfZero)
  refine ⟨Cgeom, hCgeomTop, ?_⟩
  intro delta pruned hdelta hdeltaOne hpruned hvalid hsep U hU
  let D := retainedWZCellSourceAtScales delta (delta / 2) pruned
    (fun _ => ∅) hdelta hsep
  let e : ENNReal := ENNReal.ofReal delta
  let den : ENNReal := e ^ 4 * vhalf
  have heZero : e ≠ 0 := by
    dsimp [e]
    positivity
  have heTop : e ≠ ⊤ := by
    dsimp [e]
    exact ENNReal.ofReal_ne_top
  have hdenZero : den ≠ 0 := by
    dsimp [den]
    exact mul_ne_zero (pow_ne_zero _ heZero) hvhalfZero
  have hdenTop : den ≠ ⊤ := by
    dsimp [den]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top heTop) hvhalfTop
  have hsepIndex : ∀ i j, i ≠ j →
      delta ≤ dist (direction (D.line i)) (direction (D.line j)) := by
    intro i j hij
    exact hsep (retainedIndex pruned i) (retainedIndex_mem pruned i)
      (retainedIndex pruned j) (retainedIndex_mem pruned j)
      (fun h => hij (retainedIndex_injective pruned h))
  have hpack := volume_wzContainedDirectionBallUnion_of_separated
    D U hdelta hsepIndex
  have hshell' := hshellBound delta pruned hdelta hdeltaOne hpruned
    hvalid hsep U hU
  have hraw : (wzContainedTubeCount D U : ENNReal) * den ≤
      (Cshell * e) * volume U := by
    calc
      (wzContainedTubeCount D U : ENNReal) * den =
          volume (wzContainedDirectionBallUnion D U (delta / 2)) := by
            simpa [den, e, vhalf] using hpack.symm
      _ ≤ (Cshell * e) * volume U := by
        simpa [D, e] using hshell'
  have hcancelled : (wzContainedTubeCount D U : ENNReal) ≤
      ((Cshell * e) * volume U) * den⁻¹ := by
    have hmul := mul_le_mul_right hraw den⁻¹
    calc
      (wzContainedTubeCount D U : ENNReal) =
          ((wzContainedTubeCount D U : ENNReal) * den) * den⁻¹ := by
            rw [mul_assoc, ENNReal.mul_inv_cancel hdenZero hdenTop, mul_one]
      _ ≤ ((Cshell * e) * volume U) * den⁻¹ := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have heInvPower : e * (e ^ 4)⁻¹ = e.rpow (-3) := by
    calc
      e * (e ^ 4)⁻¹ = e.rpow 1 * (e.rpow 4)⁻¹ := by
        congr 1
        · exact (ENNReal.rpow_one e).symm
        · congr 1
          exact (ENNReal.rpow_natCast e 4).symm
      _ = e.rpow 1 * e.rpow (-4) := by
        congr 1
        exact (ENNReal.rpow_neg e 4).symm
      _ = e.rpow (1 + (-4)) :=
        (ENNReal.rpow_add 1 (-4) heZero heTop).symm
      _ = e.rpow (-3) := by norm_num
  have hcoeff : ((Cshell * e) * volume U) * den⁻¹ =
      (Cgeom * e.rpow (-3)) * volume U := by
    rw [show den⁻¹ = (e ^ 4)⁻¹ * vhalf⁻¹ by
      exact ENNReal.mul_inv (Or.inl (pow_ne_zero _ heZero))
        (Or.inl (ENNReal.pow_ne_top heTop))]
    rw [← heInvPower]
    dsimp [Cgeom]
    ring
  simpa [D, e] using hcancelled.trans_eq hcoeff

/-- The separated-direction convex count obtained from the unconditional
four-dimensional shell estimate. -/
theorem separated_directions_convex_geometric_count :
    HasSeparatedDirectionsConvexGeometricCount :=
  convex_contained_direction_shell_estimate_implies_geometric_count
    convex_contained_direction_shell_estimate

/-- The nontrivial branch of the convex count automatically has the sharp
transverse volume scale.  If even one retained full tube is contained in
`U`, monotonicity and the explicit marked-tube computation give
`volume U ≳ delta³`.  Thus the later John argument may assume both a
contained tube and positive four-dimensional volume. -/
theorem volume_lower_bound_of_positive_retained_contained_tube_count
    (delta : ℝ) (pruned : Finset MarkedLine)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hvalid : ∀ line ∈ pruned, IsValidLine line)
    (hsep : ∀ a ∈ pruned, ∀ b ∈ pruned, a ≠ b →
      delta ≤ dist (direction a) (direction b))
    (U : Set E4)
    (hcount : 0 < wzContainedTubeCount
      (retainedWZCellSourceAtScales delta (delta / 2) pruned
        (fun _ => ∅) hdelta hsep) U) :
    ENNReal.ofReal (1 / 8 : ℝ) * (ENNReal.ofReal delta) ^ 3 *
        ENNReal.ofReal (Real.pi ^ 2 / 2) ≤ volume U := by
  classical
  let D := retainedWZCellSourceAtScales delta (delta / 2) pruned
    (fun _ => ∅) hdelta hsep
  change 0 < (Finset.univ.filter fun i : Fin pruned.card =>
    markedUnitTube (D.line i) D.thickness ⊆ U).card at hcount
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcount
  have hiData := Finset.mem_filter.mp hi
  have hlineValid : IsValidLine (D.line i) := by
    exact hvalid (retainedIndex pruned i) (retainedIndex_mem pruned i)
  have htubeLower :=
    volume_markedUnitTube_lower_bound hlineValid hdelta hdeltaSmall
  exact htubeLower.trans (measure_mono hiData.2)

/-- Normalized finite-dimensional convex geometry statement for the marked
source used by the Lean WZ interface.  The affine marks are untouched; only
the direction separation and the lower cardinality enter the estimate. -/
def HasSeparatedDirectionsConvexWolffEstimate : Prop :=
  ∀ beta c0 : ℝ, 0 < beta → 0 < c0 →
    ∃ Ccw : ENNReal, Ccw ≠ ⊤ ∧
      ∀ (delta : ℝ) (pruned : Finset MarkedLine),
        (hdelta : 0 < delta) → delta ≤ 1 → pruned.Nonempty →
        c0 * delta ^ (-3 + beta) ≤ (pruned.card : ℝ) →
        (∀ line ∈ pruned, IsValidLine line) →
        ∀ hsep : ∀ a ∈ pruned, ∀ b ∈ pruned, a ≠ b →
            delta ≤ dist (direction a) (direction b),
          ∀ U : Set E4, Convex ℝ U →
            (wzContainedTubeCount
              (retainedWZCellSourceAtScales delta (delta / 2) pruned
                (fun _ => ∅) hdelta hsep) U : ENNReal) ≤
              ((Ccw * (ENNReal.ofReal delta).rpow (-beta)) *
                pruned.card) * volume U

/-- The John-ellipsoid count has exactly the strength needed by the WZ
interface.  This theorem performs the complete normalization: the lower
cardinality `c0 * delta^(-3 + beta)` turns the geometric coefficient
`delta⁻³` into `c0⁻¹ * delta⁻beta * #pruned`. -/
theorem separated_directions_convex_geometric_count_implies_wolff_estimate
    (hgeom : HasSeparatedDirectionsConvexGeometricCount) :
    HasSeparatedDirectionsConvexWolffEstimate := by
  obtain ⟨Cgeom, hCgeomTop, hgeomBound⟩ := hgeom
  intro beta c0 _hbeta hc0
  let c0e : ENNReal := ENNReal.ofReal c0
  let Ccw : ENNReal := Cgeom * c0e⁻¹
  have hc0eZero : c0e ≠ 0 := by
    dsimp [c0e]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hc0)
  have hc0eTop : c0e ≠ ⊤ := by
    dsimp [c0e]
    exact ENNReal.ofReal_ne_top
  have hCcwTop : Ccw ≠ ⊤ := by
    dsimp [Ccw]
    exact ENNReal.mul_ne_top hCgeomTop (ENNReal.inv_ne_top.mpr hc0eZero)
  refine ⟨Ccw, hCcwTop, ?_⟩
  intro delta pruned hdelta hdeltaOne hpruned hsize hvalid hsep U hU
  have hdeltaeZero : ENNReal.ofReal delta ≠ 0 := by positivity
  have hdeltaeTop : ENNReal.ofReal delta ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsizeE :
      c0e * (ENNReal.ofReal delta).rpow (-3 + beta) ≤
        (pruned.card : ENNReal) := by
    calc
      c0e * (ENNReal.ofReal delta).rpow (-3 + beta) =
          ENNReal.ofReal c0 * ENNReal.ofReal (delta ^ (-3 + beta)) := by
            dsimp [c0e]
            congr 1
            exact ENNReal.ofReal_rpow_of_pos hdelta
      _ = ENNReal.ofReal (c0 * delta ^ (-3 + beta)) :=
        (ENNReal.ofReal_mul hc0.le).symm
      _ ≤ ENNReal.ofReal (pruned.card : ℝ) :=
        ENNReal.ofReal_le_ofReal hsize
      _ = (pruned.card : ENNReal) := by simp
  have hcancel :
      c0e⁻¹ *
          (c0e * (ENNReal.ofReal delta).rpow (-3 + beta)) =
        (ENNReal.ofReal delta).rpow (-3 + beta) := by
    calc
      c0e⁻¹ *
          (c0e * (ENNReal.ofReal delta).rpow (-3 + beta)) =
        (c0e⁻¹ * c0e) *
          (ENNReal.ofReal delta).rpow (-3 + beta) := by ring
      _ = (ENNReal.ofReal delta).rpow (-3 + beta) := by
        rw [ENNReal.inv_mul_cancel hc0eZero hc0eTop, one_mul]
  have hnormalizedSize :
      (ENNReal.ofReal delta).rpow (-3 + beta) ≤
        c0e⁻¹ * (pruned.card : ENNReal) := by
    rw [← hcancel]
    exact mul_le_mul_right hsizeE c0e⁻¹
  have hsplit :
      (ENNReal.ofReal delta).rpow (-3) =
        (ENNReal.ofReal delta).rpow (-beta) *
          (ENNReal.ofReal delta).rpow (-3 + beta) := by
    calc
      (ENNReal.ofReal delta).rpow (-3) =
          (ENNReal.ofReal delta).rpow ((-beta) + (-3 + beta)) := by
            congr 1
            ring
      _ = (ENNReal.ofReal delta).rpow (-beta) *
          (ENNReal.ofReal delta).rpow (-3 + beta) :=
            ENNReal.rpow_add (-beta) (-3 + beta) hdeltaeZero hdeltaeTop
  have hpower :
      (ENNReal.ofReal delta).rpow (-3) ≤
        (c0e⁻¹ * (ENNReal.ofReal delta).rpow (-beta)) *
          (pruned.card : ENNReal) := by
    rw [hsplit]
    calc
      (ENNReal.ofReal delta).rpow (-beta) *
          (ENNReal.ofReal delta).rpow (-3 + beta) ≤
        (ENNReal.ofReal delta).rpow (-beta) *
          (c0e⁻¹ * (pruned.card : ENNReal)) :=
            mul_le_mul_right hnormalizedSize _
      _ = (c0e⁻¹ * (ENNReal.ofReal delta).rpow (-beta)) *
          (pruned.card : ENNReal) := by ring
  have hcount :=
    hgeomBound delta pruned hdelta hdeltaOne hpruned hvalid hsep U hU
  calc
    (wzContainedTubeCount
        (retainedWZCellSourceAtScales delta (delta / 2) pruned
          (fun _ => ∅) hdelta hsep) U : ENNReal) ≤
        (Cgeom * (ENNReal.ofReal delta).rpow (-3)) * volume U := hcount
    _ ≤ (Cgeom *
          ((c0e⁻¹ * (ENNReal.ofReal delta).rpow (-beta)) * pruned.card)) *
        volume U := by gcongr
    _ = ((Ccw * (ENNReal.ofReal delta).rpow (-beta)) *
          pruned.card) * volume U := by
        dsimp [Ccw]
        ring

/-- The convex-Wolff estimate is now a theorem rather than an input. -/
theorem separated_directions_convex_wolff_estimate :
    HasSeparatedDirectionsConvexWolffEstimate :=
  separated_directions_convex_geometric_count_implies_wolff_estimate
    separated_directions_convex_geometric_count

/-- Specialization of the separated-direction convex theorem to the exact
`beta = 2 * theta` and half-pruned cardinality used by the cover layer. -/
theorem separated_directions_convex_wolff_specializes_to_half_pruning
    (hCW : HasSeparatedDirectionsConvexWolffEstimate)
    (theta pointConstant : ℝ)
    (htheta : 0 < theta) (hpointConstant : 0 < pointConstant) :
    ∃ Ccw : ENNReal, Ccw ≠ ⊤ ∧
      ∀ (delta : ℝ) (pruned : Finset MarkedLine),
        (hdelta : 0 < delta) → delta ≤ 1 → pruned.Nonempty →
        (pointConstant / 2) * delta ^ (-3 + 2 * theta) ≤
          (pruned.card : ℝ) →
        (∀ line ∈ pruned, IsValidLine line) →
        ∀ hsep : ∀ a ∈ pruned, ∀ b ∈ pruned, a ≠ b →
            delta ≤ dist (direction a) (direction b),
          ∀ U : Set E4, Convex ℝ U →
            (wzContainedTubeCount
              (retainedWZCellSourceAtScales delta (delta / 2) pruned
                (fun _ => ∅) hdelta hsep) U : ENNReal) ≤
              ((Ccw * (ENNReal.ofReal delta).rpow (-2 * theta)) *
                pruned.card) * volume U := by
  obtain ⟨Ccw, hCcwTop, hbound⟩ :=
    hCW (2 * theta) (pointConstant / 2) (by positivity) (by positivity)
  refine ⟨Ccw, hCcwTop, ?_⟩
  intro delta pruned hdelta hdeltaOne hpruned hsize hvalid hsep U hU
  have h :=
    hbound delta pruned hdelta hdeltaOne hpruned hsize hvalid hsep U hU
  convert h using 1 <;> ring

/-- The cover-adapted packet construction with the correct quantifier order.
The WZ loss is fixed before the packing carrier piece is extracted.  All
subsequent cutoffs are then chosen uniformly, and the Hausdorff cover layer is
selected below their common minimum. -/
theorem packing_selector_has_cover_adapted_wz_packets_at_exponent
    (ambient selector : Set MarkedLine)
    (hambientCompact : IsCompact ambient)
    (hselectorAmbient : selector ⊆ ambient)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (chi : ℝ) (d : NNReal)
    (hchi : 0 < chi) (hchiFour : chi < 4)
    (hd : (d : ℝ) = 4 - chi)
    (hdim : dimH (unitFront ambient) < (d : ENNReal)) :
    HasCoverAdaptedWZContradictionPacketsAtExponent ambient selector chi := by
  intro eta heta A hAZero hATop deltaRequested hdeltaRequested
  obtain ⟨theta, htheta, hthetaEta, centerBin, piece, hpieceMeasurable,
      hpieceCarrier, hpieceLocalized, hpieceMass, carrierDim, hcarrierDim, hcarrierDimTop,
      carrierCoverConstant, hcarrierCoverConstantTop, hcarrierCover⟩ :=
    packing_selector_extract_piece_with_wz_compatible_slack
      selector hmeasurable hvalid hselector hpacking eta heta
  let cap : ENNReal :=
    carrierPieceDirectionCapConstant selector hmeasurable hvalid hselector piece
  have hcapZero : cap ≠ 0 := by
    dsimp [cap]
    exact carrierPieceDirectionCapConstant_ne_zero selector hmeasurable hvalid
      hselector piece hpieceMass
  have hcapTop : cap ≠ ⊤ := by
    dsimp [cap]
    exact carrierPieceDirectionCapConstant_ne_top selector hmeasurable hvalid
      hselector piece
  obtain ⟨boundaryExponent, hboundaryExponent, hboundaryExponentFour,
      hboundaryPacket⟩ :=
    coherentBoundary_has_arbitrarily_small_carrierPiece_concentration_packet
      selector hmeasurable hvalid hselector hboundary piece
  obtain ⟨boundaryCenter, boundaryRadius, hboundaryRadius,
      hboundaryRadiusSmall, hboundaryLarge⟩ :=
    hboundaryPacket (1 / 4) (by norm_num) (by norm_num)
  let seed : Set E4 := Metric.ball boundaryCenter boundaryRadius
  let boundaryLower : ENNReal :=
    ((ENNReal.ofReal (1 / 4 : ℝ)).rpow
        (4 - boundaryExponent))⁻¹ *
      (ENNReal.ofReal boundaryRadius).rpow (4 - boundaryExponent)
  have hboundaryLowerPos : 0 < boundaryLower := by
    dsimp [boundaryLower]
    have hq : 0 < 4 - boundaryExponent := by linarith
    apply bot_lt_iff_ne_bot.mpr
    exact mul_ne_zero
      (ENNReal.inv_ne_zero.mpr (ne_of_lt
        (ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top)))
      (ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hboundaryRadius)
        ENNReal.ofReal_ne_top))
  have hboundaryLowerTop : boundaryLower ≠ ⊤ := by
    dsimp [boundaryLower]
    finiteness
  have hboundaryLower : boundaryLower <
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) seed := by
    simpa [boundaryLower, seed] using hboundaryLarge
  let prefactor : ENNReal :=
    boundaryLower * ((1 - dyadicMassRatio theta) * (2 : ENNReal)⁻¹)
  have hprefactorZero : prefactor ≠ 0 := by
    dsimp [prefactor]
    exact mul_ne_zero hboundaryLowerPos.ne'
      (mul_ne_zero
        (tsub_pos_iff_lt.mpr (dyadicMassRatio_lt_one htheta)).ne'
        (by norm_num))
  have hprefactorTop : prefactor ≠ ⊤ := by
    dsimp [prefactor]
    exact ENNReal.mul_ne_top hboundaryLowerTop (by finiteness)
  have hprefactorReal : 0 < prefactor.toReal :=
    ENNReal.toReal_pos hprefactorZero hprefactorTop
  have hcapReal : 0 < cap.toReal := ENNReal.toReal_pos hcapZero hcapTop
  let pointConstant : ℝ := prefactor.toReal / (16 * cap.toReal)
  have hpointConstant : 0 < pointConstant := by
    dsimp [pointConstant]
    positivity
  obtain ⟨CAll, hCAllTop, _hcarrierConstant, hcoverAll,
      hcarrierDimReal, pruningZero, hpruningZero, hpruningZeroOne,
      hpruningBound⟩ :=
    carrier_piece_has_uniform_cover_and_cover_adapted_compensation_threshold
      piece carrierCoverConstant carrierDim hcarrierCoverConstantTop
      hcarrierCover theta 8 pointConstant htheta hcarrierDim hcarrierDimTop
      (by norm_num) hpointConstant
  obtain ⟨Ccw, hCcwTop, hconvex⟩ :=
    separated_directions_convex_wolff_specializes_to_half_pruning
      separated_directions_convex_wolff_estimate
      theta pointConstant htheta hpointConstant
  have htwoThetaEta : 2 * theta < eta := by linarith
  obtain ⟨cwZero, hcwZero, hcwZeroOne, hcwBound⟩ :=
    exists_convex_wolff_coefficient_absorption_threshold
      htwoThetaEta Ccw hCcwTop
  let Cactive : ENNReal :=
    4 * (8 * (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))
  have hCactiveTop : Cactive ≠ ⊤ := by
    dsimp [Cactive]
    finiteness
  have hprefactorHalf : 0 < prefactor / 2 :=
    ENNReal.div_pos hprefactorZero (by norm_num)
  obtain ⟨activeZero, hactiveZero, hactiveZeroOne, hactiveBound⟩ :=
    exists_const_mul_two_scale_rpow_threshold
      (eta := 2 * theta) (by positivity) Cactive (prefactor / 2)
        hCactiveTop hprefactorHalf
  obtain ⟨absorbZero, habsorbZero, habsorbZeroOne, habsorbBound⟩ :=
    exists_subpower_absorption_threshold heta
  obtain ⟨Q, hQTop, hQBound⟩ :=
    exists_e4_uniform_inflated_target_covering_bound
  have hdPos : 0 < (d : ℝ) := by rw [hd]; linarith
  obtain ⟨coefficientZero, hcoefficientZero, hcoefficientZeroOne,
      hcoefficientBound⟩ :=
    exists_inflated_target_coefficient_gap_threshold
      Q A hQTop hAZero hATop (d : ℝ) chi hdPos hchi
  let meshZero : ℝ :=
    min deltaRequested
      (min pruningZero
        (min activeZero (min absorbZero (min cwZero coefficientZero))))
  have hmeshZero : 0 < meshZero := by
    dsimp [meshZero]
    exact lt_min hdeltaRequested
      (lt_min hpruningZero
        (lt_min hactiveZero
          (lt_min habsorbZero (lt_min hcwZero hcoefficientZero))))
  have hmeshZeroOne : meshZero ≤ 1 := by
    dsimp [meshZero]
    exact (min_le_right _ _).trans
      ((min_le_left _ _).trans hpruningZeroOne)
  let rho : ENNReal := ENNReal.ofReal (meshZero / 4)
  have hrho : 0 < rho := by
    dsimp [rho]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hrhoQuarter : rho ≤ 1 / 4 := by
    dsimp [rho]
    have hreal : meshZero / 4 ≤ (1 : ℝ) / 4 := by linarith
    simpa using ENNReal.ofReal_le_ofReal hreal
  obtain ⟨cover, _hdiam, _hcoverCost, levelZero, target, _htarget,
      htargetMeasurable, hmassStrict, _hmassPos, _hscale, _hlevelPos,
      hscaleRho, hdeltaPos, hdeltaHalf, _htubeDyadic, hcellDyadic,
      _hlayerFinite, hlayerCost, htargetCover, hretainedPacket, _hactive⟩ :=
    markedCarrierPiece_exists_low_cost_dyadic_target_layer
      ambient selector hambientCompact hselectorAmbient hmeasurable hvalid
      hselector piece hpieceMeasurable hpieceCarrier hpieceMass seed
      Metric.isOpen_ball.measurableSet boundaryLower hboundaryLowerPos
      hboundaryLower hdim hrho hrhoQuarter (epsilon := (1 : ENNReal))
      (by norm_num) htheta
  let delta : ℝ := ((((2 : ENNReal)⁻¹) ^ levelZero).toReal)
  have hchildTop : ((2 : ENNReal)⁻¹) ^ (levelZero + 1) ≠ ⊤ := by
    simp
  have hrhoTop : rho ≠ ⊤ := by
    dsimp [rho]
    exact ENNReal.ofReal_ne_top
  have hchildReal :
      (((2 : ENNReal)⁻¹) ^ (levelZero + 1)).toReal < meshZero / 4 := by
    have h := (ENNReal.toReal_lt_toReal hchildTop hrhoTop).2 hscaleRho
    have hrhoReal : rho.toReal = meshZero / 4 := by
      dsimp [rho]
      exact ENNReal.toReal_ofReal (by positivity)
    rw [hrhoReal] at h
    exact h
  have hdeltaChild :
      delta = 2 * (((2 : ENNReal)⁻¹) ^ (levelZero + 1)).toReal := by
    dsimp [delta]
    rw [pow_succ, ENNReal.toReal_mul]
    norm_num [ENNReal.toReal_inv]
    ring
  have hdeltaMesh : delta ≤ meshZero := by
    rw [hdeltaChild]
    nlinarith
  have hdeltaRequested' : delta ≤ deltaRequested :=
    hdeltaMesh.trans (by dsimp [meshZero]; exact min_le_left _ _)
  have hdeltaPruning : delta ≤ pruningZero :=
    hdeltaMesh.trans (by
      dsimp [meshZero]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hdeltaActive : delta ≤ activeZero :=
    hdeltaMesh.trans (by
      dsimp [meshZero]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hdeltaAbsorb : delta ≤ absorbZero :=
    hdeltaMesh.trans (by
      dsimp [meshZero]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
  have hdeltaCW : delta ≤ cwZero :=
    hdeltaMesh.trans (by
      dsimp [meshZero]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _)))))
  have hdeltaCoefficient : delta ≤ coefficientZero :=
    hdeltaMesh.trans (by
      dsimp [meshZero]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_right _ _)))))
  have hdeltaOne : delta ≤ 1 := hdeltaMesh.trans hmeshZeroOne
  let mass : ENNReal :=
    (markedCarrierPieceFrontProbability selector hmeasurable hvalid
      hselector piece : Measure E4) target
  have hmassPower : prefactor *
      (ENNReal.ofReal delta).rpow theta ≤ mass := by
    dsimp [mass]
    have hscaleOfReal :
        ENNReal.ofReal delta = ((2 : ENNReal)⁻¹) ^ levelZero := by
      dsimp [delta]
      exact ENNReal.ofReal_toReal (by simp)
    rw [hscaleOfReal]
    simpa [prefactor, dyadicMassThreshold_eq_prefactor_mul_scale_rpow,
      mul_assoc] using hmassStrict.le
  obtain ⟨retained, hretainedNonempty, hretainedAll, hseparated,
      hcount, hrealCount⟩ := hretainedPacket
  have hretained : (retained : Set MarkedLine) ⊆
      selectorLinesOverCarrierPiece selector piece := by
    intro line hline
    exact (hretainedAll hline).1
  have hactiveRetained : ∀ line ∈ retained,
      mass / 2 ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
          (markedLineSetFibreSet line target) := by
    intro line hline
    exact (hretainedAll hline).2
  have hvalidRetained : ∀ line ∈ retained, IsValidLine line := by
    intro line hline
    exact hvalid line ((hretainedAll hline).1.1)
  have hpointLower :
      pointConstant * delta ^ (-3 + 2 * theta) ≤
        (retained.card : ℝ) := by
    have hstrong : pointConstant * delta ^ (-3 + theta) ≤
        (retained.card : ℝ) := by
      simpa [pointConstant, prefactor, cap, delta, mass] using hrealCount
    calc
      pointConstant * delta ^ (-3 + 2 * theta) ≤
          pointConstant * delta ^ (-3 + theta) := by
        apply mul_le_mul_of_nonneg_left _ hpointConstant.le
        apply Real.rpow_le_rpow_of_exponent_ge hdeltaPos hdeltaOne
        linarith
      _ ≤ (retained.card : ℝ) := hstrong
  have hpruning :
      (4 * (((CAll.toReal * (4 : ℝ) ^ carrierDim.toReal + 1) * 8)) *
          (2 : ℝ) ^ (theta / 4) /
            ((2 : ℝ) ^ (theta / 4) - 1)) *
        delta ^ (3 * theta - theta / 4 - 2 * theta) ≤ pointConstant :=
    hpruningBound delta hdeltaPos hdeltaPruning
  have hactiveMass :
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal delta).rpow (3 * theta) *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤ mass / 2 := by
    have htwoScale := hactiveBound delta hdeltaPos hdeltaActive
    have hscaleMono :
        (ENNReal.ofReal delta).rpow (2 * theta) ≤
          (ENNReal.ofReal (2 * delta)).rpow (2 * theta) := by
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (by linarith))
        (by positivity)
    have hactiveScale :
        Cactive * (ENNReal.ofReal delta).rpow (2 * theta) ≤ prefactor / 2 := by
      calc
        Cactive * (ENNReal.ofReal delta).rpow (2 * theta) ≤
            Cactive * (ENNReal.ofReal (2 * delta)).rpow (2 * theta) := by gcongr
        _ ≤ prefactor / 2 := htwoScale
    have hsplit :
        (ENNReal.ofReal delta).rpow (3 * theta) =
          (ENNReal.ofReal delta).rpow (2 * theta) *
            (ENNReal.ofReal delta).rpow theta := by
      rw [show 3 * theta = 2 * theta + theta by ring]
      exact ENNReal.rpow_add_of_nonneg (2 * theta) theta
        (by positivity) htheta.le
    have hactiveMass' :
        Cactive * (ENNReal.ofReal delta).rpow (3 * theta) ≤ mass / 2 := by
      rw [hsplit, ← mul_assoc]
      calc
        (Cactive * (ENNReal.ofReal delta).rpow (2 * theta)) *
            (ENNReal.ofReal delta).rpow theta ≤
          (prefactor / 2) * (ENNReal.ofReal delta).rpow theta := by gcongr
        _ = (prefactor * (ENNReal.ofReal delta).rpow theta) / 2 := by
          simp only [div_eq_mul_inv]
          ac_rfl
        _ ≤ mass / 2 := ENNReal.div_le_div_right hmassPower 2
    simpa [Cactive, mul_assoc, mul_left_comm, mul_comm] using hactiveMass'
  have habsorbWZ : (125 : ENNReal) ≤
      (ENNReal.ofReal delta).rpow (-eta) :=
    habsorbBound delta hdeltaPos hdeltaAbsorb
  have hcwAbsorb :
      Ccw * (ENNReal.ofReal delta).rpow (-2 * theta) ≤
        (ENNReal.ofReal delta).rpow (-eta) :=
    by
      convert hcwBound delta hdeltaPos hdeltaCW using 1 <;> ring
  have hnormalized :=
    half_pruned_family_has_normalized_convex_wolff_data
      theta eta delta pointConstant retained hdeltaPos hvalidRetained
      hpointLower Ccw hcwAbsorb
      (fun pruned hpruned hsize hvalidPruned hsep U hU =>
        hconvex delta pruned hdeltaPos hdeltaOne hpruned hsize
          hvalidPruned hsep U hU)
  dsimp only at hnormalized
  obtain ⟨hgeometric, hnormalize⟩ := hnormalized
  obtain ⟨pruned, hprunedNonempty, hprunedSubset, hsepPruned,
      shadingCells, hinput, hinflation⟩ :=
    dyadic_cover_layer_pruning_assembles_wz_finite_input
      selector piece CAll carrierDim theta eta delta pointConstant levelZero
      retained target hretainedNonempty hretained hCAllTop htheta
      (by linarith) hdeltaPos hdeltaOne rfl hcellDyadic
      hpointLower hcarrierDimReal hpruning hcoverAll hvalidRetained hseparated
      hactiveRetained hactiveMass habsorbWZ
      (fun pruned =>
        (Ccw * (ENNReal.ofReal delta).rpow (-2 * theta)) * pruned.card)
      hgeometric hnormalize
  let M : ENNReal :=
    ((positiveDyadicCoverLayerIndices cover levelZero).ncard : ENNReal)
  have hMTop : M ≠ ⊤ := by
    dsimp [M]
    exact ENNReal.natCast_ne_top _
  have hhalfScale :
      ENNReal.ofReal (delta / 2) =
        ((2 : ENNReal)⁻¹) ^ (levelZero + 1) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    dsimp [delta]
    rw [ENNReal.ofReal_toReal (by simp)]
    simp [div_eq_mul_inv, pow_succ]
  have hlayerCost' :
      M * (ENNReal.ofReal (delta / 2)).rpow (d : ℝ) < 1 := by
    simpa [M, hhalfScale] using hlayerCost
  have hinflatedCover :=
    hQBound target M delta hdeltaPos hMTop
      (by simpa [M, delta] using htargetCover)
  let upperConstant : ENNReal :=
    Q * (M + 1) * (ENNReal.ofReal delta).rpow (4 - chi)
  have hupperSmall :
      upperConstant * (ENNReal.ofReal delta).rpow (chi / 2) < A⁻¹ := by
    dsimp [upperConstant]
    rw [← hd]
    exact hcoefficientBound delta M hdeltaPos hdeltaCoefficient hlayerCost'
  have hinflatedPower :
      coveringNumber (⋃ y ∈ target, Metric.ball y delta) delta ≤
        upperConstant * (ENNReal.ofReal delta).rpow (-4 + chi) := by
    simpa [upperConstant] using
      (inflated_target_covering_bound_as_power
        target Q M delta chi hdeltaPos hinflatedCover)
  let D : FiniteScaleSource pruned.card :=
    retainedWZCellSourceAtScales delta (delta / 2) pruned shadingCells
      hdeltaPos hsepPruned
  have hprunedLinePiece : ∀ i,
      retainedIndex pruned i ∈ selectorLinesOverCarrierPiece selector piece := by
    intro i
    exact hretained (hprunedSubset (retainedIndex_mem pruned i))
  have hDcomes : ComesFromSelector D selector := by
    intro i
    change retainedIndex pruned i ∈ selector
    exact (hprunedLinePiece i).1
  have hDlocalized : ∀ i,
      (direction (D.line i), offset (D.line i)) ∈
        northCarrierRegion selector ∩
          carrierMarkedCenterBin selector hmeasurable hvalid hselector centerBin := by
    intro i
    apply hpieceLocalized
    change (direction (retainedIndex pruned i),
      offset (retainedIndex pruned i)) ∈ piece
    exact (hprunedLinePiece i).2
  have hDgraph : HasNormalizedWZGraphSlab D :=
    finiteSource_hasNormalizedWZGraphSlab_of_north_center_bin
      selector hmeasurable hvalid hselector D hDcomes centerBin hDlocalized
  have hDfixed : HasFixedWZGraphNormalization D :=
    hasFixedWZGraphNormalization_of_normalizedSlab D
      (fun i => hvalid (D.line i) (hDcomes i)) hDgraph
  have hnativeInput : IsWangZakharovNativeFiniteInput D eta := by
    refine ⟨?_, hDgraph, hDfixed⟩
    simpa [D] using hinput
  refine ⟨pruned.card, D, ⋃ y ∈ target, Metric.ball y delta,
    upperConstant, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 0 < delta
    exact hdeltaPos
  · change delta ≤ deltaRequested
    exact hdeltaRequested'
  · exact hnativeInput
  · simpa [D] using hinflation
  · change upperConstant * (ENNReal.ofReal delta).rpow (chi / 2) < A⁻¹
    exact hupperSmall
  · change coveringNumber (⋃ y ∈ target, Metric.ball y delta) delta ≤
      upperConstant * (ENNReal.ofReal delta).rpow (-4 + chi)
    exact hinflatedPower

/-- The coherent boundary first supplies a quantitative positive-mass physical
ball on the retained packing piece.  The Hausdorff cover is then pigeonholed
for the probability conditioned on that ball, so the selected dyadic target is
literally the intersection of a cover layer with the boundary ball.  Its mass
coefficient retains the boundary concentration lower bound throughout the
carrier pruning and WZ assembly. -/
theorem coherent_boundary_has_cover_adapted_wz_packets
    (ambient selector : Set MarkedLine)
    (hambientCompact : IsCompact ambient)
    (hselectorAmbient : selector ⊆ ambient)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    HasCoverAdaptedWZContradictionPackets ambient selector := by
  intro hdimFour
  obtain ⟨chi, hchi, hchiFour, d, hd, hdim⟩ :=
    exists_hausdorff_exponent_gap_below_four
      (unitFront ambient) hdimFour
  refine ⟨chi, hchi, hchiFour, ?_⟩
  exact packing_selector_has_cover_adapted_wz_packets_at_exponent
    ambient selector hambientCompact hselectorAmbient hmeasurable hvalid
      hselector hpacking hboundary chi d hchi hchiFour hd hdim

/-- Cover-adapted closure of the one remaining branch, obtained by composing
the external finite estimate with the now-explicit internal packet gate. -/
theorem cover_adapted_wang_zakharov_closure
    (ambient selector : Set MarkedLine)
    (hambientCompact : IsCompact ambient)
    (hselectorAmbient : selector ⊆ ambient)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    dimH (unitFront ambient) = 4 := by
  apply dimH_eq_four_of_wz_finite_estimate_and_cover_packets
    ambient selector wang_zakharov_finite_estimate
  exact coherent_boundary_has_cover_adapted_wz_packets
    ambient selector hambientCompact hselectorAmbient hmeasurable hvalid
      hselector hpacking hboundary

end StickyKakeya4
