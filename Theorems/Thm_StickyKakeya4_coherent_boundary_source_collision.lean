import Theorems.Thm_StickyKakeya4_packing_selector_to_finite_scale_sources
import Theorems.Thm_StickyKakeya4_coherent_boundary_shrinking_packets
import Theorems.Thm_StickyKakeya4_collision_heavy_edge_decomposition
import Theorems.Thm_StickyKakeya4_uniform_collision_edge_time
import Theorems.Thm_StickyKakeya4_four_cycle_contact_frame

open MeasureTheory Set

noncomputable section

namespace StickyKakeya4

/-- The coherent boundary may be tested against the very parameter law whose
pushforward supplies a chosen coherent finite-scale source family.  Thus its
failed Frostman balls occur for the same physical measure used by the source
readback; no change of measure is hidden here. -/
theorem coherentBoundary_failure_transfers_to_parametrized_source_measure
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (ν : Measure
      ({theta : E4 // ‖theta‖ = 1} ×
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (hνprob : IsProbabilityMeasure ν)
    (μ : Measure E4)
    (hmap : Measure.map
      (frontParametrization selector hmeasurable hvalid hselector) ν = μ) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
      ∀ K : ENNReal, K ≠ ⊤ →
        ∃ (x : E4) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
          K * (ENNReal.ofReal r).rpow (4 - epsilon) <
            μ (Metric.ball x r) := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hfailure⟩ := hboundary.2
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_⟩
  intro K hKTop
  obtain ⟨x, r, hr, hrOne, hlarge⟩ :=
    hfailure ν hνprob K hKTop
  refine ⟨x, r, hr, hrOne, ?_⟩
  calc
    K * (ENNReal.ofReal r).rpow (4 - epsilon) <
        ν ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
          Metric.ball x r) := hlarge
    _ = Measure.map
          (frontParametrization selector hmeasurable hvalid hselector) ν
          (Metric.ball x r) := by
        rw [Measure.map_apply
          (measurable_frontParametrization selector hmeasurable hvalid hselector)
          Metric.isOpen_ball.measurableSet]
    _ = μ (Metric.ball x r) := by rw [hmap]

/-- A bad physical ball for the readback measure produces an actual
factor-two union failure at the same scale.  The normalized collision ledger
then yields the quantitative marked collision-support lower bound with the
geometric tube capacity already substituted. -/
theorem parametrizedCoherentSources_badBall_to_collision
    (selector ambient : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hsources : HasParametrizedCoherentFiniteScaleSources selector ambient
      hmeasurable hvalid hselector)
    (sourceEpsilon : ℝ) (hsourceEpsilon : 0 < sourceEpsilon) :
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
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ x : E4,
          C * (2 * volume (Metric.closedBall x (2 * δ))) ≤
              μ (Metric.ball x δ) →
          ∃ n : ℕ, ∃ D R : FiniteScaleSource n,
            D.thickness = δ ∧
            ComesFromSelector D selector ∧
            (∀ i, (1 / 2 : ℝ) ≤ direction (D.line i) (3 : Fin 4)) ∧
            IsAdmissibleStickySource D sourceEpsilon C ∧
            IsFractionalSourceRestriction R D ∧
            sourceUnion R ⊆ Metric.closedBall x (2 * δ) ∧
            2 * volume (sourceUnion R) ≤ sourceMass R ∧
            sourceMass R ≤
              4 * (((sourceMarkedCollisionSupport R).card : ENNReal) *
                sourceGeometricEdgeCapacity D) := by
  obtain ⟨C, hC0, hCTop, μ, hμprob, hμsupport,
      ν, hνprob, hmap, _hnorthSupport,
      _Cfront, _hCfront0, _hCfrontTop, _hfront,
      δ₀, hδ₀, hsourcesδ⟩ :=
    hsources sourceEpsilon hsourceEpsilon
  refine ⟨C, hC0, hCTop, μ, hμprob, hμsupport,
    ν, hνprob, hmap, δ₀, hδ₀, ?_⟩
  intro δ hδ hδ₀ x hbad
  obtain ⟨n, D, hDδ, hDselector, hDnorth, hDadmissible,
      hDmassLower, hDmassUpper, hlocal, _haligned⟩ := hsourcesδ δ hδ hδ₀
  obtain ⟨R, hR, hRunion, hreadback⟩ := hlocal x
  have hfailure : 2 * volume (sourceUnion R) ≤ sourceMass R := by
    apply (ENNReal.mul_le_mul_iff_left hC0 hCTop).mp
    calc
      (2 * volume (sourceUnion R)) * C =
          C * (2 * volume (sourceUnion R)) := by ac_rfl
      _ ≤
          C * (2 * volume (Metric.closedBall x (2 * δ))) := by
        gcongr
      _ ≤ μ (Metric.ball x δ) := hbad
      _ ≤ C * sourceMass R := hreadback
      _ = sourceMass R * C := by ac_rfl
  refine ⟨n, D, R, hDδ, hDselector, hDnorth, hDadmissible, hR,
    hRunion, hfailure, ?_⟩
  exact factor_two_union_failure_forces_markedCollision_cardinality_geometric
    hDadmissible hR hfailure

/-- A probability measure which fails the `(4-epsilon)` Frostman bound with
arbitrarily large finite constants has geometric bad balls below every
prescribed radius.  The constant is chosen once, before the bad ball is
returned; hence the conclusion is strong enough for the source readback. -/
theorem failedFrostman_probability_has_small_geometric_badBall
    (μ : Measure E4) (hμprob : IsProbabilityMeasure μ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilonFour : epsilon < 4)
    (hfailure : ∀ K : ENNReal, K ≠ ⊤ →
      ∃ (x : E4) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
        K * (ENNReal.ofReal r).rpow (4 - epsilon) <
          μ (Metric.ball x r))
    (C : ENNReal) (hCTop : C ≠ ⊤) :
    ∀ rho : ℝ, 0 < rho →
      ∃ (x : E4) (r : ℝ), 0 < r ∧ r < rho ∧ r ≤ 1 ∧
        C * (2 * volume (Metric.closedBall x (2 * r))) ≤
          μ (Metric.ball x r) := by
  intro rho hrho
  let rhoCap : ℝ := min rho 1
  have hrhoCap : 0 < rhoCap := by
    dsimp [rhoCap]
    positivity
  have hrhoCapOne : rhoCap ≤ 1 := min_le_right _ _
  let q : ℝ := 4 - epsilon
  have hq : 0 < q := by dsimp [q]; linarith
  let κ : ENNReal :=
    ENNReal.ofReal (√Real.pi ^ Fintype.card (Fin 4) /
      Real.Gamma ((Fintype.card (Fin 4) : ℝ) / 2 + 1))
  let volumeConstant : ENNReal :=
    C * 2 * ((ENNReal.ofReal 3) ^ 4 * κ)
  let base : ENNReal := (ENNReal.ofReal rhoCap).rpow q
  have hbase0 : base ≠ 0 := by
    exact ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hrhoCap)
      ENNReal.ofReal_ne_top)
  have hbaseTop : base ≠ ⊤ := by
    exact ne_of_lt
      (ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
  let K : ENNReal := volumeConstant + base⁻¹
  have hvolumeConstantTop : volumeConstant ≠ ⊤ := by
    dsimp [volumeConstant, κ]
    finiteness
  have hKTop : K ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    exact ⟨hvolumeConstantTop, ENNReal.inv_ne_top.mpr hbase0⟩
  obtain ⟨x, r, hr, hrOne, hlarge⟩ := hfailure K hKTop
  have hrSmallCap : r < rhoCap := by
    by_contra hnot
    have hrhoCapLe : rhoCap ≤ r := le_of_not_gt hnot
    have hpowMono : base ≤ (ENNReal.ofReal r).rpow q := by
      exact ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal hrhoCapLe) hq.le
    have hone : 1 ≤ K * (ENNReal.ofReal r).rpow q := by
      calc
        1 = base⁻¹ * base :=
          (ENNReal.inv_mul_cancel hbase0 hbaseTop).symm
        _ ≤ base⁻¹ * (ENNReal.ofReal r).rpow q := by gcongr
        _ ≤ K * (ENNReal.ofReal r).rpow q := by
          gcongr
          exact le_add_left le_rfl
    have hprobability : μ (Metric.ball x r) ≤ 1 := by
      calc
        μ (Metric.ball x r) ≤ μ Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := hμprob.measure_univ
    have honeLt : 1 < μ (Metric.ball x r) :=
      lt_of_le_of_lt hone (by simpa [q] using hlarge)
    exact (not_lt_of_ge hprobability) honeLt
  have hrSmall : r < rho :=
    hrSmallCap.trans_le (min_le_left _ _)
  have htwoThree : 2 * r < 3 * r := by nlinarith
  have hvolume :
      volume (Metric.closedBall x (2 * r)) ≤
        (ENNReal.ofReal (3 * r)) ^ 4 * κ := by
    calc
      volume (Metric.closedBall x (2 * r)) ≤
          volume (Metric.ball x (3 * r)) :=
        measure_mono (Metric.closedBall_subset_ball htwoThree)
      _ = (ENNReal.ofReal (3 * r)) ^ 4 * κ := by
        simpa [κ] using EuclideanSpace.volume_ball (Fin 4) x (3 * r)
  have hrBase : ENNReal.ofReal r ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hrOne
  have hqFour : q ≤ 4 := by dsimp [q]; linarith
  have hrpowFour :
      (ENNReal.ofReal r) ^ 4 =
        (ENNReal.ofReal r).rpow (4 : ℝ) :=
    (ENNReal.rpow_natCast (ENNReal.ofReal r) 4).symm
  have hrpow :
      (ENNReal.ofReal r) ^ 4 ≤ (ENNReal.ofReal r).rpow q := by
    rw [hrpowFour]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hrBase hqFour
  have hscale :
      (ENNReal.ofReal (3 * r)) ^ 4 * κ =
        ((ENNReal.ofReal 3) ^ 4 * κ) * (ENNReal.ofReal r) ^ 4 := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), mul_pow]
    ac_rfl
  have hbad :
      C * (2 * volume (Metric.closedBall x (2 * r))) ≤
        μ (Metric.ball x r) := by
    calc
      C * (2 * volume (Metric.closedBall x (2 * r))) ≤
          C * (2 * ((ENNReal.ofReal (3 * r)) ^ 4 * κ)) := by
        gcongr
      _ = volumeConstant * (ENNReal.ofReal r) ^ 4 := by
        rw [hscale]
        simp only [volumeConstant]
        ac_rfl
      _ ≤ volumeConstant * (ENNReal.ofReal r).rpow q := by gcongr
      _ ≤ K * (ENNReal.ofReal r).rpow q := by
        gcongr
        exact le_add_right le_rfl
      _ ≤ μ (Metric.ball x r) := le_of_lt (by simpa [q] using hlarge)
  exact ⟨x, r, hr, hrSmall, hrOne, hbad⟩

/-- Gain-preserving bad-ball form.  Any exponent `eta` strictly below the
boundary loss survives as the scale-dependent multiplicity
`r^(-eta)`.  The extra `+ 1` pays the diagonal copy before the raw
off-diagonal collision energy is read back. -/
theorem failedFrostman_probability_has_small_scaled_geometric_badBall
    (μ : Measure E4) (hμprob : IsProbabilityMeasure μ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilonFour : epsilon < 4)
    (hfailure : ∀ K : ENNReal, K ≠ ⊤ →
      ∃ (x : E4) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
        K * (ENNReal.ofReal r).rpow (4 - epsilon) <
          μ (Metric.ball x r))
    (eta : ℝ) (heta0 : 0 ≤ eta) (hetaEpsilon : eta < epsilon)
    (C : ENNReal) (hCTop : C ≠ ⊤) :
    ∀ rho : ℝ, 0 < rho →
      ∃ (x : E4) (r : ℝ), 0 < r ∧ r < rho ∧ r ≤ 1 ∧
        0 < μ (Metric.ball x r) ∧
        C * (((ENNReal.ofReal r).rpow (-eta) + 1) *
          volume (Metric.closedBall x (2 * r))) ≤
            μ (Metric.ball x r) := by
  intro rho hrho
  let rhoCap : ℝ := min rho 1
  have hrhoCap : 0 < rhoCap := by
    dsimp [rhoCap]
    positivity
  let q : ℝ := 4 - epsilon
  have hq : 0 < q := by dsimp [q]; linarith
  let κ : ENNReal :=
    ENNReal.ofReal (√Real.pi ^ Fintype.card (Fin 4) /
      Real.Gamma ((Fintype.card (Fin 4) : ℝ) / 2 + 1))
  let geometricConstant : ENNReal :=
    C * ((ENNReal.ofReal 3) ^ 4 * κ)
  let base : ENNReal := (ENNReal.ofReal rhoCap).rpow q
  have hbase0 : base ≠ 0 := by
    exact ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hrhoCap)
      ENNReal.ofReal_ne_top)
  have hbaseTop : base ≠ ⊤ := by
    exact ne_of_lt
      (ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
  let K : ENNReal := 2 * geometricConstant + base⁻¹
  have hgeometricConstantTop : geometricConstant ≠ ⊤ := by
    dsimp [geometricConstant, κ]
    finiteness
  have hKTop : K ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.mul_ne_top (by norm_num) hgeometricConstantTop
    · exact ENNReal.inv_ne_top.mpr hbase0
  obtain ⟨x, r, hr, hrOne, hlarge⟩ := hfailure K hKTop
  have hrSmallCap : r < rhoCap := by
    by_contra hnot
    have hrhoCapLe : rhoCap ≤ r := le_of_not_gt hnot
    have hpowMono : base ≤ (ENNReal.ofReal r).rpow q := by
      exact ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal hrhoCapLe) hq.le
    have hone : 1 ≤ K * (ENNReal.ofReal r).rpow q := by
      calc
        1 = base⁻¹ * base :=
          (ENNReal.inv_mul_cancel hbase0 hbaseTop).symm
        _ ≤ base⁻¹ * (ENNReal.ofReal r).rpow q := by gcongr
        _ ≤ K * (ENNReal.ofReal r).rpow q := by
          gcongr
          exact le_add_left le_rfl
    have hprobability : μ (Metric.ball x r) ≤ 1 := by
      calc
        μ (Metric.ball x r) ≤ μ Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := hμprob.measure_univ
    have honeLt : 1 < μ (Metric.ball x r) :=
      lt_of_le_of_lt hone (by simpa [q] using hlarge)
    exact (not_lt_of_ge hprobability) honeLt
  have hrSmall : r < rho :=
    hrSmallCap.trans_le (min_le_left _ _)
  have htwoThree : 2 * r < 3 * r := by nlinarith
  have hvolume :
      volume (Metric.closedBall x (2 * r)) ≤
        (ENNReal.ofReal (3 * r)) ^ 4 * κ := by
    calc
      volume (Metric.closedBall x (2 * r)) ≤
          volume (Metric.ball x (3 * r)) :=
        measure_mono (Metric.closedBall_subset_ball htwoThree)
      _ = (ENNReal.ofReal (3 * r)) ^ 4 * κ := by
        simpa [κ] using EuclideanSpace.volume_ball (Fin 4) x (3 * r)
  have hr0 : ENNReal.ofReal r ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hr)
  have hrBase : ENNReal.ofReal r ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hrOne
  have hrpowFour :
      (ENNReal.ofReal r) ^ 4 =
        (ENNReal.ofReal r).rpow (4 : ℝ) :=
    (ENNReal.rpow_natCast (ENNReal.ofReal r) 4).symm
  have hpowEta :
      (ENNReal.ofReal r).rpow (-eta) * (ENNReal.ofReal r) ^ 4 =
        (ENNReal.ofReal r).rpow (4 - eta) := by
    rw [hrpowFour, show 4 - eta = -eta + 4 by ring]
    exact (ENNReal.rpow_add (-eta) 4 hr0 ENNReal.ofReal_ne_top).symm
  have hqEta : q ≤ 4 - eta := by dsimp [q]; linarith
  have hqFour : q ≤ 4 := by dsimp [q]; linarith
  have hscaledPower :
      ((ENNReal.ofReal r).rpow (-eta) + 1) *
          (ENNReal.ofReal r) ^ 4 ≤
        2 * (ENNReal.ofReal r).rpow q := by
    calc
      ((ENNReal.ofReal r).rpow (-eta) + 1) *
            (ENNReal.ofReal r) ^ 4 =
          (ENNReal.ofReal r).rpow (4 - eta) +
            (ENNReal.ofReal r).rpow (4 : ℝ) := by
        rw [add_mul, one_mul, hpowEta, hrpowFour]
      _ ≤ (ENNReal.ofReal r).rpow q +
            (ENNReal.ofReal r).rpow q := by
        apply add_le_add
        · exact ENNReal.rpow_le_rpow_of_exponent_ge hrBase hqEta
        · exact ENNReal.rpow_le_rpow_of_exponent_ge hrBase hqFour
      _ = 2 * (ENNReal.ofReal r).rpow q := by ring
  have hscale :
      (ENNReal.ofReal (3 * r)) ^ 4 * κ =
        ((ENNReal.ofReal 3) ^ 4 * κ) * (ENNReal.ofReal r) ^ 4 := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), mul_pow]
    ac_rfl
  have hbad :
      C * (((ENNReal.ofReal r).rpow (-eta) + 1) *
          volume (Metric.closedBall x (2 * r))) ≤
        μ (Metric.ball x r) := by
    calc
      C * (((ENNReal.ofReal r).rpow (-eta) + 1) *
          volume (Metric.closedBall x (2 * r))) ≤
        C * (((ENNReal.ofReal r).rpow (-eta) + 1) *
          ((ENNReal.ofReal (3 * r)) ^ 4 * κ)) := by gcongr
      _ = geometricConstant *
          (((ENNReal.ofReal r).rpow (-eta) + 1) *
            (ENNReal.ofReal r) ^ 4) := by
        rw [hscale]
        simp only [geometricConstant]
        ac_rfl
      _ ≤ geometricConstant *
          (2 * (ENNReal.ofReal r).rpow q) := by gcongr
      _ = (2 * geometricConstant) *
          (ENNReal.ofReal r).rpow q := by ac_rfl
      _ ≤ K * (ENNReal.ofReal r).rpow q := by
        gcongr
        exact le_add_right le_rfl
      _ ≤ μ (Metric.ball x r) := le_of_lt (by simpa [q] using hlarge)
  exact ⟨x, r, hr, hrSmall, hrOne,
    lt_of_le_of_lt bot_le hlarge, hbad⟩

/-- The coherent boundary and the parametrized finite-scale source interface
already force a genuine factor-two collision source at a strictly smaller
scale.  This is the closed no-WZ bridge from the infinite boundary to the
finite collision ledger; its conclusion contains no auxiliary bad-ball
hypothesis. -/
theorem coherentBoundary_parametrizedSources_produce_collision
    (selector ambient : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (hsources : HasParametrizedCoherentFiniteScaleSources selector ambient
      hmeasurable hvalid hselector)
    (sourceEpsilon : ℝ) (hsourceEpsilon : 0 < sourceEpsilon) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
    ∃ μ : Measure E4, IsProbabilityMeasure μ ∧
    ∃ ν : Measure
        ({theta : E4 // ‖theta‖ = 1} ×
          Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)),
      IsProbabilityMeasure ν ∧
      Measure.map
          (frontParametrization selector hmeasurable hvalid hselector) ν = μ ∧
      ∃ δ₀ δ : ℝ, 0 < δ₀ ∧ 0 < δ ∧ δ < δ₀ ∧
      ∃ x : E4, ∃ n : ℕ, ∃ D R : FiniteScaleSource n,
        D.thickness = δ ∧
        ComesFromSelector D selector ∧
        (∀ i, (1 / 2 : ℝ) ≤ direction (D.line i) (3 : Fin 4)) ∧
        IsAdmissibleStickySource D sourceEpsilon C ∧
        IsFractionalSourceRestriction R D ∧
        sourceUnion R ⊆ Metric.closedBall x (2 * δ) ∧
        2 * volume (sourceUnion R) ≤ sourceMass R ∧
        sourceMass R ≤
          4 * (((sourceMarkedCollisionSupport R).card : ENNReal) *
            sourceGeometricEdgeCapacity D) := by
  obtain ⟨C, hC0, hCTop, μ, hμprob, _hμsupport,
      ν, hνprob, hmap, δ₀, hδ₀, hsource⟩ :=
    parametrizedCoherentSources_badBall_to_collision selector ambient
      hmeasurable hvalid hselector hsources sourceEpsilon hsourceEpsilon
  obtain ⟨epsilon, hepsilon, hepsilonFour, hfailure⟩ :=
    coherentBoundary_failure_transfers_to_parametrized_source_measure
      selector hmeasurable hvalid hselector hboundary ν hνprob μ hmap
  obtain ⟨x, δ, hδ, hδsmall, _hδOne, hbad⟩ :=
    failedFrostman_probability_has_small_geometric_badBall μ hμprob
      epsilon hepsilon hepsilonFour hfailure C hCTop δ₀ hδ₀
  obtain ⟨n, D, R, hDδ, hDselector, hDnorth, hDadmissible, hR,
      hRunion, hRfailure, hcollision⟩ :=
    hsource δ hδ hδsmall.le x hbad
  exact ⟨epsilon, hepsilon, hepsilonFour, C, hC0, hCTop,
    μ, hμprob, ν, hνprob, hmap, δ₀, δ, hδ₀, hδ, hδsmall,
    x, n, D, R, hDδ, hDselector, hDnorth, hDadmissible, hR,
    hRunion, hRfailure, hcollision⟩

/-- Uniform strengthening of the preceding bridge: the boundary produces
factor-two collision sources below every requested positive radius (inside
the source interface range), all for the same physical probability measure
and the same source constant. -/
theorem coherentBoundary_parametrizedSources_produce_arbitrarilySmall_collisions
    (selector ambient : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (hsources : HasParametrizedCoherentFiniteScaleSources selector ambient
      hmeasurable hvalid hselector)
    (sourceEpsilon : ℝ) (hsourceEpsilon : 0 < sourceEpsilon) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
    ∃ μ : Measure E4, IsProbabilityMeasure μ ∧
    ∃ ν : Measure
        ({theta : E4 // ‖theta‖ = 1} ×
          Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)),
      IsProbabilityMeasure ν ∧
      Measure.map
          (frontParametrization selector hmeasurable hvalid hselector) ν = μ ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ δ₀ →
        ∃ δ : ℝ, 0 < δ ∧ δ < rho ∧
        ∃ x : E4, ∃ n : ℕ, ∃ D R : FiniteScaleSource n,
          D.thickness = δ ∧
          ComesFromSelector D selector ∧
          (∀ i, (1 / 2 : ℝ) ≤ direction (D.line i) (3 : Fin 4)) ∧
          IsAdmissibleStickySource D sourceEpsilon C ∧
          IsFractionalSourceRestriction R D ∧
          sourceUnion R ⊆ Metric.closedBall x (2 * δ) ∧
          2 * volume (sourceUnion R) ≤ sourceMass R ∧
          sourceMass R ≤
            4 * (((sourceMarkedCollisionSupport R).card : ENNReal) *
              sourceGeometricEdgeCapacity D) := by
  obtain ⟨C, hC0, hCTop, μ, hμprob, _hμsupport,
      ν, hνprob, hmap, δ₀, hδ₀, hsource⟩ :=
    parametrizedCoherentSources_badBall_to_collision selector ambient
      hmeasurable hvalid hselector hsources sourceEpsilon hsourceEpsilon
  obtain ⟨epsilon, hepsilon, hepsilonFour, hfailure⟩ :=
    coherentBoundary_failure_transfers_to_parametrized_source_measure
      selector hmeasurable hvalid hselector hboundary ν hνprob μ hmap
  refine ⟨epsilon, hepsilon, hepsilonFour, C, hC0, hCTop,
    μ, hμprob, ν, hνprob, hmap, δ₀, hδ₀, ?_⟩
  intro rho hrho hrhoδ₀
  obtain ⟨x, δ, hδ, hδsmall, _hδOne, hbad⟩ :=
    failedFrostman_probability_has_small_geometric_badBall μ hμprob
      epsilon hepsilon hepsilonFour hfailure C hCTop rho hrho
  obtain ⟨n, D, R, hDδ, hDselector, hDnorth, hDadmissible, hR,
      hRunion, hRfailure, hcollision⟩ :=
    hsource δ hδ (hδsmall.le.trans hrhoδ₀) x hbad
  exact ⟨δ, hδ, hδsmall, x, n, D, R, hDδ, hDselector,
    hDnorth, hDadmissible, hR, hRunion, hRfailure, hcollision⟩

/-- The gain-preserving boundary-to-source bridge.  At every requested small
scale it produces a localized fractional source for which the full
`delta^(-epsilon/2)` multiplicity survives in the raw off-diagonal energy.
This is the quantitative input needed by degree layers and DRC; no
row-normalization loss occurs in this statement. -/
theorem coherentBoundary_parametrizedSources_produce_arbitrarilySmall_scaledOffDiagonal
    (selector ambient : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (hsources : HasParametrizedCoherentFiniteScaleSources selector ambient
      hmeasurable hvalid hselector)
    (sourceEpsilon : ℝ) (hsourceEpsilon : 0 < sourceEpsilon) :
    ∃ epsilon eta : ℝ,
      0 < epsilon ∧ epsilon < 4 ∧
      0 < eta ∧ eta < epsilon ∧
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
    ∃ μ : Measure E4, IsProbabilityMeasure μ ∧
    ∃ ν : Measure
        ({theta : E4 // ‖theta‖ = 1} ×
          Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)),
      IsProbabilityMeasure ν ∧
      Measure.map
          (frontParametrization selector hmeasurable hvalid hselector) ν = μ ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ δ₀ →
        ∃ δ : ℝ, 0 < δ ∧ δ < rho ∧
        ∃ x : E4, ∃ n : ℕ, ∃ D R : FiniteScaleSource n,
          D.thickness = δ ∧
          ComesFromSelector D selector ∧
          (∀ i, (1 / 2 : ℝ) ≤ direction (D.line i) (3 : Fin 4)) ∧
          IsAdmissibleStickySource D sourceEpsilon C ∧
          IsFractionalSourceRestriction R D ∧
          sourceUnion R ⊆ Metric.closedBall x (2 * δ) ∧
          (4 * (ENNReal.ofReal δ).rpow (-eta) + 1) *
              volume (sourceUnion R) ≤ sourceMass R ∧
          (4 * (ENNReal.ofReal δ).rpow (-eta)) * sourceMass R ≤
              sourceOffDiagonalMass R ∧
          (4 * (ENNReal.ofReal δ).rpow (-eta)) * sourceMass R ≤
              ((sourceMarkedCollisionSupport R).card : ENNReal) *
                sourceGeometricEdgeCapacity D ∧
          (4 * (ENNReal.ofReal δ).rpow (-eta)) *
              (4 * (ENNReal.ofReal δ).rpow (-eta) + 1) ≤
                ((sourceMarkedCollisionSupport R).card : ENNReal) ∧
          ∃ (y : E4) (index : Fin 4 → Fin n),
            Function.Injective index ∧
            y ∈ Metric.closedBall x (2 * δ) ∧
            ∀ k, y ∈ R.shading (index k) ∧
              0 < R.weight (index k) := by
  obtain ⟨C, hC0, hCTop, μ, hμprob, _hμsupport,
      ν, hνprob, hmap, _hnorthSupport,
      _Cfront, _hCfront0, _hCfrontTop, _hfront,
      δ₀, hδ₀, hsourcesδ⟩ :=
    hsources sourceEpsilon hsourceEpsilon
  obtain ⟨epsilon, hepsilon, hepsilonFour, hfailure⟩ :=
    coherentBoundary_failure_transfers_to_parametrized_source_measure
      selector hmeasurable hvalid hselector hboundary ν hνprob μ hmap
  let eta : ℝ := epsilon / 2
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hetaEpsilon : eta < epsilon := by dsimp [eta]; linarith
  refine ⟨epsilon, eta, hepsilon, hepsilonFour, heta, hetaEpsilon,
    C, hC0, hCTop, μ, hμprob, ν, hνprob, hmap, δ₀, hδ₀, ?_⟩
  intro rho hrho hrhoδ₀
  obtain ⟨x, δ, hδ, hδsmall, hδOne, hμball,
      hbad⟩ :=
    failedFrostman_probability_has_small_scaled_geometric_badBall
      μ hμprob epsilon hepsilon hepsilonFour hfailure eta heta.le
      hetaEpsilon (4 * C) (ENNReal.mul_ne_top (by norm_num) hCTop) rho hrho
  obtain ⟨n, D, hDδ, hDselector, hDnorth, hDadmissible,
      _hDmassLower, _hDmassUpper, hlocal, _haligned⟩ :=
    hsourcesδ δ hδ (hδsmall.le.trans hrhoδ₀)
  obtain ⟨R, hR, hRunion, hreadback⟩ := hlocal x
  let gain : ENNReal := 4 * (ENNReal.ofReal δ).rpow (-eta)
  have hscaledFailure :
      (gain + 1) *
          volume (sourceUnion R) ≤ sourceMass R := by
    apply (ENNReal.mul_le_mul_iff_left hC0 hCTop).mp
    calc
      ((gain + 1) *
          volume (sourceUnion R)) * C =
        C * ((gain + 1) *
          volume (sourceUnion R)) := by ac_rfl
      _ ≤ C * ((4 * ((ENNReal.ofReal δ).rpow (-eta) + 1)) *
          volume (sourceUnion R)) := by
        gcongr
        dsimp [gain]
        calc
          4 * (ENNReal.ofReal δ).rpow (-eta) + 1 ≤
              4 * (ENNReal.ofReal δ).rpow (-eta) + 4 := by
            simpa [add_comm] using
              (add_le_add_left (by norm_num : (1 : ENNReal) ≤ 4)
                (4 * (ENNReal.ofReal δ).rpow (-eta)))
          _ = 4 * ((ENNReal.ofReal δ).rpow (-eta) + 1) := by ring
      _ ≤ C * ((4 * ((ENNReal.ofReal δ).rpow (-eta) + 1)) *
          volume (Metric.closedBall x (2 * δ))) := by
        gcongr
      _ = (4 * C) * (((ENNReal.ofReal δ).rpow (-eta) + 1) *
          volume (Metric.closedBall x (2 * δ))) := by ring
      _ ≤ μ (Metric.ball x δ) := hbad
      _ ≤ C * sourceMass R := hreadback
      _ = sourceMass R * C := by ac_rfl
  have hmass0 : sourceMass R ≠ 0 := by
    intro hmass
    have hzero : μ (Metric.ball x δ) ≤ 0 := by
      simpa [hmass] using hreadback
    exact (not_lt_of_ge hzero) hμball
  have hoffDiagonal :=
    scaled_union_failure_forces_source_offDiagonal_of_fractional_admissible
      hDadmissible hR hmass0 hscaledFailure
  have hmarked :=
    scaled_union_failure_forces_markedCollision_cardinality_geometric
      hDadmissible hR hmass0 hscaledFailure
  have hquadratic :=
    scaled_union_failure_forces_markedCollision_cardinality_quadratic
      hDadmissible hR hmass0 hscaledFailure
  have hbaseOne : ENNReal.ofReal δ ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hδOne
  have hrpowOne : (1 : ENNReal) ≤
      (ENNReal.ofReal δ).rpow (-eta) :=
    ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      (ENNReal.ofReal_pos.mpr hδ) hbaseOne (by linarith)
  have hgain : (3 : ENNReal) < gain + 1 := by
    calc
      (3 : ENNReal) < 4 * 1 + 1 := by norm_num
      _ ≤ gain + 1 := by
        dsimp [gain]
        have hmul : (4 : ENNReal) * 1 ≤
            4 * (ENNReal.ofReal δ).rpow (-eta) := by
          simpa [mul_comm] using
            (mul_le_mul_right hrpowOne (4 : ENNReal))
        simpa [add_comm] using add_le_add_right hmul 1
  obtain ⟨y, index, hindex, hrows⟩ :=
    scaled_union_failure_has_four_distinct_common_shading_rows
      hDadmissible hR hmass0 hgain hscaledFailure
  have hyUnion : y ∈ sourceUnion R :=
    shading_subset_sourceUnion_of_weight_pos R (index 0) (hrows 0).2
      (hrows 0).1
  exact ⟨δ, hδ, hδsmall, x, n, D, R, hDδ, hDselector,
    hDnorth, hDadmissible, hR, hRunion, hscaledFailure, hoffDiagonal, hmarked,
    hquadratic, y, index, hindex, hRunion hyUnion, hrows⟩

/-- Four distinct retained rows through one physical point give an honest
four-line contact packet at the single common height of that point.  The north
chart bound makes the residual estimate uniform, while the selector and
distinct-line data are preserved exactly. -/
theorem four_commonShadingRows_give_commonHeight_selector_contactCycle
    (selector : Set MarkedLine) {n : ℕ} {D R : FiniteScaleSource n}
    {sourceEpsilon δ eta : ℝ} {C : ENNReal}
    (hDδ : D.thickness = δ)
    (hδ : 0 < δ) (heta : 0 < eta)
    (hDselector : ComesFromSelector D selector)
    (hDnorth : ∀ i, (1 / 2 : ℝ) ≤ direction (D.line i) (3 : Fin 4))
    (hD : IsAdmissibleStickySource D sourceEpsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (y : E4) (index : Fin 4 → Fin n)
    (hindex : Function.Injective index)
    (hrows : ∀ k, y ∈ R.shading (index k) ∧ 0 < R.weight (index k)) :
    Function.Injective (fun k : Fin 4 => R.line (index k)) ∧
    (∀ k, R.line (index k) ∈ selector) ∧
    (∀ k, (1 / 2 : ℝ) ≤
      direction (R.line (index k)) (3 : Fin 4)) ∧
    ∀ k,
      markedPairContactResidualNorm
          (R.line (index k), R.line (index (fourCycleNext k)))
          (y (3 : Fin 4)) < 6 * (δ + eta) ∧
      markedPairContactResidualNorm
          (R.line (index (fourCycleNext k)), R.line (index k))
          (y (3 : Fin 4)) < 6 * (δ + eta) := by
  have hRline : R.line = D.line := hR.2.1
  have hRδ : R.thickness = δ := hR.1.trans hDδ
  have hnorth : ∀ k, (1 / 2 : ℝ) ≤
      direction (R.line (index k)) (3 : Fin 4) := by
    intro k
    rw [congrFun hRline (index k)]
    exact hDnorth (index k)
  have hlineInjective :
      Function.Injective (fun k : Fin 4 => R.line (index k)) := by
    intro a b hab
    exact hindex (R.line_injective hab)
  refine ⟨hlineInjective, ?_, hnorth, ?_⟩
  · intro k
    rw [congrFun hRline (index k)]
    exact hDselector (index k)
  · intro k
    have hkiAbs : (1 / 2 : ℝ) ≤
        |direction (R.line (index k)) (3 : Fin 4)| := by
      rw [abs_of_nonneg (le_trans (by norm_num) (hnorth k))]
      exact hnorth k
    have hkjAbs : (1 / 2 : ℝ) ≤
        |direction (R.line (index (fourCycleNext k))) (3 : Fin 4)| := by
      rw [abs_of_nonneg
        (le_trans (by norm_num) (hnorth (fourCycleNext k)))]
      exact hnorth (fourCycleNext k)
    have hkiChart :
        direction (R.line (index k)) (3 : Fin 4) ≠ 0 :=
      abs_pos.mp ((lt_of_lt_of_le (by norm_num) hkiAbs))
    have hkjChart :
        direction (R.line (index (fourCycleNext k))) (3 : Fin 4) ≠ 0 :=
      abs_pos.mp ((lt_of_lt_of_le (by norm_num) hkjAbs))
    have hcontact :=
      commonShadingPoint_has_contact_residual_control hD hR y
        (hrows k).1 (hrows (fourCycleNext k)).1 hkiChart hkjChart heta
    have hkiInv :
        |(direction (R.line (index k)) (3 : Fin 4))⁻¹| ≤ 2 := by
      simpa using
        (abs_inv_le_inv_of_pos_le_abs (x :=
          direction (R.line (index k)) (3 : Fin 4))
          (kappa := (1 / 2 : ℝ)) (by norm_num) hkiAbs)
    have hkjInv :
        |(direction (R.line (index (fourCycleNext k))) (3 : Fin 4))⁻¹| ≤ 2 := by
      simpa using
        (abs_inv_le_inv_of_pos_le_abs (x :=
          direction (R.line (index (fourCycleNext k))) (3 : Fin 4))
          (kappa := (1 / 2 : ℝ)) (by norm_num) hkjAbs)
    have hcoeff :
        |(direction (R.line (index k)) (3 : Fin 4))⁻¹| +
            |(direction (R.line (index (fourCycleNext k))) (3 : Fin 4))⁻¹| + 2 ≤
          6 := by
      linarith
    have hscale : 0 ≤ R.thickness + eta := by
      rw [hRδ]
      linarith
    constructor
    · calc
        markedPairContactResidualNorm
            (R.line (index k), R.line (index (fourCycleNext k)))
            (y (3 : Fin 4)) <
            (|(direction (R.line (index k)) (3 : Fin 4))⁻¹| +
                |(direction (R.line (index (fourCycleNext k))) (3 : Fin 4))⁻¹| + 2) *
              (R.thickness + eta) := hcontact.1
        _ ≤ 6 * (R.thickness + eta) :=
          mul_le_mul_of_nonneg_right hcoeff hscale
        _ = 6 * (δ + eta) := by rw [hRδ]
    · calc
        markedPairContactResidualNorm
            (R.line (index (fourCycleNext k)), R.line (index k))
            (y (3 : Fin 4)) <
            (|(direction (R.line (index k)) (3 : Fin 4))⁻¹| +
                |(direction (R.line (index (fourCycleNext k))) (3 : Fin 4))⁻¹| + 2) *
              (R.thickness + eta) := hcontact.2
        _ ≤ 6 * (R.thickness + eta) :=
          mul_le_mul_of_nonneg_right hcoeff hscale
        _ = 6 * (δ + eta) := by rw [hRδ]

/-- A failed coherent Frostman boundary therefore produces, at every small
scale, a genuine four-line selector packet whose four cyclic contact edges
share one physical height and have `O(delta)` residual.  The quadratic marked
collision lower bound is retained for the subsequent coefficient-one
Carleson routing. -/
theorem coherentBoundary_produces_arbitrarilySmall_commonHeightContactCycles
    (selector ambient : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector)
    (hsources : HasParametrizedCoherentFiniteScaleSources selector ambient
      hmeasurable hvalid hselector)
    (sourceEpsilon : ℝ) (hsourceEpsilon : 0 < sourceEpsilon) :
    ∃ epsilon eta : ℝ,
      0 < epsilon ∧ epsilon < 4 ∧
      0 < eta ∧ eta < epsilon ∧
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ δ₀ →
        ∃ δ : ℝ, 0 < δ ∧ δ < rho ∧
        ∃ n : ℕ, ∃ D R : FiniteScaleSource n,
        ∃ y : E4, ∃ index : Fin 4 → Fin n,
          D.thickness = δ ∧
          ComesFromSelector D selector ∧
          (∀ i, (1 / 2 : ℝ) ≤ direction (D.line i) (3 : Fin 4)) ∧
          IsAdmissibleStickySource D sourceEpsilon C ∧
          IsFractionalSourceRestriction R D ∧
          (4 * (ENNReal.ofReal δ).rpow (-eta) + 1) *
              volume (sourceUnion R) ≤ sourceMass R ∧
          (4 * (ENNReal.ofReal δ).rpow (-eta)) *
              (4 * (ENNReal.ofReal δ).rpow (-eta) + 1) ≤
                ((sourceMarkedCollisionSupport R).card : ENNReal) ∧
          Function.Injective index ∧
          (∀ k, y ∈ R.shading (index k) ∧
            0 < R.weight (index k)) ∧
          Function.Injective (fun k : Fin 4 => R.line (index k)) ∧
          (∀ k, R.line (index k) ∈ selector) ∧
          (∀ k, (1 / 2 : ℝ) ≤
            direction (R.line (index k)) (3 : Fin 4)) ∧
          ∀ k,
            markedPairContactResidualNorm
                (R.line (index k), R.line (index (fourCycleNext k)))
                (y (3 : Fin 4)) < 12 * δ ∧
            markedPairContactResidualNorm
                (R.line (index (fourCycleNext k)), R.line (index k))
                (y (3 : Fin 4)) < 12 * δ := by
  obtain ⟨epsilon, eta, hepsilon, hepsilonFour, heta, hetaEpsilon,
      C, hC0, hCTop, _μ, _hμprob, _ν, _hνprob, _hmap,
      δ₀, hδ₀, hsmall⟩ :=
    coherentBoundary_parametrizedSources_produce_arbitrarilySmall_scaledOffDiagonal
      selector ambient hmeasurable hvalid hselector hboundary hsources
        sourceEpsilon hsourceEpsilon
  refine ⟨epsilon, eta, hepsilon, hepsilonFour, heta, hetaEpsilon,
    C, hC0, hCTop, δ₀, hδ₀, ?_⟩
  intro rho hrho hrhoδ₀
  obtain ⟨δ, hδ, hδrho, _x, n, D, R, hDδ, hDselector, hDnorth,
      hD, hR, _hRunion, hfailure, _hoffDiagonal, _hmarked, hquadratic,
      y, index, hindex, _hyBall, hrows⟩ := hsmall rho hrho hrhoδ₀
  obtain ⟨hlineInjective, hlineSelector, hlineNorth, hcontact⟩ :=
    four_commonShadingRows_give_commonHeight_selector_contactCycle
      selector hDδ hδ hδ hDselector hDnorth hD hR y index hindex hrows
  refine ⟨δ, hδ, hδrho, n, D, R, y, index, hDδ, hDselector,
    hDnorth, hD, hR, hfailure, hquadratic, hindex, hrows,
    hlineInjective, hlineSelector, hlineNorth, ?_⟩
  intro k
  constructor
  · convert (hcontact k).1 using 1 <;> ring
  · convert (hcontact k).2 using 1 <;> ring

end StickyKakeya4
