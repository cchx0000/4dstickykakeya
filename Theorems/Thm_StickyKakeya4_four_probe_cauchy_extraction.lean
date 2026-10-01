import Theorems.Thm_StickyKakeya4_three_packet_support

open Filter
open MeasureTheory
open scoped Topology

namespace StickyKakeya4

universe u

/-- Summable geometric motion gives the Cauchy coherence required on an
infinite retained branch. -/
theorem cauchySeq_of_geometric_successive_dist
    {X : Type u} [PseudoMetricSpace X] (u : ℕ → X)
    (C q : ℝ) (_hC : 0 ≤ C) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hstep : ∀ n, dist (u n) (u (n + 1)) ≤ C * q ^ n) :
    CauchySeq u := by
  apply cauchySeq_of_summable_dist
  exact ((summable_geometric_of_lt_one hq₀ hq₁).mul_left C).of_nonneg_of_le
    (fun n ↦ dist_nonneg) hstep

/-- A sequence in a product uniform space is Cauchy when every coordinate
sequence is Cauchy. -/
theorem cauchySeq_pi_of_coordinate
    {ι : Type u} {α : ι → Type*} [Nonempty ι]
    [∀ i, UniformSpace (α i)] (u : ℕ → (i : ι) → α i)
    (hcoordinate : ∀ i, CauchySeq (fun n ↦ u n i)) :
    CauchySeq u := by
  change Cauchy (Filter.map u atTop)
  rw [cauchy_pi_iff]
  intro i
  rw [Filter.map_map]
  change Cauchy (Filter.map (fun n ↦ u n i) atTop)
  exact hcoordinate i

/-- The manuscript's predetermined cap contraction turns any quantity whose
one-step motion is Lipschitz in the current cap radius into a geometric
successive-distance bound. -/
theorem successive_dist_le_geometric_of_contracting_cap
    {X : Type u} [PseudoMetricSpace X]
    (u : ℕ → X) (capRadius : ℕ → ℝ)
    (initialRadius branchingFactor motionConstant : ℝ)
    (hbranching : 1 < branchingFactor)
    (hmotion_nonneg : 0 ≤ motionConstant)
    (hcap_zero : capRadius 0 ≤ initialRadius)
    (hcap_step : ∀ k, capRadius (k + 1) ≤ capRadius k / branchingFactor)
    (hmotion : ∀ n,
      dist (u n) (u (n + 1)) ≤ motionConstant * capRadius n) :
    ∀ n, dist (u n) (u (n + 1)) ≤
      (motionConstant * initialRadius) * branchingFactor⁻¹ ^ n := by
  intro n
  have hbranching_pos : 0 < branchingFactor := lt_trans zero_lt_one hbranching
  have hcap := deterministic_cap_contraction_iterate
    capRadius initialRadius branchingFactor hbranching_pos
      hcap_zero hcap_step n
  calc
    dist (u n) (u (n + 1)) ≤ motionConstant * capRadius n := hmotion n
    _ ≤ motionConstant * (initialRadius / branchingFactor ^ n) :=
      mul_le_mul_of_nonneg_left hcap hmotion_nonneg
    _ = (motionConstant * initialRadius) * branchingFactor⁻¹ ^ n := by
      rw [div_eq_mul_inv, inv_pow]
      ring

/-- Finite-depth data carried by one compatible fresh-return history.  The
geometric part of the tree only has to prove Cauchy coherence, a fixed Reeb
gap, normalized flags, vanishing incidence residuals, and one uniform
horizontal noncollapse constant.  All limiting objects are then supplied by
completeness rather than postulated. -/
structure CauchyFourProbeBoundarySequence where
  approxA : ℕ → Mat3
  approxB : ℕ → Mat3
  approxTime : ℕ → Fin 4 → ℝ
  approxCoeff : ℕ → Fin 4 → E3
  timeGap : ℝ
  timeGap_pos : 0 < timeGap
  timeSeparated : ∀ n i j, i ≠ j →
    timeGap ≤ |approxTime n i - approxTime n j|
  cauchyA : CauchySeq approxA
  cauchyB : CauchySeq approxB
  cauchyTime : ∀ i, CauchySeq (fun n ↦ approxTime n i)
  cauchyCoeff : ∀ i, CauchySeq (fun n ↦ approxCoeff n i)
  coeffUnit : ∀ n i, ‖approxCoeff n i‖ = 1
  residualTendsto : ∀ i,
    Tendsto
      (fun n ↦
        (pencil (approxA n) (approxB n) (approxTime n i)).mulVec
          (approxCoeff n i))
      atTop (𝓝 0)
  noncollapseConstant : ℝ
  noncollapseConstant_pos : 0 < noncollapseConstant
  horizontalNoncollapse : ∀ (n : ℕ) (c : E3),
    noncollapseConstant * ‖c‖ ≤
      ‖horizontalFrameVector (approxA n) c‖

/-- Raw output of a geometrically contracting fresh-return path.  Unlike the
Cauchy certificate, its coherence fields are the adjacent-level estimates
that the cap contraction ledger supplies directly. -/
structure GeometricFourProbeBoundarySequence where
  approxA : ℕ → Mat3
  approxB : ℕ → Mat3
  approxTime : ℕ → Fin 4 → ℝ
  approxCoeff : ℕ → Fin 4 → E3
  timeGap : ℝ
  timeGap_pos : 0 < timeGap
  timeSeparated : ∀ n i j, i ≠ j →
    timeGap ≤ |approxTime n i - approxTime n j|
  contraction : ℝ
  contraction_nonneg : 0 ≤ contraction
  contraction_lt_one : contraction < 1
  stepConstant : ℝ
  stepConstant_nonneg : 0 ≤ stepConstant
  stepA : ∀ n i j,
    dist (approxA n i j) (approxA (n + 1) i j) ≤
      stepConstant * contraction ^ n
  stepB : ∀ n i j,
    dist (approxB n i j) (approxB (n + 1) i j) ≤
      stepConstant * contraction ^ n
  stepTime : ∀ n i,
    dist (approxTime n i) (approxTime (n + 1) i) ≤
      stepConstant * contraction ^ n
  stepCoeff : ∀ n i,
    dist (approxCoeff n i) (approxCoeff (n + 1) i) ≤
      stepConstant * contraction ^ n
  coeffUnit : ∀ n i, ‖approxCoeff n i‖ = 1
  residualTendsto : ∀ i,
    Tendsto
      (fun n ↦
        (pencil (approxA n) (approxB n) (approxTime n i)).mulVec
          (approxCoeff n i))
      atTop (𝓝 0)
  noncollapseConstant : ℝ
  noncollapseConstant_pos : 0 < noncollapseConstant
  horizontalNoncollapse : ∀ (n : ℕ) (c : E3),
    noncollapseConstant * ‖c‖ ≤
      ‖horizontalFrameVector (approxA n) c‖

/-- Fresh-return data in the literal form delivered by the carrier tree: all
labels move by at most a fixed multiple of the current cap radius, while that
radius contracts by the predetermined factor at every retained generation. -/
structure CapControlledFourProbeBoundarySequence where
  approxA : ℕ → Mat3
  approxB : ℕ → Mat3
  approxTime : ℕ → Fin 4 → ℝ
  approxCoeff : ℕ → Fin 4 → E3
  timeGap : ℝ
  timeGap_pos : 0 < timeGap
  timeSeparated : ∀ n i j, i ≠ j →
    timeGap ≤ |approxTime n i - approxTime n j|
  capRadius : ℕ → ℝ
  initialRadius : ℝ
  initialRadius_nonneg : 0 ≤ initialRadius
  branchingFactor : ℝ
  branchingFactor_gt_one : 1 < branchingFactor
  capRadius_zero : capRadius 0 ≤ initialRadius
  capRadius_step : ∀ n,
    capRadius (n + 1) ≤ capRadius n / branchingFactor
  motionConstant : ℝ
  motionConstant_nonneg : 0 ≤ motionConstant
  motionA : ∀ n i j,
    dist (approxA n i j) (approxA (n + 1) i j) ≤
      motionConstant * capRadius n
  motionB : ∀ n i j,
    dist (approxB n i j) (approxB (n + 1) i j) ≤
      motionConstant * capRadius n
  motionTime : ∀ n i,
    dist (approxTime n i) (approxTime (n + 1) i) ≤
      motionConstant * capRadius n
  motionCoeff : ∀ n i,
    dist (approxCoeff n i) (approxCoeff (n + 1) i) ≤
      motionConstant * capRadius n
  coeffUnit : ∀ n i, ‖approxCoeff n i‖ = 1
  residualTendsto : ∀ i,
    Tendsto
      (fun n ↦
        (pencil (approxA n) (approxB n) (approxTime n i)).mulVec
          (approxCoeff n i))
      atTop (𝓝 0)
  noncollapseConstant : ℝ
  noncollapseConstant_pos : 0 < noncollapseConstant
  horizontalNoncollapse : ∀ (n : ℕ) (c : E3),
    noncollapseConstant * ‖c‖ ≤
      ‖horizontalFrameVector (approxA n) c‖

/-- Read the deterministic cap contraction as the geometric ratio used by
the compactness extractor. -/
noncomputable def CapControlledFourProbeBoundarySequence.toGeometric
    (sequence : CapControlledFourProbeBoundarySequence) :
    GeometricFourProbeBoundarySequence where
  approxA := sequence.approxA
  approxB := sequence.approxB
  approxTime := sequence.approxTime
  approxCoeff := sequence.approxCoeff
  timeGap := sequence.timeGap
  timeGap_pos := sequence.timeGap_pos
  timeSeparated := sequence.timeSeparated
  contraction := sequence.branchingFactor⁻¹
  contraction_nonneg := inv_nonneg.mpr
    (le_trans zero_le_one sequence.branchingFactor_gt_one.le)
  contraction_lt_one :=
    (inv_lt_one₀ (lt_trans zero_lt_one sequence.branchingFactor_gt_one)).2
      sequence.branchingFactor_gt_one
  stepConstant := sequence.motionConstant * sequence.initialRadius
  stepConstant_nonneg :=
    mul_nonneg sequence.motionConstant_nonneg sequence.initialRadius_nonneg
  stepA := fun n i j ↦ successive_dist_le_geometric_of_contracting_cap
    (fun k ↦ sequence.approxA k i j) sequence.capRadius
      sequence.initialRadius sequence.branchingFactor sequence.motionConstant
      sequence.branchingFactor_gt_one sequence.motionConstant_nonneg
      sequence.capRadius_zero sequence.capRadius_step
      (fun k ↦ sequence.motionA k i j) n
  stepB := fun n i j ↦ successive_dist_le_geometric_of_contracting_cap
    (fun k ↦ sequence.approxB k i j) sequence.capRadius
      sequence.initialRadius sequence.branchingFactor sequence.motionConstant
      sequence.branchingFactor_gt_one sequence.motionConstant_nonneg
      sequence.capRadius_zero sequence.capRadius_step
      (fun k ↦ sequence.motionB k i j) n
  stepTime := fun n i ↦ successive_dist_le_geometric_of_contracting_cap
    (fun k ↦ sequence.approxTime k i) sequence.capRadius
      sequence.initialRadius sequence.branchingFactor sequence.motionConstant
      sequence.branchingFactor_gt_one sequence.motionConstant_nonneg
      sequence.capRadius_zero sequence.capRadius_step
      (fun k ↦ sequence.motionTime k i) n
  stepCoeff := fun n i ↦ successive_dist_le_geometric_of_contracting_cap
    (fun k ↦ sequence.approxCoeff k i) sequence.capRadius
      sequence.initialRadius sequence.branchingFactor sequence.motionConstant
      sequence.branchingFactor_gt_one sequence.motionConstant_nonneg
      sequence.capRadius_zero sequence.capRadius_step
      (fun k ↦ sequence.motionCoeff k i) n
  coeffUnit := sequence.coeffUnit
  residualTendsto := sequence.residualTendsto
  noncollapseConstant := sequence.noncollapseConstant
  noncollapseConstant_pos := sequence.noncollapseConstant_pos
  horizontalNoncollapse := sequence.horizontalNoncollapse

/-- Convert the literal cap-contraction estimates into the Cauchy boundary
certificate consumed by compactness. -/
def GeometricFourProbeBoundarySequence.toCauchy
    (sequence : GeometricFourProbeBoundarySequence) :
    CauchyFourProbeBoundarySequence where
  approxA := sequence.approxA
  approxB := sequence.approxB
  approxTime := sequence.approxTime
  approxCoeff := sequence.approxCoeff
  timeGap := sequence.timeGap
  timeGap_pos := sequence.timeGap_pos
  timeSeparated := sequence.timeSeparated
  cauchyA := cauchySeq_pi_of_coordinate sequence.approxA (fun i ↦
    cauchySeq_pi_of_coordinate (fun n j ↦ sequence.approxA n i j) (fun j ↦
      cauchySeq_of_geometric_successive_dist
        (fun n ↦ sequence.approxA n i j)
        sequence.stepConstant sequence.contraction
        sequence.stepConstant_nonneg sequence.contraction_nonneg
        sequence.contraction_lt_one (fun n ↦ sequence.stepA n i j)))
  cauchyB := cauchySeq_pi_of_coordinate sequence.approxB (fun i ↦
    cauchySeq_pi_of_coordinate (fun n j ↦ sequence.approxB n i j) (fun j ↦
      cauchySeq_of_geometric_successive_dist
        (fun n ↦ sequence.approxB n i j)
        sequence.stepConstant sequence.contraction
        sequence.stepConstant_nonneg sequence.contraction_nonneg
        sequence.contraction_lt_one (fun n ↦ sequence.stepB n i j)))
  cauchyTime := fun i ↦ cauchySeq_of_geometric_successive_dist
    (fun n ↦ sequence.approxTime n i)
      sequence.stepConstant sequence.contraction
      sequence.stepConstant_nonneg sequence.contraction_nonneg
      sequence.contraction_lt_one (fun n ↦ sequence.stepTime n i)
  cauchyCoeff := fun i ↦ cauchySeq_of_geometric_successive_dist
    (fun n ↦ sequence.approxCoeff n i)
      sequence.stepConstant sequence.contraction
      sequence.stepConstant_nonneg sequence.contraction_nonneg
      sequence.contraction_lt_one (fun n ↦ sequence.stepCoeff n i)
  coeffUnit := sequence.coeffUnit
  residualTendsto := sequence.residualTendsto
  noncollapseConstant := sequence.noncollapseConstant
  noncollapseConstant_pos := sequence.noncollapseConstant_pos
  horizontalNoncollapse := sequence.horizontalNoncollapse

/-- Uniform horizontal noncollapse survives a Cauchy limit and makes the
limiting horizontal frame injective. -/
theorem horizontal_limit_injective_of_uniform_noncollapse
    (approxA : ℕ → Mat3) (limitA : Mat3)
    (tendstoA : Tendsto approxA atTop (𝓝 limitA))
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hnoncollapse : ∀ (n : ℕ) (c : E3),
      kappa * ‖c‖ ≤ ‖horizontalFrameVector (approxA n) c‖) :
    Function.Injective (fun c : E3 ↦ limitA.mulVec c) := by
  have hlower : ∀ c : E3,
      kappa * ‖c‖ ≤ ‖horizontalFrameVector limitA c‖ := by
    intro c
    have hvector :
        Tendsto
          (fun n ↦ horizontalFrameVector (approxA n) c)
          atTop (𝓝 (horizontalFrameVector limitA c)) := by
      exact continuous_horizontalFrameVector.continuousAt.tendsto.comp
        (tendstoA.prodMk_nhds tendsto_const_nhds)
    have hnorm :
        Tendsto
          (fun n ↦ ‖horizontalFrameVector (approxA n) c‖)
          atTop (𝓝 ‖horizontalFrameVector limitA c‖) :=
      tendsto_norm.comp hvector
    apply isClosed_Ici.mem_of_tendsto hnorm
    filter_upwards [] with n
    exact hnoncollapse n c
  intro c d hcd
  change limitA.mulVec c.ofLp = limitA.mulVec d.ofLp at hcd
  have hkernel : limitA.mulVec (c - d) = 0 := by
    change limitA.mulVec (c.ofLp - d.ofLp) = 0
    rw [Matrix.mulVec_sub, hcd, sub_self]
  have hhorizontal : horizontalFrameVector limitA (c - d) = 0 := by
    unfold horizontalFrameVector
    apply (WithLp.ext_iff 2).mpr
    simpa using hkernel
  have hbound := hlower (c - d)
  rw [hhorizontal, norm_zero] at hbound
  have hnonneg : 0 ≤ kappa * ‖c - d‖ :=
    mul_nonneg hkappa.le (norm_nonneg _)
  have hproduct : kappa * ‖c - d‖ = 0 :=
    le_antisymm hbound hnonneg
  have hnorm : ‖c - d‖ = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt hkappa)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- A compatible Cauchy four-probe history with a uniform noncollapsed
horizontal frame is impossible.  This is the compactness extraction and the
Maslov terminal in one theorem; no determinant convergence and no external
Kakeya estimate are assumed. -/
theorem CauchyFourProbeBoundarySequence.impossible
    (sequence : CauchyFourProbeBoundarySequence) : False := by
  obtain ⟨limitA, tendstoA⟩ :=
    cauchySeq_tendsto_of_complete sequence.cauchyA
  obtain ⟨limitB, tendstoB⟩ :=
    cauchySeq_tendsto_of_complete sequence.cauchyB
  choose limitTime tendstoTime using fun i ↦
    cauchySeq_tendsto_of_complete (sequence.cauchyTime i)
  choose limitCoeff tendstoCoeff using fun i ↦
    cauchySeq_tendsto_of_complete (sequence.cauchyCoeff i)
  have hAinjective :
      Function.Injective (fun c : E3 ↦ limitA.mulVec c) :=
    horizontal_limit_injective_of_uniform_noncollapse
      sequence.approxA limitA tendstoA sequence.noncollapseConstant
      sequence.noncollapseConstant_pos sequence.horizontalNoncollapse
  have hframe :
      Function.Injective
        (fun c : E3 ↦ (limitA.mulVec c, limitB.mulVec c)) := by
    intro c d hcd
    exact hAinjective (congrArg Prod.fst hcd)
  let packet : FourProbeConcentrationLimit :=
    { approxA := sequence.approxA
      approxB := sequence.approxB
      approxTime := sequence.approxTime
      approxCoeff := sequence.approxCoeff
      limitA := limitA
      limitB := limitB
      limitTime := limitTime
      limitCoeff := limitCoeff
      frameInjective := hframe
      timeGap := sequence.timeGap
      timeGap_pos := sequence.timeGap_pos
      timeSeparated := sequence.timeSeparated
      tendstoA := tendstoA
      tendstoB := tendstoB
      tendstoTime := tendstoTime
      tendstoCoeff := tendstoCoeff
      coeffUnit := sequence.coeffUnit
      residualTendsto := sequence.residualTendsto }
  exact packet.no_uniform_horizontal_noncollapse
    sequence.noncollapseConstant sequence.noncollapseConstant_pos
      sequence.horizontalNoncollapse

/-- Geometrically contracting four-probe fresh-return data cannot persist to
infinite depth in the noncollapsed branch. -/
theorem GeometricFourProbeBoundarySequence.impossible
    (sequence : GeometricFourProbeBoundarySequence) : False :=
  sequence.toCauchy.impossible

/-- A cap-controlled noncollapsed four-probe path cannot survive forever. -/
theorem CapControlledFourProbeBoundarySequence.impossible
    (sequence : CapControlledFourProbeBoundarySequence) : False :=
  sequence.toGeometric.impossible

/-- Boundary-to-three-packet reduction with no pre-existing limiting plane in
the hypotheses.  It suffices that every four-separated support tuple supplies
the finite-depth Cauchy data produced by the fresh-return tree. -/
theorem probability_measure_three_packets_of_cauchy_four_probe_extraction
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (delta : ℝ)
    (hextract : ∀ s₀ ∈ nu.support, ∀ s₁ ∈ nu.support,
      ∀ s₂ ∈ nu.support, ∀ s₃ ∈ nu.support,
      delta < |s₀ - s₁| ∧ delta < |s₀ - s₂| ∧
        delta < |s₀ - s₃| ∧ delta < |s₁ - s₂| ∧
        delta < |s₁ - s₃| ∧ delta < |s₂ - s₃| →
      Nonempty CauchyFourProbeBoundarySequence) :
    ∃ t₀ t₁ t₂ : ℝ,
      (∀ s ∈ nu.support,
        |s - t₀| ≤ delta ∨ |s - t₁| ≤ delta ∨ |s - t₂| ≤ delta) ∧
      nu {s : ℝ |
        delta < |s - t₀| ∧ delta < |s - t₁| ∧ delta < |s - t₂|} = 0 := by
  apply probability_measure_three_packets_of_no_four_separated nu delta
  intro s₀ hs₀ s₁ hs₁ s₂ hs₂ s₃ hs₃ hsep
  exact (hextract s₀ hs₀ s₁ hs₁ s₂ hs₂ s₃ hs₃ hsep).elim
    CauchyFourProbeBoundarySequence.impossible

/-- Version whose extraction hypothesis consists only of adjacent-level
geometric contraction estimates. -/
theorem probability_measure_three_packets_of_geometric_four_probe_extraction
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (delta : ℝ)
    (hextract : ∀ s₀ ∈ nu.support, ∀ s₁ ∈ nu.support,
      ∀ s₂ ∈ nu.support, ∀ s₃ ∈ nu.support,
      delta < |s₀ - s₁| ∧ delta < |s₀ - s₂| ∧
        delta < |s₀ - s₃| ∧ delta < |s₁ - s₂| ∧
        delta < |s₁ - s₃| ∧ delta < |s₂ - s₃| →
      Nonempty GeometricFourProbeBoundarySequence) :
    ∃ t₀ t₁ t₂ : ℝ,
      (∀ s ∈ nu.support,
        |s - t₀| ≤ delta ∨ |s - t₁| ≤ delta ∨ |s - t₂| ≤ delta) ∧
      nu {s : ℝ |
        delta < |s - t₀| ∧ delta < |s - t₁| ∧ delta < |s - t₂|} = 0 := by
  apply probability_measure_three_packets_of_no_four_separated nu delta
  intro s₀ hs₀ s₁ hs₁ s₂ hs₂ s₃ hs₃ hsep
  exact (hextract s₀ hs₀ s₁ hs₁ s₂ hs₂ s₃ hs₃ hsep).elim
    GeometricFourProbeBoundarySequence.impossible

/-- Final tree-facing form: cap-controlled four-probe extraction forces the
surviving Reeb-time law into three packets up to a null set. -/
theorem probability_measure_three_packets_of_cap_controlled_four_probe_extraction
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (delta : ℝ)
    (hextract : ∀ s₀ ∈ nu.support, ∀ s₁ ∈ nu.support,
      ∀ s₂ ∈ nu.support, ∀ s₃ ∈ nu.support,
      delta < |s₀ - s₁| ∧ delta < |s₀ - s₂| ∧
        delta < |s₀ - s₃| ∧ delta < |s₁ - s₂| ∧
        delta < |s₁ - s₃| ∧ delta < |s₂ - s₃| →
      Nonempty CapControlledFourProbeBoundarySequence) :
    ∃ t₀ t₁ t₂ : ℝ,
      (∀ s ∈ nu.support,
        |s - t₀| ≤ delta ∨ |s - t₁| ≤ delta ∨ |s - t₂| ≤ delta) ∧
      nu {s : ℝ |
        delta < |s - t₀| ∧ delta < |s - t₁| ∧ delta < |s - t₂|} = 0 := by
  apply probability_measure_three_packets_of_no_four_separated nu delta
  intro s₀ hs₀ s₁ hs₁ s₂ hs₂ s₃ hs₃ hsep
  exact (hextract s₀ hs₀ s₁ hs₁ s₂ hs₂ s₃ hs₃ hsep).elim
    CapControlledFourProbeBoundarySequence.impossible

end StickyKakeya4
