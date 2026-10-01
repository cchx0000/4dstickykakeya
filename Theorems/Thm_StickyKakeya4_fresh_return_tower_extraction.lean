import Theorems.Thm_StickyKakeya4_four_probe_cauchy_extraction

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace StickyKakeya4

/-- A pruned finite-branching tower of fresh-return packets.  Each level is
finite, every retained node has a child, and all geometric data are attached
to nodes rather than postulated along a preselected infinite branch.  The
residual estimate is quantitative and uniform on a level. -/
structure PrunedFreshReturnFourProbeTower where
  Node : ℕ → Type
  nodeFinite : ∀ n, Finite (Node n)
  root : Node 0
  parent : ∀ n, Node (n + 1) → Node n
  hasChild : ∀ n (x : Node n), ∃ y : Node (n + 1), parent n y = x
  approxA : ∀ n, Node n → Mat3
  approxB : ∀ n, Node n → Mat3
  approxTime : ∀ n, Node n → Fin 4 → ℝ
  approxCoeff : ∀ n, Node n → Fin 4 → E3
  timeGap : ℝ
  timeGap_pos : 0 < timeGap
  timeSeparated : ∀ n (x : Node n) i j, i ≠ j →
    timeGap ≤ |approxTime n x i - approxTime n x j|
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
  motionA : ∀ n (y : Node (n + 1)) i j,
    dist (approxA n (parent n y) i j) (approxA (n + 1) y i j) ≤
      motionConstant * capRadius n
  motionB : ∀ n (y : Node (n + 1)) i j,
    dist (approxB n (parent n y) i j) (approxB (n + 1) y i j) ≤
      motionConstant * capRadius n
  motionTime : ∀ n (y : Node (n + 1)) i,
    dist (approxTime n (parent n y) i) (approxTime (n + 1) y i) ≤
      motionConstant * capRadius n
  motionCoeff : ∀ n (y : Node (n + 1)) i,
    dist (approxCoeff n (parent n y) i) (approxCoeff (n + 1) y i) ≤
      motionConstant * capRadius n
  coeffUnit : ∀ n (x : Node n) i, ‖approxCoeff n x i‖ = 1
  residualBound : ℕ → ℝ
  residualBound_nonneg : ∀ n, 0 ≤ residualBound n
  residualBound_tendsto_zero : Tendsto residualBound atTop (nhds 0)
  residualNorm : ∀ n (x : Node n) i,
    ‖(pencil (approxA n x) (approxB n x) (approxTime n x i)).mulVec
        (approxCoeff n x i)‖ ≤ residualBound n
  noncollapseConstant : ℝ
  noncollapseConstant_pos : 0 < noncollapseConstant
  horizontalNoncollapse : ∀ n (x : Node n) (c : E3),
    noncollapseConstant * ‖c‖ ≤
      ‖horizontalFrameVector (approxA n x) c‖

/-- Choice of one compatible node on every level of a pruned tower.  This is
only the compactness/choice readback of `hasChild`; none of the geometric
objects are defined recursively. -/
noncomputable def PrunedFreshReturnFourProbeTower.compatibleNode
    (tower : PrunedFreshReturnFourProbeTower) :
    (n : ℕ) → tower.Node n
  | 0 => tower.root
  | n + 1 => Classical.choose (tower.hasChild n (tower.compatibleNode n))

@[simp] theorem PrunedFreshReturnFourProbeTower.parent_compatibleNode
    (tower : PrunedFreshReturnFourProbeTower) (n : ℕ) :
    tower.parent n (tower.compatibleNode (n + 1)) =
      tower.compatibleNode n := by
  simpa [PrunedFreshReturnFourProbeTower.compatibleNode] using
    Classical.choose_spec (tower.hasChild n (tower.compatibleNode n))

/-- Extract the literal cap-controlled four-probe sequence carried by one
compatible path.  Uniform levelwise residual bounds give convergence of the
incidence residuals; no limiting plane or determinant is assumed. -/
noncomputable def PrunedFreshReturnFourProbeTower.toCapControlled
    (tower : PrunedFreshReturnFourProbeTower) :
    CapControlledFourProbeBoundarySequence where
  approxA := fun n ↦ tower.approxA n (tower.compatibleNode n)
  approxB := fun n ↦ tower.approxB n (tower.compatibleNode n)
  approxTime := fun n ↦ tower.approxTime n (tower.compatibleNode n)
  approxCoeff := fun n ↦ tower.approxCoeff n (tower.compatibleNode n)
  timeGap := tower.timeGap
  timeGap_pos := tower.timeGap_pos
  timeSeparated := fun n i j hij ↦
    tower.timeSeparated n (tower.compatibleNode n) i j hij
  capRadius := tower.capRadius
  initialRadius := tower.initialRadius
  initialRadius_nonneg := tower.initialRadius_nonneg
  branchingFactor := tower.branchingFactor
  branchingFactor_gt_one := tower.branchingFactor_gt_one
  capRadius_zero := tower.capRadius_zero
  capRadius_step := tower.capRadius_step
  motionConstant := tower.motionConstant
  motionConstant_nonneg := tower.motionConstant_nonneg
  motionA := fun n i j ↦ by
    simpa using tower.motionA n (tower.compatibleNode (n + 1)) i j
  motionB := fun n i j ↦ by
    simpa using tower.motionB n (tower.compatibleNode (n + 1)) i j
  motionTime := fun n i ↦ by
    simpa using tower.motionTime n (tower.compatibleNode (n + 1)) i
  motionCoeff := fun n i ↦ by
    simpa using tower.motionCoeff n (tower.compatibleNode (n + 1)) i
  coeffUnit := fun n i ↦
    tower.coeffUnit n (tower.compatibleNode n) i
  residualTendsto := fun i ↦ by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hevent : ∀ᶠ n in atTop, tower.residualBound n < ε :=
      (tendsto_order.1 tower.residualBound_tendsto_zero).2 ε hε
    rw [eventually_atTop] at hevent
    obtain ⟨N, hN⟩ := hevent
    refine ⟨N, ?_⟩
    intro n hn
    simpa [dist_zero_right] using
      (lt_of_le_of_lt
        (tower.residualNorm n (tower.compatibleNode n) i) (hN n hn))
  noncollapseConstant := tower.noncollapseConstant
  noncollapseConstant_pos := tower.noncollapseConstant_pos
  horizontalNoncollapse := fun n c ↦
    tower.horizontalNoncollapse n (tower.compatibleNode n) c

/-- A pruned finite-branching fresh-return tower cannot have infinite depth
in the uniformly noncollapsed four-probe branch. -/
theorem PrunedFreshReturnFourProbeTower.impossible
    (tower : PrunedFreshReturnFourProbeTower) : False :=
  tower.toCapControlled.impossible

/-- Tree-facing three-packet conclusion.  It is enough to construct a pruned
fresh-return tower from every four-separated support tuple; the tower itself
is then ruled out by cap contraction and the Maslov firewall. -/
theorem probability_measure_three_packets_of_pruned_fresh_return_tower
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (delta : ℝ)
    (hextract : ∀ s₀ ∈ nu.support, ∀ s₁ ∈ nu.support,
      ∀ s₂ ∈ nu.support, ∀ s₃ ∈ nu.support,
      delta < |s₀ - s₁| ∧ delta < |s₀ - s₂| ∧
        delta < |s₀ - s₃| ∧ delta < |s₁ - s₂| ∧
        delta < |s₁ - s₃| ∧ delta < |s₂ - s₃| →
      Nonempty PrunedFreshReturnFourProbeTower) :
    ∃ t₀ t₁ t₂ : ℝ,
      (∀ s ∈ nu.support,
        |s - t₀| ≤ delta ∨ |s - t₁| ≤ delta ∨ |s - t₂| ≤ delta) ∧
      nu {s : ℝ |
        delta < |s - t₀| ∧ delta < |s - t₁| ∧ delta < |s - t₂|} = 0 := by
  apply probability_measure_three_packets_of_no_four_separated nu delta
  intro s₀ hs₀ s₁ hs₁ s₂ hs₂ s₃ hs₃ hsep
  exact (hextract s₀ hs₀ s₁ hs₁ s₂ hs₂ s₃ hs₃ hsep).elim
    PrunedFreshReturnFourProbeTower.impossible

end StickyKakeya4
