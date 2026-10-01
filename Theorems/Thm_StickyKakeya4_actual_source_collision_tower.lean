import Theorems.Thm_StickyKakeya4_actual_source_collision_packet
import Theorems.Thm_StickyKakeya4_marked_four_cycle_return_tower

open Filter Set Topology

noncomputable section

namespace StickyKakeya4

/-- A retained finite source at which the DRC gates hold and the three-packet
stopping alternative is absent.  All collision data come from the actual
same-population marked source; `noThreePacket` is precisely the continuation
condition of the four-probe branch. -/
structure ActualSourceFourProbeContinuationNode
    (selector : Set MarkedLine) (timeGap residualBound : ℝ) where
  n : ℕ
  D : FiniteScaleSource n
  R : FiniteScaleSource n
  epsilon : ℝ
  packingConstant : ENNReal
  admissible : IsAdmissibleStickySource D epsilon packingConstant
  fractional : IsFractionalSourceRestriction R D
  line_mem_selector : ∀ i, R.line i ∈ selector
  n_pos : 0 < n
  kappa : ℝ
  kappa_pos : 0 < kappa
  chart : ∀ i, kappa ≤ |direction (R.line i) (3 : Fin 4)|
  eta : ℝ
  eta_pos : 0 < eta
  density : ℝ
  density_pos : 0 < density
  density_le_one : density ≤ 1
  collision_dense : density * (n : ℝ) * (n : ℝ) ≤
    ((sourceMarkedCollisionSupport R).card : ℝ)
  left_large : 4 ≤ density * (n : ℝ)
  right_large : 8 < density ^ 2 * (n : ℝ)
  residualBound_eq :
    (2 * kappa⁻¹ + 2) * (R.thickness + eta) = residualBound
  noThreePacket :
    ∀ (line : Fin 4 → MarkedLine) (approxTime : Fin 4 → ℝ),
      Function.Injective line →
      (∀ i, line i ∈ selector) →
      (∀ i, direction (line i) (3 : Fin 4) ≠ 0) →
      (∀ i,
        ‖(fourCycleEdgeSecant line i).2 +
            approxTime i • (fourCycleEdgeSecant line i).1‖ <
          (2 * kappa⁻¹ + 2) * (R.thickness + eta)) →
      ¬ FourTimesLieInThreePackets approxTime timeGap

/-- At a continuation node the actual-source dichotomy has only its normalized
four-probe branch: the literal three-packet output contradicts the stopping
condition. -/
theorem ActualSourceFourProbeContinuationNode.hasNormalizedPacket
    {selector : Set MarkedLine} {timeGap residualBound : ℝ}
    (node : ActualSourceFourProbeContinuationNode selector timeGap
      residualBound) :
    Nonempty (NormalizedMarkedFourCyclePacket selector timeGap
      residualBound) := by
  rcases sourceMarkedCollisionSupport_has_normalized_packet_or_three_packets
      node.admissible node.fractional selector node.line_mem_selector
      node.n_pos node.kappa node.kappa_pos node.chart node.eta node.eta_pos
      node.density node.density_pos node.density_le_one
      node.collision_dense node.left_large node.right_large timeGap with
    hpacket | hthree
  · simpa [node.residualBound_eq] using hpacket
  · obtain ⟨line, approxTime, hline, hselector, hchart, hresidual,
      hthree⟩ := hthree
    exact (node.noThreePacket line approxTime hline hselector hchart
      hresidual hthree).elim

/-- Canonical choice of the surviving normalized packet, made only after the
propositional actual-source extraction theorem. -/
noncomputable def ActualSourceFourProbeContinuationNode.toNormalizedPacket
    {selector : Set MarkedLine} {timeGap residualBound : ℝ}
    (node : ActualSourceFourProbeContinuationNode selector timeGap
      residualBound) :
    NormalizedMarkedFourCyclePacket selector timeGap residualBound :=
  Classical.choice node.hasNormalizedPacket

/-- A pruned finite-branching carrier whose every node is an actual finite
source in the four-probe continuation branch. -/
structure PrunedActualSourceFourProbeTree
    (selector : Set MarkedLine) where
  Node : ℕ → Type
  nodeFinite : ∀ n, Finite (Node n)
  root : Node 0
  parent : ∀ n, Node (n + 1) → Node n
  hasChild : ∀ n (x : Node n), ∃ y : Node (n + 1), parent n y = x
  timeGap : ℝ
  timeGap_pos : 0 < timeGap
  residualBound : ℕ → ℝ
  residualBound_nonneg : ∀ n, 0 ≤ residualBound n
  residualBound_tendsto_zero : Tendsto residualBound atTop (nhds 0)
  sourceNode : ∀ n, Node n →
    ActualSourceFourProbeContinuationNode selector timeGap (residualBound n)
  capRadius : ℕ → ℝ
  capRadius_nonneg : ∀ n, 0 ≤ capRadius n
  initialRadius : ℝ
  initialRadius_nonneg : 0 ≤ initialRadius
  branchingFactor : ℝ
  branchingFactor_gt_one : 1 < branchingFactor
  capRadius_zero : capRadius 0 ≤ initialRadius
  capRadius_step : ∀ n,
    capRadius (n + 1) ≤ capRadius n / branchingFactor

noncomputable def PrunedActualSourceFourProbeTree.packet
    {selector : Set MarkedLine}
    (tree : PrunedActualSourceFourProbeTree selector)
    (n : ℕ) (x : tree.Node n) :
    NormalizedMarkedFourCyclePacket selector tree.timeGap
      (tree.residualBound n) :=
  (tree.sourceNode n x).toNormalizedPacket

noncomputable def PrunedActualSourceFourProbeTree.line
    {selector : Set MarkedLine}
    (tree : PrunedActualSourceFourProbeTree selector)
    (n : ℕ) (x : tree.Node n) : Fin 4 → MarkedLine :=
  (tree.packet n x).line

noncomputable def PrunedActualSourceFourProbeTree.approxTime
    {selector : Set MarkedLine}
    (tree : PrunedActualSourceFourProbeTree selector)
    (n : ℕ) (x : tree.Node n) : Fin 4 → ℝ :=
  (tree.packet n x).approxTime

/-- Interscale coherence and noncollapse for the packets extracted from the
actual retained sources. -/
structure PrunedActualSourceFourProbeTower
    (selector : Set MarkedLine) where
  tree : PrunedActualSourceFourProbeTree selector
  motionConstant : ℝ
  motionConstant_nonneg : 0 ≤ motionConstant
  motionA : ∀ n (y : tree.Node (n + 1)) i j,
    dist
        (anchoredCycleA (tree.line n (tree.parent n y)) i j)
        (anchoredCycleA (tree.line (n + 1) y) i j) ≤
      motionConstant * tree.capRadius n
  motionB : ∀ n (y : tree.Node (n + 1)) i j,
    dist
        (anchoredCycleB (tree.line n (tree.parent n y)) i j)
        (anchoredCycleB (tree.line (n + 1) y) i j) ≤
      motionConstant * tree.capRadius n
  motionTime : ∀ n (y : tree.Node (n + 1)) i,
    dist
        (tree.approxTime n (tree.parent n y) i)
        (tree.approxTime (n + 1) y i) ≤
      motionConstant * tree.capRadius n
  noncollapseConstant : ℝ
  noncollapseConstant_pos : 0 < noncollapseConstant
  horizontalNoncollapse : ∀ n (x : tree.Node n) (c : E3),
    noncollapseConstant * ‖c‖ ≤
      ‖horizontalFrameVector (anchoredCycleA (tree.line n x)) c‖

/-- Forget the source bookkeeping after the actual collision graph has
produced its normalized four-probe packet at every retained node. -/
noncomputable def PrunedActualSourceFourProbeTower.toMarkedReturnTower
    {selector : Set MarkedLine}
    (tower : PrunedActualSourceFourProbeTower selector) :
    PrunedMarkedFourCycleReturnTower selector where
  Node := tower.tree.Node
  nodeFinite := tower.tree.nodeFinite
  root := tower.tree.root
  parent := tower.tree.parent
  hasChild := tower.tree.hasChild
  line := tower.tree.line
  line_mem_selector := fun n x i ↦
    (tower.tree.packet n x).line_mem_selector i
  chartNonzero := fun n x i ↦
    (tower.tree.packet n x).chartNonzero i
  approxTime := tower.tree.approxTime
  timeGap := tower.tree.timeGap
  timeGap_pos := tower.tree.timeGap_pos
  timeSeparated := fun n x i j hij ↦
    (tower.tree.packet n x).timeSeparated i j hij
  capRadius := tower.tree.capRadius
  capRadius_nonneg := tower.tree.capRadius_nonneg
  initialRadius := tower.tree.initialRadius
  initialRadius_nonneg := tower.tree.initialRadius_nonneg
  branchingFactor := tower.tree.branchingFactor
  branchingFactor_gt_one := tower.tree.branchingFactor_gt_one
  capRadius_zero := tower.tree.capRadius_zero
  capRadius_step := tower.tree.capRadius_step
  motionConstant := tower.motionConstant
  motionConstant_nonneg := tower.motionConstant_nonneg
  motionA := tower.motionA
  motionB := tower.motionB
  motionTime := tower.motionTime
  residualBound := tower.tree.residualBound
  residualBound_nonneg := tower.tree.residualBound_nonneg
  residualBound_tendsto_zero := tower.tree.residualBound_tendsto_zero
  physicalCycleResidual := fun n x i ↦
    (tower.tree.packet n x).physicalCycleResidual i
  noncollapseConstant := tower.noncollapseConstant
  noncollapseConstant_pos := tower.noncollapseConstant_pos
  horizontalNoncollapse := tower.horizontalNoncollapse

/-- The actual-source four-probe continuation branch cannot persist through an
infinite pruned tower: it is exactly the marked return tower excluded by the
Maslov firewall. -/
theorem PrunedActualSourceFourProbeTower.impossible
    {selector : Set MarkedLine}
    (tower : PrunedActualSourceFourProbeTower selector) : False :=
  tower.toMarkedReturnTower.impossible

end StickyKakeya4
