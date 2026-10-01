import Theorems.Thm_StickyKakeya4_normalized_collision_relation_packet
import Theorems.Thm_StickyKakeya4_marked_four_cycle_return_tower

open Filter Set Topology

noncomputable section

namespace StickyKakeya4

/-- Finite collision data at one retained node.  It contains no preselected
four-cycle: that packet is extracted from density by dependent random choice. -/
structure DenseSeparatedMarkedCollisionRelation
    (selector : Set MarkedLine) (timeGap residualBound : ℝ) where
  X : Finset MarkedLine
  Y : Finset MarkedLine
  disjoint : Disjoint X Y
  X_nonempty : X.Nonempty
  Y_nonempty : Y.Nonempty
  X_mem_selector : ∀ line ∈ X, line ∈ selector
  Y_mem_selector : ∀ line ∈ Y, line ∈ selector
  X_chartNonzero : ∀ line ∈ X, direction line (3 : Fin 4) ≠ 0
  Y_chartNonzero : ∀ line ∈ Y, direction line (3 : Fin 4) ≠ 0
  edge : Finset (MarkedLine × MarkedLine)
  edge_subset : edge ⊆ X ×ˢ Y
  density : ℝ
  density_pos : 0 < density
  density_le_one : density ≤ 1
  edge_dense : density * (X.card : ℝ) * (Y.card : ℝ) ≤
    (edge.card : ℝ)
  X_large : 4 ≤ density * (X.card : ℝ)
  Y_large : 8 < density ^ 2 * (Y.card : ℝ)
  edgeTime : (MarkedLine × MarkedLine) → ℝ
  edgeTimeSeparated : ∀ p ∈ edge, ∀ q ∈ edge, p ≠ q →
    timeGap ≤ |edgeTime p - edgeTime q|
  edgeResidual : ∀ p ∈ edge,
    markedPairContactResidualNorm p (edgeTime p) ≤ residualBound ∧
    markedPairContactResidualNorm (p.2, p.1) (edgeTime p) ≤ residualBound

/-- The canonical choice of a tower-ready packet from a dense collision
relation.  Choice is used only after the finite DRC existence theorem; the
geometric objects themselves are not defined recursively. -/
noncomputable def DenseSeparatedMarkedCollisionRelation.toNormalizedPacket
    {selector : Set MarkedLine} {timeGap residualBound : ℝ}
    (relation : DenseSeparatedMarkedCollisionRelation selector timeGap
      residualBound)
    (htimeGap : 0 < timeGap) :
    NormalizedMarkedFourCyclePacket selector timeGap residualBound :=
  Classical.choice
    (dense_bipartite_has_normalized_marked_four_cycle_packet
      selector relation.X relation.Y relation.disjoint relation.X_nonempty
      relation.Y_nonempty relation.X_mem_selector relation.Y_mem_selector
      relation.edge relation.edge_subset relation.density
      relation.density_pos relation.density_le_one relation.edge_dense
      relation.X_large relation.Y_large relation.edgeTime timeGap htimeGap
      relation.edgeTimeSeparated residualBound relation.edgeResidual
      relation.X_chartNonzero relation.Y_chartNonzero)

/-- A pruned tree carrying one dense collision relation at every node, along
with the contracting scale and residual schedules. -/
structure PrunedDenseMarkedCollisionRelationTree
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
  relation : ∀ n, Node n →
    DenseSeparatedMarkedCollisionRelation selector timeGap (residualBound n)
  capRadius : ℕ → ℝ
  capRadius_nonneg : ∀ n, 0 ≤ capRadius n
  initialRadius : ℝ
  initialRadius_nonneg : 0 ≤ initialRadius
  branchingFactor : ℝ
  branchingFactor_gt_one : 1 < branchingFactor
  capRadius_zero : capRadius 0 ≤ initialRadius
  capRadius_step : ∀ n,
    capRadius (n + 1) ≤ capRadius n / branchingFactor

noncomputable def PrunedDenseMarkedCollisionRelationTree.packet
    {selector : Set MarkedLine}
    (tree : PrunedDenseMarkedCollisionRelationTree selector)
    (n : ℕ) (x : tree.Node n) :
    NormalizedMarkedFourCyclePacket selector tree.timeGap
      (tree.residualBound n) :=
  (tree.relation n x).toNormalizedPacket tree.timeGap_pos

noncomputable def PrunedDenseMarkedCollisionRelationTree.line
    {selector : Set MarkedLine}
    (tree : PrunedDenseMarkedCollisionRelationTree selector)
    (n : ℕ) (x : tree.Node n) : Fin 4 → MarkedLine :=
  (tree.packet n x).line

noncomputable def PrunedDenseMarkedCollisionRelationTree.approxTime
    {selector : Set MarkedLine}
    (tree : PrunedDenseMarkedCollisionRelationTree selector)
    (n : ℕ) (x : tree.Node n) : Fin 4 → ℝ :=
  (tree.packet n x).approxTime

/-- The remaining interscale hypotheses are now stated only for the packets
canonically extracted from the node relations.  Thus line membership, chart
validity, four-time separation, and normalized residual decay are conclusions
of the finite relation data rather than independent tower assumptions. -/
structure PrunedDenseMarkedCollisionRelationTower
    (selector : Set MarkedLine) where
  tree : PrunedDenseMarkedCollisionRelationTree selector
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

/-- Forget the collision relations after DRC has extracted their actual
marked four-cycles. -/
noncomputable def PrunedDenseMarkedCollisionRelationTower.toMarkedReturnTower
    {selector : Set MarkedLine}
    (tower : PrunedDenseMarkedCollisionRelationTower selector) :
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

/-- No infinite pruned tower of dense separated marked collision relations can
satisfy the compatible motion and horizontal noncollapse estimates. -/
theorem PrunedDenseMarkedCollisionRelationTower.impossible
    {selector : Set MarkedLine}
    (tower : PrunedDenseMarkedCollisionRelationTower selector) : False :=
  tower.toMarkedReturnTower.impossible

end StickyKakeya4
