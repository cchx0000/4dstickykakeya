import Theorems.Thm_StickyKakeya4_collision_time_coherent_motion
import Theorems.Thm_StickyKakeya4_marked_four_cycle_return_tower

open Filter

noncomputable section

namespace StickyKakeya4

/-- A pruned compatible carrier whose retained four-probe packet remembers
the physical comparison height at every node. -/
structure PrunedCommonHeightAnalyticFourCycleTree
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
  packet : ∀ n, Node n →
    CommonHeightAnalyticFourCyclePacket selector timeGap (residualBound n)
  capRadius : ℕ → ℝ
  capRadius_nonneg : ∀ n, 0 ≤ capRadius n
  initialRadius : ℝ
  initialRadius_nonneg : 0 ≤ initialRadius
  branchingFactor : ℝ
  branchingFactor_gt_one : 1 < branchingFactor
  capRadius_zero : capRadius 0 ≤ initialRadius
  capRadius_step : ∀ n,
    capRadius (n + 1) ≤ capRadius n / branchingFactor

/-- Coherence data expressed only for graph frames and common physical
heights.  Collision-time motion is intentionally absent: it is derived below
from the exact collision identity. -/
structure PrunedCommonHeightAnalyticFourCycleTower
    (selector : Set MarkedLine) where
  tree : PrunedCommonHeightAnalyticFourCycleTree selector
  frameMotionConstant : ℝ
  frameMotionConstant_nonneg : 0 ≤ frameMotionConstant
  motionA : ∀ n (y : tree.Node (n + 1)) i j,
    dist
        (anchoredCycleA (tree.packet n (tree.parent n y)).line i j)
        (anchoredCycleA (tree.packet (n + 1) y).line i j) ≤
      frameMotionConstant * tree.capRadius n
  motionB : ∀ n (y : tree.Node (n + 1)) i j,
    dist
        (anchoredCycleB (tree.packet n (tree.parent n y)).line i j)
        (anchoredCycleB (tree.packet (n + 1) y).line i j) ≤
      frameMotionConstant * tree.capRadius n
  heightMotionConstant : ℝ
  heightMotionConstant_nonneg : 0 ≤ heightMotionConstant
  motionCommonHeight : ∀ n (y : tree.Node (n + 1)),
    dist (tree.packet n (tree.parent n y)).commonHeight
        (tree.packet (n + 1) y).commonHeight ≤
      heightMotionConstant * tree.capRadius n
  residualConstant : ℝ
  residualConstant_nonneg : 0 ≤ residualConstant
  residualBound_le_cap : ∀ n,
    tree.residualBound n ≤ residualConstant * tree.capRadius n
  residualBound_succ_le_cap : ∀ n,
    tree.residualBound (n + 1) ≤ residualConstant * tree.capRadius n
  noncollapseConstant : ℝ
  noncollapseConstant_pos : 0 < noncollapseConstant
  horizontalNoncollapse : ∀ n (x : tree.Node n) (c : E3),
    noncollapseConstant * ‖c‖ ≤
      ‖horizontalFrameVector
        (anchoredCycleA (tree.packet n x).line) c‖

/-- One constant controls both graph-frame motion and the collision-time
motion derived from the two residual errors. -/
def PrunedCommonHeightAnalyticFourCycleTower.motionConstant
    {selector : Set MarkedLine}
    (tower : PrunedCommonHeightAnalyticFourCycleTower selector) : ℝ :=
  max tower.frameMotionConstant
    (2 * tower.residualConstant / tower.noncollapseConstant +
      tower.heightMotionConstant)

theorem PrunedCommonHeightAnalyticFourCycleTower.motionConstant_nonneg
    {selector : Set MarkedLine}
    (tower : PrunedCommonHeightAnalyticFourCycleTower selector) :
    0 ≤ tower.motionConstant := by
  exact tower.frameMotionConstant_nonneg.trans
    (le_max_left _ _)

/-- The exact collision identity supplies the time-motion field required by
the old compactness tower. -/
theorem PrunedCommonHeightAnalyticFourCycleTower.motionCollisionTime
    {selector : Set MarkedLine}
    (tower : PrunedCommonHeightAnalyticFourCycleTower selector)
    (n : ℕ) (y : tower.tree.Node (n + 1)) (i : Fin 4) :
    dist
        (fourCycleCollisionTime
          (tower.tree.packet n (tower.tree.parent n y)).line i)
        (fourCycleCollisionTime
          (tower.tree.packet (n + 1) y).line i) ≤
      tower.motionConstant * tower.tree.capRadius n := by
  let parentPacket := tower.tree.packet n (tower.tree.parent n y)
  let childPacket := tower.tree.packet (n + 1) y
  have hraw :=
    fourCycleCollisionTime_motion_of_noncollapsed_commonHeight_returns
      parentPacket.line childPacket.line
      parentPacket.commonHeight childPacket.commonHeight
      (tower.tree.residualBound n) (tower.tree.residualBound (n + 1))
      tower.noncollapseConstant
      (tower.tree.residualBound_nonneg n)
      (tower.tree.residualBound_nonneg (n + 1))
      tower.noncollapseConstant_pos
      (tower.horizontalNoncollapse n (tower.tree.parent n y))
      (tower.horizontalNoncollapse (n + 1) y)
      parentPacket.commonHeightResidual childPacket.commonHeightResidual i
  have hparentDiv :
      tower.tree.residualBound n / tower.noncollapseConstant ≤
        (tower.residualConstant * tower.tree.capRadius n) /
          tower.noncollapseConstant :=
    (div_le_div_iff_of_pos_right tower.noncollapseConstant_pos).2
      (tower.residualBound_le_cap n)
  have hchildDiv :
      tower.tree.residualBound (n + 1) / tower.noncollapseConstant ≤
        (tower.residualConstant * tower.tree.capRadius n) /
          tower.noncollapseConstant :=
    (div_le_div_iff_of_pos_right tower.noncollapseConstant_pos).2
      (tower.residualBound_succ_le_cap n)
  have hbudget :
      tower.tree.residualBound n / tower.noncollapseConstant +
          dist parentPacket.commonHeight childPacket.commonHeight +
          tower.tree.residualBound (n + 1) / tower.noncollapseConstant ≤
        (2 * tower.residualConstant / tower.noncollapseConstant +
            tower.heightMotionConstant) * tower.tree.capRadius n := by
    calc
      tower.tree.residualBound n / tower.noncollapseConstant +
          dist parentPacket.commonHeight childPacket.commonHeight +
          tower.tree.residualBound (n + 1) / tower.noncollapseConstant ≤
          (tower.residualConstant * tower.tree.capRadius n) /
              tower.noncollapseConstant +
            tower.heightMotionConstant * tower.tree.capRadius n +
            (tower.residualConstant * tower.tree.capRadius n) /
              tower.noncollapseConstant := by
        gcongr
        exact tower.motionCommonHeight n y
      _ = (2 * tower.residualConstant / tower.noncollapseConstant +
            tower.heightMotionConstant) * tower.tree.capRadius n := by ring
  calc
    dist
        (fourCycleCollisionTime parentPacket.line i)
        (fourCycleCollisionTime childPacket.line i) ≤
      tower.tree.residualBound n / tower.noncollapseConstant +
        dist parentPacket.commonHeight childPacket.commonHeight +
        tower.tree.residualBound (n + 1) / tower.noncollapseConstant := hraw
    _ ≤ (2 * tower.residualConstant / tower.noncollapseConstant +
        tower.heightMotionConstant) * tower.tree.capRadius n := hbudget
    _ ≤ tower.motionConstant * tower.tree.capRadius n := by
      exact mul_le_mul_of_nonneg_right (le_max_right _ _)
        (tower.tree.capRadius_nonneg n)

/-- The coherence-preserving tower canonically becomes the existing marked
Maslov return tower.  In particular, `motionTime` is now a theorem rather
than part of the input data. -/
noncomputable def PrunedCommonHeightAnalyticFourCycleTower.toMarkedReturnTower
    {selector : Set MarkedLine}
    (tower : PrunedCommonHeightAnalyticFourCycleTower selector) :
    PrunedMarkedFourCycleReturnTower selector where
  Node := tower.tree.Node
  nodeFinite := tower.tree.nodeFinite
  root := tower.tree.root
  parent := tower.tree.parent
  hasChild := tower.tree.hasChild
  line := fun n x ↦ (tower.tree.packet n x).line
  line_mem_selector := fun n x i ↦
    (tower.tree.packet n x).line_mem_selector i
  chartNonzero := fun n x i ↦
    (tower.tree.packet n x).chartNonzero i
  approxTime := fun n x ↦
    fourCycleCollisionTime (tower.tree.packet n x).line
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
  motionA := fun n y i j ↦
    (tower.motionA n y i j).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (tower.tree.capRadius_nonneg n))
  motionB := fun n y i j ↦
    (tower.motionB n y i j).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (tower.tree.capRadius_nonneg n))
  motionTime := tower.motionCollisionTime
  residualBound := tower.tree.residualBound
  residualBound_nonneg := tower.tree.residualBound_nonneg
  residualBound_tendsto_zero := tower.tree.residualBound_tendsto_zero
  physicalCycleResidual := fun n x i ↦
    (tower.tree.packet n x).toNormalized.physicalCycleResidual i
  noncollapseConstant := tower.noncollapseConstant
  noncollapseConstant_pos := tower.noncollapseConstant_pos
  horizontalNoncollapse := tower.horizontalNoncollapse

/-- Therefore a coherent common-height four-probe branch cannot persist at
all scales while the horizontal frame remains uniformly noncollapsed. -/
theorem PrunedCommonHeightAnalyticFourCycleTower.impossible
    {selector : Set MarkedLine}
    (tower : PrunedCommonHeightAnalyticFourCycleTower selector) : False :=
  tower.toMarkedReturnTower.impossible

/-- The common-height continuation data before choosing a horizontal
noncollapse constant.  This is the object naturally produced by a compatible
infinite retained branch. -/
structure PrunedCommonHeightAnalyticFourCycleContinuation
    (selector : Set MarkedLine) where
  tree : PrunedCommonHeightAnalyticFourCycleTree selector
  frameMotionConstant : ℝ
  frameMotionConstant_nonneg : 0 ≤ frameMotionConstant
  motionA : ∀ n (y : tree.Node (n + 1)) i j,
    dist
        (anchoredCycleA (tree.packet n (tree.parent n y)).line i j)
        (anchoredCycleA (tree.packet (n + 1) y).line i j) ≤
      frameMotionConstant * tree.capRadius n
  motionB : ∀ n (y : tree.Node (n + 1)) i j,
    dist
        (anchoredCycleB (tree.packet n (tree.parent n y)).line i j)
        (anchoredCycleB (tree.packet (n + 1) y).line i j) ≤
      frameMotionConstant * tree.capRadius n
  heightMotionConstant : ℝ
  heightMotionConstant_nonneg : 0 ≤ heightMotionConstant
  motionCommonHeight : ∀ n (y : tree.Node (n + 1)),
    dist (tree.packet n (tree.parent n y)).commonHeight
        (tree.packet (n + 1) y).commonHeight ≤
      heightMotionConstant * tree.capRadius n
  residualConstant : ℝ
  residualConstant_nonneg : 0 ≤ residualConstant
  residualBound_le_cap : ∀ n,
    tree.residualBound n ≤ residualConstant * tree.capRadius n
  residualBound_succ_le_cap : ∀ n,
    tree.residualBound (n + 1) ≤ residualConstant * tree.capRadius n

/-- Add a quantitative horizontal lower bound to a continuation. -/
def PrunedCommonHeightAnalyticFourCycleContinuation.withNoncollapse
    {selector : Set MarkedLine}
    (continuation :
      PrunedCommonHeightAnalyticFourCycleContinuation selector)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hnoncollapse : ∀ n (x : continuation.tree.Node n) (c : E3),
      kappa * ‖c‖ ≤
        ‖horizontalFrameVector
          (anchoredCycleA (continuation.tree.packet n x).line) c‖) :
    PrunedCommonHeightAnalyticFourCycleTower selector where
  tree := continuation.tree
  frameMotionConstant := continuation.frameMotionConstant
  frameMotionConstant_nonneg := continuation.frameMotionConstant_nonneg
  motionA := continuation.motionA
  motionB := continuation.motionB
  heightMotionConstant := continuation.heightMotionConstant
  heightMotionConstant_nonneg := continuation.heightMotionConstant_nonneg
  motionCommonHeight := continuation.motionCommonHeight
  residualConstant := continuation.residualConstant
  residualConstant_nonneg := continuation.residualConstant_nonneg
  residualBound_le_cap := continuation.residualBound_le_cap
  residualBound_succ_le_cap := continuation.residualBound_succ_le_cap
  noncollapseConstant := kappa
  noncollapseConstant_pos := hkappa
  horizontalNoncollapse := hnoncollapse

/-- Exact terminal alternative for an infinite coherent common-height branch:
at every positive threshold some retained node has a quantitatively collapsed
horizontal coefficient direction.  Otherwise that threshold would give a
uniformly noncollapsed tower, already excluded by the four-time Maslov
firewall. -/
theorem PrunedCommonHeightAnalyticFourCycleContinuation.arbitrarilyCollapsed
    {selector : Set MarkedLine}
    (continuation :
      PrunedCommonHeightAnalyticFourCycleContinuation selector) :
    ∀ kappa : ℝ, 0 < kappa →
      ∃ n : ℕ, ∃ x : continuation.tree.Node n, ∃ c : E3,
        ‖horizontalFrameVector
            (anchoredCycleA (continuation.tree.packet n x).line) c‖ <
          kappa * ‖c‖ := by
  intro kappa hkappa
  by_contra hcollapse
  push Not at hcollapse
  exact (continuation.withNoncollapse kappa hkappa hcollapse).impossible

end StickyKakeya4
