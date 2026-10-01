import Theorems.Thm_StickyKakeya4_source_marked_collision_edges

open MeasureTheory Set

noncomputable section

namespace StickyKakeya4

/-- Restricting the normalized collision kernel to its literal support loses
no mass. -/
theorem sum_sourceCollisionSupport_eq_totalFlow {n : ℕ}
    (R : FiniteScaleSource n) :
    (∑ p ∈ sourceCollisionSupport R,
        sourceNormalizedCollisionFlow R p.1 p.2) =
      ∑ i, ∑ j, sourceNormalizedCollisionFlow R i j := by
  classical
  calc
    (∑ p ∈ sourceCollisionSupport R,
        sourceNormalizedCollisionFlow R p.1 p.2) =
        ∑ p ∈ (Finset.univ ×ˢ Finset.univ),
          sourceNormalizedCollisionFlow R p.1 p.2 := by
      unfold sourceCollisionSupport
      rw [Finset.sum_filter_ne_zero]
    _ = ∑ i, ∑ j, sourceNormalizedCollisionFlow R i j :=
      Finset.sum_product' Finset.univ Finset.univ
        (sourceNormalizedCollisionFlow R)

/-- A uniform capacity bound on every genuine collision edge converts the
weighted total flow into an unweighted support-cardinality estimate. -/
theorem totalFlow_le_supportCard_mul_of_edge_le
    {n : ℕ} (R : FiniteScaleSource n) (edgeCapacity : ENNReal)
    (hcap : ∀ p ∈ sourceCollisionSupport R,
      sourceNormalizedCollisionFlow R p.1 p.2 ≤ edgeCapacity) :
    (∑ i, ∑ j, sourceNormalizedCollisionFlow R i j) ≤
      ((sourceCollisionSupport R).card : ENNReal) * edgeCapacity := by
  rw [← sum_sourceCollisionSupport_eq_totalFlow R]
  calc
    (∑ p ∈ sourceCollisionSupport R,
        sourceNormalizedCollisionFlow R p.1 p.2) ≤
        ∑ _p ∈ sourceCollisionSupport R, edgeCapacity := by
      exact Finset.sum_le_sum fun p hp ↦ hcap p hp
    _ = ((sourceCollisionSupport R).card : ENNReal) * edgeCapacity := by
      simp

/-- Under factor-two union failure, any valid per-edge capacity estimate forces
enough actual marked collision edges to carry the complete retained mass. -/
theorem factor_two_union_failure_forces_collisionSupport_cardinality
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (hfailure : 2 * volume (sourceUnion R) ≤ sourceMass R)
    (edgeCapacity : ENNReal)
    (hcap : ∀ p ∈ sourceCollisionSupport R,
      sourceNormalizedCollisionFlow R p.1 p.2 ≤ edgeCapacity) :
    sourceMass R ≤
      2 * (((sourceCollisionSupport R).card : ENNReal) * edgeCapacity) := by
  calc
    sourceMass R ≤
        2 * (∑ i, ∑ j, sourceNormalizedCollisionFlow R i j) :=
      factor_two_union_failure_forces_normalizedCollisionFlow hD hR hfailure
    _ ≤ 2 * (((sourceCollisionSupport R).card : ENNReal) * edgeCapacity) := by
      gcongr
      exact totalFlow_le_supportCard_mul_of_edge_le R edgeCapacity hcap

/-- The same cardinality conclusion in the marked-line graph: injectivity of
the finite source parametrization preserves the edge count exactly. -/
theorem factor_two_union_failure_forces_markedCollisionSupport_cardinality
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (hfailure : 2 * volume (sourceUnion R) ≤ sourceMass R)
    (edgeCapacity : ENNReal)
    (hcap : ∀ p ∈ sourceCollisionSupport R,
      sourceNormalizedCollisionFlow R p.1 p.2 ≤ edgeCapacity) :
    sourceMass R ≤
      2 * (((sourceMarkedCollisionSupport R).card : ENNReal) * edgeCapacity) := by
  rw [card_sourceMarkedCollisionSupport]
  exact factor_two_union_failure_forces_collisionSupport_cardinality
    hD hR hfailure edgeCapacity hcap

end StickyKakeya4
