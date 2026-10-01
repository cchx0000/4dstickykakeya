import Theorems.Thm_StickyKakeya4_source_marked_collision_edges

open MeasureTheory Set

noncomputable section

namespace StickyKakeya4

/-- Literal support of the raw off-diagonal pair energy.  Unlike the Markov
flow, this support is defined before row normalization and therefore retains
the high-multiplicity gain furnished by a boundary bad ball. -/
def sourceRawCollisionSupport {n : ℕ} (R : FiniteScaleSource n) :
    Finset (Fin n × Fin n) := by
  classical
  exact (Finset.univ ×ˢ Finset.univ).filter fun p ↦
    p.1 ≠ p.2 ∧ sourcePairMass R p.1 p.2 ≠ 0

@[simp] theorem mem_sourceRawCollisionSupport_iff {n : ℕ}
    (R : FiniteScaleSource n) (i j : Fin n) :
    (i, j) ∈ sourceRawCollisionSupport R ↔
      i ≠ j ∧ sourcePairMass R i j ≠ 0 := by
  classical
  simp [sourceRawCollisionSupport]

/-- The raw off-diagonal energy is exactly the sum over its literal finite
support. -/
theorem sum_sourceRawCollisionSupport_eq_offDiagonal {n : ℕ}
    (R : FiniteScaleSource n) :
    (∑ p ∈ sourceRawCollisionSupport R,
      sourcePairMass R p.1 p.2) = sourceOffDiagonalMass R := by
  classical
  calc
    (∑ p ∈ sourceRawCollisionSupport R,
        sourcePairMass R p.1 p.2) =
      ∑ p ∈ (Finset.univ ×ˢ Finset.univ),
        if p.1 ≠ p.2 ∧ sourcePairMass R p.1 p.2 ≠ 0 then
          sourcePairMass R p.1 p.2 else 0 := by
      unfold sourceRawCollisionSupport
      rw [Finset.sum_filter]
    _ = ∑ i, ∑ j,
        if i ≠ j ∧ sourcePairMass R i j ≠ 0 then
          sourcePairMass R i j else 0 := by
      simpa only using
        (Finset.sum_product
          (Finset.univ : Finset (Fin n))
          (Finset.univ : Finset (Fin n))
          (fun p : Fin n × Fin n ↦
            if p.1 ≠ p.2 ∧ sourcePairMass R p.1 p.2 ≠ 0 then
              sourcePairMass R p.1 p.2 else 0))
    _ = sourceOffDiagonalMass R := by
      unfold sourceOffDiagonalMass
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · simp [hij]
      · by_cases hp : sourcePairMass R i j = 0
        · simp [hij, hp]
        · simp [hij, hp]

/-- A nonzero raw pair in an admissible fractional source survives the row
normalization.  Finiteness of the raw row rules out the only extended-real
division pathology. -/
theorem sourcePairMass_ne_zero_implies_normalizedFlow_ne_zero
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    {i j : Fin n} (hij : i ≠ j)
    (hpair : sourcePairMass R i j ≠ 0) :
    sourceNormalizedCollisionFlow R i j ≠ 0 := by
  have hrow0 : sourceOffDiagonalRowMass R i ≠ 0 := by
    intro hzero
    exact hpair
      (sourcePairMass_eq_zero_of_offDiagonalRowMass_eq_zero R hzero hij)
  have hrowTop : sourceOffDiagonalRowMass R i ≠ ⊤ :=
    sourceOffDiagonalRowMass_ne_top_of_fractional_admissibleStickySource
      hD hR i
  have hweightI : R.weight i ≠ 0 := by
    intro hzero
    exact hpair (by simp [sourcePairMass, hzero])
  have hrowMass0 : sourceRowMass R i ≠ 0 := by
    intro hzero
    have hmul : R.weight i * volume (R.shading i) = 0 := by
      simpa [sourceRowMass] using hzero
    have hvolumeZero : volume (R.shading i) = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_left hweightI
    have hintersectionZero : volume (R.shading i ∩ R.shading j) = 0 := by
      exact measure_mono_null inter_subset_left hvolumeZero
    exact hpair (by simp [sourcePairMass, hintersectionZero])
  simp only [sourceNormalizedCollisionFlow, hrow0, if_false, hij]
  exact mul_ne_zero hrowMass0
    (ENNReal.div_ne_zero.mpr ⟨hpair, hrowTop⟩)

/-- On admissible fractional sources the raw and normalized collision graphs
have exactly the same edges.  Hence raw multiplicity estimates may be fed to
the existing marked contact/DRC layer without altering the relation. -/
theorem sourceRawCollisionSupport_eq_sourceCollisionSupport
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D) :
    sourceRawCollisionSupport R = sourceCollisionSupport R := by
  classical
  ext p
  rcases p with ⟨i, j⟩
  constructor
  · intro hp
    obtain ⟨hij, hpair⟩ :=
      (mem_sourceRawCollisionSupport_iff R i j).mp hp
    exact (mem_sourceCollisionSupport_iff R i j).mpr
      (sourcePairMass_ne_zero_implies_normalizedFlow_ne_zero
        hD hR hij hpair)
  · intro hp
    have hflow : sourceNormalizedCollisionFlow R i j ≠ 0 :=
      (mem_sourceCollisionSupport_iff R i j).mp hp
    exact (mem_sourceRawCollisionSupport_iff R i j).mpr
      ⟨sourceNormalizedCollisionFlow_ne_zero_implies_ne R hflow,
        sourceNormalizedCollisionFlow_ne_zero_implies_pairMass_ne_zero
          R hflow⟩

end StickyKakeya4
