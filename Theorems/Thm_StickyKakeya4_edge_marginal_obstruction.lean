import Mathlib

/-!
# Bounded edge density does not bound conditional density

This finite probability calculation tests a measure-theoretic inference used
in Proposition 9.29, equation (453), of the original manuscript. It does not
claim a counterexample to every geometric hypothesis of that proposition or to
the main dimension theorem.

On a two-point probability space, retain only the edge `(0,0)`. Its density
relative to the product probability is at most one. The source marginal at 0
has mass 1/4, while the mass of the original cap `{0}` is 1/2. The edge mass in
the cap is 1/4, not bounded by the product 1/8 of those two masses. Conditional
normalization is therefore a substantive operation, not a density-preserving
restriction of the original product probability.
-/

open scoped ENNReal

namespace StickyKakeya4.EdgeMarginalObstruction

/-- Uniform probability weights on a two-point space. -/
def baseWeight (_ : Fin 2) : ℝ≥0∞ := 1 / 2

/-- A product-density bounded by one, supported on one diagonal edge. -/
def edgeDensity (i j : Fin 2) : ℝ≥0∞ := if i = 0 ∧ j = 0 then 1 else 0

/-- Degree relative to the original target probability. -/
def sourceDegree (i : Fin 2) : ℝ≥0∞ :=
  ∑ j, edgeDensity i j * baseWeight j

/-- Original selector mass of the cap containing just the first point. -/
def capMass : ℝ≥0∞ := ∑ i : Fin 2, if i = 0 then baseWeight i else 0

/-- Mass of the source marginal of the retained edge flow. -/
def marginalMass : ℝ≥0∞ := ∑ i, sourceDegree i * baseWeight i

/-- Actual mass of retained edges whose two endpoints lie in the cap. -/
def sameCapEdgeMass : ℝ≥0∞ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    if i = 0 ∧ j = 0 then edgeDensity i j * baseWeight i * baseWeight j else 0

theorem baseWeight_probability : ∑ i : Fin 2, baseWeight i = 1 := by
  norm_num [baseWeight, Fin.sum_univ_two]

theorem edgeDensity_le_one (i j : Fin 2) : edgeDensity i j ≤ 1 := by
  simp only [edgeDensity]
  split_ifs <;> simp

theorem masses : capMass = 1 / 2 ∧ marginalMass = 1 / 4 ∧
    sameCapEdgeMass = 1 / 4 := by
  norm_num [capMass, marginalMass, sameCapEdgeMass, sourceDegree,
    edgeDensity, baseWeight, Fin.sum_univ_two]

/-- Bounded edge density alone does not give domination by its own source
marginal times the original target probability. -/
theorem marginal_product_bound_fails :
    ¬ sameCapEdgeMass ≤ marginalMass * capMass := by
  rcases masses with ⟨hcap, hmarginal, hedge⟩
  rw [hcap, hmarginal, hedge]
  norm_num

end StickyKakeya4.EdgeMarginalObstruction
