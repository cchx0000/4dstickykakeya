import Definitions.Def_sticky_kakeya4_core

/-!
# Common-shading obstruction to a uniform hereditary union bound

A fractional restriction may retain exactly the same positive-measure shading
on every line. For unit weights, the ratio of source mass to union volume is
then the number of lines. The following calculation isolates the obstruction;
it does not assume or claim an admissible geometric family at every scale.
-/

open MeasureTheory Set
open scoped ENNReal

namespace StickyKakeya4

/-- Replace all shadings by one measurable subset, preserving every other field. -/
def commonShadingRestriction {n : ℕ} (D : FiniteScaleSource n)
    (s : Set E4) : FiniteScaleSource n :=
  { D with shading := fun _ => s }

/-- The existing restriction interface permits a common subset of all shadings. -/
theorem commonShadingRestriction_isFractional {n : ℕ}
    (D : FiniteScaleSource n) (s : Set E4) (hs : MeasurableSet s)
    (hsub : ∀ i, s ⊆ D.shading i) :
    IsFractionalSourceRestriction (commonShadingRestriction D s) D := by
  exact ⟨rfl, rfl, rfl, rfl, fun _ => hs, hsub, fun _ => le_rfl⟩

/-- With unit weights and a common shading, the source function is a constant
indicator whose value on that shading is the number of source lines. -/
theorem sourceFunction_commonShadingRestriction {n : ℕ}
    (D : FiniteScaleSource n) (s : Set E4)
    (hweight : ∀ i, D.weight i = 1) :
    sourceFunction (commonShadingRestriction D s) = s.indicator (fun _ => (n : ℝ≥0∞)) := by
  classical
  funext x
  by_cases hx : x ∈ s <;>
    simp [sourceFunction, commonShadingRestriction, hweight, hx]

/-- The common-shading restriction has mass exactly `n * volume s`. -/
theorem sourceMass_commonShadingRestriction {n : ℕ}
    (D : FiniteScaleSource n) (s : Set E4) (hs : MeasurableSet s)
    (hweight : ∀ i, D.weight i = 1) :
    sourceMass (commonShadingRestriction D s) = (n : ℝ≥0∞) * volume s := by
  rw [sourceMass, sourceFunction_commonShadingRestriction D s hweight]
  exact lintegral_indicator_const hs _

/-- A nonempty index type gives exactly the common shading as physical union. -/
theorem sourceUnion_commonShadingRestriction {n : ℕ}
    (hn : 0 < n) (D : FiniteScaleSource n) (s : Set E4)
    (hweight : ∀ i, D.weight i = 1) :
    sourceUnion (commonShadingRestriction D s) = s := by
  classical
  ext x
  simp only [sourceUnion, mem_setOf_eq,
    sourceFunction_commonShadingRestriction D s hweight]
  by_cases hx : x ∈ s <;> simp [hx, hn]

/-- A union bound for a finite, positive common shading forces its coefficient
 to be at least the number of source lines. -/
theorem commonShading_union_bound_iff {n : ℕ}
    (hn : 0 < n) (D : FiniteScaleSource n) (s : Set E4)
    (hs : MeasurableSet s) (hs0 : volume s ≠ 0) (hstop : volume s ≠ ⊤)
    (hweight : ∀ i, D.weight i = 1) (K : ℝ≥0∞) :
    sourceMass (commonShadingRestriction D s) ≤
        K * volume (sourceUnion (commonShadingRestriction D s)) ↔
      (n : ℝ≥0∞) ≤ K := by
  rw [sourceMass_commonShadingRestriction D s hs hweight,
    sourceUnion_commonShadingRestriction hn D s hweight]
  exact ENNReal.mul_le_mul_iff_left hs0 hstop

/-- Common shading has quadratic energy `n² * volume s`. -/
theorem sourceEnergy_commonShadingRestriction {n : ℕ}
    (D : FiniteScaleSource n) (s : Set E4) (hs : MeasurableSet s)
    (hweight : ∀ i, D.weight i = 1) :
    (∫⁻ x, sourceFunction (commonShadingRestriction D s) x ^ 2 ∂volume) =
      (n : ℝ≥0∞) ^ 2 * volume s := by
  classical
  have hfun : (fun x => sourceFunction (commonShadingRestriction D s) x ^ 2) =
      s.indicator (fun _ => (n : ℝ≥0∞) ^ 2) := by
    rw [sourceFunction_commonShadingRestriction D s hweight]
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hfun]
  exact lintegral_indicator_const hs _

/-- Consequently, the common-shading energy estimate has the same necessary
coefficient as the union estimate. -/
theorem commonShading_energy_bound_iff {n : ℕ}
    (hn : 0 < n) (D : FiniteScaleSource n) (s : Set E4)
    (hs : MeasurableSet s) (hs0 : volume s ≠ 0) (hstop : volume s ≠ ⊤)
    (hweight : ∀ i, D.weight i = 1) (K : ℝ≥0∞) :
    (∫⁻ x, sourceFunction (commonShadingRestriction D s) x ^ 2 ∂volume) ≤
        K * sourceMass (commonShadingRestriction D s) ↔
      (n : ℝ≥0∞) ≤ K := by
  rw [sourceEnergy_commonShadingRestriction D s hs hweight,
    sourceMass_commonShadingRestriction D s hs hweight,
    ← mul_assoc, ENNReal.mul_le_mul_iff_left hs0 hstop, pow_two]
  exact ENNReal.mul_le_mul_iff_left (by exact_mod_cast hn.ne') (by simp)

end StickyKakeya4
