import Theorems.Thm_StickyKakeya4_contact_cycle_rigidity

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- The matrix with the three given Euclidean vectors as columns. -/
def horizontalColumnMatrix (u v w : E3) : Mat3 :=
  fun i j => ![u i, v i, w i] j

/-- The horizontal frame anchored at the first of four points. -/
def horizontalAnchoredMatrix (x y z w : E3) : Mat3 :=
  horizontalColumnMatrix (y - x) (z - x) (w - x)

/-- The coordinate matrix agrees with the contact-rigidity frame. -/
theorem horizontalAnchoredMatrix_eq_anchoredMatrix (x y z w : E3) :
    horizontalAnchoredMatrix x y z w =
      ContactCycleRigidity.anchoredMatrix ![x, y, z, w] := by
  ext i j
  fin_cases j <;>
    simp [horizontalAnchoredMatrix, horizontalColumnMatrix,
      ContactCycleRigidity.anchoredMatrix]

private def horizontalDetThird (u v : E3) : E3 →ₗ[ℝ] ℝ where
  toFun w := (horizontalColumnMatrix u v w).det
  map_add' w w' := by
    simp [horizontalColumnMatrix, Matrix.det_fin_three, PiLp.add_apply]
    ring
  map_smul' a w := by
    simp [horizontalColumnMatrix, Matrix.det_fin_three, PiLp.smul_apply]
    ring

private def horizontalDetSecond (u w : E3) : E3 →ₗ[ℝ] ℝ where
  toFun v := (horizontalColumnMatrix u v w).det
  map_add' v v' := by
    simp [horizontalColumnMatrix, Matrix.det_fin_three, PiLp.add_apply]
    ring
  map_smul' a v := by
    simp [horizontalColumnMatrix, Matrix.det_fin_three, PiLp.smul_apply]
    ring

/-- A nonzero linear functional vanishes on a null translated hyperplane. -/
theorem ae_linearMap_sub_ne_zero (f : E3 →ₗ[ℝ] ℝ) (hf : f ≠ 0) (x : E3) :
    ∀ᵐ z ∂(volume : Measure E3), f (z - x) ≠ 0 := by
  have hker : volume (f.ker : Set E3) = 0 :=
    Measure.addHaar_submodule volume f.ker (fun h => hf (LinearMap.ker_eq_top.mp h))
  rw [ae_iff]
  simp only [not_not, sub_eq_add_neg]
  change volume ((fun z => z + -x) ⁻¹' (f.ker : Set E3)) = 0
  rw [measure_preimage_add_right, hker]

private theorem exists_horizontal_det_ne_zero (u : E3) (hu : u ≠ 0) :
    ∃ v w : E3, (horizontalColumnMatrix u v w).det ≠ 0 := by
  by_contra h
  push Not at h
  have h0 := h (EuclideanSpace.single 1 1) (EuclideanSpace.single 2 1)
  have h1 := h (EuclideanSpace.single 2 1) (EuclideanSpace.single 0 1)
  have h2 := h (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
  simp [horizontalColumnMatrix, Matrix.det_fin_three] at h0 h1 h2
  apply hu
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

/-- The determinant of an anchored frame is continuous in its last two points. -/
theorem continuous_horizontalAnchoredMatrix_det (x y : E3) :
    Continuous (fun p : E3 × E3 => (horizontalAnchoredMatrix x y p.1 p.2).det) := by
  simp [horizontalAnchoredMatrix, horizontalColumnMatrix, Matrix.det_fin_three]
  fun_prop

/-- Given two distinct anchors, almost every pair of further Euclidean points
completes them to a nondegenerate horizontal frame. -/
theorem ae_horizontalAnchoredMatrix_det_ne_zero_volume (x y : E3) (hxy : x ≠ y) :
    ∀ᵐ p ∂((volume : Measure E3).prod volume),
      (horizontalAnchoredMatrix x y p.1 p.2).det ≠ 0 := by
  obtain ⟨v₀, w₀, hnonzero⟩ := exists_horizontal_det_ne_zero (y - x)
    (sub_ne_zero.mpr hxy.symm)
  have hsecond : horizontalDetSecond (y - x) w₀ ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h v₀
    exact hnonzero this
  have hfirst := ae_linearMap_sub_ne_zero (horizontalDetSecond (y - x) w₀) hsecond x
  apply (Measure.ae_prod_iff_ae_ae (isClosed_eq
    (continuous_horizontalAnchoredMatrix_det x y) continuous_const).measurableSet.compl).mpr
  filter_upwards [hfirst] with z hz
  have hthird : horizontalDetThird (y - x) (z - x) ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h w₀
    exact hz this
  exact ae_linearMap_sub_ne_zero (horizontalDetThird (y - x) (z - x)) hthird x

/-- Absolute continuity is enough to transfer horizontal determinant nullity. -/
theorem ae_horizontalAnchoredMatrix_det_ne_zero_of_absolutelyContinuous
    (σ : Measure E3) (hσ : σ ≪ volume) (x y : E3) (hxy : x ≠ y) :
    ∀ᵐ p ∂(σ.prod σ), (horizontalAnchoredMatrix x y p.1 p.2).det ≠ 0 :=
  (hσ.prod hσ).ae_le (ae_horizontalAnchoredMatrix_det_ne_zero_volume x y hxy)

/-- In particular, every measure dominated by Euclidean volume has the desired
almost-everywhere horizontal nondegeneracy; no finiteness assumption is needed. -/
theorem ae_horizontalAnchoredMatrix_det_ne_zero_of_le_volume
    (σ : Measure E3) (hσ : σ ≤ volume) (x y : E3) (hxy : x ≠ y) :
    ∀ᵐ p ∂(σ.prod σ), (horizontalAnchoredMatrix x y p.1 p.2).det ≠ 0 :=
  ae_horizontalAnchoredMatrix_det_ne_zero_of_absolutelyContinuous σ
    (Measure.absolutelyContinuous_of_le hσ) x y hxy

/-- The determinant-null theorem in the exact frame used by contact-cycle
rigidity. This is the interface for selecting nondegenerate exact cycles. -/
theorem ae_contact_anchoredMatrix_det_ne_zero_of_le_volume
    (σ : Measure E3) (hσ : σ ≤ volume) (x y : E3) (hxy : x ≠ y) :
    ∀ᵐ q ∂(σ.prod σ),
      (ContactCycleRigidity.anchoredMatrix ![x, y, q.1, q.2]).det ≠ 0 := by
  simpa only [horizontalAnchoredMatrix_eq_anchoredMatrix] using
    ae_horizontalAnchoredMatrix_det_ne_zero_of_le_volume σ hσ x y hxy

end StickyKakeya4
