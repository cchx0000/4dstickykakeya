import Theorems.Thm_StickyKakeya4_horizontal_determinant_null

#print axioms StickyKakeya4.horizontalColumnMatrix
#print axioms StickyKakeya4.horizontalAnchoredMatrix
#print axioms StickyKakeya4.horizontalAnchoredMatrix_eq_anchoredMatrix
#print axioms StickyKakeya4.ae_linearMap_sub_ne_zero
#print axioms StickyKakeya4.continuous_horizontalAnchoredMatrix_det
#print axioms StickyKakeya4.ae_horizontalAnchoredMatrix_det_ne_zero_volume
#print axioms StickyKakeya4.ae_horizontalAnchoredMatrix_det_ne_zero_of_absolutelyContinuous
#print axioms StickyKakeya4.ae_horizontalAnchoredMatrix_det_ne_zero_of_le_volume
#print axioms StickyKakeya4.ae_contact_anchoredMatrix_det_ne_zero_of_le_volume

open MeasureTheory
open StickyKakeya4

example (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (x y : E3) (hxy : x ≠ y) :
    ∀ᵐ q ∂(σ.prod σ),
      (ContactCycleRigidity.anchoredMatrix ![x, y, q.1, q.2]).det ≠ 0 :=
  ae_contact_anchoredMatrix_det_ne_zero_of_le_volume σ hσ x y hxy
