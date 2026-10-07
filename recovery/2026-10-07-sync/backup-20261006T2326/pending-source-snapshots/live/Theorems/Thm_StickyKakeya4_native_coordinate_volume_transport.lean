import Definitions.Def_sticky_kakeya4_core
import Mathlib

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeCoordinateVolumeTransport
open Classical Finset MeasureTheory StickyKakeya4
open scoped ENNReal

abbrev ScalarSpace := ℝ × (ℝ × ℝ) × ℝ
abbrev PlanarSpace := (ℝ × ℝ) × ℝ × ℝ

def scalar (x : E4) : ScalarSpace := (x 0, (x 1, x 2), x 3)
def planar (x : E4) : PlanarSpace := ((x 0, x 1), x 2, x 3)

/-- A coordinate grouping is linear, but its ordinary product norm is not
claimed equal to the Euclidean norm on E4. -/
def scalarEquiv : E4 ≃ₗ[ℝ] ScalarSpace where
  toFun := scalar
  invFun := fun x => WithLp.toLp 2 ![x.1, x.2.1.1, x.2.1.2, x.2.2]
  left_inv := by intro x; ext j; fin_cases j <;> rfl
  right_inv := by rintro ⟨x,⟨⟨y,z⟩,t⟩⟩; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

def planarEquiv : E4 ≃ₗ[ℝ] PlanarSpace where
  toFun := planar
  invFun := fun x => WithLp.toLp 2 ![x.1.1, x.1.2, x.2.1, x.2.2]
  left_inv := by intro x; ext j; fin_cases j <;> rfl
  right_inv := by rintro ⟨⟨x,y⟩,⟨z,t⟩⟩; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

lemma three_last_measurePreserving :
    MeasurePreserving (fun x : Fin 3 → ℝ => ((x 0,x 1),x 2)) := by
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have h2 : MeasurePreserving (Prod.swap : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) × ℝ) :=
    Measure.measurePreserving_swap
  have h3 := (volume_preserving_finTwoArrow ℝ).prod (MeasurePreserving.id (volume : Measure ℝ))
  convert h3.comp (h2.comp h1) using 1 <;> rfl

/-- The exact product Lebesgue measure is preserved under the literal
scalar/two-normal coordinate grouping used by the CW consumer. -/
theorem scalar_measurePreserving : MeasurePreserving scalar := by
  have h1 := (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) (0 : Fin 4)).comp
    (PiLp.volume_preserving_ofLp (Fin 4))
  have h2 := (MeasurePreserving.id (volume : Measure ℝ)).prod three_last_measurePreserving
  convert h2.comp h1 using 1 <;> rfl

/-- The other rank's literal two-tangent/scalar-normal grouping has the
same exact volume law. No norm-dependent Jacobian is inserted. -/
theorem planar_measurePreserving : MeasurePreserving planar := by
  have h1 := (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) (3 : Fin 4)).comp
    (PiLp.volume_preserving_ofLp (Fin 4))
  have h2 : MeasurePreserving (Prod.swap : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ) :=
    Measure.measurePreserving_swap
  have h3 := three_last_measurePreserving.prod (MeasurePreserving.id (volume : Measure ℝ))
  have h4 : MeasurePreserving
      (MeasurableEquiv.prodAssoc : ((ℝ × ℝ) × ℝ) × ℝ ≃ᵐ (ℝ × ℝ) × ℝ × ℝ) :=
    volume_preserving_prodAssoc
  convert h4.comp (h3.comp (h2.comp h1)) using 1; rfl

theorem scalar_volume_preimage (U : Set ScalarSpace) : volume (scalar ⁻¹' U) = volume U :=
  scalar_measurePreserving.measure_preimage_emb
    scalarEquiv.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding U

theorem planar_volume_preimage (U : Set PlanarSpace) : volume (planar ⁻¹' U) = volume U :=
  planar_measurePreserving.measure_preimage_emb
    planarEquiv.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding U

/-- The SAME finite tube labels and actual tube sets pass from the already
proved E4 convex-Wolff law to the literal product-coordinate law. -/
theorem scalar_CW_transfer {I : Type*} (T : Finset I) (tube : I → Set E4) (C : ℝ≥0∞)
    (H : ∀U : Set E4, Convex ℝ U → MeasurableSet U →
      ((T.filter (fun i => tube i ⊆ U)).card : ℝ≥0∞) ≤ C * volume U * T.card) :
    ∀U : Set ScalarSpace, Convex ℝ U → MeasurableSet U →
      ((T.filter (fun i => scalar '' tube i ⊆ U)).card : ℝ≥0∞) ≤ C * volume U * T.card := by
  intro U hU hmeas
  have hconv : Convex ℝ (scalar ⁻¹' U) := hU.linear_preimage scalarEquiv.toLinearMap
  have hh := H (scalar ⁻¹' U) hconv (hmeas.preimage scalar_measurePreserving.measurable)
  simpa only [Set.image_subset_iff, scalar_volume_preimage] using hh

theorem planar_CW_transfer {I : Type*} (T : Finset I) (tube : I → Set E4) (C : ℝ≥0∞)
    (H : ∀U : Set E4, Convex ℝ U → MeasurableSet U →
      ((T.filter (fun i => tube i ⊆ U)).card : ℝ≥0∞) ≤ C * volume U * T.card) :
    ∀U : Set PlanarSpace, Convex ℝ U → MeasurableSet U →
      ((T.filter (fun i => planar '' tube i ⊆ U)).card : ℝ≥0∞) ≤ C * volume U * T.card := by
  intro U hU hmeas
  have hconv : Convex ℝ (planar ⁻¹' U) := hU.linear_preimage planarEquiv.toLinearMap
  have hh := H (planar ⁻¹' U) hconv (hmeas.preimage planar_measurePreserving.measurable)
  simpa only [Set.image_subset_iff, planar_volume_preimage] using hh

end NativeCoordinateVolumeTransport
