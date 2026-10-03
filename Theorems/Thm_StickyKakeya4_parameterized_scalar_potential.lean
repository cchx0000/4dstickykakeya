import Theorems.Thm_StickyKakeya4_scalar_borel_projection_energy

/-!
# Parameterized scalar Borel potentials

For a jointly measurable family of scalar intercepts, the native source
potential is measurable and finite almost everywhere in actual time, parameter,
and source point. The proof derives finite slice energies from bounded source
density; no energy or potential-finiteness hypothesis is assumed. Singularities
are retained in ENNReal throughout.
-/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4.ScalarProjection

variable {Z : Type*} [MeasurableSpace Z]

/-- The source-point potential of the scalar affine family with parameter z. -/
def parameterizedScalarPotential (μ : Measure ℝ) (f : Z × ℝ → ℝ) (s : ℝ)
    (p : ℝ × (Z × ℝ)) : ℝ≥0∞ :=
  ∫⁻ a', edist (f (p.2.1,p.2.2)+p.1*p.2.2)
    (f (p.2.1,a')+p.1*a') ^ (-s) ∂μ

/-- Native measurability, before any source restriction. -/
theorem measurable_parameterizedScalarPotential
    (μ : Measure ℝ) [SFinite μ] (f : Z × ℝ → ℝ) (hf : Measurable f) (s : ℝ) :
    Measurable (parameterizedScalarPotential μ f s) := by
  have hm : Measurable (fun p : (ℝ × (Z × ℝ)) × ℝ =>
      edist (f (p.1.2.1,p.1.2.2)+p.1.1*p.1.2.2)
        (f (p.1.2.1,p.2)+p.1.1*p.2) ^ (-s)) := by fun_prop
  exact hm.lintegral_prod_right'

/-- The native potential equals the target-space potential of the actual
scalar pushforward. This rewrites directly to inverseDistancePotential. -/
theorem parameterizedScalarPotential_eq_map_potential
    (μ : Measure ℝ) (f : Z × ℝ → ℝ) (hf : Measurable f) (s : ℝ)
    (t : ℝ) (z : Z) (a : ℝ) :
    parameterizedScalarPotential μ f s (t,(z,a)) =
      ∫⁻ y, edist (f (z,a)+t*a) y ^ (-s)
        ∂μ.map (fun a' => f (z,a')+t*a') := by
  exact (lintegral_map
    (f := fun y : ℝ => edist (f (z,a)+t*a) y ^ (-s))
    (g := fun a' : ℝ => f (z,a')+t*a') (by fun_prop) (by fun_prop)).symm

/-- Integrating the source potential gives the literal ordered-pair energy. -/
theorem parameterizedScalarPotential_integral_eq_pair_energy
    (μ : Measure ℝ) [IsFiniteMeasure μ] (f : Z × ℝ → ℝ) (hf : Measurable f)
    (s t : ℝ) (z : Z) :
    (∫⁻ a, parameterizedScalarPotential μ f s (t,(z,a)) ∂μ) =
      ∫⁻ p : ℝ × ℝ,
        (ENNReal.ofReal |(f (z,p.1)-f (z,p.2))+t*(p.1-p.2)|)^(-s) ∂μ.prod μ := by
  unfold parameterizedScalarPotential
  calc
    _ = ∫⁻ p : ℝ × ℝ,
        edist (f (z,p.1)+t*p.1) (f (z,p.2)+t*p.2)^(-s) ∂μ.prod μ :=
      (lintegral_prod _ (by fun_prop)).symm
    _ = _ := by
      apply lintegral_congr
      intro p
      have he : (f (z,p.1)+t*p.1)-(f (z,p.2)+t*p.2) =
          (f (z,p.1)-f (z,p.2))+t*(p.1-p.2) := by ring
      rw [edist_dist, Real.dist_eq, he]

/-- Every fixed parameter has finite integrated potential at almost every
time, with all energy input derived from bounded source density. -/
theorem ae_finite_parameterizedScalarPotential_integral
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume) (f : Z × ℝ → ℝ) (hf : Measurable f)
    (l h s : ℝ) (hs : 0 < s) (hs1 : s < 1) (z : Z) :
    ∀ᵐ t ∂volume.restrict (Icc l h),
      (∫⁻ a, parameterizedScalarPotential μ f s (t,(z,a)) ∂μ) < ∞ := by
  have hz : Measurable (fun a => f (z,a)) := by fun_prop
  filter_upwards [ae_finite_scalar_projection_pair_energy μ D hD hμ
    (fun a => f (z,a)) hz l h s hs hs1] with t ht
  rw [parameterizedScalarPotential_integral_eq_pair_energy μ f hf s t z]
  exact ht

/-- The native potential is finite almost everywhere on time × parameter ×
source, without an energy or finiteness assumption in the endpoint. -/
theorem ae_finite_parameterizedScalarPotential
    (ζ : Measure Z) [IsFiniteMeasure ζ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (hμ : μ ≤ ENNReal.ofReal D • volume) (f : Z × ℝ → ℝ) (hf : Measurable f)
    (l h s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∀ᵐ p ∂(volume.restrict (Icc l h)).prod (ζ.prod μ),
      parameterizedScalarPotential μ f s p < ∞ := by
  let Q : ℝ × Z → ℝ≥0∞ := fun p =>
    ∫⁻ a, parameterizedScalarPotential μ f s (p.1,(p.2,a)) ∂μ
  have hP := measurable_parameterizedScalarPotential μ f hf s
  have hQ : Measurable Q := by
    have hm : Measurable (fun p : (ℝ × Z) × ℝ =>
        parameterizedScalarPotential μ f s (p.1.1,(p.1.2,p.2))) :=
      hP.comp (by fun_prop)
    exact hm.lintegral_prod_right'
  have hzt : ∀ᵐ z ∂ζ, ∀ᵐ t ∂volume.restrict (Icc l h), Q (t,z) < ∞ :=
    ae_of_all _ (fun z =>
      ae_finite_parameterizedScalarPotential_integral μ D hD hμ f hf l h s hs hs1 z)
  have htz : ∀ᵐ t ∂volume.restrict (Icc l h), ∀ᵐ z ∂ζ, Q (t,z) < ∞ :=
    (Measure.ae_ae_comm (μ := ζ) (ν := volume.restrict (Icc l h))
      (p := fun z t => Q (t,z) < ∞)
      (measurableSet_lt (hQ.comp measurable_swap) measurable_const)).mp hzt
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hP measurable_const)).mpr
  filter_upwards [htz] with t ht
  have hPt : Measurable (fun p : Z × ℝ => parameterizedScalarPotential μ f s (t,p)) :=
    hP.comp (by fun_prop)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hPt measurable_const)).mpr
  filter_upwards [ht] with z hz
  apply ae_lt_top (hP.comp (show Measurable (fun a : ℝ => (t,(z,a))) by fun_prop))
  exact hz.ne

end StickyKakeya4.ScalarProjection
