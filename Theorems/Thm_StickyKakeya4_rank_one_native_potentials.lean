import Theorems.Thm_StickyKakeya4_time_changed_scalar_energy
import Theorems.Thm_StickyKakeya4_triangular_borel_front_escape

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4.RankOneNativePotentials
open ScalarProjection TriangularPotentialEscape EnergyDimension

/-- The target potential is the literal source integral, including coincident points. -/
theorem potential₁_eq_source
    (μ : Measure ℝ) (g : ℝ × ℝ → ℝ) (hg : Measurable g)
    (s : ℝ) (p : ℝ × ℝ) :
    potential₁ μ g s p = ∫⁻ a', edist (g p) (g (p.1,a'))^(-s) ∂μ := by
  unfold potential₁ inverseDistancePotential
  exact lintegral_map (by fun_prop) (hg.comp (by fun_prop))

theorem measurable_potential₁
    (μ : Measure ℝ) [SFinite μ] (g : ℝ × ℝ → ℝ) (hg : Measurable g)
    (s : ℝ) : Measurable (potential₁ μ g s) := by
  have he : potential₁ μ g s = fun p => ∫⁻ a', edist (g p) (g (p.1,a'))^(-s) ∂μ :=
    funext (potential₁_eq_source μ g hg s)
  rw [he]
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      edist (g p.1) (g (p.1.1,p.2))^(-s)) := by fun_prop
  exact hm.lintegral_prod_right'

/-- Bounded scalar source density gives finite native identity potential. -/
theorem ae_finite_identity_potential
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (D : ℝ) (hD : 0 ≤ D) (hμ : μ ≤ ENNReal.ofReal D • volume)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∀ᵐ a ∂μ, inverseDistancePotential μ s a < ∞ := by
  apply ae_lt_top (measurable_inverseDistancePotential μ s)
  have he : (∫⁻ a, inverseDistancePotential μ s a ∂μ) =
      ∫⁻ p : ℝ × ℝ, (ENNReal.ofReal |p.1-p.2|)^(-s) ∂μ.prod μ := by
    unfold inverseDistancePotential
    rw [lintegral_prod _ (by fun_prop)]
    apply lintegral_congr
    intro a
    apply lintegral_congr
    intro a'
    rw [edist_dist, Real.dist_eq]
  rw [he]
  exact (finite_source_pair_energy μ D hD hμ s hs hs1).ne

variable {Z : Type*} [MeasurableSpace Z]

/-- Generic native own-coordinate potential; specializes definitionally to potential₂ and potential₃. -/
def nativeOwnPotential (μ : Measure ℝ) (g : ℝ × (Z × ℝ) → ℝ) (s : ℝ)
    (p : ℝ × (Z × ℝ)) : ℝ≥0∞ :=
  inverseDistancePotential (μ.map (fun a => g (p.1,(p.2.1,a)))) s (g p)

theorem nativeOwnPotential_eq_source
    (μ : Measure ℝ) (g : ℝ × (Z × ℝ) → ℝ) (hg : Measurable g)
    (s : ℝ) (p : ℝ × (Z × ℝ)) :
    nativeOwnPotential μ g s p =
      ∫⁻ a', edist (g p) (g (p.1,(p.2.1,a')))^(-s) ∂μ := by
  unfold nativeOwnPotential inverseDistancePotential
  exact lintegral_map (by fun_prop) (hg.comp (by fun_prop))

theorem measurable_nativeOwnPotential
    (μ : Measure ℝ) [SFinite μ] (g : ℝ × (Z × ℝ) → ℝ) (hg : Measurable g)
    (s : ℝ) : Measurable (nativeOwnPotential μ g s) := by
  have he : nativeOwnPotential μ g s = fun p =>
      ∫⁻ a', edist (g p) (g (p.1,(p.2.1,a')))^(-s) ∂μ :=
    funext (nativeOwnPotential_eq_source μ g hg s)
  rw [he]
  have hm : Measurable (fun p : (ℝ × (Z × ℝ)) × ℝ =>
      edist (g p.1) (g (p.1.1,(p.1.2.1,p.2)))^(-s)) := by fun_prop
  exact hm.lintegral_prod_right'

/-- Translation of one's own coordinate leaves its singular native potential exactly unchanged. -/
theorem translated_nativeOwnPotential_eq
    (μ : Measure ℝ) (H : ℝ × Z → ℝ) (hH : Measurable H)
    (s : ℝ) (p : ℝ × (Z × ℝ)) :
    nativeOwnPotential μ (fun q => q.2.2+H (q.1,q.2.1)) s p =
      inverseDistancePotential μ s p.2.2 := by
  rw [nativeOwnPotential_eq_source μ _ (by fun_prop)]
  unfold inverseDistancePotential
  apply lintegral_congr
  intro a'
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq]
  congr 3
  ring

theorem ae_finite_translated_nativeOwnPotential
    (τ : Measure ℝ) [IsFiniteMeasure τ]
    (ζ : Measure Z) [IsFiniteMeasure ζ]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (D : ℝ) (hD : 0 ≤ D) (hμ : μ ≤ ENNReal.ofReal D • volume)
    (H : ℝ × Z → ℝ) (hH : Measurable H)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∀ᵐ p ∂τ.prod (ζ.prod μ),
      nativeOwnPotential μ (fun q => q.2.2+H (q.1,q.2.1)) s p < ∞ := by
  have hP := measurable_nativeOwnPotential μ (fun q => q.2.2+H (q.1,q.2.1))
    (by fun_prop) s
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hP measurable_const)).mpr
  apply ae_of_all
  intro t
  have hPt : Measurable (fun p : Z × ℝ =>
      nativeOwnPotential μ (fun q => q.2.2+H (q.1,q.2.1)) s (t,p)) :=
    hP.comp (by fun_prop)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hPt measurable_const)).mpr
  apply ae_of_all
  intro z
  filter_upwards [ae_finite_identity_potential μ D hD hμ s hs hs1] with a ha
  rw [translated_nativeOwnPotential_eq μ H hH s]
  exact ha

/-- Exact multiplication law for the first feedback coordinate's native potential. -/
theorem feedback_potential₁_eq_scaled
    (μ : Measure ℝ) (f k : ℝ → ℝ) (hf : Measurable f) (hk : Measurable k)
    (s t a : ℝ) (hkt : k t ≠ 0) :
    potential₁ μ (fun p => p.2+k p.1*f p.2) s (t,a) =
      (ENNReal.ofReal |k t|)^(-s) *
        ∫⁻ a', edist (f a+(k t)⁻¹*a) (f a'+(k t)⁻¹*a')^(-s) ∂μ := by
  have hfactor : (ENNReal.ofReal |k t|)^(-s) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (by simpa using hkt) ENNReal.ofReal_ne_top
  rw [potential₁_eq_source μ _ (by fun_prop)]
  calc
    _ = ∫⁻ a', (ENNReal.ofReal |k t|)^(-s) *
        edist (f a+(k t)⁻¹*a) (f a'+(k t)⁻¹*a')^(-s) ∂μ := by
      apply lintegral_congr
      intro a'
      simp only [edist_dist, Real.dist_eq]
      have he : (a+k t*f a)-(a'+k t*f a') =
          k t*((f a+(k t)⁻¹*a)-(f a'+(k t)⁻¹*a')) := by
        field_simp
        ring
      rw [he, abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
    _ = _ := lintegral_const_mul' _ _ hfactor

/-- Nonzero scalar feedback is finite almost everywhere in the original actual-time law. -/
theorem ae_finite_feedback_potential₁
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (D : ℝ) (hD : 0 ≤ D) (hμ : μ ≤ ENNReal.ofReal D • volume)
    (f k : ℝ → ℝ) (hf : Measurable f) (hk : Measurable k)
    (l h c : ℝ) (hc : 0 < c)
    (hknz : ∀ t ∈ Icc l h, k t ≠ 0)
    (hco : ∀ t ∈ Icc l h, ∀ u ∈ Icc l h,
      c*|t-u| ≤ |(k t)⁻¹-(k u)⁻¹|)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∀ᵐ p ∂(volume.restrict (Icc l h)).prod μ,
      potential₁ μ (fun q => q.2+k q.1*f q.2) s p < ∞ := by
  have hfin := ae_finite_time_changed_scalar_potential μ D hD hμ f hf
    (fun t => (k t)⁻¹) (by fun_prop) l h c hc hco s hs hs1
  have hmem : ∀ᵐ p ∂(volume.restrict (Icc l h)).prod μ, p.1 ∈ Icc l h := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Icc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ae_of_all _ (fun _ => ht)
  filter_upwards [hfin, hmem] with p hp hpt
  rw [feedback_potential₁_eq_scaled μ f k hf hk s p.1 p.2 (hknz p.1 hpt)]
  exact ENNReal.mul_lt_top (by
    apply lt_top_iff_ne_top.mpr
    exact ENNReal.rpow_ne_top_of_ne_zero
      (by simpa using hknz p.1 hpt) ENNReal.ofReal_ne_top) hp

/-- The zero-feedback branch is the identity source map on the original interval. -/
theorem ae_finite_zero_feedback_potential₁
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (D : ℝ) (hD : 0 ≤ D) (hμ : μ ≤ ENNReal.ofReal D • volume)
    (f k : ℝ → ℝ) (hf : Measurable f) (hk : Measurable k)
    (l h : ℝ) (hkzero : ∀ t ∈ Icc l h, k t = 0)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∀ᵐ p ∂(volume.restrict (Icc l h)).prod μ,
      potential₁ μ (fun q => q.2+k q.1*f q.2) s p < ∞ := by
  have hP := measurable_potential₁ μ (fun q => q.2+k q.1*f q.2) (by fun_prop) s
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hP measurable_const)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  filter_upwards [ae_finite_identity_potential μ D hD hμ s hs hs1] with a ha
  rw [potential₁_eq_source μ _ (by fun_prop)]
  simpa only [hkzero t ht, zero_mul, add_zero, inverseDistancePotential] using ha

end StickyKakeya4.RankOneNativePotentials
