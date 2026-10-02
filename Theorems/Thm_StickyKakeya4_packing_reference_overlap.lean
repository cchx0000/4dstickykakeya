import Theorems.Thm_StickyKakeya4_packing_reference_nets

open Filter MeasureTheory Set Metric
open scoped ENNReal Topology

namespace StickyKakeya4

attribute [local instance] Classical.propDecidable

/-!
Uniform overlap bounds for the supported reference nets.  Compactness of one
fixed unit ball, followed by translation and dilation, gives a scale-independent
bound in any proper real normed space.  A separate integral counting lemma
transfers a pointwise overlap bound to arbitrary measurable source preimages.
-/

/-- Separated images cannot use the same open ball of a finite cover if the
separation is twice the covering radius.  The domain need not itself carry
a metric, and no injectivity of the image map is assumed separately. -/
theorem image_separated_card_le_finite_cover_card
    {A X : Type*} [PseudoMetricSpace X]
    (points : Finset A) (image : A → X) (s : Set X) (r : ℝ)
    (centers : Finset X) (hcover : coversAtRadius s r centers)
    (hsupported : ∀ x ∈ points, image x ∈ s)
    (hseparated : ∀ x ∈ points, ∀ y ∈ points,
      x ≠ y → 2 * r ≤ dist (image x) (image y)) :
    points.card ≤ centers.card := by
  classical
  have hchoice (x : points) : ∃ c : centers, dist (image x) c < r := by
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcover (hsupported x x.property))
    obtain ⟨hcCenters, hxc⟩ := Set.mem_iUnion.mp hc
    exact ⟨⟨c, hcCenters⟩, Metric.mem_ball.mp hxc⟩
  let assignment : points → centers := fun x => Classical.choose (hchoice x)
  have hassignment (x : points) : dist (image x) (assignment x) < r :=
    Classical.choose_spec (hchoice x)
  apply Finset.card_le_card_of_injective (f := assignment)
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  have hsep := hseparated x x.property y y.property hne
  have hdist : dist (image x) (image y) < 2 * r := by
    calc
      dist (image x) (image y) ≤
          dist (image x) (assignment x) + dist (assignment x : X) (image y) :=
        dist_triangle _ _ _
      _ < r + r := add_lt_add (hassignment x) (by
        rw [hxy, dist_comm]
        exact hassignment y)
      _ = 2 * r := by ring
  exact (not_lt_of_ge hsep) hdist

/-- In a proper real normed space, a finite `tau / 2`-separated family lying
in a radius-`tau` closed ball has a cardinality bound independent of the center
and of the positive scale. -/
theorem exists_uniform_separated_ball_card_bound
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] :
    ∃ K : ℕ, ∀ (tau : ℝ), 0 < tau → ∀ (p : E) (points : Finset E),
      (∀ x ∈ points, dist x p ≤ tau) →
      (∀ x ∈ points, ∀ y ∈ points, x ≠ y → tau / 2 ≤ dist x y) →
      points.card ≤ K := by
  classical
  obtain ⟨cover, _hcoverUnit, hcoverFinite, hcover⟩ :=
    (isCompact_closedBall (0 : E) 1).finite_cover_balls (show 0 < (1 / 4 : ℝ) by norm_num)
  refine ⟨hcoverFinite.toFinset.card, ?_⟩
  intro tau htau p points hnear hsep
  let image : E → E := fun x => tau⁻¹ • (x - p)
  have hcover' : coversAtRadius (Metric.closedBall (0 : E) 1)
      (1 / 4) hcoverFinite.toFinset := by
    simpa only [coversAtRadius, Set.Finite.coe_toFinset] using hcover
  apply image_separated_card_le_finite_cover_card points image
    (Metric.closedBall (0 : E) 1) (1 / 4) hcoverFinite.toFinset hcover'
  · intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖image x‖ = tau⁻¹ * dist x p := by
        simp only [image, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr htau.le),
          dist_eq_norm]
      _ ≤ tau⁻¹ * tau := mul_le_mul_of_nonneg_left (hnear x hx) (inv_nonneg.mpr htau.le)
      _ = 1 := inv_mul_cancel₀ htau.ne'
  · intro x hx y hy hxy
    have hnorm : dist (image x) (image y) = tau⁻¹ * dist x y := by
      simp only [image, dist_smul₀, Real.norm_of_nonneg (inv_nonneg.mpr htau.le),
        dist_sub_right]
    rw [hnorm]
    have hscaled := mul_le_mul_of_nonneg_left (hsep x hx y hy hxy)
      (inv_nonneg.mpr htau.le)
    have hhalf : tau⁻¹ * (tau / 2) = (1 / 2 : ℝ) := by
      field_simp
    rw [hhalf] at hscaled
    norm_num at hscaled ⊢
    exact hscaled

/-- Open balls of radius `tau` about a `tau / 2`-separated finite family
have uniformly bounded multiplicity, independent of the scale and family. -/
theorem exists_uniform_separated_ball_overlap_bound
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] :
    ∃ K : ℕ, ∀ (tau : ℝ), 0 < tau → ∀ centers : Finset E,
      (∀ x ∈ centers, ∀ y ∈ centers, x ≠ y → tau / 2 ≤ dist x y) →
      ∀ p : E, (centers.filter fun c => p ∈ Metric.ball c tau).card ≤ K := by
  classical
  obtain ⟨K, hK⟩ := exists_uniform_separated_ball_card_bound E
  refine ⟨K, ?_⟩
  intro tau htau centers hsep p
  apply hK tau htau p
  · intro c hc
    have hcBall := (Finset.mem_filter.mp hc).2
    simpa only [Metric.mem_ball, dist_comm] using hcBall.le
  · intro x hx y hy hxy
    exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy

/-- Integrating a finite pointwise overlap bound controls the total mass of
a measurable family by the mass of any containing target.  The target itself
need not be measurable, and the ambient measure need not be finite. -/
theorem sum_measure_le_mul_of_multiplicity_bound
    {A I : Type*} [MeasurableSpace A]
    (mu : Measure A) (indices : Finset I) (family : I → Set A)
    (target : Set A) (K : ℕ)
    (hmeasurable : ∀ i ∈ indices, MeasurableSet (family i))
    (hsubset : ∀ i ∈ indices, family i ⊆ target)
    (hoverlap : ∀ x, (indices.filter fun i => x ∈ family i).card ≤ K) :
    (∑ i ∈ indices, mu (family i)) ≤ (K : ENNReal) * mu target := by
  classical
  have hcount (x : A) :
      (∑ i ∈ indices, (family i).indicator (fun _ => (1 : ENNReal)) x) =
        ((indices.filter fun i => x ∈ family i).card : ENNReal) := by
    calc
      (∑ i ∈ indices, (family i).indicator (fun _ => (1 : ENNReal)) x) =
          ∑ _i ∈ indices.filter (fun i => x ∈ family i), (1 : ENNReal) := by
        rw [Finset.sum_filter]
        rfl
      _ = ((indices.filter fun i => x ∈ family i).card : ENNReal) := by simp
  calc
    (∑ i ∈ indices, mu (family i)) =
        ∑ i ∈ indices, ∫⁻ x, (family i).indicator (fun _ => (1 : ENNReal)) x ∂mu := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [lintegral_indicator_const (hmeasurable i hi), one_mul]
    _ = ∫⁻ x, ∑ i ∈ indices,
        (family i).indicator (fun _ => (1 : ENNReal)) x ∂mu := by
      exact (lintegral_finsetSum indices
        (fun i hi => measurable_const.indicator (hmeasurable i hi))).symm
    _ ≤ ∫⁻ x, target.indicator (fun _ => (K : ENNReal)) x ∂mu := by
      apply lintegral_mono
      intro x
      dsimp only
      by_cases hx : x ∈ target
      · rw [Set.indicator_of_mem hx, hcount]
        exact_mod_cast hoverlap x
      · rw [Set.indicator_of_notMem hx]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro i hi
        exact Set.indicator_of_notMem (fun hxi => hx (hsubset i hi hxi)) _
    _ ≤ (K : ENNReal) * mu target := lintegral_indicator_const_le target _

/-- A uniform lower mass for every member of a bounded-overlap measurable
family gives the corresponding local counting inequality.  In applications
the family consists of source preimages of the reference-net balls. -/
theorem card_mul_le_mul_measure_of_mass_lower_and_overlap
    {A I : Type*} [MeasurableSpace A]
    (mu : Measure A) (indices : Finset I) (family : I → Set A)
    (target : Set A) (a : ENNReal) (K : ℕ)
    (hmeasurable : ∀ i ∈ indices, MeasurableSet (family i))
    (hsubset : ∀ i ∈ indices, family i ⊆ target)
    (hlower : ∀ i ∈ indices, a ≤ mu (family i))
    (hoverlap : ∀ x, (indices.filter fun i => x ∈ family i).card ≤ K) :
    (indices.card : ENNReal) * a ≤ (K : ENNReal) * mu target := by
  calc
    (indices.card : ENNReal) * a = ∑ _i ∈ indices, a := by simp
    _ ≤ ∑ i ∈ indices, mu (family i) := Finset.sum_le_sum hlower
    _ ≤ (K : ENNReal) * mu target :=
      sum_measure_le_mul_of_multiplicity_bound mu indices family target K
        hmeasurable hsubset hoverlap

end StickyKakeya4
