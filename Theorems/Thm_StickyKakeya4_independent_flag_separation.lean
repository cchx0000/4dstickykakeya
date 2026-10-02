import Theorems.Thm_StickyKakeya4_old_neighbor_disintegration
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Fresh independent genuine flags and quantitative normal separation

The original occurrence `ω` retains all its ordered endpoints and inherited,
possibly correlated marks. Two *new* labels are appended with conditional law
`κ ω ⊗ η ω`; none of the original coordinates is replaced. This is the
probability construction of the lossless conditional-flag tensor step.

A pointwise closed-normal-cap bound for the first kernel bounds the entire
close-label discarded marginal by `c • Γ`. The complementary separated
marginal dominates `(1 - c) • Γ`, on every measurable set of occurrences,
not merely in total mass. Kernels of actual old flags preserve their genuine
incidence support under this construction.

These conclusions concern the two designated fresh flags. They do **not**
assert that every inherited old normal lies in either designated cap. The
paper's literal all-retained-normals-in-cap hypothesis is stronger; a geometric
lemma that uses designated genuine flags at the cycle vertices is still needed
before these probability estimates can be used for the geometric routing.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StickyKakeya4.IndependentFlagSeparation

variable {Ω L R Y X : Type*}
  [MeasurableSpace Ω] [MeasurableSpace L] [MeasurableSpace R]
  [MeasurableSpace Y] [MeasurableSpace X]

/-- Append two conditionally independent fresh labels, retaining the whole
original occurrence as the first coordinate. -/
noncomputable def freshExtension (Γ : Measure Ω)
    (κ : Kernel Ω L) (η : Kernel Ω R) : Measure (Ω × (L × R)) :=
  Γ.compProd (κ.prod η)

/-- Conditional independence is the actual product law on label rectangles. -/
theorem fresh_labels_rectangle (κ : Kernel Ω L) [IsMarkovKernel κ]
    (η : Kernel Ω R) [IsMarkovKernel η] (ω : Ω) (s : Set L) (t : Set R) :
    κ.prod η ω (s ×ˢ t) = κ ω s * η ω t :=
  Kernel.prod_apply_prod

/-- Fresh labels conserve the full original occurrence law exactly. -/
theorem fresh_extension_original (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (η : Kernel Ω R) [IsMarkovKernel η] :
    (freshExtension Γ κ η).map Prod.fst = Γ :=
  MarkovEndpointPreservation.extension_fst Γ (κ.prod η)

/-- In particular every ordered-endpoint observable and every inherited mark
has exactly the original law, with all original correlations intact. -/
theorem fresh_extension_observable (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (η : Kernel Ω R) [IsMarkovKernel η]
    (endpoint : Ω → Y) (hendpoint : Measurable endpoint) :
    (freshExtension Γ κ η).map (fun p => endpoint p.1) = Γ.map endpoint :=
  MarkovEndpointPreservation.extension_endpoint Γ (κ.prod η) endpoint hendpoint

/-- Equation (419)'s actual old-neighbor disintegration followed by the fresh
independent extension still has precisely the original ordered-edge law. -/
theorem disintegrated_fresh_original [StandardBorelSpace X] [Nonempty X]
    (Γ : Measure (X × X)) [IsFiniteMeasure Γ]
    (κ : Kernel (X × X) L) [IsMarkovKernel κ]
    (η : Kernel (X × X) R) [IsMarkovKernel η] :
    (freshExtension (Γ.fst.compProd (OldNeighborDisintegration.oldNeighbor Γ))
      κ η).map Prod.fst = Γ := by
  rw [OldNeighborDisintegration.old_neighbor_disintegration]
  exact fresh_extension_original Γ κ η

/-- If each endpoint kernel is supported on genuine incidence labels, the
fresh extension has two genuine labels almost everywhere. The first coordinate
is unchanged, so this support statement retains the original physical point. -/
theorem fresh_extension_genuine
    (Γ : Measure Ω) (κ : Kernel Ω L) [IsMarkovKernel κ]
    (η : Kernel Ω R) [IsMarkovKernel η]
    (G₁ : Set (Ω × L)) (hG₁ : MeasurableSet G₁)
    (G₂ : Set (Ω × R)) (hG₂ : MeasurableSet G₂)
    (hκ : ∀ ω, ∀ᵐ l ∂κ ω, (ω, l) ∈ G₁)
    (hη : ∀ ω, ∀ᵐ r ∂η ω, (ω, r) ∈ G₂) :
    ∀ᵐ p ∂freshExtension Γ κ η,
      (p.1, p.2.1) ∈ G₁ ∧ (p.1, p.2.2) ∈ G₂ := by
  apply Measure.ae_compProd_of_ae_ae
    ((hG₁.preimage (by fun_prop)).inter (hG₂.preimage (by fun_prop)))
  apply Filter.Eventually.of_forall
  intro ω
  rw [Kernel.prod_apply]
  apply (Measure.ae_prod_iff_ae_ae
    ((hG₁.preimage (by fun_prop)).inter (hG₂.preimage (by fun_prop)))).2
  filter_upwards [hκ ω] with l hl
  filter_upwards [hη ω] with r hr
  exact ⟨hl, hr⟩

/-- Any label-dependent thinning keeps both genuine fresh flags; it never
substitutes their normals for inherited labels. -/
theorem restricted_fresh_genuine
    (Γ : Measure Ω) (κ : Kernel Ω L) [IsMarkovKernel κ]
    (η : Kernel Ω R) [IsMarkovKernel η]
    (G₁ : Set (Ω × L)) (hG₁ : MeasurableSet G₁)
    (G₂ : Set (Ω × R)) (hG₂ : MeasurableSet G₂)
    (hκ : ∀ ω, ∀ᵐ l ∂κ ω, (ω, l) ∈ G₁)
    (hη : ∀ ω, ∀ᵐ r ∂η ω, (ω, r) ∈ G₂)
    (B : Set (Ω × (L × R))) :
    ∀ᵐ p ∂(freshExtension Γ κ η).restrict B,
      (p.1, p.2.1) ∈ G₁ ∧ (p.1, p.2.2) ∈ G₂ :=
  ae_restrict_of_ae (fresh_extension_genuine Γ κ η G₁ hG₁ G₂ hG₂ hκ hη)

/-- Exact fiber formula for the occurrence marginal of a label-dependent cut. -/
theorem restricted_original_apply (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsSFiniteKernel κ]
    (B : Set (Ω × L)) (hB : MeasurableSet B)
    (s : Set Ω) (hs : MeasurableSet s) :
    ((Γ.compProd κ).restrict B).map Prod.fst s =
      ∫⁻ ω in s, κ ω (Prod.mk ω ⁻¹' B) ∂Γ := by
  rw [Measure.map_apply measurable_fst hs,
    Measure.restrict_apply (measurable_fst hs),
    Measure.compProd_apply ((measurable_fst hs).inter hB),
    ← lintegral_indicator hs]
  apply lintegral_congr
  intro ω
  by_cases hω : ω ∈ s
  · simp [hω, Set.preimage, Set.indicator_of_mem]
  · simp [hω, Set.preimage, Set.indicator_of_notMem]

/-- Pointwise conditional loss gives a measure-valued original-law loss. -/
theorem restricted_original_le (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsSFiniteKernel κ]
    (B : Set (Ω × L)) (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hbound : ∀ ω, κ ω (Prod.mk ω ⁻¹' B) ≤ c) :
    ((Γ.compProd κ).restrict B).map Prod.fst ≤ c • Γ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [restricted_original_apply Γ κ B hB s hs, Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∫⁻ _ in s, c ∂Γ := lintegral_mono (fun ω => hbound ω)
    _ = c * Γ s := by simp

/-- Pointwise conditional retention gives a measure-valued original-law lower
bound without normalizing or replacing any original occurrence. -/
theorem le_restricted_original (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsSFiniteKernel κ]
    (B : Set (Ω × L)) (hB : MeasurableSet B) (a : ℝ≥0∞)
    (hbound : ∀ ω, a ≤ κ ω (Prod.mk ω ⁻¹' B)) :
    a • Γ ≤ ((Γ.compProd κ).restrict B).map Prod.fst := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [restricted_original_apply Γ κ B hB s hs, Measure.smul_apply, smul_eq_mul]
  calc
    _ = ∫⁻ _ in s, a ∂Γ := by simp
    _ ≤ _ := lintegral_mono (fun ω => hbound ω)

/-- The complement retains the complementary fraction as an occurrence
measure, not merely as a scalar mass. -/
theorem complement_original_ge (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (B : Set (Ω × L)) (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hbound : ∀ ω, κ ω (Prod.mk ω ⁻¹' B) ≤ c) :
    (1 - c) • Γ ≤ ((Γ.compProd κ).restrict Bᶜ).map Prod.fst := by
  apply le_restricted_original Γ κ Bᶜ hB.compl (1 - c)
  intro ω
  rw [Set.preimage_compl, prob_compl_eq_one_sub (measurable_prodMk_left hB)]
  exact tsub_le_tsub_left (hbound ω) 1

section NormalSeparation

variable {N : Type*} [MetricSpace N] [MeasurableSpace N]
  [BorelSpace N] [SecondCountableTopology N]

/-- The discarded event uses the closed cap convention from the paper. -/
def closeNormals (n₁ : Ω × L → N) (n₂ : Ω × R → N) (θ : ℝ) :
    Set (Ω × (L × R)) :=
  {p | dist (n₁ (p.1, p.2.1)) (n₂ (p.1, p.2.2)) ≤ θ}

/-- The closed-normal relation is measurable even when the designated normal
maps also depend on the full original occurrence. -/
theorem measurableSet_closeNormals
    (n₁ : Ω × L → N) (hn₁ : Measurable n₁)
    (n₂ : Ω × R → N) (hn₂ : Measurable n₂) (θ : ℝ) :
    MeasurableSet (closeNormals n₁ n₂ θ) := by
  apply measurableSet_le _ measurable_const
  exact (hn₁.comp (by fun_prop)).dist (hn₂.comp (by fun_prop))

/-- Independent fresh labels make the first cap estimate valid after fixing
any second label; no independence of inherited labels is asserted. -/
theorem close_normals_fiber_le
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (η : Kernel Ω R) [IsMarkovKernel η]
    (n₁ : Ω × L → N) (hn₁ : Measurable n₁)
    (n₂ : Ω × R → N) (hn₂ : Measurable n₂)
    (θ : ℝ) (c : ℝ≥0∞)
    (hcap : ∀ ω z, κ ω {l | dist (n₁ (ω, l)) z ≤ θ} ≤ c) (ω : Ω) :
    κ.prod η ω (Prod.mk ω ⁻¹' closeNormals n₁ n₂ θ) ≤ c := by
  rw [Kernel.prod_apply, Measure.prod_apply_symm
    (measurable_prodMk_left (measurableSet_closeNormals n₁ hn₁ n₂ hn₂ θ))]
  calc
    _ ≤ ∫⁻ _r, c ∂η ω := lintegral_mono (fun r => hcap ω (n₂ (ω, r)))
    _ = c := by simp

/-- Every measurable original-occurrence set loses at most its `c` fraction. -/
theorem close_original_le
    (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (η : Kernel Ω R) [IsMarkovKernel η]
    (n₁ : Ω × L → N) (hn₁ : Measurable n₁)
    (n₂ : Ω × R → N) (hn₂ : Measurable n₂)
    (θ : ℝ) (c : ℝ≥0∞)
    (hcap : ∀ ω z, κ ω {l | dist (n₁ (ω, l)) z ≤ θ} ≤ c) :
    ((freshExtension Γ κ η).restrict (closeNormals n₁ n₂ θ)).map Prod.fst ≤
      c • Γ :=
  restricted_original_le Γ (κ.prod η) _ (measurableSet_closeNormals n₁ hn₁ n₂ hn₂ θ)
    c (close_normals_fiber_le κ η n₁ hn₁ n₂ hn₂ θ c hcap)

/-- Separated designated normals retain at least the `1-c` fraction of the
original law on every measurable original-occurrence set. -/
theorem separated_original_ge
    (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (η : Kernel Ω R) [IsMarkovKernel η]
    (n₁ : Ω × L → N) (hn₁ : Measurable n₁)
    (n₂ : Ω × R → N) (hn₂ : Measurable n₂)
    (θ : ℝ) (c : ℝ≥0∞)
    (hcap : ∀ ω z, κ ω {l | dist (n₁ (ω, l)) z ≤ θ} ≤ c) :
    (1 - c) • Γ ≤
      ((freshExtension Γ κ η).restrict (closeNormals n₁ n₂ θ)ᶜ).map Prod.fst :=
  complement_original_ge Γ (κ.prod η) _ (measurableSet_closeNormals n₁ hn₁ n₂ hn₂ θ)
    c (close_normals_fiber_le κ η n₁ hn₁ n₂ hn₂ θ c hcap)

/-- The separated event really has strict normal separation almost
everywhere. This is a property of the designated fresh labels only. -/
theorem separated_normals_ae
    (Γ : Measure Ω) (κ : Kernel Ω L) (η : Kernel Ω R)
    (n₁ : Ω × L → N) (hn₁ : Measurable n₁)
    (n₂ : Ω × R → N) (hn₂ : Measurable n₂) (θ : ℝ) :
    ∀ᵐ p ∂(freshExtension Γ κ η).restrict (closeNormals n₁ n₂ θ)ᶜ,
      θ < dist (n₁ (p.1, p.2.1)) (n₂ (p.1, p.2.2)) := by
  filter_upwards [ae_restrict_mem (measurableSet_closeNormals n₁ hn₁ n₂ hn₂ θ).compl]
    with p hp
  exact lt_of_not_ge hp

/-- The scalar retained-mass estimate is a consequence of the stronger
occurrence-marginal lower bound. -/
theorem separated_mass_ge
    (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (η : Kernel Ω R) [IsMarkovKernel η]
    (n₁ : Ω × L → N) (hn₁ : Measurable n₁)
    (n₂ : Ω × R → N) (hn₂ : Measurable n₂)
    (θ : ℝ) (c : ℝ≥0∞)
    (hcap : ∀ ω z, κ ω {l | dist (n₁ (ω, l)) z ≤ θ} ≤ c) :
    (1 - c) * Γ univ ≤
      (freshExtension Γ κ η).restrict (closeNormals n₁ n₂ θ)ᶜ univ := by
  have h := separated_original_ge Γ κ η n₁ hn₁ n₂ hn₂ θ c hcap univ
  simpa only [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] using h

/-- A nonzero original mass leaves positive separated mass when `c < 1`. -/
theorem separated_mass_pos
    (Γ : Measure Ω) [SFinite Γ] (hΓ : 0 < Γ univ)
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (η : Kernel Ω R) [IsMarkovKernel η]
    (n₁ : Ω × L → N) (hn₁ : Measurable n₁)
    (n₂ : Ω × R → N) (hn₂ : Measurable n₂)
    (θ : ℝ) (c : ℝ≥0∞) (hc : c < 1)
    (hcap : ∀ ω z, κ ω {l | dist (n₁ (ω, l)) z ≤ θ} ≤ c) :
    0 < (freshExtension Γ κ η).restrict (closeNormals n₁ n₂ θ)ᶜ univ :=
  (ENNReal.mul_pos (ne_of_gt (tsub_pos_iff_lt.mpr hc)) (ne_of_gt hΓ)).trans_le
    (separated_mass_ge Γ κ η n₁ hn₁ n₂ hn₂ θ c hcap)

/-- Every measurable endpoint observable inherits the same discarded-law
budget, including the ordered pair of original endpoints. -/
theorem close_observable_le
    (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (η : Kernel Ω R) [IsMarkovKernel η]
    (n₁ : Ω × L → N) (hn₁ : Measurable n₁)
    (n₂ : Ω × R → N) (hn₂ : Measurable n₂)
    (θ : ℝ) (c : ℝ≥0∞)
    (hcap : ∀ ω z, κ ω {l | dist (n₁ (ω, l)) z ≤ θ} ≤ c)
    (endpoint : Ω → Y) (hendpoint : Measurable endpoint) :
    ((freshExtension Γ κ η).restrict (closeNormals n₁ n₂ θ)).map
        (fun p => endpoint p.1) ≤ c • Γ.map endpoint := by
  have h := Measure.map_mono
    (close_original_le Γ κ η n₁ hn₁ n₂ hn₂ θ c hcap) hendpoint
  simpa only [Measure.map_smul, Measure.map_map hendpoint measurable_fst,
    Function.comp_def] using h

/-- The lower bound is inherited by every measurable endpoint observable. -/
theorem separated_observable_ge
    (Γ : Measure Ω) [SFinite Γ]
    (κ : Kernel Ω L) [IsMarkovKernel κ]
    (η : Kernel Ω R) [IsMarkovKernel η]
    (n₁ : Ω × L → N) (hn₁ : Measurable n₁)
    (n₂ : Ω × R → N) (hn₂ : Measurable n₂)
    (θ : ℝ) (c : ℝ≥0∞)
    (hcap : ∀ ω z, κ ω {l | dist (n₁ (ω, l)) z ≤ θ} ≤ c)
    (endpoint : Ω → Y) (hendpoint : Measurable endpoint) :
    (1 - c) • Γ.map endpoint ≤
      ((freshExtension Γ κ η).restrict (closeNormals n₁ n₂ θ)ᶜ).map
        (fun p => endpoint p.1) := by
  have h := Measure.map_mono
    (separated_original_ge Γ κ η n₁ hn₁ n₂ hn₂ θ c hcap) hendpoint
  simpa only [Measure.map_smul, Measure.map_map hendpoint measurable_fst,
    Function.comp_def] using h

/-- Endpoint kernels are pulled back along the original endpoint maps, then
sampled independently. The input cap hypothesis is stated directly for the
first normal *law*, as in the paper's conditional-normal estimate. -/
theorem endpoint_normal_law_separation
    (Γ : Measure Ω) [SFinite Γ]
    (left right : Ω → X) (hleft : Measurable left) (hright : Measurable right)
    (κ : Kernel X L) [IsMarkovKernel κ]
    (η : Kernel X R) [IsMarkovKernel η]
    (n₁ : L → N) (hn₁ : Measurable n₁)
    (n₂ : R → N) (hn₂ : Measurable n₂)
    (θ : ℝ) (c : ℝ≥0∞)
    (hcap : ∀ ω z, ((κ (left ω)).map n₁) (Metric.closedBall z θ) ≤ c) :
    let μ := freshExtension Γ (κ.comap left hleft) (η.comap right hright)
    let B := closeNormals (fun p : Ω × L => n₁ p.2) (fun p : Ω × R => n₂ p.2) θ
    μ.map Prod.fst = Γ ∧
      (μ.restrict B).map Prod.fst ≤ c • Γ ∧
      (1 - c) • Γ ≤ (μ.restrict Bᶜ).map Prod.fst := by
  dsimp only
  have hcap' : ∀ ω z, (κ.comap left hleft) ω
      {l | dist (n₁ l) z ≤ θ} ≤ c := by
    intro ω z
    have h := hcap ω z
    rw [Measure.map_apply hn₁ measurableSet_closedBall] at h
    exact h
  exact ⟨fresh_extension_original Γ _ _,
    close_original_le Γ _ _ _ (hn₁.comp measurable_snd) _ (hn₂.comp measurable_snd)
      θ c hcap',
    separated_original_ge Γ _ _ _ (hn₁.comp measurable_snd) _ (hn₂.comp measurable_snd)
      θ c hcap'⟩

end NormalSeparation

end StickyKakeya4.IndependentFlagSeparation
