import Theorems.Thm_StickyKakeya4_finite_scale_source_mass

open MeasureTheory Set

namespace StickyKakeya4

/-- The unnormalized formula for conditioning a measure on a measurable
positive-mass source.  Keeping the scalar visible is essential for the
coefficient-one descendant ledger. -/
noncomputable def normalizedRestrictionMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (source : Set α) : Measure α :=
  (μ source)⁻¹ • μ.restrict source

theorem normalizedRestrictionMeasure_apply {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {source target : Set α}
    (_hsource : MeasurableSet source) (htarget : MeasurableSet target) :
    normalizedRestrictionMeasure μ source target =
      (μ source)⁻¹ * μ (target ∩ source) := by
  rw [normalizedRestrictionMeasure, Measure.smul_apply]
  change (μ source)⁻¹ * (μ.restrict source) target = _
  rw [Measure.restrict_apply htarget]

/-- A normalized retained law is dominated by the root law with exactly the
inverse retained mass as coefficient. -/
theorem normalizedRestrictionMeasure_apply_le_root {α : Type*}
    [MeasurableSpace α] (μ : Measure α) {source target : Set α}
    (hsource : MeasurableSet source) (htarget : MeasurableSet target) :
    normalizedRestrictionMeasure μ source target ≤
      (μ source)⁻¹ * μ target := by
  rw [normalizedRestrictionMeasure_apply μ hsource htarget]
  exact mul_le_mul_right
    (measure_mono (Set.inter_subset_left : target ∩ source ⊆ target))
    ((μ source)⁻¹)

/-- Domination survives physical readback.  Thus every conditioned descendant
can reuse the finite source built for the root law, with the sole explicit
cost `μ source` inverse; no product structure is falsely asserted for the
conditioned law. -/
theorem map_normalizedRestrictionMeasure_apply_le_root
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {source : Set α} (hsource : MeasurableSet source)
    (f : α → β) (hf : Measurable f) {target : Set β}
    (htarget : MeasurableSet target) :
    Measure.map f (normalizedRestrictionMeasure μ source) target ≤
      (μ source)⁻¹ * Measure.map f μ target := by
  rw [Measure.map_apply hf htarget, Measure.map_apply hf htarget]
  exact normalizedRestrictionMeasure_apply_le_root μ hsource
    (htarget.preimage hf)

/-- The unnormalized retained pushforward is coefficient-one dominated by the
root pushforward.  This is the form summed in the Carleson ledger. -/
theorem map_restrict_apply_le_root
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (source : Set α)
    (f : α → β) (hf : Measurable f) {target : Set β}
    (htarget : MeasurableSet target) :
    Measure.map f (μ.restrict source) target ≤ Measure.map f μ target := by
  rw [Measure.map_apply hf htarget, Measure.map_apply hf htarget,
    Measure.restrict_apply (htarget.preimage hf)]
  exact measure_mono (Set.inter_subset_left : f ⁻¹' target ∩ source ⊆ f ⁻¹' target)

/-- Exact cancellation of the normalization coefficient after pushforward.
This turns the probability-law boundary oracle back into the unnormalized
mass-conserving descendant ledger. -/
theorem mass_mul_map_normalizedRestrictionMeasure_apply
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {source : Set α} (hsource : MeasurableSet source)
    (hsourceZero : μ source ≠ 0) (hsourceTop : μ source ≠ ⊤)
    (f : α → β) (hf : Measurable f) {target : Set β}
    (htarget : MeasurableSet target) :
    μ source *
        Measure.map f (normalizedRestrictionMeasure μ source) target =
      Measure.map f (μ.restrict source) target := by
  rw [Measure.map_apply hf htarget, Measure.map_apply hf htarget,
    normalizedRestrictionMeasure_apply μ hsource (htarget.preimage hf),
    Measure.restrict_apply (htarget.preimage hf)]
  calc
    μ source * ((μ source)⁻¹ * μ (f ⁻¹' target ∩ source)) =
        ((μ source)⁻¹ * μ source) * μ (f ⁻¹' target ∩ source) := by ac_rfl
    _ = μ (f ⁻¹' target ∩ source) := by
      rw [ENNReal.inv_mul_cancel hsourceZero hsourceTop, one_mul]

/-- Compose conditioned-law domination with any root finite-source readback.
The same fractional source `R` pays for the descendant ball; the exact and
only extra coefficient is the inverse mass of the retained parameter source.
-/
theorem map_normalizedRestrictionMeasure_apply_le_scaled_sourceMass
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {source : Set α} (hsource : MeasurableSet source)
    (f : α → β) (hf : Measurable f) {target : Set β}
    (htarget : MeasurableSet target) {n : ℕ} (R : FiniteScaleSource n)
    (C : ENNReal)
    (hrootReadback : Measure.map f μ target ≤ C * sourceMass R) :
    Measure.map f (normalizedRestrictionMeasure μ source) target ≤
      (μ source)⁻¹ * C * sourceMass R := by
  calc
    Measure.map f (normalizedRestrictionMeasure μ source) target ≤
        (μ source)⁻¹ * Measure.map f μ target :=
      map_normalizedRestrictionMeasure_apply_le_root μ hsource f hf htarget
    _ ≤ (μ source)⁻¹ * (C * sourceMass R) :=
      mul_le_mul_right hrootReadback ((μ source)⁻¹)
    _ = (μ source)⁻¹ * C * sourceMass R := by ac_rfl

/-- A root finite-source readback pays every unnormalized retained descendant
with coefficient one. -/
theorem map_restrict_apply_le_sourceMass
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (source : Set α)
    (f : α → β) (hf : Measurable f) {target : Set β}
    (htarget : MeasurableSet target) {n : ℕ} (R : FiniteScaleSource n)
    (C : ENNReal)
    (hrootReadback : Measure.map f μ target ≤ C * sourceMass R) :
    Measure.map f (μ.restrict source) target ≤ C * sourceMass R :=
  (map_restrict_apply_le_root μ source f hf htarget).trans hrootReadback

/-- Positive finite retained mass makes the normalized restriction have total
mass one. -/
theorem normalizedRestrictionMeasure_apply_univ {α : Type*}
    [MeasurableSpace α] (μ : Measure α) {source : Set α}
    (hsource : MeasurableSet source) (hsourceZero : μ source ≠ 0)
    (hsourceTop : μ source ≠ ⊤) :
    normalizedRestrictionMeasure μ source Set.univ = 1 := by
  rw [normalizedRestrictionMeasure_apply μ hsource MeasurableSet.univ,
    Set.univ_inter, ENNReal.inv_mul_cancel hsourceZero hsourceTop]

/-- The explicit normalized restriction can be passed directly to any theorem
quantifying over probability laws, including the coherent-boundary oracle. -/
theorem normalizedRestrictionMeasure_isProbabilityMeasure {α : Type*}
    [MeasurableSpace α] (μ : Measure α) {source : Set α}
    (hsource : MeasurableSet source) (hsourceZero : μ source ≠ 0)
    (hsourceTop : μ source ≠ ⊤) :
    IsProbabilityMeasure (normalizedRestrictionMeasure μ source) := by
  constructor
  exact normalizedRestrictionMeasure_apply_univ μ hsource hsourceZero hsourceTop

/-- A normalized restriction is supported on the retained parameter source. -/
theorem normalizedRestrictionMeasure_compl_eq_zero {α : Type*}
    [MeasurableSpace α] (μ : Measure α) {source : Set α}
    (hsource : MeasurableSet source) :
    normalizedRestrictionMeasure μ source sourceᶜ = 0 := by
  rw [normalizedRestrictionMeasure_apply μ hsource hsource.compl]
  simp

/-- Replace the weights and shadings of a finite source while retaining its
marked lines, affine fibre marks, and entire carrier tree.  This is the
source-level representation of a retained parameter sublaw. -/
noncomputable def retainedSource {n : ℕ} (D : FiniteScaleSource n)
    (retainedShading : Fin n → Set E4) (retainedWeight : Fin n → ENNReal) :
    FiniteScaleSource n where
  thickness := D.thickness
  line := D.line
  line_injective := D.line_injective
  shading := retainedShading
  weight := retainedWeight
  fibreMark := D.fibreMark
  tree := D.tree
  line_in_carrier := D.line_in_carrier

/-- Any measurable coefficient-one decrease of the weights and shadings is a
fractional restriction of the original source.  In particular the affine
fibre mark and an arbitrary nested carrier tree are preserved definitionally. -/
theorem retainedSource_isFractionalSourceRestriction {n : ℕ}
    (D : FiniteScaleSource n)
    (retainedShading : Fin n → Set E4) (retainedWeight : Fin n → ENNReal)
    (hMeasurable : ∀ i, MeasurableSet (retainedShading i))
    (hShading : ∀ i, retainedShading i ⊆ D.shading i)
    (hWeight : ∀ i, retainedWeight i ≤ D.weight i) :
    IsFractionalSourceRestriction
      (retainedSource D retainedShading retainedWeight) D := by
  exact ⟨rfl, rfl, rfl, rfl, hMeasurable, hShading, hWeight⟩

/-- Normalized cell weights are monotone in the retained cell mass.  No
renormalization is performed, so the comparison has coefficient one. -/
theorem normalizedPartitionWeight_mono {C : ENNReal} {delta : ℝ}
    {qRetained qRoot : ENNReal} (hq : qRetained ≤ qRoot) :
    normalizedPartitionWeight C delta qRetained ≤
      normalizedPartitionWeight C delta qRoot := by
  unfold normalizedPartitionWeight
  exact ENNReal.div_le_div_right hq (C * (ENNReal.ofReal delta) ^ 3)

/-- A ball-localized source made from retained cell masses is a fractional
restriction of the root full-tube source made from the original cell masses.
This is the missing coefficient-one bridge between a retained parameter law
and the finite collision source; it keeps the line, affine mark, and carrier
tree fixed. -/
theorem activeBallRestriction_isFractionalSourceRestriction_of_cellMass_le
    {n : ℕ} (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line)
    (qRetained qRoot : Fin n → ENNReal) (C : ENNReal)
    (active : Set (Fin n)) (x : E4) (radius : ℝ)
    (hq : ∀ i, qRetained i ≤ qRoot i) :
    IsFractionalSourceRestriction
      (activeBallRestriction delta line hline qRetained C active x radius)
      (fullMarkedTubeSource delta line hline qRoot C) := by
  classical
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ active
    · simp only [activeBallRestriction, hi, if_true]
      exact (measurableSet_markedUnitTube (line i) delta).inter
        Metric.isClosed_closedBall.measurableSet
    · simp [activeBallRestriction, hi]
  · intro i
    by_cases hi : i ∈ active <;>
      simp [activeBallRestriction, fullMarkedTubeSource, hi]
  · intro i
    by_cases hi : i ∈ active
    · simpa [activeBallRestriction, fullMarkedTubeSource, hi] using
        normalizedPartitionWeight_mono (C := C) (delta := delta) (hq i)
    · simp [activeBallRestriction, fullMarkedTubeSource, hi]

/-- The unlocalized retained full-tube source is already a fractional source
restriction of the root source.  This is useful before choosing a physical
ball or a stopping-tree descendant. -/
theorem fullMarkedTubeSource_isFractionalSourceRestriction_of_cellMass_le
    {n : ℕ} (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line)
    (qRetained qRoot : Fin n → ENNReal) (C : ENNReal)
    (hq : ∀ i, qRetained i ≤ qRoot i) :
    IsFractionalSourceRestriction
      (fullMarkedTubeSource delta line hline qRetained C)
      (fullMarkedTubeSource delta line hline qRoot C) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro i
    exact measurableSet_markedUnitTube (line i) delta
  · intro i
    rfl
  · intro i
    exact normalizedPartitionWeight_mono (C := C) (delta := delta) (hq i)

end StickyKakeya4
