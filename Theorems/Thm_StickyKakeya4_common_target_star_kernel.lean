import Theorems.Thm_StickyKakeya4_positive_flag_conditioning
import Theorems.Thm_StickyKakeya4_weighted_growth_star_split
import Theorems.Thm_StickyKakeya4_normalized_target_growth
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Actual stationary common-target stars of whole old occurrences

The common-target kernel disintegrates `(target,id)_#Γ` for the unweighted
aggregate old occurrence Γ. Each sample is an entire old occurrence, including
its source, target, time, and inherited flags. Before any success restriction,
each of the three independent fresh occurrences has exactly marginal Γ, while
the inherited occurrence and its source index are held fixed.

Finite source-index probabilities are derived from the actual restrictions
`Γ.restrict {index=i}`: they equal `e_i / ∑ e_j` almost everywhere at the target.
Source masses are the original selector masses `σ S_i`, never occurrence-source
masses. Original ordered-pair product domination yields target domination;
bounded measurable RN representatives give `e_i = (σ S_i) w_i`, with `w_i≤1`.

On a comparable selector-mass layer `q≤σ(S_i)≤2q`, multiplicity `∑w_i≥24`
retains at least half of every measurable part of the inherited high branch.
A high branch containing half the incoming mass therefore leaves at least one
quarter in actual four-distinct stars. Disjoint genuine source cuts make these
four *physical* sources distinct, and all fresh copies have the inherited target.

Stationarity is a PRE-CUT statement. After high-branch and four-distinct cuts,
the fresh marginals are only proved dominated by Γ. The inherited retained
marginal has the proved half lower bound and original-source upper bound.
No post-cut stationarity, time alignment, cross-cap payment, or terminal
geometric conclusion is asserted. The normalized index/occurrence mixture is
also supplied as an auxiliary construction, with zero-weight indices excluded.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.FourDistinctSources

variable {A I : Type*} [MeasurableSpace A] [Fintype I]
  [MeasurableSpace I] [MeasurableSingletonClass I]

/-- A measurable finite index observable sends three independent labels to the
actual finite triple law of its singleton masses. -/
theorem measure_triple_event_eq_ofReal_tripleProbability
    (μ : Measure A) [IsFiniteMeasure μ] (idx : A → I) (hidx : Measurable idx)
    (E : I → I → I → Prop) :
    (μ.prod (μ.prod μ)) {u : A × (A × A) | E (idx u.1) (idx u.2.1) (idx u.2.2)} =
      ENNReal.ofReal (tripleProbability
        (fun j => (μ (idx ⁻¹' {j})).toReal) E) := by
  classical
  let f : A × (A × A) → I × (I × I) := Prod.map idx (Prod.map idx idx)
  have hf : Measurable f := hidx.prodMap (hidx.prodMap hidx)
  let s : Finset (I × (I × I)) := Finset.univ.filter (fun v => E v.1 v.2.1 v.2.2)
  have hevent : {u : A × (A × A) | E (idx u.1) (idx u.2.1) (idx u.2.2)} =
      f ⁻¹' (↑s : Set (I × (I × I))) := by
    ext u
    simp [s, f]
  have hfiber (v : I × (I × I)) : f ⁻¹' {v} =
      (idx ⁻¹' {v.1}) ×ˢ ((idx ⁻¹' {v.2.1}) ×ˢ (idx ⁻¹' {v.2.2})) := by
    ext u
    simp [f, Prod.ext_iff]
  rw [hevent, ← sum_measure_preimage_singleton s (fun v _ => hf (measurableSet_singleton v))]
  simp_rw [hfiber, Measure.prod_prod]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  unfold tripleProbability tripleExpectation
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  apply Finset.sum_congr rfl
  intro k _
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : E j k l
  · simp only [h, if_true, mul_one]
    rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    simp only [ENNReal.ofReal_toReal (measure_ne_top μ _), mul_assoc]
  · simp [h]

/-- The inherited source stays fixed; only the other three labels are sampled. -/
theorem measure_fourDistinct_eq_ofReal
    (μ : Measure A) [IsProbabilityMeasure μ] (idx : A → I) (hidx : Measurable idx)
    (i : I) :
    (μ.prod (μ.prod μ)) {u : A × (A × A) |
      FourDistinct i (idx u.1) (idx u.2.1) (idx u.2.2)} =
      ENNReal.ofReal (fourDistinctProbability
        (fun j => (μ (idx ⁻¹' {j})).toReal) i) :=
  measure_triple_event_eq_ofReal_tripleProbability μ idx hidx (FourDistinct i)

/-- Normalized real weights give a lower bound for the mass of the genuine
measurable event, rather than merely a formal finite sum. -/
theorem measure_fourDistinct_ge_half_of_normalizedWeights
    (μ : Measure A) [IsProbabilityMeasure μ] (idx : A → I) (hidx : Measurable idx)
    (w : I → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∀ j, w j ≤ 1)
    (hweights : ∀ j, (μ (idx ⁻¹' {j})).toReal = normalizedWeights w j)
    (K : ℝ) (hK : 12 ≤ K) (hN : K ≤ ∑ j, w j) (i : I) :
    (1 : ℝ≥0∞) / 2 ≤
      (μ.prod (μ.prod μ)) {u : A × (A × A) |
        FourDistinct i (idx u.1) (idx u.2.1) (idx u.2.2)} := by
  rw [measure_fourDistinct_eq_ofReal μ idx hidx i,
    show (fun j => (μ (idx ⁻¹' {j})).toReal) = normalizedWeights w from funext hweights]
  calc
    (1 : ℝ≥0∞) / 2 = ENNReal.ofReal ((1 : ℝ) / 2) := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (weighted_four_distinct_probability_ge_half w hw0 hw1 K hK hN i)

/-- ENNReal singleton masses are exactly the normalized source weights; high
multiplicity then gives at least one half in the actual product measure. -/
theorem measure_fourDistinct_ge_half_of_ennreal_weights
    (μ : Measure A) [IsProbabilityMeasure μ] (idx : A → I) (hidx : Measurable idx)
    (w : I → ℝ≥0∞) (hw : ∀ j, w j ≤ 1)
    (hweights : ∀ j, μ (idx ⁻¹' {j}) = w j / ∑ k, w k)
    (K : ℝ) (hK : 12 ≤ K) (hN : ENNReal.ofReal K ≤ ∑ j, w j) (i : I) :
    (1 : ℝ≥0∞) / 2 ≤
      (μ.prod (μ.prod μ)) {u : A × (A × A) |
        FourDistinct i (idx u.1) (idx u.2.1) (idx u.2.2)} := by
  rw [measure_fourDistinct_eq_ofReal μ idx hidx i]
  simp_rw [hweights]
  calc
    (1 : ℝ≥0∞) / 2 = ENNReal.ofReal ((1 : ℝ) / 2) := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (ennreal_weighted_four_distinct_probability_ge_half w hw K hK hN i)

/-- A useful real-valued version of the same genuine event estimate. -/
theorem measure_fourDistinct_toReal_ge_half_of_ennreal_weights
    (μ : Measure A) [IsProbabilityMeasure μ] (idx : A → I) (hidx : Measurable idx)
    (w : I → ℝ≥0∞) (hw : ∀ j, w j ≤ 1)
    (hweights : ∀ j, μ (idx ⁻¹' {j}) = w j / ∑ k, w k)
    (K : ℝ) (hK : 12 ≤ K) (hN : ENNReal.ofReal K ≤ ∑ j, w j) (i : I) :
    (1 : ℝ) / 2 ≤
      ((μ.prod (μ.prod μ)) {u : A × (A × A) |
        FourDistinct i (idx u.1) (idx u.2.1) (idx u.2.2)}).toReal := by
  have h := measure_fourDistinct_ge_half_of_ennreal_weights μ idx hidx w hw hweights K hK hN i
  have ht := ENNReal.toReal_mono (measure_ne_top (μ.prod (μ.prod μ)) _) h
  norm_num at ht ⊢
  exact ht

end StickyKakeya4.FourDistinctSources


namespace StickyKakeya4.CommonTargetStarKernel

namespace ConditionalIndexDensity

variable {Ω X I : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [StandardBorelSpace Ω] [Nonempty Ω]

 theorem atom_density (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target)
    (A : Set Ω) (hA : MeasurableSet A) :
    (Γ.map target).withDensity (fun x =>
      (Γ.map (fun ω => (target ω, ω))).condKernel x A) =
      (Γ.restrict A).map target := by
  let ρ := Γ.map (fun ω => (target ω, ω))
  have hf : ρ.fst = Γ.map target := Measure.fst_map_prodMk measurable_id
  have hd : (Γ.map target).compProd ρ.condKernel = ρ := by
    rw [← hf]
    exact ρ.disintegrate ρ.condKernel
  apply Measure.ext
  intro s hs
  rw [withDensity_apply _ hs, Measure.map_apply htarget hs,
    Measure.restrict_apply (htarget hs)]
  change (∫⁻ x in s, ρ.condKernel x A ∂Γ.map target) = _
  rw [← Measure.compProd_apply_prod hs hA, hd]
  dsimp only [ρ]
  rw [Measure.map_apply (show Measurable (fun ω => (target ω, ω)) from htarget.prodMk measurable_id) (hs.prod hA)]
  rfl

 theorem weighted_ratio_ae (σ μ : Measure X) [IsFiniteMeasure σ]
    (f g k : X → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hk : Measurable k) (hμ : μ = σ.withDensity f)
    (hkg : μ.withDensity k = σ.withDensity g)
    (hfin : ∀ᵐ x ∂μ, f x ≠ ∞) :
    k =ᵐ[μ] fun x => g x / f x := by
  have heq : (fun x => f x * k x) =ᵐ[σ] g := by
    apply (withDensity_eq_iff_of_sigmaFinite (hf.mul hk).aemeasurable hg.aemeasurable).mp
    rw [withDensity_mul σ hf hk, ← hμ]
    exact hkg
  have heqμ := (withDensity_absolutelyContinuous σ f).ae_le heq
  rw [← hμ] at heqμ
  have hpos : ∀ᵐ x ∂μ, f x ≠ 0 := by
    rw [hμ, ae_withDensity_iff hf]
    exact Filter.Eventually.of_forall (fun x hx => hx)
  filter_upwards [heqμ, hpos, hfin] with x heq hx0 hxT
  rw [← heq, mul_comm (f x) (k x), ENNReal.mul_div_cancel_right hx0 hxT]

section FiniteIndex
variable [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [StandardBorelSpace Ω] [Nonempty Ω] in
 theorem index_partition (Γ : Measure Ω) (idx : Ω → I) (hidx : Measurable idx) :
    Γ = Measure.sum (fun i => Γ.restrict (idx ⁻¹' {i})) := by
  have hcover : (⋃ i, idx ⁻¹' {i}) = Set.univ := by
    ext ω
    simp
  have hdisj : Pairwise (fun i j => Disjoint (idx ⁻¹' {i}) (idx ⁻¹' {j})) := by
    intro i j hij
    exact Disjoint.preimage idx (Set.disjoint_singleton.mpr hij)
  simpa [hcover] using Measure.restrict_iUnion (μ := Γ) hdisj
    (fun i => hidx (measurableSet_singleton i))

omit [StandardBorelSpace Ω] [Nonempty Ω] in
 theorem total_target_density (σ : Measure X) (Γ : Measure Ω)
    (target : Ω → X) (htarget : Measurable target)
    (idx : Ω → I) (hidx : Measurable idx)
    (e : I → X → ℝ≥0∞) (he : ∀ i, Measurable (e i))
    (hdens : ∀ i, (Γ.restrict (idx ⁻¹' {i})).map target = σ.withDensity (e i)) :
    Γ.map target = σ.withDensity (fun x => ∑ i, e i x) := by
  calc
    Γ.map target = (Measure.sum (fun i => Γ.restrict (idx ⁻¹' {i}))).map target :=
      congrArg (Measure.map target) (index_partition Γ idx hidx)
    _ = Measure.sum (fun i => (Γ.restrict (idx ⁻¹' {i})).map target) :=
      Measure.map_sum htarget.aemeasurable
    _ = Measure.sum (fun i => σ.withDensity (e i)) := by simp_rw [hdens]
    _ = σ.withDensity (∑' i, e i) := (withDensity_tsum he).symm
    _ = σ.withDensity (fun x => ∑ i, e i x) := by simp [tsum_fintype, Finset.sum_fn]

 theorem conditional_index_ratio_ae (σ : Measure X) [IsFiniteMeasure σ]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target)
    (idx : Ω → I) (hidx : Measurable idx)
    (e : I → X → ℝ≥0∞) (he : ∀ i, Measurable (e i))
    (hefin : ∀ i x, e i x ≠ ∞)
    (hdens : ∀ i, (Γ.restrict (idx ⁻¹' {i})).map target = σ.withDensity (e i))
    (i : I) :
    (fun x => (Γ.map (fun ω => (target ω, ω))).condKernel x (idx ⁻¹' {i}))
      =ᵐ[Γ.map target] fun x => e i x / ∑ j, e j x := by
  apply weighted_ratio_ae σ (Γ.map target) (fun x => ∑ j, e j x) (e i)
    (fun x => (Γ.map (fun ω => (target ω, ω))).condKernel x (idx ⁻¹' {i}))
  · exact Finset.measurable_sum _ (fun j _ => he j)
  · exact he i
  · exact Kernel.measurable_coe _ (hidx (measurableSet_singleton i))
  · exact total_target_density σ Γ target htarget idx hidx e he hdens
  · rw [atom_density Γ target htarget _ (hidx (measurableSet_singleton i)), hdens i]
  · exact Filter.Eventually.of_forall (fun x => ENNReal.sum_ne_top.mpr (fun j _ => hefin j x))
end FiniteIndex

end ConditionalIndexDensity


variable {Ω X I : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- Keep the full old occurrence beside its target. -/
def targetOccurrence (Γ : Measure Ω) (target : Ω → X) : Measure (X × Ω) :=
  Γ.map (fun ω => (target ω, ω))

instance targetOccurrence_isFinite (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) : IsFiniteMeasure (targetOccurrence Γ target) := by
  unfold targetOccurrence
  infer_instance

theorem targetOccurrence_fst (Γ : Measure Ω) (target : Ω → X) :
    (targetOccurrence Γ target).fst = Γ.map target :=
  Measure.fst_map_prodMk measurable_id

/-- A genuine source cut inherits its selector-product bound from the same
original ordered-pair law, without replacing any inherited coordinate. -/
theorem source_cut_joint_le (σ : Measure X) [SFinite σ]
    (Γ : Measure Ω) (source target : Ω → X)
    (hsource : Measurable source) (htarget : Measurable target)
    (S : Set X) (hS : MeasurableSet S)
    (hroot : Γ.map (fun ω => (source ω, target ω)) ≤ σ.prod σ) :
    (Γ.restrict (source ⁻¹' S)).map (fun ω => (source ω, target ω)) ≤
      (σ.restrict S).prod σ := by
  have hm : Measurable (fun ω => (source ω, target ω)) := hsource.prodMk htarget
  have hpre : (fun ω => (source ω, target ω)) ⁻¹' (S ×ˢ univ) = source ⁻¹' S := by
    ext ω
    simp
  calc
    _ = (Γ.map (fun ω => (source ω, target ω))).restrict (S ×ˢ univ) := by
      rw [Measure.restrict_map hm (hS.prod MeasurableSet.univ), hpre]
    _ ≤ (σ.prod σ).restrict (S ×ˢ univ) := Measure.restrict_mono_measure hroot _
    _ = (σ.restrict S).prod σ := (Measure.restrict_prod_eq_prod_univ S).symm

/-- Product domination uses the original selector source mass `σ S`. -/
theorem target_le_selector_source_mass (σ : Measure X) [SFinite σ]
    (Γ : Measure Ω) (source target : Ω → X)
    (hsource : Measurable source) (htarget : Measurable target)
    (S : Set X)
    (hdom : Γ.map (fun ω => (source ω, target ω)) ≤ (σ.restrict S).prod σ) :
    Γ.map target ≤ (σ S) • σ := by
  have h := Measure.map_mono hdom measurable_snd
  rw [Measure.map_map measurable_snd (hsource.prodMk htarget),
    Measure.map_snd_prod] at h
  simpa only [Function.comp_def, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter] using h

/-- The same source-cut product bound proves actual source membership, even
when the old occurrence contains arbitrary additional marks. -/
theorem source_piece_genuine (σ : Measure X) [SFinite σ]
    (Γ : Measure Ω) (source target : Ω → X)
    (hsource : Measurable source) (htarget : Measurable target)
    (S : Set X) (hS : MeasurableSet S)
    (hdom : Γ.map (fun ω => (source ω, target ω)) ≤ (σ.restrict S).prod σ) :
    ∀ᵐ ω ∂Γ, source ω ∈ S := by
  have hm : Measurable (fun ω => (source ω, target ω)) := hsource.prodMk htarget
  have h := hdom (Sᶜ ×ˢ univ)
  rw [Measure.map_apply hm (hS.compl.prod MeasurableSet.univ),
    Measure.prod_prod, Measure.restrict_apply hS.compl] at h
  simp only [Set.compl_inter_self, measure_empty, zero_mul] at h
  have hpre : (fun ω => (source ω, target ω)) ⁻¹' (Sᶜ ×ˢ univ) =
      {ω | source ω ∉ S} := by
    ext ω
    simp
  rw [hpre] at h
  exact ae_iff.mpr (le_antisymm h bot_le)

/-- The normalized target law is a genuine submeasure of the selector. -/
theorem normalized_target_le_selector (σ : Measure X) [IsFiniteMeasure σ]
    (Γ : Measure Ω) (source target : Ω → X)
    (hsource : Measurable source) (htarget : Measurable target)
    (S : Set X) (hS : σ S ≠ 0)
    (hdom : Γ.map (fun ω => (source ω, target ω)) ≤ (σ.restrict S).prod σ) :
    (σ S)⁻¹ • Γ.map target ≤ σ := by
  have h := smul_le_smul_left (σ S)⁻¹
    (target_le_selector_source_mass σ Γ source target hsource htarget S hdom)
  simpa only [smul_smul, ENNReal.inv_mul_cancel hS (measure_ne_top σ S), one_smul] using h

/-- A pointwise bounded measurable representative of the density of `ν≤σ`. -/
def boundedWeight (σ ν : Measure X) (x : X) : ℝ≥0∞ := min (ν.rnDeriv σ x) 1

theorem measurable_boundedWeight (σ ν : Measure X) : Measurable (boundedWeight σ ν) :=
  (Measure.measurable_rnDeriv ν σ).min measurable_const

theorem boundedWeight_le_one (σ ν : Measure X) (x : X) : boundedWeight σ ν x ≤ 1 :=
  min_le_right _ _

/-- Clipping changes only a null set, so this remains the actual target density. -/
theorem boundedWeight_density (σ : Measure X) [IsFiniteMeasure σ]
    (ν : Measure X) (hν : ν ≤ σ) : σ.withDensity (boundedWeight σ ν) = ν := by
  let : IsFiniteMeasure ν := isFiniteMeasure_of_le σ hν
  calc
    _ = σ.withDensity (ν.rnDeriv σ) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_le_one_of_le hν] with x hx
      exact min_eq_left hx
    _ = ν := Measure.withDensity_rnDeriv_eq ν σ hν.absolutelyContinuous

/-- The actual normalized source-cut target weight, using selector mass. -/
def sourceWeight (σ : Measure X) (Γ : Measure Ω) (target : Ω → X) (S : Set X) :
    X → ℝ≥0∞ := boundedWeight σ ((σ S)⁻¹ • Γ.map target)

theorem sourceWeight_density (σ : Measure X) [IsFiniteMeasure σ]
    (Γ : Measure Ω) (source target : Ω → X)
    (hsource : Measurable source) (htarget : Measurable target)
    (S : Set X) (hS : σ S ≠ 0)
    (hdom : Γ.map (fun ω => (source ω, target ω)) ≤ (σ.restrict S).prod σ) :
    σ.withDensity (sourceWeight σ Γ target S) = (σ S)⁻¹ • Γ.map target :=
  boundedWeight_density σ _
    (normalized_target_le_selector σ Γ source target hsource htarget S hS hdom)

/-- Multiplying the normalized weight by its original selector source mass
recovers the actual target density, not a substituted occurrence-source mass. -/
theorem sourceWeight_target_density (σ : Measure X) [IsFiniteMeasure σ]
    (Γ : Measure Ω) (source target : Ω → X)
    (hsource : Measurable source) (htarget : Measurable target)
    (S : Set X) (hS : σ S ≠ 0)
    (hdom : Γ.map (fun ω => (source ω, target ω)) ≤ (σ.restrict S).prod σ) :
    σ.withDensity (fun x => σ S * sourceWeight σ Γ target S x) = Γ.map target := by
  change σ.withDensity ((σ S) • sourceWeight σ Γ target S) = _
  rw [withDensity_smul (σ S) (show Measurable (sourceWeight σ Γ target S) from
      measurable_boundedWeight _ _),
    sourceWeight_density σ Γ source target hsource htarget S hS hdom,
    smul_smul, ENNReal.mul_inv_cancel hS (measure_ne_top σ S), one_smul]

section TargetFibers

variable [StandardBorelSpace Ω] [Nonempty Ω]

/-- Disintegration samples a whole old occurrence, not an unmarked source point. -/
def occurrenceFiber (Γ : Measure Ω) [IsFiniteMeasure Γ] (target : Ω → X) : Kernel X Ω :=
  (targetOccurrence Γ target).condKernel

instance occurrenceFiber_isMarkov (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) : IsMarkovKernel (occurrenceFiber Γ target) := by
  unfold occurrenceFiber
  infer_instance

theorem occurrence_fiber_disintegration (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) :
    (Γ.map target).compProd (occurrenceFiber Γ target) = targetOccurrence Γ target := by
  rw [← targetOccurrence_fst]
  exact (targetOccurrence Γ target).disintegrate (targetOccurrence Γ target).condKernel

/-- Every measurable old-incidence property of the graph survives disintegration. -/
theorem occurrence_fiber_graph_ae (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target)
    (G : Set (X × Ω)) (hG : MeasurableSet G)
    (hΓ : ∀ᵐ ω ∂Γ, (target ω, ω) ∈ G) :
    ∀ᵐ x ∂Γ.map target, ∀ᵐ ω ∂occurrenceFiber Γ target x, (x, ω) ∈ G := by
  apply Measure.ae_ae_of_ae_compProd
  rw [occurrence_fiber_disintegration, targetOccurrence]
  exact (ae_map_iff (htarget.prodMk measurable_id).aemeasurable hG).mpr hΓ

/-- The conditional copy lies at exactly the inherited target, almost everywhere. -/
theorem occurrence_fiber_same_target [MeasurableEq X]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target) :
    ∀ᵐ x ∂Γ.map target, ∀ᵐ ω ∂occurrenceFiber Γ target x, target ω = x := by
  apply occurrence_fiber_graph_ae Γ target htarget
    {p | target p.2 = p.1} (measurableSet_eq_fun (htarget.comp measurable_snd) measurable_fst)
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- Zero-density fibers may be arbitrary, but every positive-weight fiber
retains all old graph properties outside one selector-null set. -/
theorem occurrence_fiber_graph_on_positive_weight
    (σ : Measure X) (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target)
    (q : ℝ≥0∞) (w : X → ℝ≥0∞) (hw : Measurable w)
    (hdensity : σ.withDensity w = q⁻¹ • Γ.map target)
    (G : Set (X × Ω)) (hG : MeasurableSet G)
    (hΓ : ∀ᵐ ω ∂Γ, (target ω, ω) ∈ G) :
    ∀ᵐ x ∂σ, w x ≠ 0 → ∀ᵐ ω ∂occurrenceFiber Γ target x, (x, ω) ∈ G := by
  apply (ae_withDensity_iff hw).mp
  rw [hdensity]
  exact (Measure.smul_absolutelyContinuous (c := q⁻¹)).ae_le
    (occurrence_fiber_graph_ae Γ target htarget G hG hΓ)

end TargetFibers

section FiniteIndex

variable [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- Normalized finite-index measure, with a fixed probability completion at zero total. -/
def indexMeasure (w : I → X → ℝ≥0∞) (default : I) (x : X) : Measure I :=
  if (∑ i, w i x) = 0 then Measure.dirac default
  else ∑ i, (w i x / ∑ j, w j x) • Measure.dirac i

/-- The finite probability law is measurably constructed from the target weights. -/
def indexKernel (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (hbound : ∀ i x, w i x ≤ 1) (default : I) : Kernel X I where
  toFun := indexMeasure w default
  measurable' := by
    have _ := hbound
    unfold indexMeasure
    apply Measurable.ite
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
    · exact measurable_const
    · apply Finset.measurable_sum
      intro i _
      exact ((hw i).div (by fun_prop)).smul_measure (Measure.dirac i)

omit [MeasurableSingletonClass I] in
theorem indexKernel_apply (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (hbound : ∀ i x, w i x ≤ 1) (default : I) (x : X) : indexKernel w hw hbound default x = indexMeasure w default x := rfl

instance indexKernel_isMarkov (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (hbound : ∀ i x, w i x ≤ 1) (default : I) : IsMarkovKernel (indexKernel w hw hbound default) where
  isProbabilityMeasure x := by
    constructor
    rw [indexKernel_apply, indexMeasure]
    split_ifs with hzero
    · simp
    · simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ,
        Set.indicator_of_mem (Set.mem_univ _) _, Pi.one_apply, smul_eq_mul, mul_one]
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      change (∑ i, w i x) / (∑ i, w i x) = 1
      exact ENNReal.div_self hzero (ENNReal.sum_ne_top.mpr
        (fun i _ => ne_top_of_le_ne_top ENNReal.one_ne_top (hbound i x)))

/-- Zero weights are assigned zero probability whenever the target total is positive. -/
theorem indexKernel_singleton (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (hbound : ∀ i x, w i x ≤ 1) (default : I) (x : X) (hN : (∑ j, w j x) ≠ 0) (i : I) :
    indexKernel w hw hbound default x {i} = w i x / ∑ j, w j x := by
  classical
  rw [indexKernel_apply, indexMeasure, if_neg hN]
  simp [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply',
    Set.indicator_apply, smul_eq_mul]

/-- A zero-weight index cannot be selected at a target with nonzero total. -/
theorem indexKernel_ae_nonzero (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (hbound : ∀ i x, w i x ≤ 1) (default : I) (x : X)
    (hN : (∑ j, w j x) ≠ 0) :
    ∀ᵐ i ∂indexKernel w hw hbound default x, w i x ≠ 0 := by
  rw [ae_iff_of_countable]
  intro i hi hzero
  apply hi
  rw [indexKernel_singleton w hw hbound default x hN i, hzero, ENNReal.zero_div]

section WholeOccurrences

variable [StandardBorelSpace Ω] [Nonempty Ω]

/-- The index-dependent fiber kernel still samples entire old occurrences. -/
def occurrenceFamily (Γ : I → Measure Ω) [∀ i, IsFiniteMeasure (Γ i)]
    (target : Ω → X) : Kernel (X × I) Ω where
  toFun p := occurrenceFiber (Γ p.2) target p.1
  measurable' := measurable_from_prod_countable_left (fun i =>
    (occurrenceFiber (Γ i) target).measurable)

instance occurrenceFamily_isMarkov (Γ : I → Measure Ω) [∀ i, IsFiniteMeasure (Γ i)]
    (target : Ω → X) : IsMarkovKernel (occurrenceFamily Γ target) where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure (occurrenceFiber (Γ p.2) target p.1)
    infer_instance

/-- First sample an actual normalized source index, then a genuine full old
occurrence from that index's conditional target fiber. -/
def taggedOccurrenceKernel (Γ : I → Measure Ω) [∀ i, IsFiniteMeasure (Γ i)]
    (target : Ω → X) (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (hbound : ∀ i x, w i x ≤ 1) (default : I) : Kernel X (I × Ω) :=
  (indexKernel w hw hbound default).compProd (occurrenceFamily Γ target)

instance taggedOccurrenceKernel_isMarkov
    (Γ : I → Measure Ω) [∀ i, IsFiniteMeasure (Γ i)]
    (target : Ω → X) (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (hbound : ∀ i x, w i x ≤ 1) (default : I) :
    IsMarkovKernel (taggedOccurrenceKernel Γ target w hw hbound default) := by
  unfold taggedOccurrenceKernel
  infer_instance

/-- The actual index marginal is the constructed finite probability law. -/
theorem taggedOccurrenceKernel_index
    (Γ : I → Measure Ω) [∀ i, IsFiniteMeasure (Γ i)]
    (target : Ω → X) (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (hbound : ∀ i x, w i x ≤ 1) (default : I) (x : X) :
    (taggedOccurrenceKernel Γ target w hw hbound default x).map Prod.fst =
      indexKernel w hw hbound default x := by
  rw [← Kernel.fst_apply, taggedOccurrenceKernel, Kernel.fst_compProd]

/-- In particular each selected source has precisely the normalized weight. -/
theorem taggedOccurrenceKernel_index_mass
    (Γ : I → Measure Ω) [∀ i, IsFiniteMeasure (Γ i)]
    (target : Ω → X) (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (hbound : ∀ i x, w i x ≤ 1) (default : I) (x : X)
    (hN : (∑ j, w j x) ≠ 0) (i : I) :
    taggedOccurrenceKernel Γ target w hw hbound default x (Prod.fst ⁻¹' {i}) =
      w i x / ∑ j, w j x := by
  rw [← Measure.map_apply measurable_fst (measurableSet_singleton i),
    taggedOccurrenceKernel_index, indexKernel_singleton w hw hbound default x hN i]

/-- Positive-weight fiber properties lift to the actual tagged sample. -/
theorem taggedOccurrenceKernel_ae
    (Γ : I → Measure Ω) [∀ i, IsFiniteMeasure (Γ i)]
    (target : Ω → X) (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (hbound : ∀ i x, w i x ≤ 1) (default : I) (x : X)
    (hN : (∑ j, w j x) ≠ 0)
    (G : Set (I × Ω)) (hG : MeasurableSet G)
    (hfib : ∀ i, w i x ≠ 0 → ∀ᵐ ω ∂occurrenceFiber (Γ i) target x, (i, ω) ∈ G) :
    ∀ᵐ p ∂taggedOccurrenceKernel Γ target w hw hbound default x, p ∈ G := by
  apply Kernel.ae_compProd_of_ae_ae hG
  filter_upwards [indexKernel_ae_nonzero w hw hbound default x hN] with i hi
  exact hfib i hi

end WholeOccurrences

end FiniteIndex

section Stationary

variable [StandardBorelSpace Ω] [Nonempty Ω]

/-- Independent fresh full occurrences from one fixed target fiber. -/
def tripleOccurrenceKernel (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) : Kernel X (Ω × (Ω × Ω)) :=
  (occurrenceFiber Γ target).prod
    ((occurrenceFiber Γ target).prod (occurrenceFiber Γ target))

instance tripleOccurrenceKernel_isMarkov (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) : IsMarkovKernel (tripleOccurrenceKernel Γ target) := by
  unfold tripleOccurrenceKernel
  infer_instance

/-- The inherited occurrence stays fixed; only three new full occurrences are sampled. -/
def starExtension (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target) : Measure (Ω × (Ω × (Ω × Ω))) :=
  Γ.compProd ((tripleOccurrenceKernel Γ target).comap target htarget)

theorem star_extension_original (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target) :
    (starExtension Γ target htarget).map Prod.fst = Γ :=
  MarkovEndpointPreservation.extension_fst Γ _

/-- A single unconditioned fresh full occurrence has exactly the old law Γ. -/
theorem single_fresh_stationary (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target) :
    (Γ.compProd ((occurrenceFiber Γ target).comap target htarget)).map Prod.snd = Γ := by
  ext s hs
  rw [Measure.map_apply measurable_snd hs,
    Measure.compProd_apply (measurable_snd hs)]
  change (∫⁻ ω, occurrenceFiber Γ target (target ω) s ∂Γ) = Γ s
  rw [← lintegral_map (Kernel.measurable_coe _ hs) htarget]
  have h := congrArg (fun μ : Measure (X × Ω) => μ (univ ×ˢ s))
    (occurrence_fiber_disintegration Γ target)
  rw [Measure.compProd_apply_prod MeasurableSet.univ hs, Measure.restrict_univ,
    targetOccurrence, Measure.map_apply (show Measurable (fun ω => (target ω, ω)) from
      htarget.prodMk measurable_id) (MeasurableSet.univ.prod hs)] at h
  have hpre : (fun ω => (target ω, ω)) ⁻¹' (univ ×ˢ s) = s := by
    ext ω
    simp
  rw [hpre] at h
  exact h

/-- Marginals of each of the three independent fiber draws are the fiber itself. -/
theorem triple_fiber_first (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (x : X) :
    (tripleOccurrenceKernel Γ target x).map Prod.fst = occurrenceFiber Γ target x := by
  rw [← Kernel.fst_apply, tripleOccurrenceKernel, Kernel.fst_prod]

theorem triple_fiber_second (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (x : X) :
    (tripleOccurrenceKernel Γ target x).map (fun p => p.2.1) = occurrenceFiber Γ target x := by
  change (tripleOccurrenceKernel Γ target x).map (Prod.fst ∘ Prod.snd) = _
  rw [← Measure.map_map measurable_fst measurable_snd,
    ← Kernel.snd_apply, tripleOccurrenceKernel, Kernel.snd_prod,
    ← Kernel.fst_apply, Kernel.fst_prod]

theorem triple_fiber_third (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (x : X) :
    (tripleOccurrenceKernel Γ target x).map (fun p => p.2.2) = occurrenceFiber Γ target x := by
  change (tripleOccurrenceKernel Γ target x).map (Prod.snd ∘ Prod.snd) = _
  rw [← Measure.map_map measurable_snd measurable_snd,
    ← Kernel.snd_apply, tripleOccurrenceKernel, Kernel.snd_prod,
    ← Kernel.snd_apply, Kernel.snd_prod]

/-- A fiber marginal identity gives its unconditioned old-occurrence law. -/
theorem star_fresh_stationary (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target)
    (coordinate : Ω × (Ω × Ω) → Ω) (hcoordinate : Measurable coordinate)
    (hfiber : ∀ x, (tripleOccurrenceKernel Γ target x).map coordinate =
      occurrenceFiber Γ target x) :
    (starExtension Γ target htarget).map (fun p => coordinate p.2) = Γ := by
  refine Eq.trans ?_ (single_fresh_stationary Γ target htarget)
  ext s hs
  rw [Measure.map_apply (show Measurable (fun p : Ω × (Ω × (Ω × Ω)) =>
      coordinate p.2) from hcoordinate.comp measurable_snd) hs,
    Measure.map_apply measurable_snd hs, starExtension,
    Measure.compProd_apply ((show Measurable (fun p : Ω × (Ω × (Ω × Ω)) =>
      coordinate p.2) from hcoordinate.comp measurable_snd) hs),
    Measure.compProd_apply (measurable_snd hs)]
  apply lintegral_congr
  intro ω
  change tripleOccurrenceKernel Γ target (target ω) (coordinate ⁻¹' s) =
    occurrenceFiber Γ target (target ω) s
  rw [← Measure.map_apply hcoordinate hs, hfiber]

/-- All three new whole-occurrence marginals are Γ *before* any success cut.
The inherited occurrence is a fourth coordinate, not a fourth random draw. -/
theorem star_all_fresh_stationary (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target) :
    (starExtension Γ target htarget).map (fun p => p.2.1) = Γ ∧
      (starExtension Γ target htarget).map (fun p => p.2.2.1) = Γ ∧
      (starExtension Γ target htarget).map (fun p => p.2.2.2) = Γ := by
  exact ⟨star_fresh_stationary Γ target htarget Prod.fst measurable_fst
      (triple_fiber_first Γ target),
    star_fresh_stationary Γ target htarget (fun p => p.2.1) (by fun_prop)
      (triple_fiber_second Γ target),
    star_fresh_stationary Γ target htarget (fun p => p.2.2) (by fun_prop)
      (triple_fiber_third Γ target)⟩

/-- Every cut keeps each fresh old-occurrence marginal dominated by Γ.
Equality is deliberately not asserted after the four-distinct success cut. -/
theorem star_cut_fresh_le (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target)
    (coordinate : Ω × (Ω × Ω) → Ω) (hcoordinate : Measurable coordinate)
    (hfiber : ∀ x, (tripleOccurrenceKernel Γ target x).map coordinate =
      occurrenceFiber Γ target x) (E : Set (Ω × (Ω × (Ω × Ω)))) :
    ((starExtension Γ target htarget).restrict E).map (fun p => coordinate p.2) ≤ Γ := by
  exact (Measure.map_mono Measure.restrict_le_self (hcoordinate.comp measurable_snd)).trans_eq
    (star_fresh_stationary Γ target htarget coordinate hcoordinate hfiber)

/-- Every original incidence predicate holds for all three new whole
occurrences at the same inherited target. -/
theorem star_extension_genuine
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target)
    (G : Set (X × Ω)) (hG : MeasurableSet G)
    (hΓ : ∀ᵐ ω ∂Γ, (target ω, ω) ∈ G) :
    ∀ᵐ p ∂starExtension Γ target htarget,
      (target p.1, p.2.1) ∈ G ∧
      (target p.1, p.2.2.1) ∈ G ∧ (target p.1, p.2.2.2) ∈ G := by
  apply Measure.ae_compProd_of_ae_ae
    ((hG.preimage (by fun_prop)).inter
      ((hG.preimage (by fun_prop)).inter (hG.preimage (by fun_prop))))
  have hf := ae_of_ae_map htarget.aemeasurable
    (occurrence_fiber_graph_ae Γ target htarget G hG hΓ)
  filter_upwards [hf] with ω hω
  change ∀ᵐ p ∂tripleOccurrenceKernel Γ target (target ω), _
  rw [tripleOccurrenceKernel, Kernel.prod_apply, Kernel.prod_apply]
  apply (Measure.ae_prod_iff_ae_ae
    ((hG.preimage (by fun_prop)).inter
      ((hG.preimage (by fun_prop)).inter (hG.preimage (by fun_prop))))).mpr
  filter_upwards [hω] with a ha
  apply (Measure.ae_prod_iff_ae_ae
    (MeasurableSet.const ((target ω, a) ∈ G) |>.inter
      ((hG.preimage (by fun_prop)).inter (hG.preimage (by fun_prop))))).mpr
  filter_upwards [hω] with b hb
  filter_upwards [hω] with c hc
  exact ⟨ha, hb, hc⟩

/-- All three fresh old occurrences share the original target, exactly a.e. -/
theorem star_extension_common_target [MeasurableEq X]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target) :
    ∀ᵐ p ∂starExtension Γ target htarget,
      target p.2.1 = target p.1 ∧
      target p.2.2.1 = target p.1 ∧ target p.2.2.2 = target p.1 := by
  apply star_extension_genuine Γ target htarget {p | target p.2 = p.1}
    (measurableSet_eq_fun (htarget.comp measurable_snd) measurable_fst)
  exact Filter.Eventually.of_forall (fun _ => rfl)

section StationaryIndex

variable [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- Four distinct source indices, with the inherited occurrence and its index fixed. -/
def starSuccess (index : Ω → I) : Set (Ω × (Ω × (Ω × Ω))) :=
  {p | FourDistinctSources.FourDistinct (index p.1) (index p.2.1)
    (index p.2.2.1) (index p.2.2.2)}

omit [StandardBorelSpace Ω] [Nonempty Ω] in
theorem measurableSet_starSuccess (index : Ω → I) (hindex : Measurable index) :
    MeasurableSet (starSuccess index) := by
  have hfinite : MeasurableSet {a : I × (I × (I × I)) |
      FourDistinctSources.FourDistinct a.1 a.2.1 a.2.2.1 a.2.2.2} :=
    (Set.toFinite _).measurableSet
  exact hfinite.preimage (show Measurable (fun p : Ω × (Ω × (Ω × Ω)) =>
    (index p.1, (index p.2.1, (index p.2.2.1, index p.2.2.2)))) by fun_prop)

/-- The probability of the genuine triple event is the finite source-index
probability derived from actual target densities, not a supplied certificate. -/
theorem stationary_fiber_distinct_probability
    (σ : Measure X) [IsFiniteMeasure σ] (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target)
    (index : Ω → I) (hindex : Measurable index)
    (e : I → X → ℝ≥0∞) (he : ∀ i, Measurable (e i))
    (hefin : ∀ i x, e i x ≠ ∞)
    (hdens : ∀ i, (Γ.restrict (index ⁻¹' {i})).map target = σ.withDensity (e i)) :
    ∀ᵐ x ∂Γ.map target, ∀ i : I,
      tripleOccurrenceKernel Γ target x {p | FourDistinctSources.FourDistinct
        i (index p.1) (index p.2.1) (index p.2.2)} =
      ENNReal.ofReal (FourDistinctSources.fourDistinctProbability
        (fun j => (e j x / ∑ k, e k x).toReal) i) := by
  have hr := ae_all_iff.mpr (fun i =>
    ConditionalIndexDensity.conditional_index_ratio_ae σ Γ target htarget
      index hindex e he hefin hdens i)
  filter_upwards [hr] with x hx i
  change ((occurrenceFiber Γ target).prod
    ((occurrenceFiber Γ target).prod (occurrenceFiber Γ target))) x _ = _
  rw [Kernel.prod_apply, Kernel.prod_apply,
    FourDistinctSources.measure_fourDistinct_eq_ofReal _ index hindex i]
  congr 1
  unfold FourDistinctSources.fourDistinctProbability
  congr 1
  funext j
  exact congrArg ENNReal.toReal (hx j)

omit [StandardBorelSpace Ω] [Nonempty Ω] in
/-- Restricting the inherited base is exactly a restriction of the full extension. -/
theorem restrict_source_compProd (μ : Measure Ω) [SFinite μ]
    {L : Type*} [MeasurableSpace L] (κ : Kernel Ω L) [IsSFiniteKernel κ]
    (H : Set Ω) (hH : MeasurableSet H) :
    (μ.restrict H).compProd κ = (μ.compProd κ).restrict (Prod.fst ⁻¹' H) := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.restrict_apply hs,
    Measure.compProd_apply (hs.inter (measurable_fst hH)), ← lintegral_indicator hH]
  apply lintegral_congr
  intro ω
  by_cases hω : ω ∈ H <;> simp [Set.preimage, hω]

/-- Keep the original high-branch occurrence, sample three stationary fiber
copies, and then retain exactly the four-distinct tuples. -/
def retainedStar (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target) (index : Ω → I) (H : Set Ω) :
    Measure (Ω × (Ω × (Ω × Ω))) :=
  ((Γ.restrict H).compProd ((tripleOccurrenceKernel Γ target).comap target htarget)).restrict
    (starSuccess index)

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
/-- After either cut, all marginal domination comes from an actual submeasure
of the unconditioned stationary extension. -/
theorem retainedStar_le_full (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target) (index : Ω → I)
    (H : Set Ω) (hH : MeasurableSet H) :
    retainedStar Γ target htarget index H ≤ starExtension Γ target htarget := by
  unfold retainedStar
  rw [restrict_source_compProd _ _ H hH]
  exact Measure.restrict_le_self.trans Measure.restrict_le_self

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
/-- The retained inherited marginal is always dominated by its high-branch base. -/
theorem retainedStar_original_le (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target) (index : Ω → I) (H : Set Ω) :
    (retainedStar Γ target htarget index H).map Prod.fst ≤ Γ.restrict H := by
  have h := MarkovEndpointPreservation.restriction_endpoint_le (Γ.restrict H)
    ((tripleOccurrenceKernel Γ target).comap target htarget) (starSuccess index)
    id measurable_id
  simpa only [Measure.map_id, id_eq, retainedStar] using h

/-- A pointwise numerical finite-index estimate lifts to a measure-valued
half-retention statement for the fixed inherited occurrence. The fiber
probability is derived from actual disintegration above. -/
theorem retainedStar_original_ge_half
    (σ : Measure X) [IsFiniteMeasure σ] (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target)
    (index : Ω → I) (hindex : Measurable index)
    (e : I → X → ℝ≥0∞) (he : ∀ i, Measurable (e i))
    (hefin : ∀ i x, e i x ≠ ∞)
    (hdens : ∀ i, (Γ.restrict (index ⁻¹' {i})).map target = σ.withDensity (e i))
    (H : Set Ω) (hH : MeasurableSet H)
    (hhalf : ∀ ω ∈ H, (1 : ℝ) / 2 ≤ FourDistinctSources.fourDistinctProbability
      (fun j => (e j (target ω) / ∑ k, e k (target ω)).toReal) (index ω)) :
    (1 / 2 : ℝ≥0∞) • Γ.restrict H ≤
      (retainedStar Γ target htarget index H).map Prod.fst := by
  have hp := ae_of_ae_map htarget.aemeasurable
    (stationary_fiber_distinct_probability σ Γ target htarget index hindex e he hefin hdens)
  have hf : ∀ᵐ ω ∂Γ.restrict H,
      (1 / 2 : ℝ≥0∞) ≤
      ((tripleOccurrenceKernel Γ target).comap target htarget) ω
        (Prod.mk ω ⁻¹' starSuccess index) := by
    filter_upwards [ae_restrict_of_ae hp, ae_restrict_mem hH] with ω hω hωH
    change (1 / 2 : ℝ≥0∞) ≤ tripleOccurrenceKernel Γ target (target ω)
      {p | FourDistinctSources.FourDistinct (index ω) (index p.1) (index p.2.1) (index p.2.2)}
    rw [hω (index ω)]
    simpa using ENNReal.ofReal_le_ofReal (hhalf ω hωH)
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul]
  change _ ≤ (((Γ.restrict H).compProd _).restrict (starSuccess index)).map Prod.fst s
  rw [IndependentFlagSeparation.restricted_original_apply _ _ _
    (measurableSet_starSuccess index hindex) s hs]
  calc
    _ = ∫⁻ _ in s, (1 / 2 : ℝ≥0∞) ∂Γ.restrict H := by simp
    _ ≤ _ := lintegral_mono_ae (ae_restrict_of_ae hf)

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
/-- Post-cut fresh marginals are submeasures of the old aggregate Γ; no
post-cut stationarity is claimed. -/
theorem retainedStar_fresh_le (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target) (index : Ω → I)
    (H : Set Ω) (hH : MeasurableSet H)
    (coordinate : Ω × (Ω × Ω) → Ω) (hcoordinate : Measurable coordinate)
    (hfiber : ∀ x, (tripleOccurrenceKernel Γ target x).map coordinate =
      occurrenceFiber Γ target x) :
    (retainedStar Γ target htarget index H).map (fun p => coordinate p.2) ≤ Γ :=
  (Measure.map_mono (retainedStar_le_full Γ target htarget index H hH)
    (hcoordinate.comp measurable_snd)).trans_eq
      (star_fresh_stationary Γ target htarget coordinate hcoordinate hfiber)

omit [StandardBorelSpace Ω] [Nonempty Ω] in
/-- All original occurrences belong to their actual selector source piece. -/
theorem source_index_genuine
    (σ : Measure X) [SFinite σ] (Γ : Measure Ω)
    (source target : Ω → X) (hsource : Measurable source) (htarget : Measurable target)
    (index : Ω → I) (hindex : Measurable index)
    (S : I → Set X) (hS : ∀ i, MeasurableSet (S i))
    (hdom : ∀ i, (Γ.restrict (index ⁻¹' {i})).map (fun ω => (source ω, target ω)) ≤
      (σ.restrict (S i)).prod σ) :
    ∀ᵐ ω ∂Γ, source ω ∈ S (index ω) := by
  rw [ConditionalIndexDensity.index_partition Γ index hindex, Measure.ae_sum_iff]
  intro i
  filter_upwards [source_piece_genuine σ (Γ.restrict (index ⁻¹' {i}))
      source target hsource htarget (S i) (hS i) (hdom i),
    ae_restrict_mem (hindex (measurableSet_singleton i))] with ω hω hi
  have hi' : index ω = i := hi
  simpa only [hi'] using hω

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
/-- The retained tuples consist of three genuine old copies at the unchanged
target, in addition to the inherited old occurrence. -/
theorem retainedStar_genuine
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (target : Ω → X) (htarget : Measurable target) (index : Ω → I)
    (H : Set Ω) (hH : MeasurableSet H)
    (G : Set (X × Ω)) (hG : MeasurableSet G)
    (hΓ : ∀ᵐ ω ∂Γ, (target ω, ω) ∈ G) :
    ∀ᵐ p ∂retainedStar Γ target htarget index H,
      (target p.1, p.2.1) ∈ G ∧
      (target p.1, p.2.2.1) ∈ G ∧ (target p.1, p.2.2.2) ∈ G :=
  (retainedStar_le_full Γ target htarget index H hH).absolutelyContinuous.ae_le
    (star_extension_genuine Γ target htarget G hG hΓ)

/-- With disjoint actual selector source cuts, four distinct source indices
really give four distinct physical sources of the full old occurrences. -/
theorem retainedStar_four_distinct_physical_sources
    (σ : Measure X) [SFinite σ] (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (source target : Ω → X) (hsource : Measurable source) (htarget : Measurable target)
    (index : Ω → I) (hindex : Measurable index)
    (S : I → Set X) (hS : ∀ i, MeasurableSet (S i))
    (hdisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hdom : ∀ i, (Γ.restrict (index ⁻¹' {i})).map (fun ω => (source ω, target ω)) ≤
      (σ.restrict (S i)).prod σ)
    (H : Set Ω) (hH : MeasurableSet H) :
    ∀ᵐ p ∂retainedStar Γ target htarget index H,
      FourDistinctSources.FourDistinct (source p.1) (source p.2.1)
        (source p.2.2.1) (source p.2.2.2) := by
  let A := {ω | source ω ∈ S (index ω)}
  have hA : MeasurableSet A := by
    have hset : A = ⋃ i, (index ⁻¹' {i}) ∩ (source ⁻¹' S i) := by
      ext ω
      simp [A]
    rw [hset]
    exact MeasurableSet.iUnion (fun i =>
      (hindex (measurableSet_singleton i)).inter (hsource (hS i)))
  have hΓ : ∀ᵐ ω ∂Γ, ω ∈ A :=
    source_index_genuine σ Γ source target hsource htarget index hindex S hS hdom
  have hOld : ∀ᵐ p ∂starExtension Γ target htarget, p.1 ∈ A :=
    Measure.ae_compProd_of_ae_fst _ hA hΓ
  have hOld' := (retainedStar_le_full Γ target htarget index H hH).absolutelyContinuous.ae_le hOld
  have hNew := retainedStar_genuine Γ target htarget index H hH
    (Prod.snd ⁻¹' A) (measurable_snd hA) hΓ
  have hSuccess : ∀ᵐ p ∂retainedStar Γ target htarget index H, p ∈ starSuccess index :=
    ae_restrict_mem (measurableSet_starSuccess index hindex)
  have hneq (a b : Ω) (hab : index a ≠ index b) (ha : a ∈ A) (hb : b ∈ A) :
      source a ≠ source b := by
    intro heq
    exact Set.disjoint_left.mp (hdisjoint hab) (heq ▸ ha) hb
  filter_upwards [hOld', hNew, hSuccess] with p h0 hf hs
  obtain ⟨h1, h2, h3⟩ := hf
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := hs
  exact ⟨hneq _ _ h01 h0 h1, hneq _ _ h02 h0 h2, hneq _ _ h03 h0 h3,
    hneq _ _ h12 h1 h2, hneq _ _ h13 h1 h3, hneq _ _ h23 h2 h3⟩

/-- End-to-end stationary star extraction from actual selector source-cut
product domination. Source weights are constructed from the target marginals;
`N≥24` and comparable original selector source masses yield half retention of
the inherited high branch as a measure, with all old marks still present. -/
theorem selector_cut_retainedStar_original_ge_half
    (σ : Measure X) [IsFiniteMeasure σ] (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (source target : Ω → X) (hsource : Measurable source) (htarget : Measurable target)
    (index : Ω → I) (hindex : Measurable index) (S : I → Set X)
    (hdom : ∀ i, (Γ.restrict (index ⁻¹' {i})).map (fun ω => (source ω, target ω)) ≤
      (σ.restrict (S i)).prod σ)
    (q K : ℝ) (hq : 0 < q) (hK : 24 ≤ K)
    (hlower : ∀ i, q ≤ (σ (S i)).toReal) (hupper : ∀ i, (σ (S i)).toReal ≤ 2 * q)
    (H : Set Ω) (hH : MeasurableSet H)
    (hN : ∀ ω ∈ H, ENNReal.ofReal K ≤ ∑ i,
      sourceWeight σ (Γ.restrict (index ⁻¹' {i})) target (S i) (target ω)) :
    (1 / 2 : ℝ≥0∞) • Γ.restrict H ≤
      (retainedStar Γ target htarget index H).map Prod.fst := by
  let w : I → X → ℝ≥0∞ := fun i =>
    sourceWeight σ (Γ.restrict (index ⁻¹' {i})) target (S i)
  let e : I → X → ℝ≥0∞ := fun i x => σ (S i) * w i x
  have hS (i : I) : σ (S i) ≠ 0 := by
    intro hi
    have h := hlower i
    rw [hi, ENNReal.toReal_zero] at h
    exact (not_le_of_gt hq) h
  have hw (i : I) : Measurable (w i) := measurable_boundedWeight _ _
  have hw1 (i : I) (x : X) : w i x ≤ 1 := boundedWeight_le_one _ _ _
  have he (i : I) : Measurable (e i) := measurable_const.mul (hw i)
  have hef (i : I) (x : X) : e i x ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top σ _)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (hw1 i x))
  have hd (i : I) : (Γ.restrict (index ⁻¹' {i})).map target = σ.withDensity (e i) :=
    (sourceWeight_target_density σ _ source target hsource htarget (S i) (hS i) (hdom i)).symm
  apply retainedStar_original_ge_half σ Γ target htarget index hindex e he hef hd H hH
  intro ω hω
  have hp := NormalizedTargetGrowth.stationary_ennreal_four_distinct_probability_ge_half
    (fun i => (σ (S i)).toReal) (fun i => w i (target ω)) q K hq hK
    hlower hupper (fun i => hw1 i (target ω)) (hN ω hω) (index ω)
  have hcoeff (i : I) : ENNReal.ofReal (σ (S i)).toReal = σ (S i) :=
    ENNReal.ofReal_toReal (measure_ne_top σ _)
  simpa only [hcoeff] using hp

/-- A high branch containing half the incoming mass leaves at least a quarter
in actual four-distinct whole-occurrence stars. This is a restriction, not a
renormalized success law. -/
theorem selector_cut_retainedStar_mass_ge_quarter
    (σ : Measure X) [IsFiniteMeasure σ] (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (source target : Ω → X) (hsource : Measurable source) (htarget : Measurable target)
    (index : Ω → I) (hindex : Measurable index) (S : I → Set X)
    (hdom : ∀ i, (Γ.restrict (index ⁻¹' {i})).map (fun ω => (source ω, target ω)) ≤
      (σ.restrict (S i)).prod σ)
    (q K : ℝ) (hq : 0 < q) (hK : 24 ≤ K)
    (hlower : ∀ i, q ≤ (σ (S i)).toReal) (hupper : ∀ i, (σ (S i)).toReal ≤ 2 * q)
    (H : Set Ω) (hH : MeasurableSet H)
    (hN : ∀ ω ∈ H, ENNReal.ofReal K ≤ ∑ i,
      sourceWeight σ (Γ.restrict (index ⁻¹' {i})) target (S i) (target ω))
    (hhalf : (1 / 2 : ℝ≥0∞) * Γ univ ≤ Γ H) :
    (1 / 4 : ℝ≥0∞) * Γ univ ≤ retainedStar Γ target htarget index H univ := by
  have h := selector_cut_retainedStar_original_ge_half σ Γ source target hsource htarget
    index hindex S hdom q K hq hK hlower hupper H hH hN univ
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ] at h
  calc
    (1 / 4 : ℝ≥0∞) * Γ univ =
        (1 / 2 : ℝ≥0∞) * ((1 / 2 : ℝ≥0∞) * Γ univ) := by
      rw [← mul_assoc]
      norm_num [← ENNReal.mul_inv]
    _ ≤ (1 / 2 : ℝ≥0∞) * Γ H := mul_le_mul_right hhalf _
    _ ≤ _ := h

end StationaryIndex

end Stationary

end StickyKakeya4.CommonTargetStarKernel
