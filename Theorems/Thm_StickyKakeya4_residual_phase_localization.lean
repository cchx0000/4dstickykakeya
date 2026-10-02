import Theorems.Thm_StickyKakeya4_packing_reference_overlap
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# Constructive localization of a finite near-phase graph

The source cells are the first-hit disjointification of a finite measurable
cover. Edges are assigned by their first endpoint, so their masses add exactly.
The density selection uses squared block masses, never the number of blocks or
a lower bound on the mass of a first-hit cell.
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.ResidualPhaseLocalization

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

/-- The first member of an ordered finite cover containing the source. -/
def firstHit (A : Fin n → Set X) (i : Fin n) : Set X := disjointed A i

/-- Assign every edge according to the first-hit cell of its first endpoint. -/
def assignedGraph (ν : Measure (X × X)) (A : Fin n → Set X) (i : Fin n) :
    Measure (X × X) := ν.restrict ((Prod.fst : X × X → X) ⁻¹' firstHit A i)

theorem measurableSet_firstHit (A : Fin n → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (i : Fin n) : MeasurableSet (firstHit A i) := by
  rw [firstHit, disjointed_eq_inter_compl]
  exact (hA i).inter (MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => (hA j).compl)

omit [MeasurableSpace X] in
theorem firstHit_subset (A : Fin n → Set X) (i : Fin n) : firstHit A i ⊆ A i :=
  disjointed_subset A i

omit [MeasurableSpace X] in
theorem firstHit_pairwiseDisjoint (A : Fin n → Set X) :
    Pairwise (fun i j => Disjoint (firstHit A i) (firstHit A j)) := disjoint_disjointed A

omit [MeasurableSpace X] in
theorem iUnion_firstHit (A : Fin n → Set X) : (⋃ i, firstHit A i) = ⋃ i, A i :=
  iUnion_disjointed

/-- The constructed cells form a measurable a.e. partition of the source. -/
theorem firstHit_ae_partition (σ : Measure X) (A : Fin n → Set X)
    (hcover : ∀ᵐ x ∂σ, x ∈ ⋃ i, A i) :
    ∀ᵐ x ∂σ, ∃! i, x ∈ firstHit A i := by
  filter_upwards [hcover] with x hx
  rw [← iUnion_firstHit A] at hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  exact Set.disjoint_left.mp (firstHit_pairwiseDisjoint A hji) hj hi

/-- The first-hit construction gives the exact edge-mass split. The only
covering assumption is a.e. coverage of the original source measure. -/
theorem sum_assignedGraph_mass (σ : Measure X) (ν : Measure (X × X))
    (hdom : ν ≤ σ.prod σ) (A : Fin n → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hcover : ∀ᵐ x ∂σ, x ∈ ⋃ i, A i) :
    (∑ i, assignedGraph ν A i univ) = ν univ := by
  have hcoverProd : ∀ᵐ p ∂σ.prod σ, p.1 ∈ ⋃ i, A i :=
    Measure.quasiMeasurePreserving_fst.ae hcover
  have hcoverν : ∀ᵐ p ∂ν, p ∈ ⋃ i, (Prod.fst : X × X → X) ⁻¹' firstHit A i := by
    filter_upwards [ae_mono hdom hcoverProd] with p hp
    simpa only [← preimage_iUnion, iUnion_firstHit, mem_preimage] using hp
  have hdisj : Pairwise (fun i j => Disjoint ((Prod.fst : X × X → X) ⁻¹' firstHit A i) ((Prod.fst : X × X → X) ⁻¹' firstHit A j)) := by
    intro i j hij
    exact (firstHit_pairwiseDisjoint A hij).preimage _
  have hm : ∀ i, MeasurableSet ((Prod.fst : X × X → X) ⁻¹' firstHit A i) :=
    fun i => (measurableSet_firstHit A hA i).preimage measurable_fst
  have heq := Measure.restrict_iUnion_apply (μ := ν) hdisj hm MeasurableSet.univ
  rw [Measure.restrict_eq_self_of_ae_mem hcoverν, tsum_fintype] at heq
  exact heq.symm

/-- Any verified endpoint containment puts the assigned graph below the
product measure on its enlarged block. First-hit partitioning is constructed. -/
theorem assignedGraph_le_block_product (σ : Measure X) (ν : Measure (X × X))
    (hdom : ν ≤ σ.prod σ) (A D : Fin n → Set X)
    (hendpoint : ∀ i, ∀ᵐ p ∂ν, p.1 ∈ A i → p ∈ D i ×ˢ D i) (i : Fin n) :
    assignedGraph ν A i ≤ (σ.prod σ).restrict (D i ×ˢ D i) := by
  apply Measure.restrict_mono' _ hdom
  filter_upwards [hendpoint i] with p hp
  exact fun hpi => hp (firstHit_subset A i hpi)

/-- The assigned mass is bounded by the square of the original block mass,
including zero-mass blocks. -/
theorem assignedGraph_mass_le_sq (σ : Measure X) [IsFiniteMeasure σ]
    (ν : Measure (X × X)) (hdom : ν ≤ σ.prod σ) (A D : Fin n → Set X)
    (hendpoint : ∀ i, ∀ᵐ p ∂ν, p.1 ∈ A i → p ∈ D i ×ˢ D i) (i : Fin n) :
    (assignedGraph ν A i univ).toReal ≤ (σ (D i)).toReal ^ 2 := by
  have h := assignedGraph_le_block_product σ ν hdom A D hendpoint i univ
  rw [Measure.restrict_apply_univ, Measure.prod_prod] at h
  have ht : σ (D i) * σ (D i) ≠ ∞ :=
    ENNReal.mul_ne_top (measure_ne_top σ _) (measure_ne_top σ _)
  simpa only [ENNReal.toReal_mul, pow_two] using ENNReal.toReal_mono ht h

/-- A source-null block carries no assigned graph at all, so it is never
silently normalized as a positive cell. -/
theorem assignedGraph_eq_zero_of_block_null (σ : Measure X) [IsFiniteMeasure σ]
    (ν : Measure (X × X)) (hdom : ν ≤ σ.prod σ) (A D : Fin n → Set X)
    (hendpoint : ∀ i, ∀ᵐ p ∂ν, p.1 ∈ A i → p ∈ D i ×ˢ D i)
    (i : Fin n) (hnull : σ (D i) = 0) : assignedGraph ν A i = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  have h := assignedGraph_le_block_product σ ν hdom A D hendpoint i univ
  simpa only [Measure.restrict_apply_univ, Measure.prod_prod, hnull, zero_mul,
    nonpos_iff_eq_zero] using h

/-- Exact real-valued splitting, without discarding zero cells. -/
theorem sum_assignedGraph_mass_toReal (σ : Measure X) [IsFiniteMeasure σ]
    (ν : Measure (X × X)) (hdom : ν ≤ σ.prod σ) (A : Fin n → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hcover : ∀ᵐ x ∂σ, x ∈ ⋃ i, A i) :
    (∑ i, (assignedGraph ν A i univ).toReal) = (ν univ).toReal := by
  let : IsFiniteMeasure ν := isFiniteMeasure_of_le (σ.prod σ) hdom
  rw [← sum_assignedGraph_mass σ ν hdom A hA hcover,
    ENNReal.toReal_sum (fun i _ => by
      change (ν.restrict _) univ ≠ ∞
      exact measure_ne_top _ _)]

/-- A weighted pigeonhole principle with zero-weight cells treated exactly.
The denominator is the sum of weights, with no cardinality loss. -/
theorem exists_weighted_density_ge_average {I : Type*} [Fintype I]
    (e w : I → ℝ) (_he : ∀ i, 0 ≤ e i) (hw : ∀ i, 0 ≤ w i)
    (hew : ∀ i, e i ≤ w i) (hE : 0 < ∑ i, e i) :
    ∃ i, 0 < w i ∧ (∑ j, e j) / (∑ j, w j) ≤ e i / w i := by
  classical
  have hS : 0 < ∑ i, w i := hE.trans_le (Finset.sum_le_sum fun i _ => hew i)
  obtain ⟨i₀, _, hi₀⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hw i)).mp hS
  by_contra hn
  have hlt : ∀ i, 0 < w i → e i < ((∑ j, e j) / (∑ j, w j)) * w i := by
    intro i hi
    have hnot : ¬ (∑ j, e j) / (∑ j, w j) ≤ e i / w i :=
      fun h => hn ⟨i, hi, h⟩
    exact (div_lt_iff₀ hi).mp (lt_of_not_ge hnot)
  have hle : ∀ i, e i ≤ ((∑ j, e j) / (∑ j, w j)) * w i := by
    intro i
    by_cases hi : 0 < w i
    · exact (hlt i hi).le
    · have hz : w i = 0 := le_antisymm (le_of_not_gt hi) (hw i)
      rw [hz, mul_zero]
      exact (hew i).trans_eq hz
  have hs := Finset.sum_lt_sum (fun i _ => hle i) ⟨i₀, Finset.mem_univ _, hlt i₀ hi₀⟩
  rw [← Finset.mul_sum, div_mul_cancel₀ _ hS.ne'] at hs
  exact (lt_irrefl _ hs)

/-- A finite measurable bounded-overlap block family has its total original
source mass controlled independently of the number of blocks. -/
theorem sum_block_mass_le (σ : Measure X) [IsFiniteMeasure σ]
    (D : Fin n → Set X) (hD : ∀ i, MeasurableSet (D i)) (K : ℕ)
    (hoverlap : ∀ x, (Finset.univ.filter fun i => x ∈ D i).card ≤ K) :
    (∑ i, (σ (D i)).toReal) ≤ (K : ℝ) * (σ univ).toReal := by
  classical
  have h := sum_measure_le_mul_of_multiplicity_bound σ Finset.univ D univ K
    (fun i _ => hD i) (fun _ _ => subset_univ _) hoverlap
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simpa only [ENNReal.toReal_sum (fun i _ => measure_ne_top σ _),
    ENNReal.toReal_mul, ENNReal.toReal_natCast] using hreal

/-- The squared block-mass budget uses only an upper mass bound and overlap;
there is no lower block-mass or balanced-cell hypothesis. -/
theorem sum_sq_block_mass_le (σ : Measure X) [IsFiniteMeasure σ]
    (D : Fin n → Set X) (hD : ∀ i, MeasurableSet (D i)) (K : ℕ)
    (hoverlap : ∀ x, (Finset.univ.filter fun i => x ∈ D i).card ≤ K)
    (B : ℝ) (hB : 0 ≤ B) (hupper : ∀ i, (σ (D i)).toReal ≤ B) :
    (∑ i, (σ (D i)).toReal ^ 2) ≤ B * K * (σ univ).toReal := by
  calc
    (∑ i, (σ (D i)).toReal ^ 2) ≤ ∑ i, B * (σ (D i)).toReal := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [ENNReal.toReal_nonneg (a := σ (D i)), hupper i]
    _ = B * (∑ i, (σ (D i)).toReal) := (Finset.mul_sum _ _ _).symm
    _ ≤ B * ((K : ℝ) * (σ univ).toReal) :=
      mul_le_mul_of_nonneg_left (sum_block_mass_le σ D hD K hoverlap) hB
    _ = B * K * (σ univ).toReal := by ring

/-- A positive graph admits an actual assigned block whose normalized density
is at least the global mass divided by the sum of squared block masses. -/
theorem exists_assignedGraph_density_ge_average
    (σ : Measure X) [IsFiniteMeasure σ] (ν : Measure (X × X))
    (hdom : ν ≤ σ.prod σ) (A D : Fin n → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hcover : ∀ᵐ x ∂σ, x ∈ ⋃ i, A i)
    (hendpoint : ∀ i, ∀ᵐ p ∂ν, p.1 ∈ A i → p ∈ D i ×ˢ D i)
    (hpositive : 0 < (ν univ).toReal) :
    0 < ∑ i, (σ (D i)).toReal ^ 2 ∧
    ∃ i, 0 < (σ (D i)).toReal ∧
      (ν univ).toReal / (∑ j, (σ (D j)).toReal ^ 2) ≤
        (assignedGraph ν A i univ).toReal / (σ (D i)).toReal ^ 2 := by
  have hsum := sum_assignedGraph_mass_toReal σ ν hdom A hA hcover
  have hle := assignedGraph_mass_le_sq σ ν hdom A D hendpoint
  have hE : 0 < ∑ i, (assignedGraph ν A i univ).toReal := by rwa [hsum]
  refine ⟨hE.trans_le (Finset.sum_le_sum fun i _ => hle i), ?_⟩
  obtain ⟨i, hi, hdensity⟩ := exists_weighted_density_ge_average
    (fun i => (assignedGraph ν A i univ).toReal) (fun i => (σ (D i)).toReal ^ 2)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => sq_nonneg _) hle hE
  refine ⟨i, ?_, ?_⟩
  · have hn : 0 ≤ (σ (D i)).toReal := ENNReal.toReal_nonneg
    nlinarith
  · simpa only [hsum] using hdensity

/-- Upper block mass and overlap turn the weighted average into the desired
source-mass times block-scale denominator, without a number-of-cells loss. -/
theorem exists_assignedGraph_density_ge_mass_budget
    (σ : Measure X) [IsFiniteMeasure σ] (ν : Measure (X × X))
    (hdom : ν ≤ σ.prod σ) (A D : Fin n → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hD : ∀ i, MeasurableSet (D i))
    (hcover : ∀ᵐ x ∂σ, x ∈ ⋃ i, A i)
    (hendpoint : ∀ i, ∀ᵐ p ∂ν, p.1 ∈ A i → p ∈ D i ×ˢ D i)
    (K : ℕ) (hoverlap : ∀ x, (Finset.univ.filter fun i => x ∈ D i).card ≤ K)
    (B : ℝ) (hB : 0 ≤ B) (hupper : ∀ i, (σ (D i)).toReal ≤ B)
    (hpositive : 0 < (ν univ).toReal) :
    ∃ i, 0 < (σ (D i)).toReal ∧
      (ν univ).toReal / (B * K * (σ univ).toReal) ≤
        (assignedGraph ν A i univ).toReal / (σ (D i)).toReal ^ 2 := by
  obtain ⟨hS, i, hi, hdensity⟩ := exists_assignedGraph_density_ge_average
    σ ν hdom A D hA hcover hendpoint hpositive
  refine ⟨i, hi, le_trans ?_ hdensity⟩
  exact div_le_div_of_nonneg_left hpositive.le hS
    (sum_sq_block_mass_le σ D hD K hoverlap B hB hupper)


/-- A fixed enlargement of the containing ball preserves the uniform bound
for families separated by one half of the unexpanded scale. -/
theorem exists_uniform_expanded_indexed_ball_card_bound
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (R : ℝ) (_hR : 0 < R) :
    ∃ K : ℕ, ∀ (tau : ℝ), 0 < tau → ∀ {A : Type*} (p : E) (points : Finset A) (centers : A → E),
      (∀ x ∈ points, dist (centers x) p ≤ R * tau) →
      (∀ x ∈ points, ∀ y ∈ points, x ≠ y → tau / 2 ≤ dist (centers x) (centers y)) →
      points.card ≤ K := by
  classical
  obtain ⟨cover, _hcoverBall, hcoverFinite, hcover⟩ :=
    (isCompact_closedBall (0 : E) R).finite_cover_balls (show 0 < (1 / 4 : ℝ) by norm_num)
  refine ⟨hcoverFinite.toFinset.card, ?_⟩
  intro tau htau A p points centers hnear hsep
  let image : A → E := fun x => tau⁻¹ • (centers x - p)
  have hcover' : coversAtRadius (Metric.closedBall (0 : E) R)
      (1 / 4) hcoverFinite.toFinset := by
    simpa only [coversAtRadius, Set.Finite.coe_toFinset] using hcover
  apply image_separated_card_le_finite_cover_card points image
    (Metric.closedBall (0 : E) R) (1 / 4) hcoverFinite.toFinset hcover'
  · intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖image x‖ = tau⁻¹ * dist (centers x) p := by
        simp only [image, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr htau.le),
          dist_eq_norm]
      _ ≤ tau⁻¹ * (R * tau) :=
        mul_le_mul_of_nonneg_left (hnear x hx) (inv_nonneg.mpr htau.le)
      _ = R := by field_simp
  · intro x hx y hy hxy
    have hnorm : dist (image x) (image y) = tau⁻¹ * dist (centers x) (centers y) := by
      simp only [image, dist_smul₀, Real.norm_of_nonneg (inv_nonneg.mpr htau.le),
        dist_sub_right]
    rw [hnorm]
    have hscaled := mul_le_mul_of_nonneg_left (hsep x hx y hy hxy)
      (inv_nonneg.mpr htau.le)
    have hhalf : tau⁻¹ * (tau / 2) = (1 / 2 : ℝ) := by field_simp
    rw [hhalf] at hscaled
    norm_num at hscaled ⊢
    exact hscaled

/-- The uniform fixed-expansion overlap bound for a finite indexed family. -/
theorem exists_uniform_expanded_indexed_ball_overlap_bound
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (R : ℝ) (hR : 0 < R) :
    ∃ K : ℕ, ∀ (tau : ℝ), 0 < tau →
      ∀ {A : Type*} (indices : Finset A) (centers : A → E),
      (∀ i ∈ indices, ∀ j ∈ indices, i ≠ j → tau / 2 ≤ dist (centers i) (centers j)) →
      ∀ p : E,
        (indices.filter fun i => p ∈ Metric.ball (centers i) (R * tau)).card ≤ K := by
  classical
  obtain ⟨K, hK⟩ := exists_uniform_expanded_indexed_ball_card_bound E R hR
  refine ⟨K, ?_⟩
  intro tau htau A indices centers hsep p
  apply hK tau htau p _ centers
  · intro i hi
    have hiBall := (Finset.mem_filter.mp hi).2
    simpa only [Metric.mem_ball, dist_comm] using hiBall.le
  · intro i hi j hj hij
    exact hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij

/-- A version directly suited to finite first-hit partitions. -/
theorem exists_uniform_expanded_fin_ball_overlap_bound
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (R : ℝ) (hR : 0 < R) :
    ∃ K : ℕ, ∀ (tau : ℝ), 0 < tau → ∀ (n : ℕ) (centers : Fin n → E),
      (∀ i j, i ≠ j → tau / 2 ≤ dist (centers i) (centers j)) →
      ∀ p : E,
        (Finset.univ.filter fun i => p ∈ Metric.ball (centers i) (R * tau)).card ≤ K := by
  classical
  obtain ⟨K, hK⟩ := exists_uniform_expanded_indexed_ball_overlap_bound E R hR
  refine ⟨K, ?_⟩
  intro tau htau n centers hsep p
  exact hK tau htau Finset.univ centers (fun i _ j _ hij => hsep i j hij) p

/-- Small phase balls pulled back to the actual source. -/
def phaseCover {E : Type*} [PseudoMetricSpace E]
    (f : X → E) (centers : Fin n → E) (tau : ℝ) (i : Fin n) : Set X :=
  f ⁻¹' Metric.ball (centers i) tau

/-- Expanded phase blocks keep both endpoints of every assigned near edge. -/
def phaseBlock {E : Type*} [PseudoMetricSpace E]
    (f : X → E) (centers : Fin n → E) (L tau : ℝ) (i : Fin n) : Set X :=
  f ⁻¹' Metric.ball (centers i) ((L + 2) * tau)

/-- The actual bounded measurable endpoint graph. -/
def graphMeasure (σ : Measure X) (h : X × X → ℝ≥0∞) : Measure (X × X) :=
  (σ.prod σ).withDensity h

theorem graphMeasure_le_product (σ : Measure X) (h : X × X → ℝ≥0∞)
    (hbound : ∀ p, h p ≤ 1) : graphMeasure σ h ≤ σ.prod σ := by
  calc
    graphMeasure σ h ≤ (σ.prod σ).withDensity (1 : X × X → ℝ≥0∞) :=
      withDensity_mono (ae_of_all _ hbound)
    _ = σ.prod σ := withDensity_one

omit [MeasurableSpace X] in
/-- The endpoint support condition, combined with a small source ball,
constructively puts both endpoints inside the enlarged block. -/
theorem near_phase_endpoints_in_block {E : Type*} [PseudoMetricSpace E]
    (f : X → E) (centers : Fin n → E) (L tau : ℝ)
    (hL : 0 ≤ L) (htau : 0 < tau) (i : Fin n) (p : X × X)
    (hnear : dist (f p.1) (f p.2) ≤ L * tau)
    (hfirst : p.1 ∈ phaseCover f centers tau i) :
    p ∈ phaseBlock f centers L tau i ×ˢ phaseBlock f centers L tau i := by
  have hx : dist (f p.1) (centers i) < tau := hfirst
  have hyx : dist (f p.2) (f p.1) ≤ L * tau := by simpa only [dist_comm] using hnear
  constructor
  · change dist (f p.1) (centers i) < (L + 2) * tau
    nlinarith [mul_nonneg hL htau.le]
  · change dist (f p.2) (centers i) < (L + 2) * tau
    have ht := dist_triangle (f p.2) (f p.1) (centers i)
    nlinarith

/-- The measurable graph support supplies endpoint containment for the
constructed assignment, rather than asking for a localization certificate. -/
theorem graphMeasure_ae_endpoints_in_block {E : Type*} [PseudoMetricSpace E]
    (σ : Measure X) (h : X × X → ℝ≥0∞) (hh : Measurable h)
    (f : X → E) (centers : Fin n → E) (L tau : ℝ)
    (hL : 0 ≤ L) (htau : 0 < tau)
    (hnear : ∀ p, h p ≠ 0 → dist (f p.1) (f p.2) ≤ L * tau) (i : Fin n) :
    ∀ᵐ p ∂graphMeasure σ h, p.1 ∈ phaseCover f centers tau i →
      p ∈ phaseBlock f centers L tau i ×ˢ phaseBlock f centers L tau i := by
  apply (ae_withDensity_iff hh).mpr
  exact ae_of_all _ fun p hp => near_phase_endpoints_in_block f centers L tau hL htau i p
    (hnear p hp)

/-- Localization data generated by first-hit assignment. Its fields are
conclusions; callers do not supply a partition or an edge-mass split. -/
structure LocalizationConclusion (σ : Measure X) (ν : Measure (X × X))
    (A D : Fin n → Set X) (K : ℕ) (B : ℝ) : Prop where
  cells_measurable : ∀ i, MeasurableSet (firstHit A i)
  cells_disjoint : Pairwise (fun i j => Disjoint (firstHit A i) (firstHit A j))
  cells_partition : ∀ᵐ x ∂σ, ∃! i, x ∈ firstHit A i
  cells_subordinate : ∀ i, firstHit A i ⊆ A i
  blocks_measurable : ∀ i, MeasurableSet (D i)
  exact_mass_split : (∑ i, assignedGraph ν A i univ) = ν univ
  block_domination : ∀ i, assignedGraph ν A i ≤ (σ.prod σ).restrict (D i ×ˢ D i)
  bounded_overlap : ∀ x, (Finset.univ.filter fun i => x ∈ D i).card ≤ K
  square_mass_budget : (∑ i, (σ (D i)).toReal ^ 2) ≤ B * K * (σ univ).toReal
  positive_square_mass : 0 < ∑ i, (σ (D i)).toReal ^ 2
  selected_block : ∃ i, 0 < (σ (D i)).toReal ∧
    (ν univ).toReal / (∑ j, (σ (D j)).toReal ^ 2) ≤
      (assignedGraph ν A i univ).toReal / (σ (D i)).toReal ^ 2 ∧
    (ν univ).toReal / (B * K * (σ univ).toReal) ≤
      (assignedGraph ν A i univ).toReal / (σ (D i)).toReal ^ 2

/-- Construction for a general measurable finite cover and verified endpoint
blocks. All first-hit partition and exact mass-splitting fields are proved. -/
theorem construct_localization (σ : Measure X) [IsFiniteMeasure σ]
    (ν : Measure (X × X)) (hdom : ν ≤ σ.prod σ) (A D : Fin n → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hD : ∀ i, MeasurableSet (D i))
    (hcover : ∀ᵐ x ∂σ, x ∈ ⋃ i, A i)
    (hendpoint : ∀ i, ∀ᵐ p ∂ν, p.1 ∈ A i → p ∈ D i ×ˢ D i)
    (K : ℕ) (hoverlap : ∀ x, (Finset.univ.filter fun i => x ∈ D i).card ≤ K)
    (B : ℝ) (hB : 0 ≤ B) (hupper : ∀ i, (σ (D i)).toReal ≤ B)
    (hpositive : 0 < (ν univ).toReal) : LocalizationConclusion σ ν A D K B := by
  have hbudget := sum_sq_block_mass_le σ D hD K hoverlap B hB hupper
  obtain ⟨hS, i, hi, hdensity⟩ := exists_assignedGraph_density_ge_average
    σ ν hdom A D hA hcover hendpoint hpositive
  exact {
    cells_measurable := measurableSet_firstHit A hA
    cells_disjoint := firstHit_pairwiseDisjoint A
    cells_partition := firstHit_ae_partition σ A hcover
    cells_subordinate := firstHit_subset A
    blocks_measurable := hD
    exact_mass_split := sum_assignedGraph_mass σ ν hdom A hA hcover
    block_domination := assignedGraph_le_block_product σ ν hdom A D hendpoint
    bounded_overlap := hoverlap
    square_mass_budget := hbudget
    positive_square_mass := hS
    selected_block := ⟨i, hi, hdensity,
      (div_le_div_of_nonneg_left hpositive.le hS hbudget).trans hdensity⟩ }

/-- Uniform fixed-expansion localization of an actual bounded near-phase
graph. The constant depends only on the phase space and the expansion L.
The cover, first-hit cells, endpoint assignment, overlap, exact mass split,
and normalized density lower bound are all constructed or verified here.
The cubic source bound is an upper bound only; zero cells are harmless. -/
theorem exists_uniform_near_phase_graph_localization
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E] (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℕ, ∀ (σ : Measure X) [IsFiniteMeasure σ]
      (f : X → E), Measurable f → ∀ (n : ℕ) (centers : Fin n → E)
      (tau : ℝ), 0 < tau →
      (∀ i j, i ≠ j → tau / 2 ≤ dist (centers i) (centers j)) →
      (∀ᵐ x ∂σ, ∃ i, dist (f x) (centers i) < tau) →
      ∀ (h : X × X → ℝ≥0∞), Measurable h → (∀ p, h p ≤ 1) →
      (∀ p, h p ≠ 0 → dist (f p.1) (f p.2) ≤ L * tau) →
      ∀ (C : ℝ), 0 ≤ C →
      (∀ i, (σ (phaseBlock f centers L tau i)).toReal ≤ C * tau ^ 3) →
      0 < (graphMeasure σ h univ).toReal →
      LocalizationConclusion σ (graphMeasure σ h)
        (phaseCover f centers tau) (phaseBlock f centers L tau) K (C * tau ^ 3) := by
  obtain ⟨K, hK⟩ := exists_uniform_expanded_fin_ball_overlap_bound E (L + 2) (by linarith)
  refine ⟨K, ?_⟩
  intro σ _ f hf n centers tau htau hsep hcover h hh hbound hnear C hC hupper hpositive
  apply construct_localization σ (graphMeasure σ h) (graphMeasure_le_product σ h hbound)
    (phaseCover f centers tau) (phaseBlock f centers L tau)
    (fun _ => hf measurableSet_ball) (fun _ => hf measurableSet_ball)
    ?_ (graphMeasure_ae_endpoints_in_block σ h hh f centers L tau hL htau hnear)
    K (fun x => hK tau htau n centers hsep (f x)) (C * tau ^ 3) (by positivity) hupper hpositive
  filter_upwards [hcover] with x hx
  simpa only [mem_iUnion, phaseCover, mem_preimage, Metric.mem_ball] using hx

end StickyKakeya4.ResidualPhaseLocalization
