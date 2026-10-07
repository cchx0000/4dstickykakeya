import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

noncomputable section
namespace NativeSeparatedGramDeterminant
open Classical Finset InnerProductSpace Submodule Module
open scoped BigOperators InnerProductSpace

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι] [Fintype ι]

omit [Fintype ι] in
/-- The correction subtracted by Gram--Schmidt lies in the span of earlier
vectors, so actual distance from that span bounds the orthogonalized norm. -/
lemma infDist_le_norm_gramSchmidt (f : ι → V) (i : ι) :
    Metric.infDist (f i) (Submodule.span ℝ (f '' Set.Iio i) : Set V) ≤
      ‖gramSchmidt ℝ f i‖ := by
  let p : V := ∑ j ∈ Finset.Iio i,
    (ℝ ∙ gramSchmidt ℝ f j).starProjection (f i)
  have hp : p ∈ Submodule.span ℝ (f '' Set.Iio i) := by
    dsimp [p]
    rw [← span_gramSchmidt_Iio ℝ f i]
    apply Submodule.sum_mem
    intro j hj
    rw [Submodule.starProjection_singleton]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,mem_Iio.mp hj,rfl⟩)
  simpa only [dist_eq_norm, p, ← gramSchmidt_def] using
    Metric.infDist_le_dist_of_mem hp (x := f i)

omit [Fintype ι] in
lemma inner_gramSchmidt_self (f : ι → V) (i : ι) :
    inner ℝ (gramSchmidt ℝ f i) (f i) = ‖gramSchmidt ℝ f i‖^2 := by
  conv_lhs => rw [gramSchmidt_def'' ℝ f i]
  rw [inner_add_right, inner_sum]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hz : (∑ j ∈ Finset.Iio i,
      inner ℝ (gramSchmidt ℝ f i)
        ((inner ℝ (gramSchmidt ℝ f j) (f i) / ‖gramSchmidt ℝ f j‖^2) •
          gramSchmidt ℝ f j)) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [inner_smul_right, gramSchmidt_orthogonal ℝ f (ne_of_gt (mem_Iio.mp hj)), mul_zero]
  rw [hz, add_zero, real_inner_self_eq_norm_sq]

/-- On a basis, the Gram determinant is the product of the squared actual
Gram--Schmidt lengths. -/
theorem gram_det_eq_prod_norm_sq [FiniteDimensional ℝ V] (b : Basis ι ℝ V) :
    (Matrix.gram ℝ b).det = (∏ i, ‖gramSchmidt ℝ b i‖)^2 := by
  let hdim : finrank ℝ V = Fintype.card ι := finrank_eq_card_basis b
  let o := gramSchmidtOrthonormalBasis hdim (b : ι → V)
  have hoi (i : ι) : inner ℝ (o i) (b i) = ‖gramSchmidt ℝ b i‖ := by
    have hn : ‖gramSchmidt ℝ b i‖ ≠ 0 := norm_ne_zero_iff.mpr
      (gramSchmidt_ne_zero i b.linearIndependent)
    have hne : gramSchmidtNormed ℝ (b : ι → V) i ≠ 0 := by
      exact (gramSchmidtNormed_orthonormal b.linearIndependent).ne_zero i
    dsimp [o]
    rw [gramSchmidtOrthonormalBasis_apply hdim hne, gramSchmidtNormed,
      inner_smul_left, inner_gramSchmidt_self]
    simp only [RCLike.conj_to_real, RCLike.ofReal_real_eq_id, id_eq]
    field_simp
  have hdet : o.toBasis.det (b : ι → V) = ∏ i, ‖gramSchmidt ℝ b i‖ := by
    rw [gramSchmidtOrthonormalBasis_det hdim]
    exact prod_congr rfl (fun i _ => hoi i)
  rw [Matrix.gram_eq_conjTranspose_mul o, Matrix.det_mul, Matrix.det_conjTranspose]
  change star (o.toBasis.det (b : ι → V)) * o.toBasis.det (b : ι → V) = _
  rw [hdet, star_trivial, pow_two]

theorem basis_gram_det_lower [FiniteDimensional ℝ V] (b : Basis ι ℝ V)
    (r : ℝ) (hr : 0 ≤ r)
    (H : ∀ i, r ≤ Metric.infDist (b i)
      (Submodule.span ℝ ((b : ι → V) '' Set.Iio i) : Set V)) :
    r^(2*Fintype.card ι) ≤ (Matrix.gram ℝ b).det := by
  rw [gram_det_eq_prod_norm_sq]
  have hp : r^(Fintype.card ι) ≤ ∏ i, ‖gramSchmidt ℝ b i‖ := by
    calc
      _ = ∏ _i : ι, r := by simp
      _ ≤ _ := prod_le_prod (fun _ _ => hr)
        (fun i _ => (H i).trans (infDist_le_norm_gramSchmidt b i))
  have hh := pow_le_pow_left₀ (pow_nonneg hr _) hp 2
  simpa only [← pow_mul, Nat.mul_comm (Fintype.card ι) 2] using hh

/-- Successive distances to actual earlier spans give the quantitative Gram
lower bound in an arbitrary real inner-product space. Only the tuple's own
finite span is used; no ambient dimension or wedge certificate is assumed. -/
theorem gram_det_lower_of_span_distance (f : ι → V)
    (hf : LinearIndependent ℝ f) (r : ℝ) (hr : 0 ≤ r)
    (H : ∀ i, r ≤ Metric.infDist (f i)
      (Submodule.span ℝ (f '' Set.Iio i) : Set V)) :
    r^(2*Fintype.card ι) ≤ (Matrix.gram ℝ f).det := by
  let P := Submodule.span ℝ (Set.range f)
  let b : Basis ι ℝ P := Basis.span hf
  have : FiniteDimensional ℝ P := b.finiteDimensional_of_finite
  have hbi (i : ι) : (b i : V) = f i := Basis.coe_span_apply hf i
  have hb (i : ι) : r ≤ Metric.infDist (b i)
      (Submodule.span ℝ ((b : ι → P) '' Set.Iio i) : Set P) := by
    apply (Metric.le_infDist ⟨0,Submodule.zero_mem _⟩).mpr
    intro x hx
    have hx' : (x : V) ∈ Submodule.span ℝ (f '' Set.Iio i) := by
      have hh := Submodule.apply_mem_span_image_of_mem_span P.subtype hx
      change (x : V) ∈ Submodule.span ℝ
        (P.subtype '' ((b : ι → P) '' Set.Iio i)) at hh
      rw [Set.image_image] at hh
      have he : (fun x => P.subtype (b x)) = f := funext hbi
      rwa [he] at hh
    have hh := (H i).trans (Metric.infDist_le_dist_of_mem hx')
    simpa only [dist_eq_norm, Submodule.coe_norm, Submodule.coe_sub, hbi] using hh
  have hh := basis_gram_det_lower b r hr hb
  have he : Matrix.gram ℝ b = Matrix.gram ℝ f := by
    ext i j
    change inner ℝ (b i) (b j) = inner ℝ (f i) (f j)
    rw [Submodule.coe_inner, hbi, hbi]
  rwa [he] at hh

end NativeSeparatedGramDeterminant
