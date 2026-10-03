import Theorems.Thm_StickyKakeya4_rank_one_borel_front_escape
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Determinant
import Theorems.Thm_StickyKakeya4_invertible_front_frostman_transport

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology Matrix.Norms.Operator
noncomputable section
namespace StickyKakeya4.RankOneGeneralInputEscape
open TriangularPotentialEscape RankOneBorelFrontEscape EnergyDimension

def sourceLinearEquiv : Source ≃ₗ[ℝ] Vector where
  toFun := sourceVector
  invFun := fun z => ((z 0,z 1),z 2)
  left_inv := by intro z; rfl
  right_inv := by intro z; ext i; fin_cases i <;> rfl
  map_add' := by intro z w; ext i; fin_cases i <;> rfl
  map_smul' := by intro r z; ext i; fin_cases i <;> rfl

/-- A nonzero input functional is the first row of an invertible matrix. -/
theorem exists_input_matrix (v : Vector) (hv : v ≠ 0) :
    ∃ R : Matrix3, R.det ≠ 0 ∧ ∀ z : Vector, R.mulVec z 0 = dotProduct v z := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  fin_cases i
  · refine ⟨Matrix.of ![v, ![0,1,0], ![0,0,1]], ?_, fun _ => rfl⟩
    rw [Matrix.det_fin_three]
    simpa using hi
  · refine ⟨Matrix.of ![v, ![1,0,0], ![0,0,1]], ?_, fun _ => rfl⟩
    rw [Matrix.det_fin_three]
    simpa using hi
  · refine ⟨Matrix.of ![v, ![1,0,0], ![0,1,0]], ?_, fun _ => rfl⟩
    rw [Matrix.det_fin_three]
    simpa using hi

def sourceChange (R : Matrix3) (hR : R.det ≠ 0) : Source ≃ₗ[ℝ] Source :=
  sourceLinearEquiv.trans
    (((Matrix.toLin' R).equivOfDetNeZero (by simpa using hR)).trans sourceLinearEquiv.symm)

lemma sourceChange_apply (R : Matrix3) (hR : R.det ≠ 0) (z : Source) :
    sourceVector (sourceChange R hR z) = R.mulVec (sourceVector z) := by
  change sourceLinearEquiv (sourceLinearEquiv.symm _) = _
  simp only [LinearEquiv.apply_symm_apply]
  rfl

/-- The transformed bounded source has a product reference derived from its
original bounded Lebesgue density and bounded chart support. -/
theorem transformed_source_product_domination
    (e : Source ≃ₗ[ℝ] Source)
    (σ : Measure Source) [IsFiniteMeasure σ]
    (D R : ℝ) (_hD : 0 ≤ D) (hR : 0 ≤ R)
    (hdom : σ ≤ ENNReal.ofReal D • volume)
    (hsupport : σ (Metric.closedBall 0 R)ᶜ = 0) :
    ∃ M : ℝ, 0 < M ∧ ∃ D' : ℝ≥0∞, D' ≠ ∞ ∧
      σ.map e ≤ D' •
        (((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).prod
          (volume.restrict (Icc (-M) M))) := by
  let ec := e.toContinuousLinearEquiv
  let M : ℝ := ‖ec.toContinuousLinearMap‖ * R + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let box : Set Source := (Icc (-M) M ×ˢ Icc (-M) M) ×ˢ Icc (-M) M
  have hbox : MeasurableSet box := (measurableSet_Icc.prod measurableSet_Icc).prod measurableSet_Icc
  have hpre : Metric.closedBall (0:Source) R ⊆ e ⁻¹' box := by
    intro z hz
    have hn : ‖e z‖ ≤ ‖ec.toContinuousLinearMap‖ * R := by
      exact (ec.toContinuousLinearMap.le_opNorm z).trans
        (mul_le_mul_of_nonneg_left (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
          (norm_nonneg _))
    have hzn : ‖e z‖ < M := by dsimp [M]; linarith
    have h₁ : |(e z).1.1| < M :=
      (norm_fst_le (e z).1).trans_lt ((norm_fst_le (e z)).trans_lt hzn)
    have h₂ : |(e z).1.2| < M :=
      (norm_snd_le (e z).1).trans_lt ((norm_fst_le (e z)).trans_lt hzn)
    have h₃ : |(e z).2| < M := (norm_snd_le (e z)).trans_lt hzn
    exact ⟨⟨⟨(abs_lt.mp h₁).1.le,(abs_lt.mp h₁).2.le⟩,
      ⟨(abs_lt.mp h₂).1.le,(abs_lt.mp h₂).2.le⟩⟩,
      ⟨(abs_lt.mp h₃).1.le,(abs_lt.mp h₃).2.le⟩⟩
  have he : Measurable e := ec.continuous.measurable
  have hsmap : (σ.map e) boxᶜ = 0 := by
    rw [Measure.map_apply he hbox.compl]
    exact measure_mono_null (compl_subset_compl.mpr hpre) hsupport
  have hrestrict : (σ.map e).restrict box = σ.map e :=
    Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hsmap)
  have hdet : LinearMap.det e.toLinearMap ≠ 0 := e.isUnit_det'.ne_zero
  let J : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹|
  let : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    change ((volume : Measure ℝ).prod volume).IsAddHaarMeasure
    infer_instance
  let : (volume : Measure Source).IsAddHaarMeasure := by
    change ((volume : Measure (ℝ × ℝ)).prod volume).IsAddHaarMeasure
    infer_instance
  have hmap : (volume : Measure Source).map e = J • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
  have hglobal : σ.map e ≤ (ENNReal.ofReal D * J) • volume := by
    calc
      σ.map e ≤ (ENNReal.ofReal D • (volume : Measure Source)).map e :=
        Measure.map_mono hdom he
      _ = (ENNReal.ofReal D * J) • volume := by
        rw [Measure.map_smul, hmap, smul_smul]
  refine ⟨M,hM,ENNReal.ofReal D*J,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,?_⟩
  rw [← hrestrict]
  have hb : (volume : Measure Source).restrict box =
      (((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).prod
        (volume.restrict (Icc (-M) M))) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    rfl
  simpa only [Measure.restrict_smul, hb] using Measure.restrict_mono_measure hglobal box


/-- Constant input is handled by a constant scalar function; nonzero input is
converted by an actual invertible source basis. -/
theorem exists_input_normalization (v : Vector) (f : ℝ → ℝ) (hf : Measurable f) :
    ∃ (e : Source ≃ₗ[ℝ] Source) (g : ℝ → ℝ), Measurable g ∧
      ∀ z : Source, f (dotProduct v (sourceVector z)) = g ((e z).1.1) := by
  by_cases hv : v = 0
  · refine ⟨LinearEquiv.refl ℝ Source, fun _ => f 0, measurable_const, ?_⟩
    intro z
    simp only [hv, zero_dotProduct]
  · obtain ⟨R,hR,hfirst⟩ := exists_input_matrix v hv
    refine ⟨sourceChange R hR,f,hf,?_⟩
    intro z
    congr 1
    have hh := congrArg (fun x : Vector => x 0) (sourceChange_apply R hR z)
    exact (hfirst (sourceVector z)).symm.trans hh.symm

def vectorChange (e : Source ≃ₗ[ℝ] Source) : Vector ≃ₗ[ℝ] Vector :=
  sourceLinearEquiv.symm.trans (e.trans sourceLinearEquiv)

lemma vectorChange_source (e : Source ≃ₗ[ℝ] Source) (z : Source) :
    vectorChange e (sourceVector z) = sourceVector (e z) := by
  change sourceLinearEquiv (e (sourceLinearEquiv.symm (sourceLinearEquiv z))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

def conjugatedMatrix (e : Source ≃ₗ[ℝ] Source) (L : Matrix3) : Matrix3 :=
  LinearMap.toMatrix' ((vectorChange e).toLinearMap.comp
    ((Matrix.toLin' L).comp (vectorChange e).symm.toLinearMap))

lemma conjugatedMatrix_apply (e : Source ≃ₗ[ℝ] Source) (L : Matrix3) (x : Vector) :
    (conjugatedMatrix e L).mulVec (vectorChange e x) = vectorChange e (L.mulVec x) := by
  change Matrix.toLin' (conjugatedMatrix e L) (vectorChange e x) = _
  rw [conjugatedMatrix, Matrix.toLin'_toMatrix']
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

def generalSpatial (L : Matrix3) (u c v : Vector) (f : ℝ → ℝ)
    (p : ℝ × Source) : Vector := c + L.mulVec (sourceVector p.2) +
      f (dotProduct v (sourceVector p.2)) • u + p.1 • sourceVector p.2

def generalPoint (L : Matrix3) (u c v : Vector) (f : ℝ → ℝ)
    (p : ℝ × Source) : E4 := WithLp.toLp 2
      ![generalSpatial L u c v f p 0, generalSpatial L u c v f p 1,
        generalSpatial L u c v f p 2, p.1]

lemma conjugated_spatial
    (e : Source ≃ₗ[ℝ] Source) (L : Matrix3) (u c v : Vector)
    (f g : ℝ → ℝ)
    (hfg : ∀ z : Source, f (dotProduct v (sourceVector z)) = g ((e z).1.1))
    (t : ℝ) (z : Source) :
    vectorChange e (generalSpatial L u c v f (t,z)) =
      spatial (conjugatedMatrix e L) (vectorChange e u) (vectorChange e c) g (t,e z) := by
  simp only [generalSpatial, spatial, map_add, map_smul]
  rw [hfg, ← vectorChange_source, conjugatedMatrix_apply]


lemma measurable_generalPoint (L : Matrix3) (u c v : Vector) (f : ℝ → ℝ)
    (hf : Measurable f) : Measurable (generalPoint L u c v f) := by
  have hz (j : Fin 3) : Measurable (fun p : ℝ × Source => sourceVector p.2 j) := by
    fin_cases j <;> dsimp [sourceVector] <;> fun_prop
  have hd : Measurable (fun p : ℝ × Source => dotProduct v (sourceVector p.2)) := by
    simp only [dotProduct]
    fun_prop
  have hsp (j : Fin 3) : Measurable (fun p => generalSpatial L u c v f p j) := by
    simp only [generalSpatial, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec]
    change Measurable (fun p : ℝ × Source =>
      c j + dotProduct (L j) (sourceVector p.2) +
        f (dotProduct v (sourceVector p.2)) * u j + p.1 * sourceVector p.2 j)
    have hL : Measurable (fun p : ℝ × Source => dotProduct (L j) (sourceVector p.2)) := by
      simp only [dotProduct]
      fun_prop
    fun_prop
  unfold generalPoint
  apply (WithLp.measurable_toLp 2 (Fin 4 → ℝ)).comp
  apply measurable_pi_lambda
  intro i
  fin_cases i
  · exact hsp 0
  · exact hsp 1
  · exact hsp 2
  · exact measurable_fst

open InvertibleFrontFrostmanTransport

theorem point_conjugacy
    (e : Source ≃ₗ[ℝ] Source) (L : Matrix3) (u c v : Vector)
    (f g : ℝ → ℝ)
    (hfg : ∀ z : Source, f (dotProduct v (sourceVector z)) = g ((e z).1.1))
    (p : ℝ × Source) :
    spacetimeLift e (generalPoint L u c v f p) =
      actualPoint (conjugatedMatrix e L) (vectorChange e u) (vectorChange e c) g (p.1,e p.2) := by
  have hh := conjugated_spatial e L u c v f g hfg p.1 p.2
  ext i
  fin_cases i
  · exact congrArg (fun z : Vector => z 0) hh
  · exact congrArg (fun z : Vector => z 1) hh
  · exact congrArg (fun z : Vector => z 2) hh
  · rfl

/-- The time law and source law are their literal pushforwards, and the output
change is a fixed linear equivalence. -/
theorem actual_law_conjugacy
    (τ : Measure ℝ) (σ : Measure Source) [SFinite τ] [SFinite σ]
    (e : Source ≃ₗ[ℝ] Source) (L : Matrix3) (u c v : Vector)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ z : Source, f (dotProduct v (sourceVector z)) = g ((e z).1.1)) :
    ((τ.prod (σ.map e)).map
      (actualPoint (conjugatedMatrix e L) (vectorChange e u) (vectorChange e c) g)) =
        (((τ.prod σ).map (generalPoint L u c v f)).map (spacetimeLift e)) := by
  have he : Measurable e := e.toContinuousLinearEquiv.continuous.measurable
  have hprod : τ.prod (σ.map e) = (τ.prod σ).map (Prod.map id e) := by
    simpa only [Measure.map_id] using Measure.map_prod_map τ σ measurable_id he
  rw [hprod, Measure.map_map
      (measurable_actualPoint _ _ _ _ hg) (measurable_id.prodMap he),
    Measure.map_map (spacetimeLift e).continuous.measurable (measurable_generalPoint L u c v f hf)]
  congr 1
  funext p
  exact (point_conjugacy e L u c v f g hfg p).symm

/-- Arbitrary scalar input v·a is reduced by a source basis whose density and
bounded product reference are derived from the original Lebesgue-dominated law. -/
theorem exists_general_input_supported_frostman_bounded
    (σ : Measure Source) [IsFiniteMeasure σ] (hσ : σ ≠ 0)
    (D R : ℝ) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hdom : σ ≤ ENNReal.ofReal D • volume)
    (hbounded : σ (Metric.closedBall 0 R)ᶜ = 0)
    (lo hi : ℝ) (hlohi : lo < hi)
    (L : Matrix3) (u c v : Vector) (f : ℝ → ℝ) (hf : Measurable f)
    (K : Set E4)
    (hsupport : (((volume.restrict (Icc lo hi)).prod σ).map
      (generalPoint L u c v f)) Kᶜ = 0)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∃ ν : Measure E4, IsProbabilityMeasure ν ∧ ν Kᶜ = 0 ∧
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x r, 0 < r →
        ν (Metric.ball x r) ≤ C*ENNReal.ofReal r^(1+3*s) := by
  obtain ⟨e,g,hg,hfg⟩ := exists_input_normalization v f hf
  obtain ⟨M,_hM,D',hD',hdom'⟩ := transformed_source_product_domination e σ D R hD hR hdom hbounded
  let μ : Measure ℝ := volume.restrict (Icc (-M) M)
  have hμ : μ ≤ ENNReal.ofReal (1:ℝ) • volume := by
    simpa only [ENNReal.ofReal_one, one_smul] using
      (Measure.restrict_le_self : volume.restrict (Icc (-M) M) ≤ volume)
  have he : Measurable e := e.toContinuousLinearEquiv.continuous.measurable
  have hσ' : σ.map e ≠ 0 := (Measure.map_ne_zero_iff he.aemeasurable).mpr hσ
  have hs' : (((volume.restrict (Icc lo hi)).prod (σ.map e)).map
      (actualPoint (conjugatedMatrix e L) (vectorChange e u) (vectorChange e c) g))
        ((spacetimeLift e) '' K)ᶜ = 0 := by
    rw [actual_law_conjugacy _ σ e L u c v f g hf hg hfg,
      map_image_compl_eq]
    exact hsupport
  apply pullback_supported_frostman_from_image (spacetimeLift e) K (1+3*s)
  exact exists_rank_one_borel_supported_frostman μ μ μ 1 1 1
    (by norm_num) (by norm_num) (by norm_num) hμ hμ hμ
    (σ.map e) hσ' D' hD' hdom' lo hi hlohi
    (conjugatedMatrix e L) (vectorChange e u) (vectorChange e c) g hg
    ((spacetimeLift e) '' K) hs' s hs hs1

theorem general_input_front_dimH_eq_four_bounded
    (σ : Measure Source) [IsFiniteMeasure σ] (hσ : σ ≠ 0)
    (D R : ℝ) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hdom : σ ≤ ENNReal.ofReal D • volume)
    (hbounded : σ (Metric.closedBall 0 R)ᶜ = 0)
    (lo hi : ℝ) (hlohi : lo < hi)
    (L : Matrix3) (u c v : Vector) (f : ℝ → ℝ) (hf : Measurable f)
    (K : Set E4)
    (hsupport : (((volume.restrict (Icc lo hi)).prod σ).map
      (generalPoint L u c v f)) Kᶜ = 0) : dimH K = 4 := by
  apply TriangularBorelFrontEscape.dimH_eq_four_of_triangular_frostman K
  intro s hs hs1
  exact exists_general_input_supported_frostman_bounded σ hσ D R hD hR hdom hbounded
    lo hi hlohi L u c v f hf K hsupport s hs hs1


/-- Boundedness is derived by taking one positive bounded piece of the original
law. The final support is still the literal original front. -/
theorem exists_general_input_supported_frostman
    (σ : Measure Source) [IsFiniteMeasure σ] (hσ : σ ≠ 0)
    (D : ℝ) (hD : 0 ≤ D) (hdom : σ ≤ ENNReal.ofReal D • volume)
    (lo hi : ℝ) (hlohi : lo < hi)
    (L : Matrix3) (u c v : Vector) (f : ℝ → ℝ) (hf : Measurable f)
    (K : Set E4)
    (hsupport : (((volume.restrict (Icc lo hi)).prod σ).map
      (generalPoint L u c v f)) Kᶜ = 0)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∃ ν : Measure E4, IsProbabilityMeasure ν ∧ ν Kᶜ = 0 ∧
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x r, 0 < r →
        ν (Metric.ball x r) ≤ C*ENNReal.ofReal r^(1+3*s) := by
  have hmass : σ (⋃ n : ℕ, Metric.closedBall (0:Source) n) ≠ 0 := by
    rw [Metric.iUnion_closedBall_nat]
    exact fun hz => hσ (Measure.measure_univ_eq_zero.mp hz)
  obtain ⟨n,hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hmass
  let σ' := σ.restrict (Metric.closedBall (0:Source) n)
  have hσ' : σ' ≠ 0 := by
    intro hz
    exact hn.ne' (Measure.restrict_eq_zero.mp hz)
  have hdom' : σ' ≤ ENNReal.ofReal D • volume := Measure.restrict_le_self.trans hdom
  have hbounded : σ' (Metric.closedBall (0:Source) n)ᶜ = 0 := by
    simp [σ', Measure.restrict_apply measurableSet_closedBall.compl]
  have hs' : (((volume.restrict (Icc lo hi)).prod σ').map
      (generalPoint L u c v f)) Kᶜ = 0 := by
    apply le_antisymm _ bot_le
    exact (Measure.map_mono (Measure.prod_mono le_rfl Measure.restrict_le_self)
      (measurable_generalPoint L u c v f hf) Kᶜ).trans_eq hsupport
  exact exists_general_input_supported_frostman_bounded σ' hσ' D n hD
    (by positivity) hdom' hbounded lo hi hlohi L u c v f hf K hs' s hs hs1

/-- Full-dimensional actual fronts for every Borel selector of the form
c+L a+u f(v·a), with arbitrary real matrix and vectors, including v=0 and u=0. -/
theorem general_input_front_dimH_eq_four
    (σ : Measure Source) [IsFiniteMeasure σ] (hσ : σ ≠ 0)
    (D : ℝ) (hD : 0 ≤ D) (hdom : σ ≤ ENNReal.ofReal D • volume)
    (lo hi : ℝ) (hlohi : lo < hi)
    (L : Matrix3) (u c v : Vector) (f : ℝ → ℝ) (hf : Measurable f)
    (K : Set E4)
    (hsupport : (((volume.restrict (Icc lo hi)).prod σ).map
      (generalPoint L u c v f)) Kᶜ = 0) : dimH K = 4 := by
  apply TriangularBorelFrontEscape.dimH_eq_four_of_triangular_frostman K
  intro s hs hs1
  exact exists_general_input_supported_frostman σ hσ D hD hdom
    lo hi hlohi L u c v f hf K hsupport s hs hs1

end StickyKakeya4.RankOneGeneralInputEscape
