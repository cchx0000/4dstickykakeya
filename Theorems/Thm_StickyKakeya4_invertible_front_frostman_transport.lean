import Theorems.Thm_StickyKakeya4_triangular_potential_escape
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4.InvertibleFrontFrostmanTransport
open TriangularPotentialEscape

/-- Spatial triple followed by actual time, as a linear coordinate equivalence. -/
def spacetimeCoordinates : E4 ≃ₗ[ℝ] (Source × ℝ) where
  toFun y := (((y 0,y 1),y 2),y 3)
  invFun p := WithLp.toLp 2 ![p.1.1.1,p.1.1.2,p.1.2,p.2]
  left_inv y := by ext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨⟨a,b⟩,c⟩,t⟩; rfl
  map_add' y z := by rfl
  map_smul' r y := by rfl

/-- A fixed spatial source-coordinate change lifts to spacetime and leaves actual time intact. -/
def spacetimeLift (e : Source ≃ₗ[ℝ] Source) : E4 ≃L[ℝ] E4 :=
  ((spacetimeCoordinates.trans (e.prodCongr (LinearEquiv.refl ℝ ℝ))).trans
    spacetimeCoordinates.symm).toContinuousLinearEquiv

@[simp] theorem spacetimeLift_apply_zero (e : Source ≃ₗ[ℝ] Source) (y : E4) :
    spacetimeLift e y 0 = (e ((y 0,y 1),y 2)).1.1 := rfl

@[simp] theorem spacetimeLift_apply_one (e : Source ≃ₗ[ℝ] Source) (y : E4) :
    spacetimeLift e y 1 = (e ((y 0,y 1),y 2)).1.2 := rfl

@[simp] theorem spacetimeLift_apply_two (e : Source ≃ₗ[ℝ] Source) (y : E4) :
    spacetimeLift e y 2 = (e ((y 0,y 1),y 2)).2 := rfl

@[simp] theorem spacetimeLift_apply_three (e : Source ≃ₗ[ℝ] Source) (y : E4) :
    spacetimeLift e y 3 = y 3 := rfl

@[simp] theorem spacetimeLift_symm (e : Source ≃ₗ[ℝ] Source) :
    (spacetimeLift e).symm = spacetimeLift e.symm := by
  ext y i
  fin_cases i <;> rfl

/-- A positive inverse Lipschitz constant derived from the actual output equivalence. -/
def inverseBound (e : E4 ≃L[ℝ] E4) : ℝ := max 1 ‖e.symm.toContinuousLinearMap‖

theorem inverseBound_pos (e : E4 ≃L[ℝ] E4) : 0 < inverseBound e :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem preimage_ball_subset (e : E4 ≃L[ℝ] E4) (x : E4) (r : ℝ) :
    e ⁻¹' Metric.ball x r ⊆ Metric.ball (e.symm x) (inverseBound e*r) := by
  intro y hy
  change dist (e y) x < r at hy
  change dist y (e.symm x) < inverseBound e*r
  calc
    dist y (e.symm x) = dist (e.symm (e y)) (e.symm x) := by simp
    _ ≤ ‖e.symm.toContinuousLinearMap‖*dist (e y) x :=
      e.symm.lipschitz.dist_le_mul (e y) x
    _ ≤ inverseBound e*dist (e y) x :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
    _ < inverseBound e*r := mul_lt_mul_of_pos_left hy (inverseBound_pos e)

/-- Ball growth transported by the literal output pushforward. -/
theorem linearEquiv_map_ball_bound
    (e : E4 ≃L[ℝ] E4) (μ : Measure E4) (q : ℝ) (C : ℝ≥0∞)
    (hball : ∀ x r, 0 < r → μ (Metric.ball x r) ≤ C*ENNReal.ofReal r^q)
    (x : E4) (r : ℝ) (hr : 0 < r) :
    (μ.map e) (Metric.ball x r) ≤
      (C*ENNReal.ofReal (inverseBound e)^q)*ENNReal.ofReal r^q := by
  rw [Measure.map_apply e.continuous.measurable Metric.isOpen_ball.measurableSet]
  calc
    _ ≤ μ (Metric.ball (e.symm x) (inverseBound e*r)) :=
      measure_mono (preimage_ball_subset e x r)
    _ ≤ C*ENNReal.ofReal (inverseBound e*r)^q :=
      hball _ _ (mul_pos (inverseBound_pos e) hr)
    _ = _ := by
      rw [ENNReal.ofReal_mul (inverseBound_pos e).le,
        ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
      ring

theorem transported_constant_ne_top
    (e : E4 ≃L[ℝ] E4) (q : ℝ) (C : ℝ≥0∞) (hC : C ≠ ∞) :
    C*ENNReal.ofReal (inverseBound e)^q ≠ ∞ := by
  apply ENNReal.mul_ne_top hC
  exact ENNReal.rpow_ne_top_of_ne_zero
    (ENNReal.ofReal_ne_zero_iff.mpr (inverseBound_pos e)) ENNReal.ofReal_ne_top

/-- The support statement is exact for arbitrary sets; no measurability of the target is imposed. -/
theorem linearEquiv_map_compl
    (e : E4 ≃L[ℝ] E4) (μ : Measure E4) (K : Set E4) :
    (μ.map e) Kᶜ = μ (e ⁻¹' K)ᶜ := by
  exact e.toHomeomorph.measurableEmbedding.map_apply μ Kᶜ

/-- Literal actual source-map laws commute with the fixed output change. -/
theorem linearEquiv_map_actual_law
    {X : Type*} [MeasurableSpace X] (η : Measure X)
    (F : X → E4) (hF : Measurable F) (e : E4 ≃L[ℝ] E4) :
    (η.map F).map e = η.map (fun x => e (F x)) :=
  Measure.map_map e.continuous.measurable hF

/-- A finite nonzero actual measure with ball growth can be transported and normalized. -/
theorem normalize_linearEquiv_supported_ball_bound
    (e : E4 ≃L[ℝ] E4) (μ : Measure E4) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (K : Set E4) (hsupport : μ (e ⁻¹' K)ᶜ = 0)
    (q : ℝ) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hball : ∀ x r, 0 < r → μ (Metric.ball x r) ≤ C*ENNReal.ofReal r^q) :
    ∃ ν : Measure E4, IsProbabilityMeasure ν ∧ ν Kᶜ = 0 ∧
      ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ x r, 0 < r →
        ν (Metric.ball x r) ≤ B*ENNReal.ofReal r^q := by
  apply normalize_supported_ball_bound (μ.map e)
    ((Measure.map_ne_zero_iff e.continuous.measurable.aemeasurable).mpr hμ)
    K (by rw [linearEquiv_map_compl]; exact hsupport) q
    (C*ENNReal.ofReal (inverseBound e)^q) (transported_constant_ne_top e q C hC)
  exact linearEquiv_map_ball_bound e μ q C hball

/-- Probability Frostman measures transport without renormalization. -/
theorem transport_supported_frostman
    (e : E4 ≃L[ℝ] E4) (K : Set E4) (q : ℝ)
    (h : ∃ μ : Measure E4, IsProbabilityMeasure μ ∧ μ (e ⁻¹' K)ᶜ = 0 ∧
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x r, 0 < r →
        μ (Metric.ball x r) ≤ C*ENNReal.ofReal r^q) :
    ∃ ν : Measure E4, IsProbabilityMeasure ν ∧ ν Kᶜ = 0 ∧
      ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ x r, 0 < r →
        ν (Metric.ball x r) ≤ B*ENNReal.ofReal r^q := by
  obtain ⟨μ,hμ,hs,C,hC,hball⟩ := h
  let : IsProbabilityMeasure μ := hμ
  refine ⟨μ.map e, Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable,
    ?_, C*ENNReal.ofReal (inverseBound e)^q, transported_constant_ne_top e q C hC,
    linearEquiv_map_ball_bound e μ q C hball⟩
  rw [linearEquiv_map_compl]
  exact hs

/-- Pull a supported Frostman measure back from the changed output coordinates. -/
theorem pullback_supported_frostman_from_image
    (e : E4 ≃L[ℝ] E4) (K : Set E4) (q : ℝ)
    (h : ∃ μ : Measure E4, IsProbabilityMeasure μ ∧ μ (e '' K)ᶜ = 0 ∧
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x r, 0 < r →
        μ (Metric.ball x r) ≤ C*ENNReal.ofReal r^q) :
    ∃ ν : Measure E4, IsProbabilityMeasure ν ∧ ν Kᶜ = 0 ∧
      ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ x r, 0 < r →
        ν (Metric.ball x r) ≤ B*ENNReal.ofReal r^q := by
  apply transport_supported_frostman e.symm K q
  have he : e.symm ⁻¹' K = e '' K := by
    ext y
    constructor
    · intro hy
      exact ⟨e.symm y,hy,e.apply_symm_apply y⟩
    · rintro ⟨x,hx,rfl⟩
      simpa using hx
  rwa [he]

/-- Actual image support survives an output equivalence exactly. -/
theorem map_image_compl_eq
    (e : E4 ≃L[ℝ] E4) (μ : Measure E4) (K : Set E4) :
    (μ.map e) (e '' K)ᶜ = μ Kᶜ := by
  rw [linearEquiv_map_compl]
  congr 1
  ext x
  simp

end StickyKakeya4.InvertibleFrontFrostmanTransport
