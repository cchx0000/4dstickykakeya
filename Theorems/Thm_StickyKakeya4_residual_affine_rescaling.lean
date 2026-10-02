import Theorems.Thm_StickyKakeya4_angular_residual_shell
import Theorems.Thm_StickyKakeya4_actual_slope_source_bounds
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# Actual common affine normalization of residual shell edges

A single positive scale and a single physical root normalize both endpoints.
The closest time and its literal time window are unchanged; residuals and
secants rescale together. These are identities for the original source, not
weak-limit transfers.
-/

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace StickyKakeya4.ResidualAffineRescaling

/-- Recover an original slope from normalized coordinates. -/
def physicalSlope (a₀ : E3) (τ : ℝ) (x : E3) : E3 := a₀ + τ • x

/-- Normalize a physical slope about the same fixed old root. -/
def normalizedSlope (a₀ : E3) (τ : ℝ) (a : E3) : E3 := τ⁻¹ • (a - a₀)

/-- The rescaled intercept uses the same physical root for every endpoint. -/
def normalizedIntercept (b : E3 → E3) (a₀ : E3) (τ : ℝ) (x : E3) : E3 :=
  τ⁻¹ • (b (physicalSlope a₀ τ x) - b a₀)

@[simp] theorem physicalSlope_normalizedSlope (a₀ a : E3) (τ : ℝ) (hτ : τ ≠ 0) :
    physicalSlope a₀ τ (normalizedSlope a₀ τ a) = a := by
  simp [physicalSlope, normalizedSlope, smul_smul, hτ]

@[simp] theorem normalizedSlope_physicalSlope (a₀ x : E3) (τ : ℝ) (hτ : τ ≠ 0) :
    normalizedSlope a₀ τ (physicalSlope a₀ τ x) = x := by
  simp [physicalSlope, normalizedSlope, smul_smul, hτ]

@[simp] theorem normalizedSlope_root (a₀ : E3) (τ : ℝ) : normalizedSlope a₀ τ a₀ = 0 := by
  simp [normalizedSlope]

@[simp] theorem normalizedIntercept_zero (b : E3 → E3) (a₀ : E3) (τ : ℝ) :
    normalizedIntercept b a₀ τ 0 = 0 := by simp [normalizedIntercept, physicalSlope]

/-- Both normalized secants are the common scalar multiple of the original
physical secants. -/
theorem normalized_secants (b : E3 → E3) (a₀ a a' : E3) (τ : ℝ) (hτ : τ ≠ 0) :
    normalizedSlope a₀ τ a - normalizedSlope a₀ τ a' = τ⁻¹ • (a - a') ∧
      normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a) -
        normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a') = τ⁻¹ • (b a - b a') := by
  constructor
  · simp only [normalizedSlope, ← smul_sub]
    congr 1
    abel
  · simp only [normalizedIntercept, physicalSlope_normalizedSlope a₀ _ τ hτ, ← smul_sub]
    congr 1
    abel

/-- Closest collision time is invariant under a common nonzero scalar. -/
theorem collisionTime_smul (α β : E3) (c : ℝ) (hc : c ≠ 0) :
    collisionTime (c • α) (c • β) = collisionTime α β := by
  by_cases hα : α = 0
  · simp [collisionTime, hα]
  have hn : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr hα
  simp only [collisionTime, real_inner_smul_left, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

/-- The full residual vector, rather than only its norm, rescales exactly. -/
theorem collisionResidual_smul (α β : E3) (c : ℝ) (hc : c ≠ 0) :
    collisionResidual (c • α) (c • β) = c • collisionResidual α β := by
  rw [collisionResidual, collisionTime_smul α β c hc, collisionResidual]
  module

/-- The old collision time of actual physical endpoints is unchanged. -/
theorem normalized_collisionTime (b : E3 → E3) (a₀ a a' : E3) (τ : ℝ) (hτ : τ ≠ 0) :
    collisionTime (normalizedSlope a₀ τ a - normalizedSlope a₀ τ a')
      (normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a) -
        normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a')) =
      collisionTime (a - a') (b a - b a') := by
  rw [(normalized_secants b a₀ a a' τ hτ).1, (normalized_secants b a₀ a a' τ hτ).2]
  exact collisionTime_smul _ _ _ (inv_ne_zero hτ)

/-- The original physical edge residual rescales by exactly `τ⁻¹`. -/
theorem normalized_collisionResidual (b : E3 → E3) (a₀ a a' : E3) (τ : ℝ) (hτ : τ ≠ 0) :
    collisionResidual (normalizedSlope a₀ τ a - normalizedSlope a₀ τ a')
      (normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a) -
        normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a')) =
      τ⁻¹ • collisionResidual (a - a') (b a - b a') := by
  rw [(normalized_secants b a₀ a a' τ hτ).1, (normalized_secants b a₀ a a' τ hτ).2]
  exact collisionResidual_smul _ _ _ (inv_ne_zero hτ)

/-- The physical angular shell is precisely the normalized unit shell. -/
theorem normalized_shell_iff (a₀ a a' : E3) (τ : ℝ) (hτ : 0 < τ) :
    (1 < ‖normalizedSlope a₀ τ a - normalizedSlope a₀ τ a'‖ ∧
      ‖normalizedSlope a₀ τ a - normalizedSlope a₀ τ a'‖ ≤ 2) ↔
      τ < ‖a - a'‖ ∧ ‖a - a'‖ ≤ 2 * τ := by
  have he : ‖normalizedSlope a₀ τ a - normalizedSlope a₀ τ a'‖ = ‖a - a'‖ / τ := by
    rw [(normalized_secants (fun a => a) a₀ a a' τ hτ.ne').1,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
    ring
  rw [he, lt_div_iff₀ hτ, div_le_iff₀ hτ, one_mul]

/-- Residual radius and the literal closest-time window transform together. -/
theorem normalized_residual_time_iff (b : E3 → E3) (a₀ a a' : E3)
    (τ ρ : ℝ) (hτ : 0 < τ) (J : Set ℝ) :
    (‖collisionResidual (normalizedSlope a₀ τ a - normalizedSlope a₀ τ a')
      (normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a) -
        normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a'))‖ ≤ ρ / τ ∧
      collisionTime (normalizedSlope a₀ τ a - normalizedSlope a₀ τ a')
        (normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a) -
          normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a')) ∈ J) ↔
      ‖collisionResidual (a - a') (b a - b a')‖ ≤ ρ ∧ collisionTime (a - a') (b a - b a') ∈ J := by
  rw [normalized_collisionResidual b a₀ a a' τ hτ.ne',
    normalized_collisionTime b a₀ a a' τ hτ.ne', norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
  have he : τ⁻¹ * ‖collisionResidual (a - a') (b a - b a')‖ =
      ‖collisionResidual (a - a') (b a - b a')‖ / τ := by ring
  rw [he, div_le_div_iff_of_pos_right hτ]

/-- The genuine inverse-secant weight acquires exactly a factor `τ`,
including its infinite value at a zero secant. -/
theorem inverse_secant_weight_rescale (α : E3) (τ : ℝ) (hτ : 0 < τ) :
    (ENNReal.ofReal ‖τ⁻¹ • α‖)⁻¹ = ENNReal.ofReal τ * (ENNReal.ofReal ‖α‖)⁻¹ := by
  have ht0 : ENNReal.ofReal τ ≠ 0 := by simp [hτ.not_ge]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ),
    ENNReal.ofReal_mul (inv_pos.mpr hτ).le, ENNReal.ofReal_inv_of_pos hτ,
    ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top)
      (Or.inl (ENNReal.inv_ne_top.mpr ht0)), inv_inv]

/-- The literal normalized residual-content density equals `τ` times the
original physical density, with the same old root and time window. -/
theorem normalized_residualContentWeight (b : E3 → E3) (a₀ a a' : E3)
    (τ ρ : ℝ) (hτ : 0 < τ) (J : Set ℝ) :
    residualContentWeight J (normalizedSlope a₀ τ a - normalizedSlope a₀ τ a')
      (normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a) -
        normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a')) (ρ / τ) =
      ENNReal.ofReal τ * residualContentWeight J (a - a') (b a - b a') ρ := by
  classical
  have hsec := (normalized_secants b a₀ a a' τ hτ.ne').1
  have hne : (normalizedSlope a₀ τ a - normalizedSlope a₀ τ a' ≠ 0) ↔ a - a' ≠ 0 := by
    rw [hsec, smul_ne_zero_iff]
    simp [hτ.ne']
  have hcut := normalized_residual_time_iff b a₀ a a' τ ρ hτ J
  simp only [residualContentWeight, hne, hcut]
  split_ifs
  · rw [hsec, inverse_secant_weight_rescale _ τ hτ]
  · simp

/-- The density identity integrates against the actual physical edge measure,
including arbitrary restrictions from selected source cells. -/
theorem weightedResidualContent_rescale (μ : Measure (E3 × E3))
    (b : E3 → E3) (a₀ : E3) (τ ρ : ℝ) (hτ : 0 < τ) (J : Set ℝ) :
    weightedResidualContent μ
      (fun p => normalizedSlope a₀ τ p.1 - normalizedSlope a₀ τ p.2)
      (fun p => normalizedIntercept b a₀ τ (normalizedSlope a₀ τ p.1) -
        normalizedIntercept b a₀ τ (normalizedSlope a₀ τ p.2)) J (ρ / τ) =
      ENNReal.ofReal τ * weightedResidualContent μ (fun p => p.1 - p.2)
        (fun p => b p.1 - b p.2) J ρ := by
  simp only [weightedResidualContent, normalized_residualContentWeight b a₀ _ _ τ ρ hτ J]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The fixed spacetime affine map associated with one root and one scale.
The time coordinate is unchanged and the spatial coordinate is sheared and dilated. -/
def frontAffineMap (a₀ b₀ : E3) (τ : ℝ) : (E3 × ℝ) →ᵃ[ℝ] (E3 × ℝ) where
  toFun p := (τ⁻¹ • (p.1 - b₀ - p.2 • a₀), p.2)
  linear :=
    { toFun := fun p => (τ⁻¹ • (p.1 - p.2 • a₀), p.2)
      map_add' := by
        intro p q
        apply Prod.ext
        · change τ⁻¹ • ((p.1 + q.1) - (p.2 + q.2) • a₀) =
            τ⁻¹ • (p.1 - p.2 • a₀) + τ⁻¹ • (q.1 - q.2 • a₀)
          module
        · rfl
      map_smul' := by
        intro c p
        apply Prod.ext
        · change τ⁻¹ • (c • p.1 - (c * p.2) • a₀) = c • (τ⁻¹ • (p.1 - p.2 • a₀))
          module
        · rfl }
  map_vadd' := by
    intro p v
    apply Prod.ext
    · change τ⁻¹ • ((v.1 + p.1) - b₀ - (v.2 + p.2) • a₀) =
        τ⁻¹ • (v.1 - v.2 • a₀) + τ⁻¹ • (p.1 - b₀ - p.2 • a₀)
      module
    · rfl

/-- The explicit inverse uses exactly the same root and scale. -/
def frontUnscale (a₀ b₀ : E3) (τ : ℝ) (p : E3 × ℝ) : E3 × ℝ :=
  (τ • p.1 + b₀ + p.2 • a₀, p.2)

theorem frontUnscale_leftInverse (a₀ b₀ : E3) (τ : ℝ) (hτ : τ ≠ 0) :
    Function.LeftInverse (frontUnscale a₀ b₀ τ) (frontAffineMap a₀ b₀ τ) := by
  intro p
  apply Prod.ext
  · change τ • (τ⁻¹ • (p.1 - b₀ - p.2 • a₀)) + b₀ + p.2 • a₀ = p.1
    simp only [smul_smul, mul_inv_cancel₀ hτ, one_smul]
    abel
  · rfl

theorem frontUnscale_rightInverse (a₀ b₀ : E3) (τ : ℝ) (hτ : τ ≠ 0) :
    Function.RightInverse (frontUnscale a₀ b₀ τ) (frontAffineMap a₀ b₀ τ) := by
  intro p
  apply Prod.ext
  · change τ⁻¹ • (τ • p.1 + b₀ + p.2 • a₀ - b₀ - p.2 • a₀) = p.1
    have he : τ • p.1 + b₀ + p.2 • a₀ - b₀ - p.2 • a₀ = τ • p.1 := by abel
    rw [he, smul_smul, inv_mul_cancel₀ hτ, one_smul]
  · rfl

/-- A genuine fixed affine equivalence, not a time-dependent change of maps. -/
def frontAffineEquiv (a₀ b₀ : E3) (τ : ℝ) (hτ : τ ≠ 0) : (E3 × ℝ) ≃ᵃ[ℝ] (E3 × ℝ) :=
  AffineEquiv.ofBijective ⟨(frontUnscale_leftInverse a₀ b₀ τ hτ).injective,
    (frontUnscale_rightInverse a₀ b₀ τ hτ).surjective⟩

/-- The repository's actual four-dimensional points have canonical linear
spatial-height coordinates. -/
def heightCoordinates : E4 ≃ₗ[ℝ] (E3 × ℝ) where
  toFun p := (horizontalProjection p, p (Fin.last 3))
  invFun p := ActualSlopeSource.heightPoint p.1 p.2
  left_inv := by
    intro p
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ActualSlopeSource.heightPoint_last _ _
    · exact ActualSlopeSource.heightPoint_castSucc _ _ j
  right_inv := by
    intro p
    exact Prod.ext (ActualSlopeSource.horizontalProjection_heightPoint p.1 p.2)
      (ActualSlopeSource.heightPoint_last p.1 p.2)
  map_add' := by
    intro p q
    exact Prod.ext (horizontalProjection_add p q) rfl
  map_smul' := by
    intro c p
    exact Prod.ext (horizontalProjection_smul c p) rfl

/-- The same fixed invertible affine map on the literal original `E4`. -/
def frontAffineEquiv4 (a₀ b₀ : E3) (τ : ℝ) (hτ : τ ≠ 0) : E4 ≃ᵃ[ℝ] E4 :=
  (heightCoordinates.toAffineEquiv.trans (frontAffineEquiv a₀ b₀ τ hτ)).trans
    heightCoordinates.symm.toAffineEquiv

/-- Exact front-map identity for the original physical endpoint at every
height. No source support or limiting front is substituted. -/
theorem normalized_frontPoint (b : E3 → E3) (a₀ a : E3) (τ s : ℝ) (hτ : τ ≠ 0) :
    ActualSlopeSource.heightPoint
      (normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a) + s • normalizedSlope a₀ τ a) s =
      frontAffineEquiv4 a₀ (b a₀) τ hτ (ActualSlopeSource.heightPoint (b a + s • a) s) := by
  change ActualSlopeSource.heightPoint
      (normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a) + s • normalizedSlope a₀ τ a) s =
    ActualSlopeSource.heightPoint
      (τ⁻¹ • (horizontalProjection (ActualSlopeSource.heightPoint (b a + s • a) s) - b a₀ -
        ActualSlopeSource.heightPoint (b a + s • a) s (Fin.last 3) • a₀))
      (ActualSlopeSource.heightPoint (b a + s • a) s (Fin.last 3))
  rw [ActualSlopeSource.horizontalProjection_heightPoint, ActualSlopeSource.heightPoint_last]
  congr 1
  rw [normalizedIntercept, physicalSlope_normalizedSlope a₀ a τ hτ]
  simp only [normalizedSlope]
  module

/-- The spatial part of the front identity in explicit physical coordinates. -/
theorem normalized_front_spatial (b : E3 → E3) (a₀ a : E3) (τ s : ℝ) (hτ : τ ≠ 0) :
    normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a) + s • normalizedSlope a₀ τ a =
      τ⁻¹ • (b a + s • a - b a₀ - s • a₀) := by
  rw [normalizedIntercept, physicalSlope_normalizedSlope a₀ a τ hτ]
  simp only [normalizedSlope]
  module

theorem measurable_normalizedSlope (a₀ : E3) (τ : ℝ) : Measurable (normalizedSlope a₀ τ) := by
  unfold normalizedSlope
  fun_prop

theorem measurable_normalizedIntercept (b : E3 → E3) (hb : Measurable b) (a₀ : E3) (τ : ℝ) :
    Measurable (normalizedIntercept b a₀ τ) := by
  unfold normalizedIntercept physicalSlope
  fun_prop

set_option maxHeartbeats 400000 in
/-- Pushforward to the actual normalized endpoint coordinates carries the
literal residual content with the exact inverse-secant factor. -/
theorem weightedResidualContent_map_normalized (μ : Measure (E3 × E3))
    (b : E3 → E3) (hb : Measurable b) (a₀ : E3) (τ ρ : ℝ) (hτ : 0 < τ)
    (J : Set ℝ) (hJ : MeasurableSet J) :
    weightedResidualContent
      (μ.map (fun p => (normalizedSlope a₀ τ p.1, normalizedSlope a₀ τ p.2)))
      (fun p => p.1 - p.2)
      (fun p => normalizedIntercept b a₀ τ p.1 - normalizedIntercept b a₀ τ p.2) J (ρ / τ) =
      ENNReal.ofReal τ * weightedResidualContent μ (fun p => p.1 - p.2)
        (fun p => b p.1 - b p.2) J ρ := by
  have hn := measurable_normalizedIntercept b hb a₀ τ
  have hp : Measurable (fun p : E3 × E3 => (normalizedSlope a₀ τ p.1, normalizedSlope a₀ τ p.2)) :=
    ((measurable_normalizedSlope a₀ τ).comp measurable_fst).prodMk
      ((measurable_normalizedSlope a₀ τ).comp measurable_snd)
  have hw : Measurable (fun p : E3 × E3 => residualContentWeight J (p.1 - p.2)
      (normalizedIntercept b a₀ τ p.1 - normalizedIntercept b a₀ τ p.2) (ρ / τ)) :=
    measurable_residualContentWeight (X := E3 × E3) (fun p : E3 × E3 => p.1 - p.2)
      (fun p : E3 × E3 => normalizedIntercept b a₀ τ p.1 - normalizedIntercept b a₀ τ p.2)
      (measurable_fst.sub measurable_snd)
      ((hn.comp measurable_fst).sub (hn.comp measurable_snd)) J hJ (ρ / τ)
  exact (lintegral_map (μ := μ) hw hp).trans (weightedResidualContent_rescale μ b a₀ τ ρ hτ J)

/-- Three-dimensional Lebesgue measure transforms with the exact cubic
Jacobian under the selected common slope normalization. -/
theorem map_volume_normalizedSlope (a₀ : E3) (τ : ℝ) (hτ : 0 < τ) :
    (volume : Measure E3).map (normalizedSlope a₀ τ) = ENNReal.ofReal (τ ^ 3) • volume := by
  have htrans : (volume : Measure E3).map (fun a => a - a₀) = volume := by
    simpa only [sub_eq_add_neg] using map_add_right_eq_self (volume : Measure E3) (-a₀)
  change (volume : Measure E3).map ((fun a : E3 => τ⁻¹ • a) ∘ (fun a => a - a₀)) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), htrans,
    Measure.map_addHaar_smul volume (inv_ne_zero hτ.ne')]
  simp only [finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_nonneg (pow_nonneg hτ.le 3)]

/-- The actual block source is transported and divided by its actual total
mass. No separate normalized-density assumption is introduced. -/
def normalizedSource (σ : Measure E3) (a₀ : E3) (τ : ℝ) : Measure E3 :=
  (σ univ)⁻¹ • σ.map (normalizedSlope a₀ τ)

/-- A finite positive block becomes a probability under the actual transport. -/
theorem normalizedSource_isProbability (σ : Measure E3) [IsFiniteMeasure σ]
    (hσpos : 0 < σ univ) (a₀ : E3) (τ : ℝ) :
    IsProbabilityMeasure (normalizedSource σ a₀ τ) := by
  constructor
  rw [normalizedSource, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_normalizedSlope a₀ τ) MeasurableSet.univ, Set.preimage_univ,
    ENNReal.inv_mul_cancel hσpos.ne' (measure_ne_top σ univ)]

/-- The normalized density bound with its exact extended-nonnegative mass. -/
theorem normalizedSource_le_volume (σ : Measure E3) (hσ : σ ≤ volume)
    (a₀ : E3) (τ : ℝ) (hτ : 0 < τ) :
    normalizedSource σ a₀ τ ≤ ((σ univ)⁻¹ * ENNReal.ofReal (τ ^ 3)) • volume := by
  intro S
  have hmap := Measure.map_mono hσ (measurable_normalizedSlope a₀ τ)
  calc
    normalizedSource σ a₀ τ S ≤
        (σ univ)⁻¹ * ((volume : Measure E3).map (normalizedSlope a₀ τ)) S :=
      mul_le_mul_right (hmap S) (σ univ)⁻¹
    _ = _ := by
      rw [map_volume_normalizedSlope a₀ τ hτ]
      simp only [Measure.smul_apply, smul_eq_mul]
      ring

/-- The positive real block mass used by localization is exactly the mass
in the transport definition. -/
theorem normalizedSource_eq_real_mass (σ : Measure E3) [IsFiniteMeasure σ]
    (a₀ : E3) (τ : ℝ) :
    normalizedSource σ a₀ τ = (ENNReal.ofReal (σ univ).toReal)⁻¹ • σ.map (normalizedSlope a₀ τ) := by
  rw [ENNReal.ofReal_toReal (measure_ne_top σ univ)]
  rfl

/-- Explicit `τ³/m` density for the actual positive finite block source,
where `m` is its actual total mass, not a free normalization certificate. -/
theorem normalizedSource_le_real_density (σ : Measure E3) [IsFiniteMeasure σ]
    (hσpos : 0 < σ univ) (hσ : σ ≤ volume) (a₀ : E3) (τ : ℝ) (hτ : 0 < τ) :
    normalizedSource σ a₀ τ ≤ ENNReal.ofReal (τ ^ 3 / (σ univ).toReal) • volume := by
  have hm : 0 < (σ univ).toReal := ENNReal.toReal_pos hσpos.ne' (measure_ne_top σ univ)
  rw [ENNReal.ofReal_div_of_pos hm, ENNReal.ofReal_toReal (measure_ne_top σ univ), div_eq_mul_inv,
    mul_comm]
  exact normalizedSource_le_volume σ hσ a₀ τ hτ

/-- Exact support transport for each selected fixed normalization: the
normalized front point belongs to the affine image precisely when its
original physical point belongs to the original set. -/
theorem normalized_frontPoint_mem_image_iff (b : E3 → E3) (a₀ a : E3)
    (τ s : ℝ) (hτ : τ ≠ 0) (S : Set E4) :
    ActualSlopeSource.heightPoint
      (normalizedIntercept b a₀ τ (normalizedSlope a₀ τ a) + s • normalizedSlope a₀ τ a) s ∈
        frontAffineEquiv4 a₀ (b a₀) τ hτ '' S ↔
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ S := by
  rw [normalized_frontPoint b a₀ a τ s hτ]
  constructor
  · rintro ⟨p, hp, he⟩
    exact (frontAffineEquiv4 a₀ (b a₀) τ hτ).injective he ▸ hp
  · intro hp
    exact ⟨_, hp, rfl⟩

/-- The selected actual directed graph is transported without symmetrizing
its endpoints and normalized by the square of the actual block mass. -/
def normalizedDirectedGraph (μ : Measure E3) (Γ : Measure (E3 × E3))
    (a₀ : E3) (τ : ℝ) : Measure (E3 × E3) :=
  ((μ univ)⁻¹) ^ 2 • Γ.map (Prod.map (normalizedSlope a₀ τ) (normalizedSlope a₀ τ))

/-- The product of the actual normalized source has the same squared-mass
transport formula as the directed graph. -/
theorem normalizedSource_prod (μ : Measure E3) [SFinite μ] (a₀ : E3) (τ : ℝ) :
    (normalizedSource μ a₀ τ).prod (normalizedSource μ a₀ τ) =
      ((μ univ)⁻¹) ^ 2 • (μ.prod μ).map (Prod.map (normalizedSlope a₀ τ) (normalizedSlope a₀ τ)) := by
  rw [normalizedSource, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ← pow_two, Measure.map_prod_map μ μ (measurable_normalizedSlope a₀ τ)
      (measurable_normalizedSlope a₀ τ)]

/-- Actual graph domination survives the directed pair transport exactly. -/
theorem normalizedDirectedGraph_le_product (μ : Measure E3) [SFinite μ]
    (Γ : Measure (E3 × E3)) (hΓ : Γ ≤ μ.prod μ) (a₀ : E3) (τ : ℝ) :
    normalizedDirectedGraph μ Γ a₀ τ ≤
      (normalizedSource μ a₀ τ).prod (normalizedSource μ a₀ τ) := by
  rw [normalizedSource_prod μ a₀ τ]
  intro S
  exact mul_le_mul_right
    ((Measure.map_mono hΓ ((measurable_normalizedSlope a₀ τ).prodMap
      (measurable_normalizedSlope a₀ τ))) S) _

/-- Exact total mass of the normalized actual directed graph. -/
theorem normalizedDirectedGraph_mass (μ : Measure E3) (Γ : Measure (E3 × E3))
    (a₀ : E3) (τ : ℝ) :
    normalizedDirectedGraph μ Γ a₀ τ univ = ((μ univ)⁻¹) ^ 2 * Γ univ := by
  rw [normalizedDirectedGraph, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply ((measurable_normalizedSlope a₀ τ).prodMap
      (measurable_normalizedSlope a₀ τ)) MeasurableSet.univ, Set.preimage_univ]

/-- The real density gain is the actual edge mass divided by squared actual
block mass. No replacement graph or independent-source certificate appears. -/
theorem normalizedDirectedGraph_real_mass (μ : Measure E3) (Γ : Measure (E3 × E3))
    (a₀ : E3) (τ : ℝ) :
    (normalizedDirectedGraph μ Γ a₀ τ univ).toReal =
      (Γ univ).toReal / (μ univ).toReal ^ 2 := by
  rw [normalizedDirectedGraph_mass, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
  ring

/-- A dominated actual graph has normalized total mass at most one. -/
theorem normalizedDirectedGraph_mass_le_one (μ : Measure E3) [IsFiniteMeasure μ]
    (hμ : 0 < μ univ) (Γ : Measure (E3 × E3)) (hΓ : Γ ≤ μ.prod μ)
    (a₀ : E3) (τ : ℝ) : normalizedDirectedGraph μ Γ a₀ τ univ ≤ 1 := by
  have := normalizedSource_isProbability μ hμ a₀ τ
  exact (normalizedDirectedGraph_le_product μ Γ hΓ a₀ τ univ).trans (by simp)

end StickyKakeya4.ResidualAffineRescaling
