import Theorems.Thm_StickyKakeya4_two_walk_box_comparison
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 300000

noncomputable section

open MeasureTheory MeasureTheory.Measure Metric
open scoped ENNReal
namespace AdaptedBoxVolume
open TwoWalkBoxComparison

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual residual coordinates, with height first to expose the triangular shear. -/
def residualCoordinates (F : U →L[ℝ] V) (w : Walk U V) (z : ℝ)
    (p : SpaceTime U V) : ℝ × U × V :=
  (p.2.2 - z, tangentResidual w z p, normalResidual F w z p)

/-- Standard product of closed balls in the norms used by the literal adapted box. -/
def residualBox (ρ σ L : ℝ) : Set (ℝ × U × V) :=
  Metric.closedBall 0 L ×ˢ (Metric.closedBall 0 (L * ρ) ×ˢ Metric.closedBall 0 (L * σ))

lemma box_eq_preimage (F : U →L[ℝ] V) (w : Walk U V) (z ρ σ L : ℝ) :
    box F w z ρ σ L = residualCoordinates F w z ⁻¹' (residualBox ρ σ L) := by
  ext p
  simp [box, residualBox, residualCoordinates, Metric.mem_closedBall, dist_zero_right,
    Real.norm_eq_abs]

section Measure
variable [MeasureSpace U] [BorelSpace U] [SecondCountableTopology U]
  [MeasureSpace V] [BorelSpace V] [SecondCountableTopology V]
  [SFinite (volume : Measure U)] [SFinite (volume : Measure V)]
  [IsAddRightInvariant (volume : Measure U)] [IsAddRightInvariant (volume : Measure V)]

/-- Every triangular residual shear has unit volume factor. This proves measure
preservation directly from translation invariance, without assuming a determinant certificate. -/
theorem residualCoordinates_measurePreserving (F : U →L[ℝ] V) (w : Walk U V) (z : ℝ) :
    MeasurePreserving (residualCoordinates F w z) := by
  have hcycle : MeasurePreserving (fun p : SpaceTime U V => (p.2.2, p.1, p.2.1)) := by
    exact measurePreserving_swap.comp
      (volume_preserving_prodAssoc.symm MeasurableEquiv.prodAssoc)
  have ht : MeasurePreserving (fun p : ℝ × U × V => (p.1 - z, p.2)) :=
    (measurePreserving_sub_right volume z).prod (MeasurePreserving.id volume)
  have hs : MeasurePreserving (fun p : ℝ × U × V =>
      (p.1, p.2 - (w.terminalX + p.1 • w.terminalU,
        w.terminalY + p.1 • w.terminalV))) := by
    refine (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (μc := volume) (μd := volume)
      (g := fun t (p : U × V) => p - (w.terminalX + t • w.terminalU,
        w.terminalY + t • w.terminalV)) ?_ ?_
    · exact (by fun_prop : Continuous (fun p : ℝ × U × V =>
        p.2 - (w.terminalX + p.1 • w.terminalU,
          w.terminalY + p.1 • w.terminalV))).measurable
    · apply Filter.Eventually.of_forall
      intro t
      change map (fun p : U × V => p - _) ((volume : Measure U).prod volume) = _
      exact map_sub_right_eq_self _ _
  have hn : MeasurePreserving (fun p : U × V => (p.1, p.2 - F p.1)) := by
    refine (MeasurePreserving.id (volume : Measure U)).skew_product
      (μc := volume) (μd := volume) (g := fun x (y : V) => y - F x) ?_ ?_
    · exact (by fun_prop : Continuous (fun p : U × V => p.2 - F p.1)).measurable
    · exact Filter.Eventually.of_forall (fun x => map_sub_right_eq_self volume _)
  have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod hn).comp
    (hs.comp (ht.comp hcycle))
  unfold residualCoordinates tangentResidual normalResidual
  simpa only [tangentResidual, sub_sub,
    Function.comp_def, Prod.map_apply, Prod.fst_sub, Prod.snd_sub, volume_eq_prod, id_eq] using h

/-- Exact volume of the literal adapted box in arbitrary product normed spaces. -/
theorem volume_box_product (F : U →L[ℝ] V) (w : Walk U V) (z ρ σ L : ℝ) :
    volume (box F w z ρ σ L) = volume (Metric.closedBall (0 : ℝ) L) *
      (volume (Metric.closedBall (0 : U) (L * ρ)) *
        volume (Metric.closedBall (0 : V) (L * σ))) := by
  rw [box_eq_preimage, residualBox]
  rw [(residualCoordinates_measurePreserving F w z).measure_preimage
    ((isClosed_closedBall.measurableSet.prod
      (isClosed_closedBall.measurableSet.prod isClosed_closedBall.measurableSet)).nullMeasurableSet)]
  simp only [volume_eq_prod, Measure.prod_prod]

end Measure

/-- Linear part of the residual coordinate transformation. -/
def residualLinear (F : U →L[ℝ] V) (w : Walk U V) : SpaceTime U V →ₗ[ℝ] ℝ × U × V where
  toFun p := (p.2.2, p.1 - p.2.2 • w.terminalU,
    p.2.1 - p.2.2 • w.terminalV - F (p.1 - p.2.2 • w.terminalU))
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, map_sub, map_smul]
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> module
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, map_sub, RingHom.id_apply]
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd] <;> module

/-- The residual transformation is affine, including the actual box center. -/
def residualAffine (F : U →L[ℝ] V) (w : Walk U V) (z : ℝ) :
    SpaceTime U V →ᵃ[ℝ] ℝ × U × V where
  toFun := residualCoordinates F w z
  linear := residualLinear F w
  map_vadd' p v := by
    simp only [residualCoordinates, residualLinear, tangentResidual, normalResidual,
      vadd_eq_add, Prod.fst_add, Prod.snd_add, LinearMap.coe_mk, AddHom.coe_mk,
      map_add, map_sub, map_smul]
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> module

/-- Convexity is proved for the literal residual-inequality box and every scale. -/
theorem convex_box (F : U →L[ℝ] V) (w : Walk U V) (z ρ σ L : ℝ) :
    Convex ℝ (box F w z ρ σ L) := by
  rw [box_eq_preimage]
  exact ((convex_closedBall (0 : ℝ) L).prod
    ((convex_closedBall (0 : U) (L * ρ)).prod
      (convex_closedBall (0 : V) (L * σ)))).affine_preimage (residualAffine F w z)

lemma volume_closedBall_real_pair (r : ℝ) :
    volume (Metric.closedBall (0 : ℝ × ℝ) r) = ENNReal.ofReal (2 * r) ^ 2 := by
  rw [show (0 : ℝ × ℝ) = (0, 0) by rfl, ← closedBall_prod_same,
    volume_eq_prod, Measure.prod_prod, Real.volume_closedBall, pow_two]

local instance : IsAddRightInvariant (volume : Measure (ℝ × ℝ)) := by
  change IsAddRightInvariant ((volume : Measure ℝ).prod volume)
  infer_instance

/-- Native a=1 geometry: the two normal coordinates use the literal product sup norm. -/
theorem volume_box_a1 (F : ℝ →L[ℝ] ℝ × ℝ) (w : Walk ℝ (ℝ × ℝ))
    (z ρ σ L : ℝ) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hL : 0 ≤ L) :
    volume (box F w z ρ σ L) = ENNReal.ofReal ((2 * L) ^ 4 * ρ * σ ^ 2) := by
  rw [volume_box_product, Real.volume_closedBall, Real.volume_closedBall,
    volume_closedBall_real_pair]
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- Native a=2 geometry: the two tangential coordinates use the literal product sup norm. -/
theorem volume_box_a2 (F : (ℝ × ℝ) →L[ℝ] ℝ) (w : Walk (ℝ × ℝ) ℝ)
    (z ρ σ L : ℝ) (hρ : 0 ≤ ρ) (_hσ : 0 ≤ σ) (hL : 0 ≤ L) :
    volume (box F w z ρ σ L) = ENNReal.ofReal ((2 * L) ^ 4 * ρ ^ 2 * σ) := by
  rw [volume_box_product, Real.volume_closedBall, volume_closedBall_real_pair,
    Real.volume_closedBall]
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- With positive geometric scales, the a=1 box has strictly positive finite volume. -/
theorem volume_box_a1_pos_finite (F : ℝ →L[ℝ] ℝ × ℝ) (w : Walk ℝ (ℝ × ℝ))
    (z ρ σ L : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) (hL : 0 < L) :
    0 < volume (box F w z ρ σ L) ∧ volume (box F w z ρ σ L) < ⊤ := by
  rw [volume_box_a1 F w z ρ σ L hρ.le hσ.le hL.le]
  exact ⟨ENNReal.ofReal_pos.mpr (by positivity), ENNReal.ofReal_lt_top⟩

/-- With positive geometric scales, the a=2 box has strictly positive finite volume. -/
theorem volume_box_a2_pos_finite (F : (ℝ × ℝ) →L[ℝ] ℝ) (w : Walk (ℝ × ℝ) ℝ)
    (z ρ σ L : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) (hL : 0 < L) :
    0 < volume (box F w z ρ σ L) ∧ volume (box F w z ρ σ L) < ⊤ := by
  rw [volume_box_a2 F w z ρ σ L hρ.le hσ.le hL.le]
  exact ⟨ENNReal.ofReal_pos.mpr (by positivity), ENNReal.ofReal_lt_top⟩

end AdaptedBoxVolume
