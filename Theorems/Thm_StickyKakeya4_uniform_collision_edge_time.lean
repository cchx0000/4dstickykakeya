import Theorems.Thm_StickyKakeya4_collision_edge_contact_residual

open MeasureTheory Set

noncomputable section

namespace StickyKakeya4

/-- A quantitative chart lower bound controls the reciprocal amplification. -/
theorem abs_inv_le_inv_of_pos_le_abs {x kappa : ℝ}
    (hkappa : 0 < kappa) (hx : kappa ≤ |x|) :
    |x⁻¹| ≤ kappa⁻¹ := by
  rw [abs_inv]
  exact (inv_le_inv₀ (hkappa.trans_le hx) hkappa).2 hx

/-- In one uniformly nonvertical graph chart, every physical collision edge
has a contact residual with a bound independent of the individual lines. -/
theorem sourceCollisionSupport_has_uniform_contact_residual_control
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hchart : ∀ i, kappa ≤ |direction (R.line i) (3 : Fin 4)|)
    {i j : Fin n} (hedge : (i, j) ∈ sourceCollisionSupport R)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ s : ℝ,
      markedPairContactResidualNorm (R.line i, R.line j) s <
          (2 * kappa⁻¹ + 2) * (R.thickness + eta) ∧
      markedPairContactResidualNorm (R.line j, R.line i) s <
          (2 * kappa⁻¹ + 2) * (R.thickness + eta) := by
  have hiAbs : 0 < |direction (R.line i) (3 : Fin 4)| :=
    hkappa.trans_le (hchart i)
  have hjAbs : 0 < |direction (R.line j) (3 : Fin 4)| :=
    hkappa.trans_le (hchart j)
  have hiChart : direction (R.line i) (3 : Fin 4) ≠ 0 :=
    (abs_pos.mp hiAbs)
  have hjChart : direction (R.line j) (3 : Fin 4) ≠ 0 :=
    (abs_pos.mp hjAbs)
  obtain ⟨s, hforward, hreverse⟩ :=
    sourceCollisionSupport_has_contact_residual_control
      hD hR hedge hiChart hjChart heta
  have hiInv : |(direction (R.line i) (3 : Fin 4))⁻¹| ≤ kappa⁻¹ :=
    abs_inv_le_inv_of_pos_le_abs hkappa (hchart i)
  have hjInv : |(direction (R.line j) (3 : Fin 4))⁻¹| ≤ kappa⁻¹ :=
    abs_inv_le_inv_of_pos_le_abs hkappa (hchart j)
  have hcoeff :
      |(direction (R.line i) (3 : Fin 4))⁻¹| +
          |(direction (R.line j) (3 : Fin 4))⁻¹| + 2 ≤
        2 * kappa⁻¹ + 2 := by
    linarith
  have hscale : 0 ≤ R.thickness + eta := by
    have hthickness : 0 < R.thickness := by
      rw [hR.1]
      exact hD.1
    positivity
  refine ⟨s, hforward.trans_le ?_, hreverse.trans_le ?_⟩ <;>
    exact mul_le_mul_of_nonneg_right hcoeff hscale

/-- Canonical graph height chosen for every source edge.  Off the collision
support it is set to zero, so this is a total function on index pairs. -/
noncomputable def uniformSourceCollisionTime
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hchart : ∀ i, kappa ≤ |direction (R.line i) (3 : Fin 4)|)
    (eta : ℝ) (heta : 0 < eta) (i j : Fin n) : ℝ :=
  if hedge : (i, j) ∈ sourceCollisionSupport R then
    Classical.choose
      (sourceCollisionSupport_has_uniform_contact_residual_control
        hD hR hkappa hchart hedge heta)
  else 0

/-- The chosen collision height satisfies the uniform bidirectional contact
residual estimate on every support edge. -/
theorem uniformSourceCollisionTime_spec
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hchart : ∀ i, kappa ≤ |direction (R.line i) (3 : Fin 4)|)
    (eta : ℝ) (heta : 0 < eta) {i j : Fin n}
    (hedge : (i, j) ∈ sourceCollisionSupport R) :
    markedPairContactResidualNorm (R.line i, R.line j)
          (uniformSourceCollisionTime hD hR kappa hkappa hchart eta heta i j) <
        (2 * kappa⁻¹ + 2) * (R.thickness + eta) ∧
    markedPairContactResidualNorm (R.line j, R.line i)
          (uniformSourceCollisionTime hD hR kappa hkappa hchart eta heta i j) <
        (2 * kappa⁻¹ + 2) * (R.thickness + eta) := by
  rw [uniformSourceCollisionTime, dif_pos hedge]
  exact Classical.choose_spec
    (sourceCollisionSupport_has_uniform_contact_residual_control
      hD hR hkappa hchart hedge heta)

end StickyKakeya4
