import Theorems.Thm_StickyKakeya4_uniform_collision_edge_time

open MeasureTheory Set

noncomputable section

namespace StickyKakeya4

/-- The injective passage from source-index pairs to pairs of actual marked
lines.  No multiplicity is introduced or forgotten. -/
def sourceLinePair {n : ℕ} (R : FiniteScaleSource n) :
    Fin n × Fin n → MarkedLine × MarkedLine :=
  fun p => (R.line p.1, R.line p.2)

theorem sourceLinePair_injective {n : ℕ} (R : FiniteScaleSource n) :
    Function.Injective (sourceLinePair R) := by
  intro p q hpq
  apply Prod.ext
  · apply R.line_injective
    exact congrArg Prod.fst hpq
  · apply R.line_injective
    exact congrArg Prod.snd hpq

/-- Collision support expressed in the marked-line type required by the DRC
interface. -/
def sourceMarkedCollisionSupport {n : ℕ} (R : FiniteScaleSource n) :
    Finset (MarkedLine × MarkedLine) := by
  classical
  exact (sourceCollisionSupport R).image (sourceLinePair R)

theorem mem_sourceMarkedCollisionSupport_iff {n : ℕ}
    (R : FiniteScaleSource n) (p : MarkedLine × MarkedLine) :
    p ∈ sourceMarkedCollisionSupport R ↔
      ∃ i j, (i, j) ∈ sourceCollisionSupport R ∧
        p = (R.line i, R.line j) := by
  classical
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨q.1, q.2, hq, rfl⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact Finset.mem_image.mpr ⟨(i, j), hij, rfl⟩

theorem card_sourceMarkedCollisionSupport {n : ℕ}
    (R : FiniteScaleSource n) :
    (sourceMarkedCollisionSupport R).card =
      (sourceCollisionSupport R).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro p hp q hq hpq
  exact sourceLinePair_injective R hpq

theorem sourceMarkedCollisionSupport_lines_ne {n : ℕ}
    {R : FiniteScaleSource n} {p : MarkedLine × MarkedLine}
    (hp : p ∈ sourceMarkedCollisionSupport R) :
    p.1 ≠ p.2 := by
  obtain ⟨i, j, hij, rfl⟩ :=
    (mem_sourceMarkedCollisionSupport_iff R p).mp hp
  exact sourceCollisionSupport_lines_ne R hij

/-- The index-level uniform residual witness descends to every actual marked
pair in the image support. -/
theorem sourceMarkedCollisionSupport_has_uniform_contact_residual_control
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hchart : ∀ i, kappa ≤ |direction (R.line i) (3 : Fin 4)|)
    (eta : ℝ) (heta : 0 < eta) {p : MarkedLine × MarkedLine}
    (hp : p ∈ sourceMarkedCollisionSupport R) :
    ∃ s : ℝ,
      markedPairContactResidualNorm p s <
          (2 * kappa⁻¹ + 2) * (R.thickness + eta) ∧
      markedPairContactResidualNorm (p.2, p.1) s <
          (2 * kappa⁻¹ + 2) * (R.thickness + eta) := by
  obtain ⟨i, j, hij, rfl⟩ :=
    (mem_sourceMarkedCollisionSupport_iff R p).mp hp
  exact sourceCollisionSupport_has_uniform_contact_residual_control
    hD hR hkappa hchart hij heta

/-- Choose the uniform collision height on the finite marked support and set
it to zero off the support.  This remains total even for an empty source. -/
noncomputable def markedSourceCollisionTime
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hchart : ∀ i, kappa ≤ |direction (R.line i) (3 : Fin 4)|)
    (eta : ℝ) (heta : 0 < eta) :
    MarkedLine × MarkedLine → ℝ := by
  classical
  exact fun p => if hp : p ∈ sourceMarkedCollisionSupport R then
      Classical.choose
        (sourceMarkedCollisionSupport_has_uniform_contact_residual_control
          hD hR kappa hkappa hchart eta heta hp)
    else 0

/-- On the marked collision support, the transported edge time retains the
uniform bidirectional residual estimate. -/
theorem markedSourceCollisionTime_spec
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hchart : ∀ i, kappa ≤ |direction (R.line i) (3 : Fin 4)|)
    (eta : ℝ) (heta : 0 < eta) {p : MarkedLine × MarkedLine}
    (hp : p ∈ sourceMarkedCollisionSupport R) :
    markedPairContactResidualNorm p
          (markedSourceCollisionTime hD hR kappa hkappa hchart eta heta p) <
        (2 * kappa⁻¹ + 2) * (R.thickness + eta) ∧
    markedPairContactResidualNorm (p.2, p.1)
          (markedSourceCollisionTime hD hR kappa hkappa hchart eta heta p) <
        (2 * kappa⁻¹ + 2) * (R.thickness + eta) := by
  classical
  rw [markedSourceCollisionTime, dif_pos hp]
  exact Classical.choose_spec
    (sourceMarkedCollisionSupport_has_uniform_contact_residual_control
      hD hR kappa hkappa hchart eta heta hp)

end StickyKakeya4
