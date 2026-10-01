import Theorems.Thm_StickyKakeya4_contact_symplectic_edge_flow_certificate_existence

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- The complete output demanded from collision-faithful routing for one
finite retained source. -/
def HasCollisionFaithfulRoutingOutput
    {n : ℕ} (D R : FiniteScaleSource n) (ε : ℝ) (A : ENNReal) : Prop :=
  ∃ k : ℕ,
  ∃ incoming cross errorMass crossCapacity : Fin n → ENNReal,
  ∃ paidPiece paidCapacity : Fin k → Fin n → ENNReal,
  ∃ paidBudget : Fin k → ENNReal,
  ∃ crossBudget : ENNReal,
    (∀ i,
      incoming i = (∑ c, paidPiece c i) + cross i +
        Finset.univ.sum (fun j : Fin n =>
          if R.tree.parent j = some i then incoming j else 0) +
        errorMass i) ∧
    (∀ i, incoming i ≠ ⊤) ∧
    Finset.univ.sum errorMass + Finset.univ.sum errorMass ≤
      Finset.univ.sum (fun i : Fin n =>
        if R.tree.parent i = none then incoming i else 0) ∧
    (∀ c i,
      paidPiece c i ≤ paidCapacity c i * volume (sourceUnion R)) ∧
    (∀ i,
      cross i ≤ crossCapacity i * volume (sourceUnion R)) ∧
    (∀ c, ∑ i, paidCapacity c i ≤ paidBudget c) ∧
    (∑ i, crossCapacity i) ≤ crossBudget ∧
    (∑ c, paidBudget c) + crossBudget ≤
      A * (ENNReal.ofReal D.thickness).rpow (-ε) ∧
    IsCollisionFaithfulCategoryLedger R paidPiece cross errorMass

theorem hasCollisionFaithfulAbsoluteOccurrenceCategoryRouting_iff
    (selector : Set MarkedLine) :
    HasCollisionFaithfulAbsoluteOccurrenceCategoryRouting selector ↔
      ∀ ε : ℝ, 0 < ε →
      ∀ Cpack : ENNReal, Cpack ≠ 0 → Cpack ≠ ⊤ →
      ∃ A : ENNReal, A ≠ 0 ∧ A ≠ ⊤ ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (n : ℕ) (D R : FiniteScaleSource n),
        D.thickness ≤ δ₀ →
        ComesFromSelector D selector →
        IsAdmissibleStickySource D (ε / 10) Cpack →
        IsFractionalSourceRestriction R D →
        HasCollisionFaithfulRoutingOutput D R ε A := by
  rfl

/-- A genuine failure of uniform collision-faithful routing fixes one
positive exponent and one finite packing constant such that, no matter how
large a finite capacity coefficient is proposed and how small a validity
scale is requested, an admissible finite selector source has a retained
restriction with no routing output at all. -/
theorem collisionFaithfulRouting_failure_extracts_finite_counterexamples
    (selector : Set MarkedLine)
    (hfailure :
      ¬ HasCollisionFaithfulAbsoluteOccurrenceCategoryRouting selector) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ Cpack : ENNReal, Cpack ≠ 0 ∧ Cpack ≠ ⊤ ∧
      ∀ A : ENNReal, A ≠ 0 → A ≠ ⊤ →
      ∀ δ₀ : ℝ, 0 < δ₀ →
      ∃ (n : ℕ) (D R : FiniteScaleSource n),
        D.thickness ≤ δ₀ ∧
        ComesFromSelector D selector ∧
        IsAdmissibleStickySource D (ε / 10) Cpack ∧
        IsFractionalSourceRestriction R D ∧
        ¬ HasCollisionFaithfulRoutingOutput D R ε A := by
  rw [hasCollisionFaithfulAbsoluteOccurrenceCategoryRouting_iff] at hfailure
  push Not at hfailure
  exact hfailure

/-- The routing half of a coherent concentration boundary therefore supplies
the same persistent family of finite counterexample sources. -/
theorem coherentBoundary_extracts_collision_routing_counterexamples
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ Cpack : ENNReal, Cpack ≠ 0 ∧ Cpack ≠ ⊤ ∧
      ∀ A : ENNReal, A ≠ 0 → A ≠ ⊤ →
      ∀ δ₀ : ℝ, 0 < δ₀ →
      ∃ (n : ℕ) (D R : FiniteScaleSource n),
        D.thickness ≤ δ₀ ∧
        ComesFromSelector D selector ∧
        IsAdmissibleStickySource D (ε / 10) Cpack ∧
        IsFractionalSourceRestriction R D ∧
        ¬ HasCollisionFaithfulRoutingOutput D R ε A :=
  collisionFaithfulRouting_failure_extracts_finite_counterexamples
    selector hboundary.1

end StickyKakeya4
