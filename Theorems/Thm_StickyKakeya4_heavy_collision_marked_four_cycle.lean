import Theorems.Thm_StickyKakeya4_collision_heavy_edge_decomposition
import Theorems.Thm_StickyKakeya4_dense_relation_marked_four_cycle
import Theorems.Thm_StickyKakeya4_contact_symplectic_edge_flow_certificate_existence

open Set

noncomputable section

namespace StickyKakeya4

/-- The finite family of actual marked lines carried by a source. -/
def sourceLineFamily {n : ℕ} (R : FiniteScaleSource n) : Finset MarkedLine := by
  classical
  exact Finset.univ.image R.line

theorem mem_sourceLineFamily_iff {n : ℕ} (R : FiniteScaleSource n)
    (line : MarkedLine) :
    line ∈ sourceLineFamily R ↔ ∃ i, line = R.line i := by
  classical
  constructor
  · intro hline
    obtain ⟨i, hi, hiline⟩ := Finset.mem_image.mp hline
    exact ⟨i, hiline.symm⟩
  · rintro ⟨i, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem card_sourceLineFamily {n : ℕ} (R : FiniteScaleSource n) :
    (sourceLineFamily R).card = n := by
  classical
  calc
    (sourceLineFamily R).card = (Finset.univ : Finset (Fin n)).card := by
      apply Finset.card_image_iff.mpr
      intro i hi j hj hij
      exact R.line_injective hij
    _ = n := by simp

theorem sourceLineFamily_nonempty {n : ℕ} (R : FiniteScaleSource n)
    (hn : 0 < n) :
    (sourceLineFamily R).Nonempty := by
  let i : Fin n := ⟨0, hn⟩
  exact ⟨R.line i, (mem_sourceLineFamily_iff R _).2 ⟨i, rfl⟩⟩

theorem sourceMarkedHeavyCollisionSupport_subset_lineFamily_product
    {n : ℕ} (R : FiniteScaleSource n) (threshold : ENNReal) :
    sourceMarkedHeavyCollisionSupport R threshold ⊆
      sourceLineFamily R ×ˢ sourceLineFamily R := by
  classical
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_product.mpr
    ⟨(mem_sourceLineFamily_iff R _).2 ⟨q.1, rfl⟩,
      (mem_sourceLineFamily_iff R _).2 ⟨q.2, rfl⟩⟩

theorem sourceMarkedHeavyCollisionSupport_irrefl
    {n : ℕ} (R : FiniteScaleSource n) (threshold : ENNReal) :
    ∀ line, (line, line) ∉ sourceMarkedHeavyCollisionSupport R threshold := by
  intro line hline
  exact sourceMarkedHeavyCollisionSupport_lines_ne hline rfl

/-- A heavy collision relation satisfying the explicit DRC size conditions
already contains a genuine four-cycle of four actual marked selector lines.
No auxiliary left/right copy and no disjointness loss is used. -/
theorem sourceMarkedHeavyCollisionSupport_has_marked_four_cycle
    {n : ℕ} (R : FiniteScaleSource n)
    (selector : Set MarkedLine)
    (hselector : ∀ i, R.line i ∈ selector)
    (hn : 0 < n) (threshold : ENNReal)
    (c : ℝ) (hc_pos : 0 < c) (hc_le : c ≤ 1)
    (hdense : c * (n : ℝ) * (n : ℝ) ≤
      ((sourceMarkedHeavyCollisionSupport R threshold).card : ℝ))
    (hleftLarge : 4 ≤ c * (n : ℝ))
    (hrightLarge : 8 < c ^ 2 * (n : ℝ)) :
    ∃ line : Fin 4 → MarkedLine,
      Function.Injective line ∧
      (∀ i, line i ∈ selector) ∧
      (line 0, line 1) ∈ sourceMarkedHeavyCollisionSupport R threshold ∧
      (line 2, line 1) ∈ sourceMarkedHeavyCollisionSupport R threshold ∧
      (line 2, line 3) ∈ sourceMarkedHeavyCollisionSupport R threshold ∧
      (line 0, line 3) ∈ sourceMarkedHeavyCollisionSupport R threshold := by
  let lines := sourceLineFamily R
  have hlines : lines.Nonempty := sourceLineFamily_nonempty R hn
  have hlinesSelector : ∀ line ∈ lines, line ∈ selector := by
    intro line hline
    obtain ⟨i, rfl⟩ := (mem_sourceLineFamily_iff R line).1 hline
    exact hselector i
  apply dense_bipartite_has_marked_four_cycle_of_irrefl
    selector lines lines hlines hlines
    hlinesSelector hlinesSelector
    (sourceMarkedHeavyCollisionSupport R threshold)
    (sourceMarkedHeavyCollisionSupport_subset_lineFamily_product R threshold)
    (sourceMarkedHeavyCollisionSupport_irrefl R threshold)
    c hc_pos hc_le
  · simpa [lines, card_sourceLineFamily] using hdense
  · simpa [lines, card_sourceLineFamily] using hleftLarge
  · simpa [lines, card_sourceLineFamily] using hrightLarge

/-- The genuine heavy four-cycle carries the contact-geometric data furnished
by physical overlap: a nondegenerate north chart and a canonical collision
time on every cyclic edge, with the uniform residual bound.  No artificial
pairwise separation of all edge times is assumed here. -/
theorem sourceMarkedHeavyCollisionSupport_has_contact_four_cycle_packet
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (selector : Set MarkedLine)
    (hselector : ∀ i, R.line i ∈ selector)
    (hn : 0 < n)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hchart : ∀ i, kappa ≤ |direction (R.line i) (3 : Fin 4)|)
    (eta : ℝ) (heta : 0 < eta)
    (threshold : ENNReal)
    (c : ℝ) (hc_pos : 0 < c) (hc_le : c ≤ 1)
    (hdense : c * (n : ℝ) * (n : ℝ) ≤
      ((sourceMarkedHeavyCollisionSupport R threshold).card : ℝ))
    (hleftLarge : 4 ≤ c * (n : ℝ))
    (hrightLarge : 8 < c ^ 2 * (n : ℝ)) :
    ∃ (line : Fin 4 → MarkedLine) (approxTime : Fin 4 → ℝ),
      Function.Injective line ∧
      (∀ i, line i ∈ selector) ∧
      (∀ i, direction (line i) (3 : Fin 4) ≠ 0) ∧
      (∀ i,
        ‖(fourCycleEdgeSecant line i).2 +
            approxTime i • (fourCycleEdgeSecant line i).1‖ <
          (2 * kappa⁻¹ + 2) * (R.thickness + eta)) := by
  obtain ⟨line, hlineInjective, hlineSelector,
      hedge01, hedge21, hedge23, hedge03⟩ :=
    sourceMarkedHeavyCollisionSupport_has_marked_four_cycle
      R selector hselector hn threshold c hc_pos hc_le hdense
      hleftLarge hrightLarge
  let approxTime : Fin 4 → ℝ := fun i ↦
    markedSourceCollisionTime hD hR kappa hkappa hchart eta heta
      (markedCycleRelationEdge line i)
  have hedge : ∀ i,
      markedCycleRelationEdge line i ∈
        sourceMarkedHeavyCollisionSupport R threshold := by
    intro i
    fin_cases i <;>
      simp [markedCycleRelationEdge, hedge01, hedge21, hedge23, hedge03]
  have hedgeProduct : ∀ i,
      markedCycleRelationEdge line i ∈
        sourceLineFamily R ×ˢ sourceLineFamily R := by
    intro i
    exact sourceMarkedHeavyCollisionSupport_subset_lineFamily_product
      R threshold (hedge i)
  have hlineSource : ∀ i, line i ∈ sourceLineFamily R := by
    intro i
    fin_cases i
    · exact (Finset.mem_product.mp (hedgeProduct 0)).1
    · exact (Finset.mem_product.mp (hedgeProduct 0)).2
    · exact (Finset.mem_product.mp (hedgeProduct 1)).1
    · exact (Finset.mem_product.mp (hedgeProduct 2)).2
  refine ⟨line, approxTime, hlineInjective, hlineSelector, ?_, ?_⟩
  · intro i
    obtain ⟨j, hj⟩ := (mem_sourceLineFamily_iff R (line i)).1 (hlineSource i)
    rw [hj]
    exact (abs_pos.mp (lt_of_lt_of_le hkappa (hchart j)))
  · intro i
    have hres :=
      sourceMarkedHeavyCollisionSupport_has_uniform_contact_residual_control
        hD hR kappa hkappa hchart eta heta threshold (hedge i)
    fin_cases i
    · simpa [approxTime, markedCycleRelationEdge,
        fourCycleEdgeSecant, fourCycleNext,
        markedPairContactResidualNorm] using hres.1
    · simpa [approxTime, markedCycleRelationEdge,
        fourCycleEdgeSecant, fourCycleNext,
        markedPairContactResidualNorm] using hres.2
    · simpa [approxTime, markedCycleRelationEdge,
        fourCycleEdgeSecant, fourCycleNext,
        markedPairContactResidualNorm] using hres.1
    · simpa [approxTime, markedCycleRelationEdge,
        fourCycleEdgeSecant, fourCycleNext,
        markedPairContactResidualNorm] using hres.2

/-- Zero-threshold specialization: density of the actual positive normalized
collision support produces a genuine four-line contact packet.  All
threshold, light-flow, and separate edge-capacity inputs have disappeared. -/
theorem sourceMarkedCollisionSupport_has_contact_four_cycle_packet
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (selector : Set MarkedLine)
    (hselector : ∀ i, R.line i ∈ selector)
    (hn : 0 < n)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hchart : ∀ i, kappa ≤ |direction (R.line i) (3 : Fin 4)|)
    (eta : ℝ) (heta : 0 < eta)
    (c : ℝ) (hc_pos : 0 < c) (hc_le : c ≤ 1)
    (hdense : c * (n : ℝ) * (n : ℝ) ≤
      ((sourceMarkedCollisionSupport R).card : ℝ))
    (hleftLarge : 4 ≤ c * (n : ℝ))
    (hrightLarge : 8 < c ^ 2 * (n : ℝ)) :
    ∃ (line : Fin 4 → MarkedLine) (approxTime : Fin 4 → ℝ),
      Function.Injective line ∧
      (∀ i, line i ∈ selector) ∧
      (∀ i, direction (line i) (3 : Fin 4) ≠ 0) ∧
      (∀ i,
        ‖(fourCycleEdgeSecant line i).2 +
            approxTime i • (fourCycleEdgeSecant line i).1‖ <
          (2 * kappa⁻¹ + 2) * (R.thickness + eta)) := by
  apply sourceMarkedHeavyCollisionSupport_has_contact_four_cycle_packet
    hD hR selector hselector hn kappa hkappa hchart eta heta 0
      c hc_pos hc_le
  · simpa [sourceMarkedHeavyCollisionSupport_zero] using hdense
  · exact hleftLarge
  · exact hrightLarge

/-- Complete one-scale Reeb-time output of the actual collision graph.  The
four canonical collision times are either separated enough for the Maslov
four-probe firewall, or all four lie in three explicit closed Reeb packets.
Thus time separation is not silently assumed at the finite layer. -/
theorem sourceMarkedCollisionSupport_has_separated_contact_four_cycle_or_three_packets
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (selector : Set MarkedLine)
    (hselector : ∀ i, R.line i ∈ selector)
    (hn : 0 < n)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hchart : ∀ i, kappa ≤ |direction (R.line i) (3 : Fin 4)|)
    (eta : ℝ) (heta : 0 < eta)
    (c : ℝ) (hc_pos : 0 < c) (hc_le : c ≤ 1)
    (hdense : c * (n : ℝ) * (n : ℝ) ≤
      ((sourceMarkedCollisionSupport R).card : ℝ))
    (hleftLarge : 4 ≤ c * (n : ℝ))
    (hrightLarge : 8 < c ^ 2 * (n : ℝ))
    (timeGap : ℝ) :
    ∃ (line : Fin 4 → MarkedLine) (approxTime : Fin 4 → ℝ),
      Function.Injective line ∧
      (∀ i, line i ∈ selector) ∧
      (∀ i, direction (line i) (3 : Fin 4) ≠ 0) ∧
      (∀ i,
        ‖(fourCycleEdgeSecant line i).2 +
            approxTime i • (fourCycleEdgeSecant line i).1‖ <
          (2 * kappa⁻¹ + 2) * (R.thickness + eta)) ∧
      ((timeGap < |approxTime 0 - approxTime 1| ∧
        timeGap < |approxTime 0 - approxTime 2| ∧
        timeGap < |approxTime 0 - approxTime 3| ∧
        timeGap < |approxTime 1 - approxTime 2| ∧
        timeGap < |approxTime 1 - approxTime 3| ∧
        timeGap < |approxTime 2 - approxTime 3|) ∨
      ∃ t₀ t₁ t₂ : ℝ,
        (|approxTime 0 - t₀| ≤ timeGap ∨
          |approxTime 0 - t₁| ≤ timeGap ∨
          |approxTime 0 - t₂| ≤ timeGap) ∧
        (|approxTime 1 - t₀| ≤ timeGap ∨
          |approxTime 1 - t₁| ≤ timeGap ∨
          |approxTime 1 - t₂| ≤ timeGap) ∧
        (|approxTime 2 - t₀| ≤ timeGap ∨
          |approxTime 2 - t₁| ≤ timeGap ∨
          |approxTime 2 - t₂| ≤ timeGap) ∧
        (|approxTime 3 - t₀| ≤ timeGap ∨
          |approxTime 3 - t₁| ≤ timeGap ∨
          |approxTime 3 - t₂| ≤ timeGap)) := by
  obtain ⟨line, approxTime, hlineInjective, hlineSelector,
      hchartNonzero, hresidual⟩ :=
    sourceMarkedCollisionSupport_has_contact_four_cycle_packet
      hD hR selector hselector hn kappa hkappa hchart eta heta
      c hc_pos hc_le hdense hleftLarge hrightLarge
  refine ⟨line, approxTime, hlineInjective, hlineSelector,
    hchartNonzero, hresidual, ?_⟩
  exact four_reeb_times_separated_or_three_packets
    (approxTime 0) (approxTime 1) (approxTime 2) (approxTime 3) timeGap

/-- Exhaustive one-scale DRC dichotomy for the actual collision support.
If the three numerical DRC gates hold, the output is a genuine contact
four-cycle together with the separated-time/three-packet alternative.
Otherwise the failed gate is returned explicitly, so the sparse and
small-population branches remain available for Carleson payment. -/
theorem sourceMarkedCollisionSupport_contact_cycle_or_drc_obstruction
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (selector : Set MarkedLine)
    (hselector : ∀ i, R.line i ∈ selector)
    (hn : 0 < n)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hchart : ∀ i, kappa ≤ |direction (R.line i) (3 : Fin 4)|)
    (eta : ℝ) (heta : 0 < eta)
    (c : ℝ) (hc_pos : 0 < c) (hc_le : c ≤ 1)
    (timeGap : ℝ) :
    (∃ (line : Fin 4 → MarkedLine) (approxTime : Fin 4 → ℝ),
      Function.Injective line ∧
      (∀ i, line i ∈ selector) ∧
      (∀ i, direction (line i) (3 : Fin 4) ≠ 0) ∧
      (∀ i,
        ‖(fourCycleEdgeSecant line i).2 +
            approxTime i • (fourCycleEdgeSecant line i).1‖ <
          (2 * kappa⁻¹ + 2) * (R.thickness + eta)) ∧
      ((timeGap < |approxTime 0 - approxTime 1| ∧
        timeGap < |approxTime 0 - approxTime 2| ∧
        timeGap < |approxTime 0 - approxTime 3| ∧
        timeGap < |approxTime 1 - approxTime 2| ∧
        timeGap < |approxTime 1 - approxTime 3| ∧
        timeGap < |approxTime 2 - approxTime 3|) ∨
      ∃ t₀ t₁ t₂ : ℝ,
        (|approxTime 0 - t₀| ≤ timeGap ∨
          |approxTime 0 - t₁| ≤ timeGap ∨
          |approxTime 0 - t₂| ≤ timeGap) ∧
        (|approxTime 1 - t₀| ≤ timeGap ∨
          |approxTime 1 - t₁| ≤ timeGap ∨
          |approxTime 1 - t₂| ≤ timeGap) ∧
        (|approxTime 2 - t₀| ≤ timeGap ∨
          |approxTime 2 - t₁| ≤ timeGap ∨
          |approxTime 2 - t₂| ≤ timeGap) ∧
        (|approxTime 3 - t₀| ≤ timeGap ∨
          |approxTime 3 - t₁| ≤ timeGap ∨
          |approxTime 3 - t₂| ≤ timeGap))) ∨
    (((sourceMarkedCollisionSupport R).card : ℝ) <
        c * (n : ℝ) * (n : ℝ) ∨
      c * (n : ℝ) < 4 ∨
      c ^ 2 * (n : ℝ) ≤ 8) := by
  by_cases hdense : c * (n : ℝ) * (n : ℝ) ≤
      ((sourceMarkedCollisionSupport R).card : ℝ)
  · by_cases hleftLarge : 4 ≤ c * (n : ℝ)
    · by_cases hrightLarge : 8 < c ^ 2 * (n : ℝ)
      · left
        exact
          sourceMarkedCollisionSupport_has_separated_contact_four_cycle_or_three_packets
            hD hR selector hselector hn kappa hkappa hchart eta heta
            c hc_pos hc_le hdense hleftLarge hrightLarge timeGap
      · right
        exact Or.inr (Or.inr (le_of_not_gt hrightLarge))
    · right
      exact Or.inr (Or.inl (lt_of_not_ge hleftLarge))
  · right
    exact Or.inl (lt_of_not_ge hdense)

end StickyKakeya4
