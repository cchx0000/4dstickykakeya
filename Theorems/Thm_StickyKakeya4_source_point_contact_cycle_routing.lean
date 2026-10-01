import Theorems.Thm_StickyKakeya4_source_point_three_packet_routing
import Theorems.Thm_StickyKakeya4_collision_edge_contact_residual

open Set

noncomputable section

namespace StickyKakeya4

/-- Four actual rows through one source point, with their affine fibre marks
separated, also form an actual contact four-cycle at the single physical
height of that point.  The separated labels in this structure are explicitly
the affine marks; the contact residual is explicitly evaluated at the common
height.  They are not identified with the edge collision times used by the
Maslov four-probe tower. -/
structure SourcePointFourMarkedCommonHeightCycle {n : ℕ}
    (R : FiniteScaleSource n) (x : E4) (selector : Set MarkedLine)
    (timeGap eta : ℝ) where
  index : Fin 4 → Fin n
  index_injective : Function.Injective index
  active : ∀ k, x ∈ R.shading (index k) ∧ R.weight (index k) ≠ 0
  line_mem_selector : ∀ k, R.line (index k) ∈ selector
  chartNonzero : ∀ k, direction (R.line (index k)) (3 : Fin 4) ≠ 0
  affineMarkSeparated : ∀ i j, i ≠ j →
    finiteReebSeparated R.fibreMark timeGap (index i) (index j)
  commonHeightResidual : ∀ i,
    ‖(fourCycleEdgeSecant (fun k ↦ R.line (index k)) i).2 +
        x (3 : Fin 4) •
          (fourCycleEdgeSecant (fun k ↦ R.line (index k)) i).1‖ <
      (|(direction (R.line (index i)) (3 : Fin 4))⁻¹| +
          |(direction
            (R.line (index (fourCycleNext i))) (3 : Fin 4))⁻¹| + 2) *
        (R.thickness + eta)

theorem finiteReebSeparated_comm {n : ℕ} (time : Fin n → ℝ)
    (delta : ℝ) (i j : Fin n) :
    finiteReebSeparated time delta i j ↔
      finiteReebSeparated time delta j i := by
  simp only [finiteReebSeparated, abs_sub_comm]

/-- The four-mark branch of the pointwise weighted routing is upgraded to a
literal common-height contact cycle without changing rows or weights. -/
theorem sourcePoint_four_marked_rows_give_commonHeight_contactCycle
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (selector : Set MarkedLine)
    (hselector : ∀ i, R.line i ∈ selector)
    (hchart : ∀ i, direction (R.line i) (3 : Fin 4) ≠ 0)
    (x : E4) (timeGap eta : ℝ) (htimeGap : 0 ≤ timeGap)
    (heta : 0 < eta)
    {i₀ i₁ i₂ i₃ : Fin n}
    (hi₀ : x ∈ R.shading i₀ ∧ R.weight i₀ ≠ 0)
    (hi₁ : x ∈ R.shading i₁ ∧ R.weight i₁ ≠ 0)
    (hi₂ : x ∈ R.shading i₂ ∧ R.weight i₂ ≠ 0)
    (hi₃ : x ∈ R.shading i₃ ∧ R.weight i₃ ≠ 0)
    (h₁₀ : finiteReebSeparated R.fibreMark timeGap i₁ i₀)
    (h₂₀ : finiteReebSeparated R.fibreMark timeGap i₂ i₀)
    (h₂₁ : finiteReebSeparated R.fibreMark timeGap i₂ i₁)
    (h₃₀ : finiteReebSeparated R.fibreMark timeGap i₃ i₀)
    (h₃₁ : finiteReebSeparated R.fibreMark timeGap i₃ i₁)
    (h₃₂ : finiteReebSeparated R.fibreMark timeGap i₃ i₂) :
    Nonempty (SourcePointFourMarkedCommonHeightCycle R x selector
      timeGap eta) := by
  let index : Fin 4 → Fin n := ![i₀, i₁, i₂, i₃]
  have hactive : ∀ k, x ∈ R.shading (index k) ∧
      R.weight (index k) ≠ 0 := by
    intro k
    fin_cases k <;> simp [index, hi₀, hi₁, hi₂, hi₃]
  have hseparated : ∀ i j, i ≠ j →
      finiteReebSeparated R.fibreMark timeGap (index i) (index j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact (finiteReebSeparated_comm R.fibreMark timeGap i₁ i₀).mp h₁₀
    · exact (finiteReebSeparated_comm R.fibreMark timeGap i₂ i₀).mp h₂₀
    · exact (finiteReebSeparated_comm R.fibreMark timeGap i₃ i₀).mp h₃₀
    · exact h₁₀
    · exact (hij rfl).elim
    · exact (finiteReebSeparated_comm R.fibreMark timeGap i₂ i₁).mp h₂₁
    · exact (finiteReebSeparated_comm R.fibreMark timeGap i₃ i₁).mp h₃₁
    · exact h₂₀
    · exact h₂₁
    · exact (hij rfl).elim
    · exact (finiteReebSeparated_comm R.fibreMark timeGap i₃ i₂).mp h₃₂
    · exact h₃₀
    · exact h₃₁
    · exact h₃₂
    · exact (hij rfl).elim
  have hindex : Function.Injective index := by
    intro i j hij
    by_contra hne
    have hsep := hseparated i j hne
    rw [hij] at hsep
    have : timeGap < 0 := by
      simpa [finiteReebSeparated] using hsep
    exact (not_lt_of_ge htimeGap) this
  refine ⟨{
    index := index
    index_injective := hindex
    active := hactive
    line_mem_selector := fun k ↦ hselector (index k)
    chartNonzero := fun k ↦ hchart (index k)
    affineMarkSeparated := hseparated
    commonHeightResidual := ?_ }⟩
  intro i
  have hres := commonShadingPoint_has_contact_residual_control
    hD hR x (hactive i).1 (hactive (fourCycleNext i)).1
      (hchart (index i)) (hchart (index (fourCycleNext i))) heta
  simpa [fourCycleEdgeSecant, markedPairContactResidualNorm] using hres.1

/-- Named output of the honest pointwise contact route. -/
def SourcePointContactCycleOrThreePacketAlternative {n : ℕ}
    (R : FiniteScaleSource n) (x : E4) (selector : Set MarkedLine)
    (timeGap eta : ℝ) (current : ENNReal) : Prop :=
  Nonempty (SourcePointFourMarkedCommonHeightCycle R x selector
      timeGap eta) ∨
    ∃ a b c, ∃ removed continuing : ENNReal,
      removed = current * ENNReal.ofReal
        (finiteThreePacketsMass (sourcePointNormalizedWeight R x)
          R.fibreMark timeGap a b c) ∧
      continuing = current * ENNReal.ofReal
        (finiteOutsideThreePacketsMass (sourcePointNormalizedWeight R x)
          R.fibreMark timeGap a b c) ∧
      current = removed + continuing ∧
      current ≤ removed + removed

/-- Complete honest pointwise route.  The first output contains a genuine
common-height contact cycle and separately records its four affine-mark
labels.  The second output is the coefficient-one three-packet split. -/
theorem sourcePoint_commonHeight_contactCycle_or_three_packet_half_removal
    {n : ℕ} {R D : FiniteScaleSource n} {epsilon : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D epsilon C)
    (hR : IsFractionalSourceRestriction R D)
    (selector : Set MarkedLine)
    (hselector : ∀ i, R.line i ∈ selector)
    (hchart : ∀ i, direction (R.line i) (3 : Fin 4) ≠ 0)
    (x : E4)
    (hweightTop : ∀ i, R.weight i ≠ ⊤)
    (hsourceZero : sourceFunction R x ≠ 0)
    (timeGap eta : ℝ) (htimeGap : 0 ≤ timeGap) (heta : 0 < eta)
    (current : ENNReal) :
    SourcePointContactCycleOrThreePacketAlternative
      R x selector timeGap eta current := by
  unfold SourcePointContactCycleOrThreePacketAlternative
  rcases sourcePoint_four_incident_mark_samples_or_three_packet_half_removal
      R x hweightTop hsourceZero timeGap current with hfour | hthree
  · left
    obtain ⟨i₀, i₁, i₂, i₃,
      hi₀shade, hi₀weight, hi₁shade, hi₁weight,
      hi₂shade, hi₂weight, hi₃shade, hi₃weight,
      h₁₀, h₂₀, h₂₁, h₃₀, h₃₁, h₃₂⟩ := hfour
    exact sourcePoint_four_marked_rows_give_commonHeight_contactCycle
      hD hR selector hselector hchart x timeGap eta htimeGap heta
      ⟨hi₀shade, hi₀weight⟩ ⟨hi₁shade, hi₁weight⟩
      ⟨hi₂shade, hi₂weight⟩ ⟨hi₃shade, hi₃weight⟩
      h₁₀ h₂₀ h₂₁ h₃₀ h₃₁ h₃₂
  · exact Or.inr hthree

end StickyKakeya4
