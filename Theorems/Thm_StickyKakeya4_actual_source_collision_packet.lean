import Theorems.Thm_StickyKakeya4_heavy_collision_marked_four_cycle
import Theorems.Thm_StickyKakeya4_normalized_collision_relation_packet

open Set

noncomputable section

namespace StickyKakeya4

/-- Four Reeb labels are carried by three closed packets of the given radius.
This is the literal complementary output to a four-separated Maslov packet. -/
def FourTimesLieInThreePackets (time : Fin 4 → ℝ) (radius : ℝ) : Prop :=
  ∃ t₀ t₁ t₂ : ℝ, ∀ i,
    |time i - t₀| ≤ radius ∨
      |time i - t₁| ≤ radius ∨
      |time i - t₂| ≤ radius

/-- One-scale output of the actual, same-population marked collision graph.
The dense branch is normalized directly into the packet consumed by the
Maslov return tower.  If its four collision heights do not separate, the
literal three-packet alternative is retained.  No disjoint left/right copy of
the marked-line family is introduced. -/
theorem sourceMarkedCollisionSupport_has_normalized_packet_or_three_packets
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
    Nonempty (NormalizedMarkedFourCyclePacket selector timeGap
      ((2 * kappa⁻¹ + 2) * (R.thickness + eta))) ∨
    ∃ (line : Fin 4 → MarkedLine) (approxTime : Fin 4 → ℝ),
      Function.Injective line ∧
      (∀ i, line i ∈ selector) ∧
      (∀ i, direction (line i) (3 : Fin 4) ≠ 0) ∧
      (∀ i,
        ‖(fourCycleEdgeSecant line i).2 +
            approxTime i • (fourCycleEdgeSecant line i).1‖ <
          (2 * kappa⁻¹ + 2) * (R.thickness + eta)) ∧
      FourTimesLieInThreePackets approxTime timeGap := by
  obtain ⟨line, approxTime, hlineInjective, hlineSelector,
      hchartNonzero, hresidual, htime | hthree⟩ :=
    sourceMarkedCollisionSupport_has_separated_contact_four_cycle_or_three_packets
      hD hR selector hselector hn kappa hkappa hchart eta heta
      c hc_pos hc_le hdense hleftLarge hrightLarge timeGap
  · left
    refine ⟨⟨line, hlineInjective, hlineSelector, hchartNonzero,
      approxTime, ?_, ?_⟩⟩
    · intro i j hij
      obtain ⟨h₀₁, h₀₂, h₀₃, h₁₂, h₁₃, h₂₃⟩ := htime
      have h₀₁' := le_of_lt h₀₁
      have h₀₂' := le_of_lt h₀₂
      have h₀₃' := le_of_lt h₀₃
      have h₁₂' := le_of_lt h₁₂
      have h₁₃' := le_of_lt h₁₃
      have h₂₃' := le_of_lt h₂₃
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact h₀₁'
      · exact h₀₂'
      · exact h₀₃'
      · calc
          timeGap ≤ |approxTime 0 - approxTime 1| := h₀₁'
          _ = |approxTime 1 - approxTime 0| := abs_sub_comm _ _
      · exact (hij rfl).elim
      · exact h₁₂'
      · exact h₁₃'
      · calc
          timeGap ≤ |approxTime 0 - approxTime 2| := h₀₂'
          _ = |approxTime 2 - approxTime 0| := abs_sub_comm _ _
      · calc
          timeGap ≤ |approxTime 1 - approxTime 2| := h₁₂'
          _ = |approxTime 2 - approxTime 1| := abs_sub_comm _ _
      · exact (hij rfl).elim
      · exact h₂₃'
      · calc
          timeGap ≤ |approxTime 0 - approxTime 3| := h₀₃'
          _ = |approxTime 3 - approxTime 0| := abs_sub_comm _ _
      · calc
          timeGap ≤ |approxTime 1 - approxTime 3| := h₁₃'
          _ = |approxTime 3 - approxTime 1| := abs_sub_comm _ _
      · calc
          timeGap ≤ |approxTime 2 - approxTime 3| := h₂₃'
          _ = |approxTime 3 - approxTime 2| := abs_sub_comm _ _
      · exact (hij rfl).elim
    · intro i
      exact normalized_fourCycleResidual_le i _
        ((2 * kappa⁻¹ + 2) * (R.thickness + eta))
        (le_of_lt (hresidual i))
  · right
    refine ⟨line, approxTime, hlineInjective, hlineSelector,
      hchartNonzero, hresidual, ?_⟩
    obtain ⟨t₀, t₁, t₂, h₀, h₁, h₂, h₃⟩ := hthree
    refine ⟨t₀, t₁, t₂, ?_⟩
    intro i
    fin_cases i <;> assumption

end StickyKakeya4
