import Theorems.Thm_StickyKakeya4_four_probe_boundary_limit
import Mathlib.MeasureTheory.Measure.Support

open Set
open MeasureTheory

namespace StickyKakeya4

/-- Exact packing--covering duality behind the three-packet stopping.  A
nonempty set of Reeb times is either covered by three closed packets of radius
`delta`, or it contains four pairwise `delta`-separated times. -/
theorem reeb_time_support_three_packets_or_four_separated
    (support : Set ℝ) (hsupport : support.Nonempty) (delta : ℝ) :
    (∃ t₀ t₁ t₂ : ℝ, ∀ s ∈ support,
      |s - t₀| ≤ delta ∨ |s - t₁| ≤ delta ∨ |s - t₂| ≤ delta) ∨
    ∃ s₀ s₁ s₂ s₃ : ℝ,
      s₀ ∈ support ∧ s₁ ∈ support ∧ s₂ ∈ support ∧ s₃ ∈ support ∧
      delta < |s₀ - s₁| ∧ delta < |s₀ - s₂| ∧
      delta < |s₀ - s₃| ∧ delta < |s₁ - s₂| ∧
      delta < |s₁ - s₃| ∧ delta < |s₂ - s₃| := by
  classical
  obtain ⟨s₀, hs₀⟩ := hsupport
  by_cases h₀ : ∀ s ∈ support, |s - s₀| ≤ delta
  · left
    exact ⟨s₀, s₀, s₀, fun s hs => Or.inl (h₀ s hs)⟩
  · push Not at h₀
    obtain ⟨s₁, hs₁, hs₁far⟩ := h₀
    by_cases h₁ : ∀ s ∈ support,
        |s - s₀| ≤ delta ∨ |s - s₁| ≤ delta
    · left
      exact ⟨s₀, s₁, s₁, fun s hs =>
        (h₁ s hs).imp_right Or.inl⟩
    · push Not at h₁
      obtain ⟨s₂, hs₂, hs₂far₀, hs₂far₁⟩ := h₁
      by_cases h₂ : ∀ s ∈ support,
          |s - s₀| ≤ delta ∨ |s - s₁| ≤ delta ∨
            |s - s₂| ≤ delta
      · exact Or.inl ⟨s₀, s₁, s₂, h₂⟩
      · push Not at h₂
        obtain ⟨s₃, hs₃, hs₃far₀, hs₃far₁, hs₃far₂⟩ := h₂
        right
        refine ⟨s₀, s₁, s₂, s₃, hs₀, hs₁, hs₂, hs₃, ?_⟩
        constructor
        · simpa [abs_sub_comm] using hs₁far
        constructor
        · simpa [abs_sub_comm] using hs₂far₀
        constructor
        · simpa [abs_sub_comm] using hs₃far₀
        constructor
        · simpa [abs_sub_comm] using hs₂far₁
        constructor
        · simpa [abs_sub_comm] using hs₃far₁
        · simpa [abs_sub_comm] using hs₃far₂

/-- Contrapositive form used on an eternal history after the four-time output
has been removed: absence of a four-separated tuple forces an exact three-packet
cover of the surviving time support. -/
theorem reeb_time_support_three_packets_of_no_four_separated
    (support : Set ℝ) (hsupport : support.Nonempty) (delta : ℝ)
    (hnoFour : ∀ s₀ ∈ support, ∀ s₁ ∈ support,
      ∀ s₂ ∈ support, ∀ s₃ ∈ support,
      ¬ (delta < |s₀ - s₁| ∧ delta < |s₀ - s₂| ∧
        delta < |s₀ - s₃| ∧ delta < |s₁ - s₂| ∧
        delta < |s₁ - s₃| ∧ delta < |s₂ - s₃|)) :
    ∃ t₀ t₁ t₂ : ℝ, ∀ s ∈ support,
      |s - t₀| ≤ delta ∨ |s - t₁| ≤ delta ∨ |s - t₂| ≤ delta := by
  rcases reeb_time_support_three_packets_or_four_separated
      support hsupport delta with hpackets | hfour
  · exact hpackets
  · obtain ⟨s₀, s₁, s₂, s₃, hs₀, hs₁, hs₂, hs₃, hsep⟩ := hfour
    exact (hnoFour s₀ hs₀ s₁ hs₁ s₂ hs₂ s₃ hs₃ hsep).elim

/-- Measure-theoretic support bridge for the eternal three-packet branch.  If
the support of a probability law contains no four pairwise `delta`-separated
times, then three packets cover its whole support, and the set outside those
packets has zero mass. -/
theorem probability_measure_three_packets_of_no_four_separated
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (delta : ℝ)
    (hnoFour : ∀ s₀ ∈ nu.support, ∀ s₁ ∈ nu.support,
      ∀ s₂ ∈ nu.support, ∀ s₃ ∈ nu.support,
      ¬ (delta < |s₀ - s₁| ∧ delta < |s₀ - s₂| ∧
        delta < |s₀ - s₃| ∧ delta < |s₁ - s₂| ∧
        delta < |s₁ - s₃| ∧ delta < |s₂ - s₃|)) :
    ∃ t₀ t₁ t₂ : ℝ,
      (∀ s ∈ nu.support,
        |s - t₀| ≤ delta ∨ |s - t₁| ≤ delta ∨ |s - t₂| ≤ delta) ∧
      nu {s : ℝ |
        delta < |s - t₀| ∧ delta < |s - t₁| ∧ delta < |s - t₂|} = 0 := by
  have hnu_ne : nu ≠ 0 := by
    intro hzero
    have hprob : nu Set.univ = 1 := IsProbabilityMeasure.measure_univ
    simpa [hzero] using hprob
  have hsupport : nu.support.Nonempty := Measure.nonempty_support hnu_ne
  obtain ⟨t₀, t₁, t₂, hcover⟩ :=
    reeb_time_support_three_packets_of_no_four_separated
      nu.support hsupport delta hnoFour
  refine ⟨t₀, t₁, t₂, hcover, ?_⟩
  apply measure_mono_null (t := nu.supportᶜ) _ Measure.measure_compl_support
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  simp only [Set.mem_compl_iff]
  intro hsupport_s
  rcases hcover s hsupport_s with h₀ | h₁ | h₂
  · exact (not_lt_of_ge h₀) hs.1
  · exact (not_lt_of_ge h₁) hs.2.1
  · exact (not_lt_of_ge h₂) hs.2.2

/-- Symplectic-to-packet interface.  If every four-separated support tuple
produces a coherent four-probe boundary packet whose horizontal determinants
stay uniformly positive, the Maslov rank-loss firewall rules such a tuple out.
Consequently the time law is carried by three packets up to a null set. -/
theorem probability_measure_three_packets_of_four_probe_extraction
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (delta : ℝ)
    (hextract : ∀ s₀ ∈ nu.support, ∀ s₁ ∈ nu.support,
      ∀ s₂ ∈ nu.support, ∀ s₃ ∈ nu.support,
      delta < |s₀ - s₁| ∧ delta < |s₀ - s₂| ∧
        delta < |s₀ - s₃| ∧ delta < |s₁ - s₂| ∧
        delta < |s₁ - s₃| ∧ delta < |s₂ - s₃| →
      ∃ packet : FourProbeConcentrationLimit, ∃ Delta : ℝ,
        0 < Delta ∧ ∀ n, Delta ≤ |Matrix.det (packet.approxA n)|) :
    ∃ t₀ t₁ t₂ : ℝ,
      (∀ s ∈ nu.support,
        |s - t₀| ≤ delta ∨ |s - t₁| ≤ delta ∨ |s - t₂| ≤ delta) ∧
      nu {s : ℝ |
        delta < |s - t₀| ∧ delta < |s - t₁| ∧ delta < |s - t₂|} = 0 := by
  apply probability_measure_three_packets_of_no_four_separated nu delta
  intro s₀ hs₀ s₁ hs₁ s₂ hs₂ s₃ hs₃ hsep
  obtain ⟨packet, Delta, hDelta, hdet⟩ :=
    hextract s₀ hs₀ s₁ hs₁ s₂ hs₂ s₃ hs₃ hsep
  exact packet.no_uniform_horizontal_det_lower_bound Delta hDelta hdet

end StickyKakeya4
