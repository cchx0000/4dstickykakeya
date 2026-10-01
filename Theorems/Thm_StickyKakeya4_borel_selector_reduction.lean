import Definitions.Def_sticky_kakeya4_core
import Theorems.Thm_StickyKakeya4_borel_selector_foundations
import Theorems.Thm_StickyKakeya4_packing_dimension_lower_bound

open MeasureTheory Set

namespace StickyKakeya4

theorem lineCarrier_mono {s t : Set MarkedLine} (hst : s ⊆ t) :
    lineCarrier s ⊆ lineCarrier t := by
  exact Set.image_mono hst

theorem unitFront_mono {s t : Set MarkedLine} (hst : s ⊆ t) :
    unitFront s ⊆ unitFront t := by
  rintro x ⟨line, hline, u, hu, rfl⟩
  exact ⟨line, hst hline, u, hu, rfl⟩

/-- Monotonicity for the manuscript's countable-cover definition of packing
dimension.  A cover admissible for the larger set is still admissible for
every subset, with exactly the same upper Minkowski bounds. -/
theorem packingDim_mono {X : Type*} [PseudoMetricSpace X]
    {s t : Set X} (hst : s ⊆ t) : packingDim s ≤ packingDim t := by
  apply sInf_le_sInf
  intro d hd
  obtain ⟨pieces, ht, hpieces⟩ := hd
  exact ⟨pieces, hst.trans ht, hpieces⟩

theorem borel_selector_reduction (lines : Set MarkedLine)
    (hsticky : IsStickyDatum lines) :
    ∃ selector : Set MarkedLine,
      MeasurableSet selector ∧
      selector ⊆ lines ∧
      IsDirectionSelector selector ∧
      packingDim (lineCarrier selector) = 3 ∧
      unitFront selector ⊆ unitFront lines := by
  rcases hsticky with ⟨hcompact, hvalid, hfull, hpacking⟩
  obtain ⟨selector, hmeasurable, hsubset, hselector⟩ :=
    compact_full_direction_borel_selector lines hcompact hfull
  have hselectorValid : ∀ line ∈ selector, IsValidLine line := by
    intro line hline
    exact hvalid line (hsubset hline)
  have hlower : (3 : ENNReal) ≤ packingDim (lineCarrier selector) :=
    direction_selector_packingDim_lower_internal selector hmeasurable
      hselectorValid hselector
  have hupper : packingDim (lineCarrier selector) ≤ (3 : ENNReal) := by
    exact (packingDim_mono (lineCarrier_mono hsubset)).trans hpacking
  exact ⟨selector, hmeasurable, hsubset, hselector,
    le_antisymm hupper hlower, unitFront_mono hsubset⟩

end StickyKakeya4
