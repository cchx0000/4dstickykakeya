import Theorems.Thm_StickyKakeya4_borel_selector_reduction
import Theorems.Thm_StickyKakeya4_selector_closure

open MeasureTheory Set

namespace StickyKakeya4

theorem sticky_kakeya_four_dimensional (lines : Set MarkedLine)
    (hsticky : IsStickyDatum lines) :
    dimH (unitFront lines) = 4 := by
  obtain ⟨selector, hmeasurable, hsubset, hselector, hpacking, hfront⟩ :=
    borel_selector_reduction lines hsticky
  have hvalid : ∀ line ∈ selector, IsValidLine line := by
    intro line hline
    exact hsticky.2.1 line (hsubset hline)
  exact selector_closure lines selector hsticky.1 hsubset
    hmeasurable hvalid hselector hpacking

end StickyKakeya4
