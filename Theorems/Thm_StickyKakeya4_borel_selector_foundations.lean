import Theorems.Thm_StickyKakeya4_lexicographic_selector

open MeasureTheory Set

namespace StickyKakeya4

/-!
Borel selector foundation specialized to compact marked-line families.

No external measurable-selection theorem is used.  The selector is the Borel
set of lexicographic minima constructed in
`Thm_StickyKakeya4_lexicographic_selector`.
-/

/-- A compact full-direction family admits a measurable one-line-per-direction
subfamily. -/
theorem compact_full_direction_borel_selector
    (lines : Set MarkedLine)
    (hcompact : IsCompact lines)
    (hfull : FullDirection lines) :
    ∃ selector : Set MarkedLine,
      MeasurableSet selector ∧
      selector ⊆ lines ∧
      IsDirectionSelector selector :=
  compact_full_direction_lexicographic_selector lines hcompact hfull

end StickyKakeya4
