import Theorems.Thm_StickyKakeya4_borel_selector_foundations
import Theorems.Thm_StickyKakeya4_packing_dimension_lower_bound

open MeasureTheory Set
open StickyKakeya4

private theorem lineCarrier_mono_aux {s t : Set MarkedLine} (hst : s ⊆ t) :
    lineCarrier s ⊆ lineCarrier t := by
  exact Set.image_mono hst

private theorem packingDim_mono_aux {X : Type*} [PseudoMetricSpace X]
    {s t : Set X} (hst : s ⊆ t) : packingDim s ≤ packingDim t := by
  apply sInf_le_sInf
  intro d hd
  obtain ⟨pieces, ht, hpieces⟩ := hd
  exact ⟨pieces, hst.trans ht, hpieces⟩

theorem solution (lines : Set MarkedLine)
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
  refine ⟨selector, hmeasurable, hsubset, hselector, ?_, ?_⟩
  · apply le_antisymm
    · calc
        packingDim (lineCarrier selector) ≤ packingDim (lineCarrier lines) :=
          packingDim_mono_aux (lineCarrier_mono_aux hsubset)
        _ ≤ 3 := hpacking
    · exact direction_selector_packingDim_lower_internal selector hmeasurable
        (fun line hline => hvalid line (hsubset hline)) hselector
  · rintro x ⟨line, hline, t, ht, rfl⟩
    exact ⟨line, hsubset hline, t, ht, rfl⟩
