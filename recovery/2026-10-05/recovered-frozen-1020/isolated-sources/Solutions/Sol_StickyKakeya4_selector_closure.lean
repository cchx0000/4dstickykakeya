import Theorems.Thm_StickyKakeya4_packing_selector_to_finite_scale_sources
import Theorems.Thm_StickyKakeya4_uniform_marked_source_hereditary_finite_scale
import Theorems.Thm_StickyKakeya4_hereditary_finite_scale_to_frostman
import Theorems.Thm_StickyKakeya4_frostman_mass_distribution
import Theorems.Thm_StickyKakeya4_cover_adapted_wang_zakharov_closure

open MeasureTheory Set

/-!
This entry follows the compact-ambient interface needed by the original paper's
main theorem. The earlier Borel-selector-only target was stronger than the
source's explicit closure theorem; see ORIGINAL_PAPER_TARGETS.md.

This is the legacy comparison route and still uses the WZ project axiom.
It is not the desired internal no-WZ closure and is not reported as complete.
-/

open StickyKakeya4

theorem solution (ambient selector : Set MarkedLine)
    (hambientCompact : IsCompact ambient)
    (hselectorAmbient : selector ⊆ ambient)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3) :
    dimH (unitFront ambient) = 4 := by
  have hsources : HasCoherentFiniteScaleSources selector ambient :=
    packing_selector_to_finite_scale_sources selector ambient
      hambientCompact hselectorAmbient
      hmeasurable hvalid hselector hpacking
  have hroute :
      HasUniformMarkedSourceEstimate selector ∨
        HasFrontFrostmanMeasures ambient ∨
        HasCoherentConcentrationBoundary selector
          hmeasurable hvalid hselector :=
    uniform_marked_source_hereditary_finite_scale_or_front_frostman_or_boundary
      ambient selector hambientCompact hselectorAmbient
      hmeasurable hvalid hselector hpacking
  have hdim_of_frost (hfrost : HasFrontFrostmanMeasures ambient) :
      dimH (unitFront ambient) = 4 := by
    apply le_antisymm
    · calc
        dimH (unitFront ambient) ≤ dimH (Set.univ : Set E4) :=
          dimH_mono (Set.subset_univ _)
        _ = 4 := by simp [E4, Real.dimH_univ_eq_finrank]
    · exact dimH_ge_four_of_front_frostman_measures ambient hfrost
  rcases hroute with huniform | hfrost | hboundary
  · exact hdim_of_frost
      (hereditary_finite_scale_to_frostman selector ambient
        hmeasurable hvalid hselector hpacking hsources huniform)
  · exact hdim_of_frost hfrost
  · exact cover_adapted_wang_zakharov_closure
      ambient selector hambientCompact hselectorAmbient
      hmeasurable hvalid hselector hpacking hboundary
