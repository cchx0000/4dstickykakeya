import Theorems.Thm_StickyKakeya4_native_compact_volume_transport
import Theorems.Thm_StickyKakeya4_native_fixed_compact_kakeya_exponent
import Theorems.Thm_StickyKakeya4_borel_selector_reduction
import Theorems.Thm_StickyKakeya4_packing_selector_to_finite_scale_sources
import Theorems.Thm_StickyKakeya4_contact_symplectic_edge_flow_certificate_existence
import Theorems.Thm_StickyKakeya4_edge_flow_certificate_to_uniform_bound
import Theorems.Thm_StickyKakeya4_hereditary_finite_scale_to_frostman
import Theorems.Thm_StickyKakeya4_frostman_mass_distribution

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeFixedZeroOriginalTheorem
open MeasureTheory Set StickyKakeya4

/-- The original compact marked-family theorem follows from zero of the
fixed-compact extremal exponent. The Borel selector and the successful
routing/Frostman or concentration-boundary alternatives are constructed
internally from IsStickyDatum. No boundary, density, routing or intermediate
certificate is an additional hypothesis, and no identity of the fixed and
unrestricted extremal exponents is used. This theorem does not prove hzero. -/
theorem sticky_kakeya_four_dimensional_of_fixed_zero
    (hzero : NativeFixedCompactKakeyaExponent.extremalExponent=0)
    (lines : Set MarkedLine) (hsticky : IsStickyDatum lines) :
    dimH (unitFront lines)=4 := by
  have hvolume : HasWangZakharovFiniteVolumeEstimateOn NativeUnitParentNormalization.fixedCompactClass :=
    NativeFixedCompactKakeyaExponent.extremal_zero_iff_finite_volume.mp hzero
  obtain ⟨selector,hmeasurable,hsubset,hselector,hpacking,_hfront⟩ :=
    borel_selector_reduction lines hsticky
  have hvalid : ∀line∈selector,IsValidLine line :=
    fun line hline => hsticky.2.1 line (hsubset hline)
  have hdim_of_frost (hfrost : HasFrontFrostmanMeasures lines) : dimH (unitFront lines)=4 := by
    apply le_antisymm
    · calc
        dimH (unitFront lines) ≤ dimH (Set.univ : Set E4) := dimH_mono (Set.subset_univ _)
        _ = 4 := by simp [E4,Real.dimH_univ_eq_finrank]
    · exact dimH_ge_four_of_front_frostman_measures lines hfrost
  rcases contact_symplectic_edge_flow_certificate_or_front_frostman_or_boundary
      lines selector hsticky.1 hsubset hmeasurable hvalid hselector hpacking with
      hcertificates | hfrost | hboundary
  · have huniform := contact_symplectic_edge_flow_certificates_to_uniform_marked_source_estimate
      selector hcertificates
    have hsources : HasCoherentFiniteScaleSources selector lines :=
      packing_selector_to_finite_scale_sources selector lines hsticky.1 hsubset
        hmeasurable hvalid hselector hpacking
    exact hdim_of_frost (hereditary_finite_scale_to_frostman selector lines
      hmeasurable hvalid hselector hpacking hsources huniform)
  · exact hdim_of_frost hfrost
  · exact NativeCompactVolumeTransport.dimH_eq_four_from_fixed_compact_volume
      hvolume lines selector hsticky.1 hsubset hmeasurable hvalid hselector hpacking hboundary

end NativeFixedZeroOriginalTheorem
