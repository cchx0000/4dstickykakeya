import Theorems.Thm_StickyKakeya4_contact_symplectic_edge_flow_certificate_existence
import Theorems.Thm_StickyKakeya4_edge_flow_certificate_to_uniform_bound

open MeasureTheory Set

namespace StickyKakeya4

theorem uniform_marked_source_hereditary_finite_scale_or_front_frostman_or_boundary
    (ambient selector : Set MarkedLine)
    (hambientCompact : IsCompact ambient)
    (hselectorAmbient : selector ⊆ ambient)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3) :
    HasUniformMarkedSourceEstimate selector ∨
      HasFrontFrostmanMeasures ambient ∨
      HasCoherentConcentrationBoundary selector
        hmeasurable hvalid hselector := by
  rcases contact_symplectic_edge_flow_certificate_or_front_frostman_or_boundary
      ambient selector hambientCompact hselectorAmbient
      hmeasurable hvalid hselector hpacking with
      hcertificates | hfrostman | hboundary
  · exact Or.inl
      (contact_symplectic_edge_flow_certificates_to_uniform_marked_source_estimate
        selector hcertificates)
  · exact Or.inr (Or.inl hfrostman)
  · exact Or.inr (Or.inr hboundary)

end StickyKakeya4
