import Definitions.Def_sticky_kakeya4_core
import Theorems.Thm_StickyKakeya4_lossless_edge_flow_carleson
import Theorems.Thm_StickyKakeya4_finite_scale_source_mass

open MeasureTheory Set

namespace StickyKakeya4

/-- A contact/symplectic routing certificate implies the marked hereditary
finite-scale union estimate.  The proof uses exact finite-tree telescoping and
the Carleson sum of the local geometric capacities. -/
theorem contact_symplectic_edge_flow_certificates_to_uniform_marked_source_estimate
    (selector : Set MarkedLine)
    (hcertificates : HasContactSymplecticEdgeFlowCertificates selector) :
    HasUniformMarkedSourceEstimate selector := by
  intro ε hε Cpack hCpack0 hCpackTop
  obtain ⟨A, hA0, hATop, δ₀, hδ₀, hcertificate⟩ :=
    hcertificates ε hε Cpack hCpack0 hCpackTop
  refine ⟨A + A, ?_, ENNReal.add_ne_top.2 ⟨hATop, hATop⟩,
    δ₀, hδ₀, ?_⟩
  · intro hsum
    exact hA0 (add_eq_zero.mp hsum).1
  intro n D R hDδ hDselector hDadmissible hRrestriction
  obtain ⟨cert⟩ := hcertificate n D R hDδ hDselector hDadmissible
    hRrestriction
  have hrootsFinite :
      Finset.univ.sum (fun i : Fin n =>
        if R.tree.parent i = none then cert.incoming i else 0) ≠ ⊤ := by
    rw [← cert.sourceAtRoots]
    exact sourceMass_ne_top_of_fractional_admissibleStickySource
      hDadmissible hRrestriction
  have hroots_le_twice_payments :
      Finset.univ.sum (fun i : Fin n =>
        if R.tree.parent i = none then cert.incoming i else 0) ≤
      Finset.univ.sum (fun i : Fin n => cert.paid i + cert.terminalMass i) +
        Finset.univ.sum (fun i : Fin n => cert.paid i + cert.terminalMass i) :=
    lossless_edge_flow_with_half_error R.tree cert.incoming cert.paid
      cert.terminalMass cert.routingError cert.conservation hrootsFinite
        cert.smallError
  have hpayments :
      Finset.univ.sum (fun i : Fin n =>
        cert.paid i + cert.terminalMass i) ≤
      (Finset.univ.sum cert.capacity) * volume (sourceUnion R) := by
    calc
      Finset.univ.sum (fun i : Fin n =>
          cert.paid i + cert.terminalMass i) ≤
          Finset.univ.sum (fun i : Fin n =>
            cert.capacity i * volume (sourceUnion R)) := by
        exact Finset.sum_le_sum fun i _ => cert.localCharge i
      _ = (Finset.univ.sum cert.capacity) * volume (sourceUnion R) := by
        rw [Finset.sum_mul]
  calc
    sourceMass R = Finset.univ.sum (fun i : Fin n =>
        if R.tree.parent i = none then cert.incoming i else 0) := cert.sourceAtRoots
    _ ≤ Finset.univ.sum (fun i : Fin n =>
        cert.paid i + cert.terminalMass i) +
          Finset.univ.sum (fun i : Fin n =>
            cert.paid i + cert.terminalMass i) := hroots_le_twice_payments
    _ ≤ (Finset.univ.sum cert.capacity) * volume (sourceUnion R) +
          (Finset.univ.sum cert.capacity) * volume (sourceUnion R) :=
      add_le_add hpayments hpayments
    _ = ((Finset.univ.sum cert.capacity) +
          (Finset.univ.sum cert.capacity)) * volume (sourceUnion R) := by
      rw [add_mul]
    _ ≤ ((A * (ENNReal.ofReal D.thickness).rpow (-ε)) +
          (A * (ENNReal.ofReal D.thickness).rpow (-ε))) *
            volume (sourceUnion R) := by
      gcongr
      · exact cert.capacityCarleson
      · exact cert.capacityCarleson
    _ = (A + A) * (ENNReal.ofReal D.thickness).rpow (-ε) *
        volume (sourceUnion R) := by ring

end StickyKakeya4
