import Theorems.Thm_StickyKakeya4_original_ancestor_fiber_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalCarrierImageCount
open Classical OriginalAncestorCounting OriginalAncestorFiberGeometry

variable {P T K D U X : Type*} [DecidableEq K]
  [NormedAddCommGroup U]

/-- The constructed ancestor image consists of occupied ORIGINAL reference
 cells. The original reference family is not replaced by the selected core. -/
theorem occupied_ancestors_mem_reference
    (E : Finset P) (Phi : P → Finset D) (fine : D → U) (center : P → U)
    (rho : ℝ) (ancestor : T → K) (realizer : P → D → T) (Tfull : Finset T)
    (hrealizer : ∀ p ∈ E, ∀ d ∈ Phi p, realizer p d ∈ Tfull) :
    occupiedAncestors E Phi fine center rho ancestor realizer ⊆ Tfull.image ancestor := by
  intro k hk
  obtain ⟨p,hp,d,hd,hk⟩ := occupied_ancestor_has_original_realizer E Phi fine center rho ancestor realizer hk
  exact Finset.mem_image.mpr ⟨realizer p d,hrealizer p hp d (Finset.mem_filter.mp hd).1,hk⟩

/-- Geometric containment of each original fine-label realizer's full cell
 covers every tube in the constructed carrier saturation. -/
theorem labelwise_containment_covers_full_saturation
    (E : Finset P) (Phi : P → Finset D) (fine : D → U) (center : P → U)
    (rho : ℝ) (ancestor : T → K) (realizer : P → D → T) (Tfull : Finset T)
    (tube : T → Set X) (box : Set X)
    (hlabel : ∀ p ∈ E, ∀ d ∈ nearDirections Phi fine center rho p,
      ∀ t ∈ Tfull, ancestor t=ancestor (realizer p d) → tube t ⊆ box) :
    ∀ t ∈ Tfull,
      ancestor t ∈ occupiedAncestors E Phi fine center rho ancestor realizer → tube t ⊆ box := by
  intro t ht hk
  obtain ⟨p,hp,d,hd,hk⟩ := occupied_ancestor_has_original_realizer E Phi fine center rho ancestor realizer hk
  exact hlabel p hp d hd t ht hk.symm

/-- Direct original-family CW count, with the carrier lower law stated on
 every original tube's actual ancestor and the occupied image constructed
 from genuine original point/fine-label realizers. -/
theorem original_realizer_carrier_CW_count
    (E : Finset P) (Phi : P → Finset D) (fine : D → U) (center : P → U)
    (rho : ℝ) (ancestor : T → K) (realizer : P → D → T) (Tfull : Finset T)
    (tube : T → Set X) (box : Set X) {Lcarrier CW volumeBox : ℝ}
    (hrealizer : ∀ p ∈ E, ∀ d ∈ Phi p, realizer p d ∈ Tfull)
    (hAD : ∀ t ∈ Tfull,
      Lcarrier ≤ ((Tfull.filter (fun s => ancestor s=ancestor t)).card : ℝ))
    (hlabel : ∀ p ∈ E, ∀ d ∈ nearDirections Phi fine center rho p,
      ∀ t ∈ Tfull, ancestor t=ancestor (realizer p d) → tube t ⊆ box)
    (hCW : ((Tfull.filter (fun t => tube t ⊆ box)).card : ℝ) ≤ CW*volumeBox*Tfull.card) :
    ((occupiedAncestors E Phi fine center rho ancestor realizer).card : ℝ)*Lcarrier ≤
      CW*volumeBox*Tfull.card := by
  apply original_carrier_convex_count Tfull ancestor
    (occupiedAncestors E Phi fine center rho ancestor realizer) tube box
  · intro k hk
    have href := occupied_ancestors_mem_reference E Phi fine center rho ancestor realizer Tfull hrealizer hk
    obtain ⟨t,ht,hk⟩ := Finset.mem_image.mp href
    simpa only [hk] using hAD t ht
  · exact labelwise_containment_covers_full_saturation E Phi fine center rho ancestor realizer Tfull tube box hlabel
  · exact hCW

end OriginalCarrierImageCount
