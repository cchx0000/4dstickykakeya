import Theorems.Thm_StickyKakeya4_native_terminal_old_ancestor_fiber
import Theorems.Thm_StickyKakeya4_original_carrier_image_count

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeOldAncestorCWCount
open Classical Finset StickyKakeya4 NativeOriginalParentSelection
open NativeCappedOldAncestors OriginalAncestorCounting OriginalCarrierImageCount

/-- The original CW combinator consumes the COMPLETE old occupied-parent
population. Its lower fiber law is derived from the original parent/child
counts, and the tube index set is exactly the existing fullSource index set.
Containment is the separate geometric saturation statement. -/
theorem original_full_carrier_CW_count
    {Point Fine U X : Type*} [NormedAddCommGroup U]
    {n : ℕ} {D : FiniteScaleSource n} {eta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (b : ℕ)
    (H : ∀ j : Fin (b+1), ∀ q : Parent,
      (R.filter (fun i => parentLabel D a (2^j.val) i=q)).Nonempty →
        D.thickness^e*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^j.val) i=q)).card:ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^j.val) i=q)).card:ℝ) ≤
          D.thickness^(-e)*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3)
    (k : ℕ) (hk : k ≤ b)
    (points : Finset Point) (Phi : Point → Finset Fine) (fine : Fine → U)
    (center : Point → U) (rho : ℝ)
    (realizer : Point → Fine → Fin (R.image (parentLabel D a (2^b))).card)
    (tube : Fin (R.image (parentLabel D a (2^b))).card → Set X) (box : Set X)
    (CW volumeBox : ℝ)
    (hlabel : ∀ p∈points, ∀ d∈nearDirections Phi fine center rho p,
      ∀ t, oldAncestor D R a b k t=oldAncestor D R a b k (realizer p d) → tube t⊆box)
    (hCW : (((univ : Finset (Fin (R.image (parentLabel D a (2^b))).card)).filter
        (fun t => tube t⊆box)).card:ℝ) ≤ CW*volumeBox*(R.image (parentLabel D a (2^b))).card) :
    ((occupiedAncestors points Phi fine center rho (oldAncestor D R a b k) realizer).card:ℝ)*
      (D.thickness^(2*e)*(((2^b:ℕ):ℝ)/((2^k:ℕ):ℝ))^3) ≤
        CW*volumeBox*(R.image (parentLabel D a (2^b))).card := by
  have hh := original_realizer_carrier_CW_count points Phi fine center rho
    (oldAncestor D R a b k) realizer univ tube box
    (fun _ _ _ _ => mem_univ _)
    (fun i _ => full_fiber_population h R a b H k hk i)
    (fun p hp d hd t _ he => hlabel p hp d hd t he)
    (by simpa only [card_univ, Fintype.card_fin] using hCW)
  simpa only [card_univ, Fintype.card_fin] using hh

/-- When the chosen cap is terminal, the very same carrier argument has
denominator one, proved from the actual index fiber. No parent population
estimate is needed in this branch. -/
theorem original_terminal_carrier_CW_count
    {Point Fine U X : Type*} [NormedAddCommGroup U]
    {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) (a : ℝ)
    (b k : ℕ) (hk : k=b)
    (points : Finset Point) (Phi : Point → Finset Fine) (fine : Fine → U)
    (center : Point → U) (rho : ℝ)
    (realizer : Point → Fine → Fin (R.image (parentLabel D a (2^b))).card)
    (tube : Fin (R.image (parentLabel D a (2^b))).card → Set X) (box : Set X)
    (CW volumeBox : ℝ)
    (hrealizer : ∀ p∈points, ∀ d∈nearDirections Phi fine center rho p,
      tube (realizer p d)⊆box)
    (hCW : (((univ : Finset (Fin (R.image (parentLabel D a (2^b))).card)).filter
        (fun t => tube t⊆box)).card:ℝ) ≤ CW*volumeBox*(R.image (parentLabel D a (2^b))).card) :
    ((occupiedAncestors points Phi fine center rho (oldAncestor D R a b k) realizer).card:ℝ) ≤
      CW*volumeBox*(R.image (parentLabel D a (2^b))).card := by
  have hpopulation (i : Fin (R.image (parentLabel D a (2^b))).card) :
      (1:ℝ) ≤ (((univ : Finset (Fin (R.image (parentLabel D a (2^b))).card)).filter
        (fun j => oldAncestor D R a b k j=oldAncestor D R a b k i)).card:ℝ) := by
    rw [NativeTerminalOldAncestorFiber.terminal_fiber_card D R a b k hk i]
    norm_num
  have hlabel (p : Point) (hp : p∈points)
      (d : Fine) (hd : d∈nearDirections Phi fine center rho p)
      (t : Fin (R.image (parentLabel D a (2^b))).card)
      (he : oldAncestor D R a b k t=oldAncestor D R a b k (realizer p d)) : tube t⊆box := by
    have ht : t=realizer p d := terminal_injective D R a b (by simpa only [hk] using he)
    simpa only [ht] using hrealizer p hp d hd
  have hh := original_realizer_carrier_CW_count points Phi fine center rho
    (oldAncestor D R a b k) realizer univ tube box
    (fun _ _ _ _ => mem_univ _)
    (fun i _ => hpopulation i)
    (fun p hp d hd t _ he => hlabel p hp d hd t he)
    (by simpa only [card_univ, Fintype.card_fin] using hCW)
  simpa only [mul_one, card_univ, Fintype.card_fin] using hh

end NativeOldAncestorCWCount
