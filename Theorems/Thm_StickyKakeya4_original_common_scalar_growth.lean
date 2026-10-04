import Theorems.Thm_StickyKakeya4_original_directional_double_count
import Theorems.Thm_StickyKakeya4_original_common_radial_pairs
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
open Finset
open scoped Pointwise
noncomputable section
open Classical
namespace OriginalCommonScalarGrowth
open OriginalCommonRadialPairs OriginalDirectionalDoubleCount OriginalCommonFiberProjection
open OriginalCommonScalarFibers OriginalPhysicalPairTube VectorGraphCollisionEnergy PlanarShiftedNearEnergy
abbrev Point := ℝ × ℝ

/-- The complete finite p91 continuation from genuine Eq169 data. Common-C
pairs, far secants, separated A-pair collisions, and the directional upper
count are all constructed. The only radial input is an actual original-B
physical-pair tube population cap at the explicitly required width. -/
theorem original_common_scalar_growth (A B : Finset Point) (C : Finset ℝ)
    (F : Finset (Point × ℝ)) (H : Finset (Point × Point))
    {eta delta d t s r Q N tau chi mu kappa cap : ℝ}
    (heta : 0 < eta) (hdelta : 0 < delta) (hd : 0 < d) (ht : 0 ≤ t) (hs : 0 < s)
    (hr : 0 < r) (hQ : 0 < Q) (htau : 0 < tau) (hchi : 0 ≤ chi) (hcap0 : 0 ≤ cap)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (hF : F ⊆ B ×ˢ C) (hFmass : tau*B.card*C.card ≤ (F.card : ℝ))
    (hH : H ⊆ B ×ˢ B)
    (hmissing : (((B ×ˢ B) \ H).card : ℝ) ≤ mu*(B.card : ℝ)^2)
    (hBballs : ∀ b ∈ B, ((B.filter (fun b' => ‖b'-b‖ ≤ d)).card : ℝ) ≤ kappa*B.card)
    (hpairbudget : mu+kappa ≤ tau^2/4)
    (hbox : ∀ b ∈ B, ‖b‖ ≤ 1)
    (hradial : ∀ bb ∈ H, ((physicalPairTube B (8*eta/s) bb).card : ℝ) ≤ cap*B.card)
    (hscale : s+eta ≤ d*t)
    (hAsep : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → eta ≤ ‖a-a'‖)
    (hCsep : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → delta ≤ |c-c'|)
    (hCcap : ∀ c ∈ C, ((C.filter (fun c' => |c'-c| ≤ t)).card : ℝ) ≤ chi*C.card)
    (hret : r*N ≤ A.card)
    (hcover : (((A+F.image productValue-F.image productValue).image (roundPoint eta)).card : ℝ) ≤ Q*N)
    (hscalarbudget : 32*chi ≤ r*(tau^2/2)^2/Q) :
    (tau^2/4)*((r*(tau^2/2)^2/Q)/(2*(2*((eta/d)/delta)+2)))*C.card ≤ cap*A.card := by
  obtain ⟨R,hRH,hRB,hRmass,hRfibers⟩ := exists_common_radial_pairs B C F H hC htau.le
    hF hFmass hH hmissing hBballs hpairbudget
  have hdistinct : ∀ bb ∈ R, bb.1 ≠ bb.2 := by
    intro bb hbb heq
    have hh := (hRfibers bb hbb).1
    rw [heq,sub_self,norm_zero] at hh
    exact (not_le_of_gt hd) hh
  have hcounts : ∀ bb ∈ R,
      ((r*(tau^2/2)^2/Q)/(2*(2*((eta/d)/delta)+2)))*A.card*C.card ≤
        (projectedPairs A (bb.1-bb.2) eta s).card := by
    intro bb hbb
    exact common_fiber_projected_pairs A C F bb.1 bb.2 heta hdelta hd ht hr hQ
      (by positivity) hchi hA hC (hRfibers bb hbb).1 hscale hAsep hCsep hCcap
      hret (hRfibers bb hbb).2 hcover hscalarbudget
  exact original_pair_double_count_growth A B C R heta hs hcap0 (by positivity) hA hB
    hRB hRmass hdistinct hbox (fun bb hbb => hradial bb (hRH hbb)) hcounts
end OriginalCommonScalarGrowth
