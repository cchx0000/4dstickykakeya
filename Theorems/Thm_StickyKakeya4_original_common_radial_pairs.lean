import Theorems.Thm_StickyKakeya4_original_common_scalar_fibers
import Theorems.Thm_StickyKakeya4_original_scalar_collision_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open Finset
open scoped BigOperators
noncomputable section
open Classical
namespace OriginalCommonRadialPairs
open OriginalCommonScalarFibers
abbrev Point := ℝ × ℝ

def closePairs (B : Finset Point) (d : ℝ) :=
  (B ×ˢ B).filter (fun bb => ‖bb.1-bb.2‖ < d)

def farPairs (H : Finset (Point × Point)) (d : ℝ) :=
  H.filter (fun bb => d ≤ ‖bb.1-bb.2‖)

/-- Native original B ball counts control actual near-diagonal ordered pairs. -/
theorem closePairs_card (B : Finset Point) {d kappa : ℝ}
    (hballs : ∀ b ∈ B, ((B.filter (fun b' => ‖b'-b‖ ≤ d)).card : ℝ) ≤ kappa*B.card) :
    ((closePairs B d).card : ℝ) ≤ kappa*(B.card : ℝ)^2 := by
  let P := closePairs B d
  have hfib : ∀ b ∈ B, ((P.filter (fun bb => bb.1=b)).card : ℝ) ≤ kappa*B.card := by
    intro b hb
    have hh : (P.filter (fun bb => bb.1=b)).card ≤
        (B.filter (fun b' => ‖b'-b‖ ≤ d)).card := by
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro bb hbb
        obtain ⟨hbbP,hbb1⟩ := Finset.mem_filter.mp hbb
        obtain ⟨hbbB,hclose⟩ := Finset.mem_filter.mp hbbP
        refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hbbB).2,?_⟩
        rw [hbb1,norm_sub_rev] at hclose
        exact hclose.le
      · intro bb hbb cc hcc hbc
        exact Prod.ext ((Finset.mem_filter.mp hbb).2.trans (Finset.mem_filter.mp hcc).2.symm) hbc
    exact (Nat.cast_le.mpr hh).trans (hballs b hb)
  have hsum : (P.card : ℝ)=∑ b ∈ B, ((P.filter (fun bb => bb.1=b)).card : ℝ) := by
    have hh : P.card=∑ b ∈ B, (P.filter (fun bb => bb.1=b)).card :=
      Finset.card_eq_sum_card_fiberwise (fun bb hbb =>
        (Finset.mem_product.mp (Finset.mem_filter.mp hbb).1).1)
    exact_mod_cast hh
  rw [hsum]
  calc
    _ ≤ ∑ _b ∈ B, kappa*(B.card : ℝ) := Finset.sum_le_sum hfib
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- Prune short original B secants in addition to the actual missing radial
pairs; both deletion costs are counted on the original B² carrier. -/
theorem farPairs_complement_card (B : Finset Point) (H : Finset (Point × Point))
    {d mu kappa : ℝ}
    (hbad : (((B ×ˢ B) \ H).card : ℝ) ≤ mu*(B.card : ℝ)^2)
    (hballs : ∀ b ∈ B, ((B.filter (fun b' => ‖b'-b‖ ≤ d)).card : ℝ) ≤ kappa*B.card) :
    (((B ×ˢ B) \ farPairs H d).card : ℝ) ≤ (mu+kappa)*(B.card : ℝ)^2 := by
  have hsub : (B ×ˢ B) \ farPairs H d ⊆ ((B ×ˢ B) \ H) ∪ closePairs B d := by
    intro bb hbb
    obtain ⟨hbbB,hnot⟩ := Finset.mem_sdiff.mp hbb
    by_cases hh : bb ∈ H
    · have hn : ¬d ≤ ‖bb.1-bb.2‖ := fun h => hnot (Finset.mem_filter.mpr ⟨hh,h⟩)
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbbB,lt_of_not_ge hn⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hbbB,hh⟩)
  have hc : (((B ×ˢ B) \ farPairs H d).card : ℝ) ≤
      (((B ×ˢ B) \ H).card : ℝ)+(closePairs B d).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hnear := closePairs_card B hballs
  nlinarith only [hc,hbad,hnear]

/-- Construct the actual common-C/radial/secant graph needed by p91.
The radial graph remains the caller's genuine original graph; all newly
selected pairs keep their original common scalar labels. -/
theorem exists_common_radial_pairs (B : Finset Point) (C : Finset ℝ)
    (F : Finset (Point × ℝ)) (H : Finset (Point × Point))
    {tau d mu kappa : ℝ} (hC : C.Nonempty) (htau : 0 ≤ tau)
    (hF : F ⊆ B ×ˢ C) (hmass : tau*B.card*C.card ≤ (F.card : ℝ))
    (hH : H ⊆ B ×ˢ B)
    (hbad : (((B ×ˢ B) \ H).card : ℝ) ≤ mu*(B.card : ℝ)^2)
    (hballs : ∀ b ∈ B, ((B.filter (fun b' => ‖b'-b‖ ≤ d)).card : ℝ) ≤ kappa*B.card)
    (hbudget : mu+kappa ≤ tau^2/4) :
    ∃ R : Finset (Point × Point), R ⊆ H ∧ R ⊆ B ×ˢ B ∧
      (tau^2/4)*(B.card : ℝ)^2 ≤ R.card ∧
      ∀ bb ∈ R, d ≤ ‖bb.1-bb.2‖ ∧ (tau^2/2)*C.card ≤ (commonFiber F C bb.1 bb.2).card := by
  let R := richPairs B C F (tau^2/2) ∩ farPairs H d
  have hfar := farPairs_complement_card B H hbad hballs
  have hbad' : (((B ×ˢ B) \ farPairs H d).card : ℝ) ≤ (tau^2/4)*(B.card : ℝ)^2 :=
    hfar.trans (mul_le_mul_of_nonneg_right hbudget (by positivity))
  have hR := richPairs_inter_card_lower B C F (farPairs H d) hC htau hF hmass hbad'
  refine ⟨R,?_,?_,hR,?_⟩
  · intro bb hbb
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hbb).2).1
  · intro bb hbb
    exact hH (Finset.mem_filter.mp (Finset.mem_inter.mp hbb).2).1
  · intro bb hbb
    obtain ⟨hrich,hfar⟩ := Finset.mem_inter.mp hbb
    exact ⟨(Finset.mem_filter.mp hfar).2,richPairs_common_lower B C F (tau^2/2) hrich⟩
end OriginalCommonRadialPairs
