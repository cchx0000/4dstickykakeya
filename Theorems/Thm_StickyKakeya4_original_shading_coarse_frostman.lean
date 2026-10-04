import Theorems.Thm_StickyKakeya4_original_shading_cell_mass
import Theorems.Thm_StickyKakeya4_original_shading_grid_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace OriginalShadingCoarseFrostman
local instance : DecidableEq (ℤ×ℤ) := Classical.decEq _
open DyadicOriginalFiberSelection OriginalShadingCellMass OriginalShadingGridGeometry

/-- Original fine-shading Frostman control transfers to the actual occupied
coarse grid, paying only the verified logarithmic retention and radius 2R.
The case 2R>1 uses total original mass, not an out-of-range profile premise. -/
theorem coarse_grid_frostman {X : Type*} (Y : Finset X) (p : X → ℝ×ℝ)
    (j : ℕ) {h L K s : ℝ} (hh : 0<h) (hL : 0≤L) (hK : 1≤K) (hs : 0≤s)
    (hretain : (Y.card : ℝ) ≤ L*(bin Y (fun y => grid h (p y)) j).card)
    (hpoint : ∀ (x : ℝ×ℝ) (r : ℝ), h≤r → r≤1 →
      ((Y.filter (fun y => InBox (p y) x r)).card : ℝ) ≤ K*r^s*Y.card)
    (x : ℝ×ℝ) {R : ℝ} (hR : h≤R) :
    let U := (bin Y (fun y => grid h (p y)) j).image (fun y => grid h (p y))
    ((U.filter (fun c => InBox (corner h c) x R)).card : ℝ) ≤
      2*L*(K*(2*R)^s)*U.card := by
  let U := (bin Y (fun y => grid h (p y)) j).image (fun y => grid h (p y))
  let V := U.filter (fun c => InBox (corner h c) x R)
  have hRpos : 0<R := hh.trans_le hR
  have hB : 0 ≤ K*(2*R)^s := mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
  change (V.card : ℝ) ≤ 2*L*(K*(2*R)^s)*U.card
  apply coarse_fraction_from_original_points Y (fun y => grid h (p y)) j V L
    (K*(2*R)^s) hL hB hretain (Finset.filter_subset _ _)
  have hsub : Y.filter (fun y => grid h (p y)∈V) ⊆
      Y.filter (fun y => InBox (p y) x (2*R)) := by
    intro y hy
    obtain ⟨hy,hc⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hy,coarse_box_original_preimage hh hR (p y) x
      (Finset.mem_filter.mp hc).2⟩
  have hcard : ((Y.filter (fun y => grid h (p y)∈V)).card : ℝ) ≤
      (Y.filter (fun y => InBox (p y) x (2*R))).card := by
    exact_mod_cast Finset.card_le_card hsub
  by_cases htop : 2*R≤1
  · exact hcard.trans (hpoint x (2*R) (by linarith) htop)
  · have hpow : 1 ≤ (2*R)^s := Real.one_le_rpow (by linarith) hs
    have hfac : 1 ≤ K*(2*R)^s := by nlinarith only [hK,hpow]
    have htotal : ((Y.filter (fun y => grid h (p y)∈V)).card : ℝ) ≤ Y.card := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    exact htotal.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac
        (show (0:ℝ)≤Y.card by positivity))

end OriginalShadingCoarseFrostman
