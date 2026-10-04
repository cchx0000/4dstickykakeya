import Theorems.Thm_StickyKakeya4_original_shading_cell_mass
import Theorems.Thm_StickyKakeya4_original_shading_representatives
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

noncomputable section
open Classical
namespace OriginalShadingRepresentativeFrostman
local instance : DecidableEq (ℤ×ℤ) := Classical.decEq _
open DyadicOriginalFiberSelection OriginalShadingCellMass OriginalShadingGridGeometry
open OriginalShadingRepresentatives

/-- The separated representatives inherit the original shading profile.
The factor18 is exactly two for occupancy and nine for cell coloring. -/
theorem original_representative_frostman {X : Type*}
    (Y R : Finset X) (p : X → ℝ×ℝ) (j : ℕ) {h L K s : ℝ}
    (hh : 0<h) (hL : 0≤L) (hK : 1≤K) (hs : 0≤s)
    (hRY : R ⊆ bin Y (fun y => grid h (p y)) j)
    (hinj : Set.InjOn (fun y => grid h (p y)) (↑R))
    (hretain : (Y.card : ℝ) ≤ L*(bin Y (fun y => grid h (p y)) j).card)
    (hRcard : ((bin Y (fun y => grid h (p y)) j).image
      (fun y => grid h (p y))).card ≤ 9*R.card)
    (hpoint : ∀ (x : ℝ×ℝ) (r : ℝ), h≤r → r≤1 →
      ((Y.filter (fun y => InBox (p y) x r)).card : ℝ) ≤ K*r^s*Y.card)
    (x : ℝ×ℝ) {r : ℝ} (hr : h≤r) :
    ((R.filter (fun y => InBox (p y) x r)).card : ℝ) ≤
      18*L*(K*(2*r)^s)*R.card := by
  let U := (bin Y (fun y => grid h (p y)) j).image (fun y => grid h (p y))
  let Z := R.filter (fun y => InBox (p y) x r)
  let V := Z.image (fun y => grid h (p y))
  have hV : V ⊆ U := Finset.image_subset_image ((Finset.filter_subset _ _).trans hRY)
  have hrpos : 0<r := hh.trans_le hr
  have hB : 0≤K*(2*r)^s := mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
  have hcap : ((Y.filter (fun y => grid h (p y)∈V)).card : ℝ) ≤
      (K*(2*r)^s)*Y.card := by
    by_cases htop : 2*r≤1
    · have hsub : Y.filter (fun y => grid h (p y)∈V) ⊆
          Y.filter (fun y => InBox (p y) x (2*r)) := by
        intro y hy
        obtain ⟨hy,hc⟩ := Finset.mem_filter.mp hy
        obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hc
        have hc := (same_cell_close hh (p y) (p a) he.symm).trans
          (Finset.mem_filter.mp ha).2
        exact Finset.mem_filter.mpr ⟨hy,hc.mono (by linarith)⟩
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        (hpoint x (2*r) (by linarith) htop)
    · have hpow : 1≤(2*r)^s := Real.one_le_rpow (by linarith) hs
      have hfac : 1≤K*(2*r)^s := by nlinarith only [hK,hpow]
      have htotal : ((Y.filter (fun y => grid h (p y)∈V)).card : ℝ) ≤Y.card :=
        Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      exact htotal.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac
          (show (0:ℝ)≤Y.card by positivity))
  have hcoarse := coarse_fraction_from_original_points Y (fun y => grid h (p y)) j
    V L (K*(2*r)^s) hL hB hretain hV hcap
  have heq : V.card=Z.card := Finset.card_image_iff.mpr
    (hinj.mono (Finset.filter_subset _ _))
  rw [heq] at hcoarse
  have hcard : (U.card : ℝ) ≤9*R.card := by exact_mod_cast hRcard
  have hfinal := hcoarse.trans (mul_le_mul_of_nonneg_left hcard
    (show 0≤2*L*(K*(2*r)^s) by positivity))
  change (Z.card : ℝ) ≤ _
  nlinarith only [hfinal]

end OriginalShadingRepresentativeFrostman
