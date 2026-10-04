import Theorems.Thm_StickyKakeya4_original_shading_cell_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

noncomputable section
open Classical
open scoped BigOperators
namespace OriginalShadingCellMass
open DyadicOriginalFiberSelection OriginalShadingCellSelection

/-- The local occupancy class has at most twice its common lower occupancy
per occupied cell, with the ORIGINAL shading fibers. -/
theorem bin_card_le_twice_occupancy {X C : Type*}
    (Y : Finset X) (grid : X → C) (j : ℕ) :
    (bin Y grid j).card ≤ 2 * 2^j * ((bin Y grid j).image grid).card := by
  calc
    _ = ∑ c∈(bin Y grid j).image grid, (fiber (bin Y grid j) grid c).card :=
      (fiber_sum _ _).symm
    _ ≤ ∑ _c∈(bin Y grid j).image grid, 2^(j+1) :=
      Finset.sum_le_sum (fun c hc => (bin_fiber_bounds Y grid j hc).2.le)
    _ = _ := by simp [pow_succ]; ring

/-- Uniform cell-count binning preserves the original fine shading mass
through the product of the two selected dyadic parameters. -/
theorem original_mass_le_four_log_occupancy_cells {X C : Type*}
    (Y : Finset X) (grid : X → C) (j k L : ℕ)
    (hretain : Y.card ≤ L*(bin Y grid j).card)
    (hcells : ((bin Y grid j).image grid).card < 2^(k+1)) :
    Y.card ≤ 4*L*2^j*2^k := by
  have hbin := bin_card_le_twice_occupancy Y grid j
  have h := hretain.trans (Nat.mul_le_mul_left L hbin)
  have h' := Nat.mul_le_mul_left (L*(2*2^j)) hcells.le
  simp only [pow_succ] at h'
  nlinarith only [h,h']

/-- A selected collection of cells is charged to fine points of this same
original shading, without using a global point-cell maximum. -/
theorem selected_cells_original_charge {X C : Type*}
    (Y : Finset X) (grid : X → C) (j : ℕ) (V : Finset C)
    (hV : V ⊆ (bin Y grid j).image grid) :
    2^j * V.card ≤ (Y.filter (fun y => grid y∈V)).card := by
  apply original_cell_charge Y V grid (2^j)
  intro c hc
  have h := (bin_fiber_bounds Y grid j (hV hc)).1
  rw [fiber_bin_eq Y grid j (hV hc)] at h
  exact h

/-- Actual fine-point concentration transfers to COARSE cell concentration
with the explicit factor two times the actual retention loss. -/
theorem coarse_fraction_from_original_points {X C : Type*}
    (Y : Finset X) (grid : X → C) (j : ℕ) (V : Finset C) (L B : ℝ)
    (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hretain : (Y.card : ℝ) ≤ L*(bin Y grid j).card)
    (hV : V ⊆ (bin Y grid j).image grid)
    (hcap : ((Y.filter (fun y => grid y∈V)).card : ℝ) ≤ B*Y.card) :
    (V.card : ℝ) ≤ 2*L*B*((bin Y grid j).image grid).card := by
  have hcharge : (2:ℝ)^j*V.card ≤ (Y.filter (fun y => grid y∈V)).card := by
    exact_mod_cast selected_cells_original_charge Y grid j V hV
  have hbin : ((bin Y grid j).card : ℝ) ≤
      2*(2:ℝ)^j*((bin Y grid j).image grid).card := by
    exact_mod_cast bin_card_le_twice_occupancy Y grid j
  have hmass := hretain.trans (mul_le_mul_of_nonneg_left hbin hL)
  have hcap' := hcap.trans (mul_le_mul_of_nonneg_left hmass hB)
  have hpow : (0:ℝ)<2^j := by positivity
  nlinarith only [hcharge,hcap',hpow]

end OriginalShadingCellMass
