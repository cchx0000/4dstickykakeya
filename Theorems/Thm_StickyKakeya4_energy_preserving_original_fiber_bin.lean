import Theorems.Thm_StickyKakeya4_heavy_energy_bin_selection
import Theorems.Thm_StickyKakeya4_original_fiber_energy_collapse

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped BigOperators
noncomputable section

namespace EnergyPreservingOriginalFiberBin
open TwoTubePathCollisionCount DyadicOriginalFiberSelection

/-- A single actual original-fiber bin retains original label mass and has
large UNWEIGHTED additive energy. All population caps are derived from the
constructed dyadic bin, rather than supplied as certificates. -/
theorem exists_energy_preserving_bin
    {G P : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq P]
    (A : Finset G) (W : Finset P) (f : P → G)
    (hA : A.Nonempty) (hW : W.Nonempty) {nu : ℝ} (hnu : 0<nu)
    (he : nu*(A.card : ℝ)*(W.card : ℝ)^2 ≤
      ((collisions (A.product W) (fun p => p.1+f p.2)).card : ℝ)) :
    ∃ j<levelCount W, (bin W f j).Nonempty ∧
      nu*(W.card : ℝ)≤2*(levelCount W : ℝ)*(bin W f j).card ∧
      nu*(A.card : ℝ)*(((bin W f j).image f).card : ℝ)^2 ≤
        8*(levelCount W : ℝ)^2*(Finset.addEnergy A ((bin W f j).image f) : ℝ) := by
  obtain ⟨j,hj,hbin,hm,hebin⟩ :=
    HeavyEnergyBinSelection.exists_original_energy_bin A W f hA hW hnu he
  have hf : ∀ s∈(bin W f j).image f, (fiber (bin W f j) f s).card≤2^(j+1) :=
    fun s hs => (bin_fiber_bounds W f j hs).2.le
  have hcollapse := OriginalFiberEnergyCollapse.labelled_sum_energy_le A (bin W f j) f (2^(j+1)) hf
  have hcollapseR : ((collisions (A.product (bin W f j)) (fun p => p.1+f p.2)).card : ℝ) ≤
      4*((2:ℝ)^j)^2*(Finset.addEnergy A ((bin W f j).image f) : ℝ) := by
    have hcast : ((collisions (A.product (bin W f j)) (fun p => p.1+f p.2)).card : ℝ) ≤
        ((2:ℝ)^(j+1))^2*(Finset.addEnergy A ((bin W f j).image f) : ℝ) := by
      exact_mod_cast hcollapse
    calc
      _ ≤ _ := hcast
      _ = _ := by rw [pow_succ]; ring
  have hmass : 2^j*((bin W f j).image f).card≤(bin W f j).card := by
    rw [← fiber_sum (bin W f j) f]
    have hs := Finset.sum_le_sum (fun s (hs : s∈(bin W f j).image f) => (bin_fiber_bounds W f j hs).1)
    simpa only [Finset.sum_const,Nat.nsmul_eq_mul,Nat.mul_comm] using hs
  have hmassW : (2:ℝ)^j*((((bin W f j).image f).card : ℕ) : ℝ)≤(W.card : ℝ) := by
    exact_mod_cast hmass.trans (Finset.card_le_card (Finset.filter_subset _ _))
  have hpow := pow_le_pow_left₀ (by positivity : 0≤(2:ℝ)^j*((((bin W f j).image f).card : ℕ) : ℝ)) hmassW 2
  have hlow := mul_le_mul_of_nonneg_left hpow (mul_nonneg hnu.le (Nat.cast_nonneg A.card))
  have hupp := mul_le_mul_of_nonneg_left hcollapseR (by positivity : 0≤2*(levelCount W : ℝ)^2)
  have hcombined := hlow.trans (hebin.trans hupp)
  have hh : 0<((2:ℝ)^j)^2 := by positivity
  have hfinal : nu*(A.card : ℝ)*(((bin W f j).image f).card : ℝ)^2 ≤
      8*(levelCount W : ℝ)^2*(Finset.addEnergy A ((bin W f j).image f) : ℝ) := by
    apply (mul_le_mul_iff_left₀ hh).mp
    nlinarith only [hcombined]
  exact ⟨j,hj,hbin,hm,hfinal⟩

end EnergyPreservingOriginalFiberBin
