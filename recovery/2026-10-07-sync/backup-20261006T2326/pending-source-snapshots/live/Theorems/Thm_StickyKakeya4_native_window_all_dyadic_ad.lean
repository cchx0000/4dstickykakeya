import Theorems.Thm_StickyKakeya4_native_window_middle_contraction
import Theorems.Thm_StickyKakeya4_native_window_coarse_contraction

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeWindowAllDyadicAD
open Classical Finset NativeWindowXYLabels NativeWindowNesting NativeWindowRealInterpolation
open NativeWindowMiddleContraction NativeWindowCoarseContraction NativeWindowInterpolationCost
open NativeWindowCoarseEndpoint NativeWindowQuotientTransport NativeReferenceXYGridPoints
open NativeSquaredGrainQueries FiniteVoronoiRealADCoarsening

/-- One finite menu supplies every dyadic coarse time window of the SAME
source, after the final chart contraction, at every real spatial radius.
The explicit second bound is the actual global quotient population needed
for the paper's localized occupied-cell cover formulation. -/
theorem all_dyadic_windows {k l J : ℕ} (S : Finset (XY k l))
    (m : ℕ) (hm : 6 ≤ m) (hJ : 0 < J) (hl : l ≤ 2) {K s : ℝ}
    (hK : 1 ≤ K) (hs : 0 ≤ s) (hs2 : s ≤ 2)
    (H : ∀i : Fin (J+1),∀z∈S,
      ADBounds (points S (factor m (NativeFixedHorizontalMenu.depths J m i))
        (mu m*(factor m (NativeFixedHorizontalMenu.depths J m i):ℝ)) z)
        (mu m*(factor m (NativeFixedHorizontalMenu.depths J m i):ℝ)) K s)
    (Hglobal : ∀i : Fin (J+1),∀z∈S,
      ((atPoint S (factor m (NativeFixedHorizontalMenu.depths J m i)) z).card:ℝ) ≤
        K*(windowHalfWidth m (NativeFixedHorizontalMenu.depths J m i):ℝ)^s)
    (Hheight : ∀w∈S,|w.1| ≤ 4*(factor m m:ℤ))
    (v : ℕ) (hfinal : mu m*((2^v:ℕ):ℝ)/512 ≤ 1) (z : XY k l) (hz : z∈S) :
    let B : ℝ := ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)
    let rho := mu m*((2^v:ℕ):ℝ)/512
    let C := (2:ℝ)^40*K*B^2
    ADBounds (points S (2^v) rho z) rho C s ∧
      ((atPoint S (2^v) z).card:ℝ) ≤ C*rho^(-s) := by
  intro B rho C
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hrho : 0 < rho := by dsimp [rho]; exact div_pos (mul_pos (mu_pos m) (by positivity)) (by norm_num)
  have hB1 : 1 ≤ B := by
    dsimp [B]
    exact_mod_cast (by positivity : 0 < (2:ℕ)^((phaseDepth m-m)/J+1))
  by_cases hmid : v ≤ phaseDepth m-m
  · let f := phaseDepth m-v
    have hmf : m ≤ f := by dsimp [f]; omega
    have hfb : f ≤ phaseDepth m := Nat.sub_le _ _
    have hfactor : factor m f=2^v := by
      unfold factor
      congr 1
      dsimp [f]
      omega
    have HH := middle_contracted_AD S m hm hJ hl hK hs hs2 H Hglobal f hmf hfb z hz
    dsimp only at HH
    rw [hfactor] at HH
    have hcost : (512:ℝ)^s*(36*K*B^2) ≤ C := final_middle_cost_le hKp.le hs2
    exact ⟨AD_mono _ hrho (by positivity) hcost HH.1,
      HH.2.trans (mul_le_mul_of_nonneg_right hcost (by positivity))⟩
  · let D := (2:ℕ)^(v-(phaseDepth m-m))
    have hD : 0 < D := by dsimp [D]; positivity
    have hR : 0 < factor m m := by unfold factor; positivity
    have hmb : m ≤ phaseDepth m := by unfold phaseDepth; omega
    have hscale := window_mesh_halfWidth m m hm le_rfl hmb
    have hbase : mu m*(factor m m:ℝ)=(1/64:ℝ) := by
      norm_num [windowHalfWidth] at hscale
      nlinarith only [hscale]
    have hprod : factor m m*D=2^v := by
      unfold factor
      dsimp [D]
      rw [←pow_add]
      congr 1
      omega
    have hphysical : (mu m*(factor m m:ℝ))*(D:ℝ)/512=rho := by
      dsimp [rho]
      rw [mul_assoc,←Nat.cast_mul,hprod]
    have HG0 : ((atPoint S (factor m m) z).card:ℝ) ≤ K*(32:ℝ)^s := by
      have hh := Hglobal 0 z hz
      norm_num [NativeFixedHorizontalMenu.depths_zero,windowHalfWidth] at hh
      exact hh
    have HH := coarse_contracted_AD S (factor m m) D hR hD Hheight z hz
      (by rw [hbase]) hK hs hs2 HG0 (by rw [hphysical]; exact hfinal)
    rw [hprod,hphysical] at HH
    have hcost : (2:ℝ)^40*K ≤ C := final_coarse_cost_le hKp.le hB1
    exact ⟨AD_mono _ hrho (by positivity) hcost HH.1,
      HH.2.trans (mul_le_mul_of_nonneg_right hcost (by positivity))⟩

end NativeWindowAllDyadicAD
