import Theorems.Thm_StickyKakeya4_native_window_coarse_endpoint
import Theorems.Thm_StickyKakeya4_native_grid_center_contraction
import Theorems.Thm_StickyKakeya4_native_window_interpolation_cost

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeWindowCoarseContraction
open Classical Finset NativeWindowXYLabels NativeWindowNesting NativeWindowRealInterpolation
open NativeWindowCoarseEndpoint NativeGridCenterContraction NativeWindowInterpolationCost
open FiniteVoronoiRealADCoarsening

/-- All time windows beyond the coarsest prepared one have final mesh at
least1/32768. The actual global quotient count and each occupied center
therefore suffice; no source AD is tested outside its original range. -/
theorem coarse_contracted_AD {k l : ℕ} (S : Finset (XY k l))
    (R D : ℕ) (hR : 0 < R) (hD : 0 < D)
    (hheight : ∀w∈S,|w.1| ≤ 4*(R:ℤ)) (z : XY k l) (hz : z∈S)
    {mu K s : ℝ} (hmu64 : (1/64:ℝ) ≤ mu)
    (hK : 1 ≤ K) (hs : 0 ≤ s) (hs2 : s ≤ 2)
    (Hglobal : ((atPoint S R z).card:ℝ) ≤ K*(32:ℝ)^s)
    (hfinal : mu*(D:ℝ)/512 ≤ 1) :
    ADBounds (points S (R*D) (mu*(D:ℝ)/512) z) (mu*(D:ℝ)/512)
      ((2:ℝ)^40*K) s ∧
    ((atPoint S (R*D) z).card:ℝ) ≤ ((2:ℝ)^40*K)*(mu*(D:ℝ)/512)^(-s) := by
  have hmu : 0 < mu := lt_of_lt_of_le (by norm_num) hmu64
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hrho : 0 < mu*(D:ℝ)/512 := by positivity
  let G := K*(32:ℝ)^s
  have hG1 : 1 ≤ G := one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow (by norm_num) hs)
  have htotal : ((atPoint S (R*D) z).card:ℝ) ≤ G := by
    rw [←large_coarsen_eq S R D hR hD hheight z hz]
    exact (Nat.cast_le.mpr (card_image_le)).trans Hglobal
  have hmesh : (1/32768:ℝ) ≤ mu*(D:ℝ)/512 := by
    have hh := le_mul_of_one_le_right hmu.le hD1
    linarith only [hh,hmu64]
  have hcost : (32768:ℝ)^s*G ≤ (2:ℝ)^40*K := by
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 1048576) hs2
    norm_num at hp
    calc
      _ = (1048576:ℝ)^s*K := by
        dsimp [G]
        rw [show (1048576:ℝ)=32768*32 by norm_num,Real.mul_rpow (by norm_num) (by norm_num)]
        ring
      _ ≤ 1099511627776*K := mul_le_mul_of_nonneg_right hp hKp.le
      _ = _ := by norm_num
  have HGpoints : ((points S (R*D) (mu*(D:ℝ)/512) z).card:ℝ) ≤ G := by
    rw [points_card S (R*D) hrho]
    exact htotal
  have HH := NativeADFixedContraction.coarse_mesh_AD
    (points S (R*D) (mu*(D:ℝ)/512) z) (by norm_num : (1:ℝ) ≤ 32768) hmesh hs HGpoints
  rw [max_eq_right hG1] at HH
  have hpow1 : 1 ≤ (32768:ℝ)^s := Real.one_le_rpow (by norm_num) hs
  have hGc : G ≤ (2:ℝ)^40*K :=
    (le_mul_of_one_le_left (le_trans (by norm_num) hG1) hpow1).trans hcost
  refine ⟨AD_mono _ hrho (by positivity) hcost HH,?_⟩
  have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrho hfinal (neg_nonpos.mpr hs)
  exact (htotal.trans hGc).trans (le_mul_of_one_le_right (by positivity) hp)

end NativeWindowCoarseContraction
