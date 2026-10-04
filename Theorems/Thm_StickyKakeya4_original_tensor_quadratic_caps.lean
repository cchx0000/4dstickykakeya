import Theorems.Thm_StickyKakeya4_original_tensor_frostman
import Theorems.Thm_StickyKakeya4_projection_annulus_energy
import Theorems.Thm_StickyKakeya4_finite_plane_projection_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalTensorQuadraticCaps
open OriginalTensorFrostman GKZOriginalGapEnergy

/-- Once the original tensor dimension is at least two, its original weak
profile gives a genuine quadratic point-window cap at every available scale. -/
theorem original_tensor_quadratic_window (A : Finset ℝ) (m : ℕ)
    {delta K u : ℝ} (hd : 0 < delta) (hK : 0 ≤ K) (hmu : 2 ≤ u*(m:ℝ))
    (hprofile : ScalarFrostman A delta K u) (c : Fin m → ℝ) (r : ℝ)
    (hr : delta ≤ r) (hr1 : r ≤ 1) :
    (((tensor A m).filter (fun a => ∀ i, |a i-c i| ≤ r)).card:ℝ) ≤
      K^m*r^2*(tensor A m).card := by
  have hrpos := hd.trans_le hr
  have hc := original_tensor_frostman A m hprofile c r hr hr1
  rw [mul_pow,← Real.rpow_mul_natCast hrpos.le u m] at hc
  have hp : r^(u*(m:ℝ)) ≤ r^2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_ge hrpos hr1 hmu
  exact hc.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (pow_nonneg hK m)) (Nat.cast_nonneg _))

/-- Large radii use only actual total mass, so the tensor cap is valid at
ALL radii above the original mesh without a new regularity assumption. -/
theorem original_tensor_allscale_quadratic (A : Finset ℝ) (m : ℕ)
    {delta K u : ℝ} (hd : 0 < delta) (hK : 1 ≤ K) (hmu : 2 ≤ u*(m:ℝ))
    (hprofile : ScalarFrostman A delta K u) (c : Fin m → ℝ) (r : ℝ)
    (hr : delta ≤ r) :
    (((tensor A m).filter (fun a => ∀ i, |a i-c i| ≤ r)).card:ℝ) ≤
      K^m*r^2*(tensor A m).card := by
  by_cases hr1 : r ≤ 1
  · exact original_tensor_quadratic_window A m hd (le_trans (by norm_num) hK)
      hmu hprofile c r hr hr1
  · have hrlo : 1 ≤ r := (lt_of_not_ge hr1).le
    have hp : 1 ≤ r^2 := one_le_pow₀ hrlo
    have hKpow : 1 ≤ K^m := one_le_pow₀ hK
    have hprod : 1 ≤ K^m*r^2 := one_le_mul_of_one_le_of_one_le hKpow hp
    have hc : (((tensor A m).filter (fun a => ∀ i, |a i-c i| ≤ r)).card:ℝ) ≤
        (tensor A m).card := Nat.cast_le.mpr (Finset.card_filter_le _ _)
    exact hc.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hprod (show (0:ℝ) ≤ (tensor A m).card from Nat.cast_nonneg _))

def dyadicScale (k j : ℕ) : ℝ := 2^j*ProjectionAnnulusEnergy.mesh k

lemma dyadicScale_bounds (k j : ℕ) (hj : j ≤ k) :
    ProjectionAnnulusEnergy.mesh k ≤ dyadicScale k j ∧ dyadicScale k j ≤ 1 := by
  have hd := (ProjectionAnnulusEnergy.mesh_pos k).le
  have hlo : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have hhi := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj
  have htop : (2:ℝ)^k*ProjectionAnnulusEnergy.mesh k=1 :=
    FinitePlaneProjectionGrid.two_pow_reciprocal k
  constructor
  · simpa only [one_mul,dyadicScale] using mul_le_mul_of_nonneg_right hlo hd
  · exact (mul_le_mul_of_nonneg_right hhi hd).trans_eq htop

lemma dyadicScale_sum (k : ℕ) :
    ∑ j∈Finset.range (k+1), dyadicScale k j ≤ 2 := by
  have hs : (∑ j∈Finset.range (k+1), (2:ℝ)^j)=2^(k+1)-1 := by
    rw [geom_sum_eq]
    · norm_num
    · norm_num
  have htop : (2:ℝ)^k*ProjectionAnnulusEnergy.mesh k=1 :=
    FinitePlaneProjectionGrid.two_pow_reciprocal k
  have hid : (∑ j∈Finset.range (k+1), dyadicScale k j)=
      (2^(k+1)-1)*ProjectionAnnulusEnergy.mesh k := by
    unfold dyadicScale
    rw [← Finset.sum_mul,hs]
  rw [hid,pow_succ]
  have hdelta := (ProjectionAnnulusEnergy.mesh_pos k).le
  nlinarith only [htop,hdelta]

end OriginalTensorQuadraticCaps
