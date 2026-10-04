import Theorems.Thm_StickyKakeya4_projection_annulus_energy
import Theorems.Thm_StickyKakeya4_original_two_projection_cartesian
import Theorems.Thm_StickyKakeya4_gkz_original_gap_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open Classical

namespace OriginalNativeRobustResiduals
open ProjectionAnnulusEnergy OriginalTwoProjectionCartesian GKZOriginalGapEnergy

theorem original_point_profile_restrict (P R : Finset Point) {delta K u theta : ℝ}
    (hd : 0≤delta) (hK : 0≤K) (htheta : 0<theta) (hRP : R⊆P)
    (hmass : theta*(P.card:ℝ)≤R.card) (hprofile : PointFrostman P delta K u) :
    PointFrostman R delta (K/theta) u := by
  intro c r hr hr1
  have hc : ((ball R c r).card:ℝ)≤K*r^u*P.card :=
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hRP))).trans (hprofile c r hr hr1)
  have hcoef : 0≤K*r^u := mul_nonneg hK (Real.rpow_nonneg (hd.trans hr) u)
  have hm := mul_le_mul_of_nonneg_left hmass hcoef
  have hp := mul_le_mul_of_nonneg_left hc htheta.le
  apply (mul_le_mul_iff_of_pos_right htheta).mp
  have he : (K/theta*r^u*(R.card:ℝ))*theta=K*r^u*R.card := by field_simp
  rw [he]
  nlinarith only [hm,hp]

/-- Fixed weaker exponents and constants apply to every original source
in a compact range of dimensions. -/
theorem original_point_profile_mono (P : Finset Point) {delta K K' t u : ℝ}
    (hd : 0<delta) (hK : 0≤K) (hKK : K≤K') (hut : u≤t)
    (hprofile : PointFrostman P delta K t) : PointFrostman P delta K' u := by
  intro c r hr hr1
  have hp := Real.rpow_le_rpow_of_exponent_ge (hd.trans_le hr) hr1 hut
  exact (hprofile c r hr hr1).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hKK hp (Real.rpow_nonneg (hd.le.trans hr) t) (hK.trans hKK)) (Nat.cast_nonneg _))

theorem original_scalar_profile_mono (C : Finset ℝ) {delta K K' t u : ℝ}
    (hd : 0<delta) (hK : 0≤K) (hKK : K≤K') (hut : u≤t)
    (hprofile : ScalarFrostman C delta K t) : ScalarFrostman C delta K' u := by
  intro c r hr hr1
  have hp := Real.rpow_le_rpow_of_exponent_ge (hd.trans_le hr) hr1 hut
  exact (hprofile c r hr hr1).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hKK hp (Real.rpow_nonneg (hd.le.trans hr) t) (hK.trans hKK)) (Nat.cast_nonneg _))

lemma original_projection_cover_mono (Q R : Finset Point) (delta c : ℝ) (hQR : Q⊆R) :
    ((alphabet Q delta c).card:ℝ)≤(alphabet R delta c).card :=
  Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hQR))

/-- Every residual above delta^(e/2) of the original mass still meets
the local delta^(-e) profile budget when the original loss is delta^(-e/4). -/
theorem original_robust_residual_profile (P R : Finset Point) {delta e u : ℝ}
    (hd : 0<delta) (hd1 : delta≤1) (he : 0<e) (hRP : R⊆P)
    (hmass : delta^(e/2)*(P.card:ℝ)≤R.card)
    (hprofile : PointFrostman P delta (delta^(-e/4)) u) :
    PointFrostman R delta (delta^(-e)) u := by
  have hp := original_point_profile_restrict P R hd.le (Real.rpow_nonneg hd.le _)
    (Real.rpow_pos_of_pos hd _) hRP hmass hprofile
  have heq : delta^(-e/4)/delta^(e/2)=delta^(-3*e/4) := by
    rw [← Real.rpow_sub hd]
    congr 1
    ring
  rw [heq] at hp
  exact original_point_profile_mono R hd (Real.rpow_nonneg hd.le _)
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith only [he])) (le_refl u) hp

/-- The local square-root threshold on every retained residual exceeds
the desired global threshold on the original population. -/
theorem original_robust_residual_threshold {delta e N R : ℝ}
    (hd : 0<delta) (hd1 : delta≤1) (he : 0<e) (_hN : 0≤N)
    (hmass : delta^(e/2)*N≤R) :
    delta^(-e/4)*Real.sqrt N≤delta^(-e)*Real.sqrt R := by
  have hs := Real.sqrt_le_sqrt hmass
  have hid : Real.sqrt (delta^(e/2)*N)=delta^(e/4)*Real.sqrt N := by
    rw [Real.sqrt_mul (Real.rpow_nonneg hd.le _)]
    congr 1
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hd.le]
    congr 1
    ring
  rw [hid] at hs
  have hm := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hd.le (-e))
  have hp := Real.rpow_le_rpow_of_exponent_ge hd hd1
    (show -3*e/4≤-e/4 by linarith only [he])
  have hpN := mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg N)
  have heq : delta^(-e)*(delta^(e/4)*Real.sqrt N)=delta^(-3*e/4)*Real.sqrt N := by
    rw [← mul_assoc,← Real.rpow_add hd]
    congr 1
    congr 1
    ring
  rw [heq] at hm
  exact hpN.trans hm

/-- The global density delta^(e/4) pays uncovered mass, weighted bad
piece mass, and the local delta^e query threshold simultaneously. -/
theorem original_robust_global_query_slack {delta e : ℝ} (hd : 0<delta)
    (hsmall : delta^(e/4)≤1/4) :
    delta^(e/2)+delta^(e/2)+delta^e<delta^(e/4) := by
  let z := delta^(e/4)
  have hz : 0<z := Real.rpow_pos_of_pos hd _
  have hzsmall : z≤1/4 := hsmall
  have hz1 : z≤1 := by linarith only [hzsmall]
  have hz2 : z^2≤1 := by simpa only [one_pow] using pow_le_pow_left₀ hz.le hz1 2
  have hhalf : delta^(e/2)=z^2 := by
    rw [← Real.rpow_mul_natCast hd.le (e/4) 2]
    congr 1
    ring
  have hfull : delta^e=z^4 := by
    rw [← Real.rpow_mul_natCast hd.le (e/4) 4]
    congr 1
    ring
  rw [hhalf,hfull]
  change z^2+z^2+z^4<z
  have hm := mul_le_mul_of_nonneg_left hzsmall hz.le
  have hpow := mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz2)
  nlinarith only [hm,hpow,hz]

end OriginalNativeRobustResiduals
