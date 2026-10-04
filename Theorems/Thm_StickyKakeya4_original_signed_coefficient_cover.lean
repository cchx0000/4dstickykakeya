import Theorems.Thm_StickyKakeya4_original_rounded_ring_product
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalSignedCoefficientCover
open OriginalRoundedRuzsaCover OriginalRoundedRingProduct

/-- One genuine original small linear-image cover controls the original
self-sum, with the inverse coefficient loss kept explicit. -/
theorem original_self_sum_cover (A : Finset ℝ) {delta x : ℝ}
    (hd : 0 < delta) (hx : x≠0) :
    ((cells delta (A+A)).card:ℝ)*(cells delta A).card ≤
      (384*(2/|x|+2))*((cells delta (A+dilate x A)).card:ℝ)^2 := by
  have htri := original_rounded_sum_triangle A (dilate x A) A hd
  rw [add_comm (dilate x A) A] at htri
  have hinv := original_inverse_dilation_cover A hd hx
  have hI : 0 ≤ 2/|x|+2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hinv
    (show (0:ℝ)≤(cells delta (A+A)).card from Nat.cast_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left htri hI
  nlinarith only [h1,h2]

/-- The self-sum loss is uniform over original coefficients bounded away
from zero; it is derived before any fixed union of dilates is used. -/
theorem original_self_sum_small_cover (A : Finset ℝ) {delta x tau M : ℝ}
    (hd : 0 < delta) (hA : A.Nonempty) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hx : tau ≤ |x|)
    (hsmall : ((cells delta (A+dilate x A)).card:ℝ) ≤ M*(cells delta A).card) :
    ((cells delta (A+A)).card:ℝ) ≤ (1536/tau)*M^2*(cells delta A).card := by
  have hxpos : 0 < |x| := htau.trans_le hx
  have hh := original_self_sum_cover A hd (abs_pos.mp hxpos)
  have hfactor : 384*(2/|x|+2) ≤ 1536/tau := by
    have hrec : 2/|x| ≤ 2/tau := div_le_div_of_nonneg_left (by norm_num) htau hx
    have hone : 2 ≤ 2/tau := (le_div_iff₀ htau).mpr (by nlinarith only [htau1])
    rw [show (1536:ℝ)/tau=768*(2/tau) by ring]
    linarith only [hrec,hone]
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (cells delta (A+dilate x A)).card) hsmall 2
  have hm := mul_le_mul hfactor hpow (sq_nonneg _)
    (show 0 ≤ 1536/tau by positivity)
  have hN : (0:ℝ) < (cells delta A).card := Nat.cast_pos.mpr (hA.image _).card_pos
  apply (mul_le_mul_iff_left₀ hN).mp
  nlinarith only [hh,hm]

lemma original_negative_dilate_identity (A : Finset ℝ) (y : ℝ) :
    A+dilate (-y) A=A-dilate y A := by
  ext z
  constructor
  · intro hz
    obtain ⟨a,ha,v,hv,rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_sub.mpr ⟨a,ha,y*b,Finset.mem_image_of_mem _ hb,by ring⟩
  · intro hz
    obtain ⟨a,ha,v,hv,rfl⟩ := Finset.mem_sub.mp hz
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_add.mpr ⟨a,ha,(-y)*b,Finset.mem_image_of_mem _ hb,by ring⟩

/-- A signed original coefficient is controlled by the original self-sum
and its positive coefficient cover, through the rounded difference triangle. -/
theorem original_negative_small_cover (A : Finset ℝ) {delta y S M : ℝ}
    (hd : 0 < delta) (hA : A.Nonempty) (hS : 0 ≤ S)
    (hself : ((cells delta (A+A)).card:ℝ) ≤ S*(cells delta A).card)
    (hsmall : ((cells delta (A+dilate y A)).card:ℝ) ≤ M*(cells delta A).card) :
    ((cells delta (A+dilate (-y) A)).card:ℝ) ≤ 256*S*M*(cells delta A).card := by
  rw [original_negative_dilate_identity]
  have hh := original_rounded_sub_sum_triangle A A (dilate y A) hd
  rw [add_comm (dilate y A) A] at hh
  have hp := mul_le_mul hself hsmall (Nat.cast_nonneg _)
    (show 0 ≤ S*((cells delta A).card:ℝ) by positivity)
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤256)
  have hN : (0:ℝ) < (cells delta A).card := Nat.cast_pos.mpr (hA.image _).card_pos
  apply (mul_le_mul_iff_left₀ hN).mp
  nlinarith only [hh,hm]

end OriginalSignedCoefficientCover
