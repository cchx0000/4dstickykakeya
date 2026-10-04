import Theorems.Thm_StickyKakeya4_original_native_projection_recode
import Theorems.Thm_StickyKakeya4_original_weighted_third_query_cover
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
noncomputable section
open Classical

namespace OriginalNativeRecodedQueryCover
open ProjectionAnnulusEnergy ActualRoundedAdditiveEnergy OriginalTwoProjectionCartesian
open OriginalTwoProjectionRealGraph OriginalRecodedGraphSource OriginalNativeProjectionRecode
open OriginalWeightedThirdQueryCover OriginalNormalizedFractionalCoefficientProfile
open OriginalFractionalLinearCoefficientProfile

def queryLoss (h x : ℝ) : ℝ := (8+2*|x|)*(64/h^2+2)*(8/h+4)

/-- The complete final query code is charged to the ORIGINAL planar
projection alphabet. Both floor errors and the actual change of mesh are
included, with the same original source points throughout. -/
theorem original_native_recoded_query_cover (Q : Finset Point)
    {delta h a b c0 c : ℝ} (hd : 0 < delta) (hh : 0 < h)
    (hab : h≤|b-a|) (ha : |a|≤1) (hb : |b|≤1)
    (hc0 : |c0|≤1) (hc : |c|≤1)
    (h0a : h≤|c0-a|) (h0b : h≤|b-c0|) (hbc : h≤|b-c|) :
    (((sourceGraph Q delta (h*delta/64) a b (leftWeight a b c0) (rightWeight a b c0)).image
      (OriginalBourgainGraphTransfer.code (normalizedCoefficient a b c0 c))).card:ℝ)≤
      queryLoss h (normalizedCoefficient a b c0 c)*(alphabet Q delta c).card := by
  let x := normalizedCoefficient a b c0 c
  have hs : 0<h*delta/64 := by positivity
  have hfirst := original_recoded_query_cover (realGraph Q delta a b) hs
    (leftWeight a b c0) (rightWeight a b c0) x
  have hsecond := original_exact_weighted_query_cover (realGraph Q delta a b)
    a b c0 c h delta hh hd (abs_pos.mp (hh.trans_le hab))
    (abs_pos.mp (hh.trans_le h0b)) (abs_pos.mp (hh.trans_le h0a)) hb hc0 hbc
  have hthird := real_query_cover Q hd hh hab ha hb hc
  have hsecond' : (((realGraph Q delta a b).image (fun p => rounded (h*delta/64)
      (weightedValue (leftWeight a b c0) (rightWeight a b c0) x p))).card:ℝ)≤
      (64/h^2+2)*((realGraph Q delta a b).image
        (fun z => rounded (delta/4) (linearValue a b c z))).card := hsecond
  rw [original_source_graph_eq]
  apply hfirst.trans
  have h2 := mul_le_mul_of_nonneg_left hsecond' (show 0≤8+2*|x| by positivity)
  have h3 := mul_le_mul_of_nonneg_left hthird
    (show 0≤(8+2*|x|)*(64/h^2+2) by positivity)
  dsimp only [queryLoss]
  nlinarith only [h2,h3]

lemma original_normalized_reference_one {a b c0 h : ℝ} (hh : 0<h)
    (h0a : h≤|c0-a|) (h0b : h≤|b-c0|) : normalizedCoefficient a b c0 c0=1 := by
  unfold normalizedCoefficient
  apply div_self
  exact div_ne_zero (abs_pos.mp (hh.trans_le h0a)) (abs_pos.mp (hh.trans_le h0b))

/-- The BSG restricted sumset bound is produced by one actual original
third query, rather than assumed on the re-rounded integer graph. -/
theorem original_native_restricted_sum_cover (Q : Finset Point)
    {delta h a b c0 : ℝ} (hd : 0<delta) (hh : 0<h)
    (hab : h≤|b-a|) (ha : |a|≤1) (hb : |b|≤1) (hc0 : |c0|≤1)
    (h0a : h≤|c0-a|) (h0b : h≤|b-c0|) :
    (((sourceGraph Q delta (h*delta/64) a b (leftWeight a b c0) (rightWeight a b c0)).image
      (fun z => z.1+z.2)).card:ℝ)≤
      (10*(64/h^2+2)*(8/h+4))*(alphabet Q delta c0).card := by
  have hc := original_native_recoded_query_cover Q hd hh hab ha hb hc0 hc0 h0a h0b h0b
  rw [original_normalized_reference_one hh h0a h0b] at hc
  have he : OriginalBourgainGraphTransfer.code 1=(fun z : ℤ × ℤ => z.1+z.2) := by
    funext z
    exact original_code_one z
  rw [he] at hc
  simpa only [queryLoss,abs_one,show (8:ℝ)+2*1=10 by norm_num] using hc

end OriginalNativeRecodedQueryCover
