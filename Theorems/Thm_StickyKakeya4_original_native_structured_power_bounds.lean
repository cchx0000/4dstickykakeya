import Theorems.Thm_StickyKakeya4_original_structured_graph_growth
import Theorems.Thm_StickyKakeya4_original_native_recoded_query_cover
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000
noncomputable section

namespace OriginalNativeStructuredPowerBounds
open OriginalTwoProjectionCartesian OriginalNativeRecodedQueryCover

/-- The losses from the original geometric code and both exact mesh
transfers are fixed powers of the transverse separation. -/
theorem original_geometric_cover_power_bounds {h x : ℝ} (hh : 0<h) (hh1 : h≤1)
    (hx : |x|≤4/h^2) :
    fiberBound h≤64/h^2 ∧
      10*(64/h^2+2)*(8/h+4)≤7920/h^3 ∧
      queryLoss h x≤12672/h^5 := by
  have h1 : 1≤1/h := (le_div_iff₀ hh).mpr (by simpa only [one_mul] using hh1)
  have h2 : 1≤1/h^2 := by
    have hs := pow_le_pow_left₀ hh.le hh1 2
    apply (le_div_iff₀ (sq_pos_of_pos hh)).mpr
    simpa only [one_mul,one_pow] using hs
  have hsum1 : 6/h+2≤8/h := by
    simp only [div_eq_mul_inv,one_mul] at h1 ⊢
    linarith only [h1]
  have hsum2 : 64/h^2+2≤66/h^2 := by
    simp only [div_eq_mul_inv,one_mul] at h2 ⊢
    linarith only [h2]
  have hsum3 : 8/h+4≤12/h := by
    simp only [div_eq_mul_inv,one_mul] at h1 ⊢
    linarith only [h1]
  have hsum4 : 8+2*|x|≤16/h^2 := by
    simp only [div_eq_mul_inv,one_mul] at hx h2 ⊢
    linarith only [hx,h2]
  refine ⟨?_,?_,?_⟩
  · have hs := pow_le_pow_left₀ (show 0≤6/h+2 by positivity) hsum1 2
    unfold fiberBound
    calc
      _ ≤ (8/h)^2 := hs
      _ = 64/h^2 := by ring
  · have hp := mul_le_mul hsum2 hsum3 (show 0≤8/h+4 by positivity) (by positivity : 0≤66/h^2)
    have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤10)
    calc
      _ ≤ 10*((66/h^2)*(12/h)) := by nlinarith only [hm]
      _ = 7920/h^3 := by ring
  · have hp := mul_le_mul hsum2 hsum3 (show 0≤8/h+4 by positivity) (by positivity : 0≤66/h^2)
    have hq := mul_le_mul hsum4 hp
      (show 0≤(64/h^2+2)*(8/h+4) by positivity) (by positivity : 0≤16/h^2)
    unfold queryLoss
    calc
      _ ≤ (16/h^2)*((66/h^2)*(12/h)) := by nlinarith only [hq]
      _ = 12672/h^5 := by ring

/-- The BSG losses enter the graph-growth comparison with a fixed
exponent 77. No number of words, scales, or source points enters it. -/
theorem original_bsg_fixed_power_comparison {lam q J K L Z : ℝ}
    (hlam : 0<lam)
    (hcomparison : q*(lam^4/4096)^3*Z <
      2*J*(536870912*K^3/(lam^9*(lam^4/4096)))^5*L) :
    q*lam^77*Z < (2:ℝ)^242*J*K^15*L := by
  have hm := mul_lt_mul_of_pos_left hcomparison
    (show 0<(4096:ℝ)^8*lam^45*(lam^4/4096)^5 by positivity)
  have hleft : (4096:ℝ)^8*lam^45*(lam^4/4096)^5*(q*(lam^4/4096)^3*Z)=q*lam^77*Z := by ring
  have hright : (4096:ℝ)^8*lam^45*(lam^4/4096)^5*
      (2*J*(536870912*K^3/(lam^9*(lam^4/4096)))^5*L)=(2:ℝ)^242*J*K^15*L := by
    field_simp
    ring
  rwa [hleft,hright] at hm

end OriginalNativeStructuredPowerBounds
