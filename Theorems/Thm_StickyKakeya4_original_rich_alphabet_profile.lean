import Theorems.Thm_StickyKakeya4_original_shared_fiber_pruning
import Theorems.Thm_StickyKakeya4_original_two_projection_real_graph

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace OriginalRichAlphabetProfile
open ProjectionAnnulusEnergy ActualRoundedAdditiveEnergy OriginalTwoProjectionCartesian
open OriginalTwoProjectionRealGraph OriginalSharedFiberPruning

def scalarValue (delta lam : ℝ) (p : Point) : ℝ :=
  (delta/4)*(scalarCode delta lam p:ℝ)

lemma realAlphabet_eq_image (P : Finset Point) (delta lam : ℝ) :
    realAlphabet P delta lam=P.image (scalarValue delta lam) := by
  unfold realAlphabet IntegerBinRealNearEnergy.realGrid alphabet
  rw [Finset.image_image]
  rfl

/-- A ball of actual rounded scalar representatives charges a slightly wider
strip through the original planar points, at the same center and scale. -/
lemma original_scalar_ball_lift {delta lam r c : ℝ} (hd : 0 < delta)
    (hr : delta/4 ≤ r) {p : Point} (hp : |scalarValue delta lam p-c| ≤ r) :
    |projection lam p-4*c| ≤ 8*r := by
  have he := round_error hd (projection lam p)
  have hid : projection lam p-4*c =
      (projection lam p-delta*(rounded delta (projection lam p):ℝ))+
        4*(scalarValue delta lam p-c) := by
    unfold scalarValue scalarCode
    ring
  rw [hid]
  have htri := abs_add_le
    (projection lam p-delta*(rounded delta (projection lam p):ℝ))
    (4*(scalarValue delta lam p-c))
  rw [abs_of_nonneg he.1,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 4)] at htri
  nlinarith only [htri,he.2,hp,hr]

/-- The original strip profile yields an absolute scalar-label window cap;
large query radii are handled by original total mass. -/
theorem original_weighted_scalar_cap (P : Finset Point)
    {delta lam H u N : ℝ} (hd : 0 < delta) (hH : 0 ≤ H) (_hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hN : 0 ≤ N) (hmass : (P.card : ℝ) ≤ N)
    (hprofile : ∀ c r : ℝ, delta ≤ r → r ≤ 1 →
      ((P.filter (fun p => |projection lam p-c| ≤ r)).card : ℝ) ≤ H*r^u*N)
    (c r : ℝ) (hr : delta/4 ≤ r) (hr1 : r ≤ 1) :
    ((P.filter (fun p => |scalarValue delta lam p-c| ≤ r)).card : ℝ) ≤
      8*(1+H)*r^u*N := by
  have hrpos : 0 < r := (by positivity : 0 < delta/4).trans_le hr
  have hrpow : 0 ≤ r^u := Real.rpow_nonneg hrpos.le u
  by_cases hsmall : 8*r ≤ 1
  · have hsub : P.filter (fun p => |scalarValue delta lam p-c| ≤ r) ⊆
        P.filter (fun p => |projection lam p-4*c| ≤ 8*r) := by
      intro p hp
      obtain ⟨hpP,hpnear⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hpP,original_scalar_ball_lift hd hr hpnear⟩
    have hc := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (hprofile (4*c) (8*r) (by linarith only [hr,hd]) hsmall)
    have hpow : (8*r)^u=(8:ℝ)^u*r^u := Real.mul_rpow (by norm_num) hrpos.le
    rw [hpow] at hc
    have height : (8:ℝ)^u ≤ 8 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 8) hu1
    have hm := mul_le_mul_of_nonneg_right height (show 0 ≤ H*r^u*N by positivity)
    have hbase : 0 ≤ r^u*N := mul_nonneg hrpow hN
    nlinarith only [hc,hm,hbase]
  · have hrpowlo : r ≤ r^u := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hrpos hr1 hu1
    have hone : 1 ≤ 8*r^u := by linarith only [hsmall,hrpowlo]
    have hc : ((P.filter (fun p => |scalarValue delta lam p-c| ≤ r)).card : ℝ) ≤ N :=
      (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans hmass
    have hm := mul_le_mul_of_nonneg_right hone hN
    have hplus : 0 ≤ H*r^u*N := by positivity
    nlinarith only [hc,hm,hplus]

/-- Uniform original lower fibers turn the actual weighted strip cap into
an unweighted profile of the actual retained scalar alphabet. -/
theorem original_rich_alphabet_profile (P R : Finset Point)
    {delta lam H u N m L : ℝ} (hd : 0 < delta) (hH : 0 ≤ H)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hN : 0 ≤ N) (hm : 0 < m) (_hL : 0 ≤ L)
    (hmass : (P.card : ℝ) ≤ N)
    (hprofile : ∀ c r : ℝ, delta ≤ r → r ≤ 1 →
      ((P.filter (fun p => |projection lam p-c| ≤ r)).card : ℝ) ≤ H*r^u*N)
    (hR : R ⊆ rich P (scalarValue delta lam) m)
    (hbalance : N ≤ L*m*(realAlphabet R delta lam).card) :
    ∀ c r : ℝ, delta/4 ≤ r → r ≤ 1 →
      (((realAlphabet R delta lam).filter (fun a => |a-c| ≤ r)).card : ℝ) ≤
        (8*(1+H)*L)*r^u*(realAlphabet R delta lam).card := by
  rw [realAlphabet_eq_image] at hbalance ⊢
  intro c r hr hr1
  have hc := original_rich_window_charge P R (scalarValue delta lam) m
    (fun a => |a-c| ≤ r) hR
  have hp := original_weighted_scalar_cap P hd hH hu hu1 hN hmass hprofile c r hr hr1
  have hrpos : 0 < r := (by positivity : 0 < delta/4).trans_le hr
  have hb := mul_le_mul_of_nonneg_left hbalance
    (show 0 ≤ 8*(1+H)*r^u by positivity)
  apply (mul_le_mul_iff_left₀ hm).mp
  nlinarith only [hc,hp,hb]

end OriginalRichAlphabetProfile
