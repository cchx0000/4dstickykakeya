import Theorems.Thm_StickyKakeya4_original_weak_scalar_word_cost
import Theorems.Thm_StickyKakeya4_native_quarter_scale_parameters

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
noncomputable section

namespace OriginalWeakScalarPowerParameters
open OriginalWeakScalarWordCost

/-- Positive powers are selected only AFTER the fixed total word length
and degree. The explicit margins pay for both normalization and ring costs. -/
theorem exists_original_weak_power_margins (W d : ℕ) {u gap : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hgap : 0 < gap) (hgap1 : gap ≤ 1) :
    ∃ epsilon eta g : ℝ, 0 < epsilon ∧ 0 < eta ∧ 0 < g ∧
      2*eta/u ≤ 1 ∧
      0 < 1-(4*(d:ℝ)*(1+u/2)/u)*eta ∧
      2*g ≤ (gap/2)*u-eta-costExponent W d epsilon eta (2*eta/u) ∧
      2*g ≤ gap-gap/2-(4*(d:ℝ)*(1+u/2)/u)*eta-
        costExponent W d epsilon eta (2*eta/u) := by
  let P : ℝ := ((W+1:ℕ):ℝ)*((d+2:ℕ):ℝ)
  let Q : ℝ := ((W+1:ℕ):ℝ)*(2*((d-1:ℕ):ℝ)+2*(d:ℝ)/u)
  let H : ℝ := 4*(d:ℝ)*(1+u/2)/u
  let g : ℝ := u*gap/8
  let Z : ℝ := Q+H+1+2/u
  let epsilon := g/(2*P)
  let eta := g/(2*Z)
  have hP : 0 < P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hg : 0 < g := by dsimp [g]; positivity
  have hg1 : g ≤ 1/8 := by
    dsimp [g]
    have hh := mul_le_mul hu1 hgap1 hgap.le (by norm_num : (0:ℝ)≤1)
    nlinarith only [hh]
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have heps : 0 < epsilon := div_pos hg (by positivity)
  have heta : 0 < eta := div_pos hg (by positivity)
  have he : P*epsilon=g/2 := by dsimp [epsilon]; field_simp
  have ht : Z*eta=g/2 := by dsimp [eta]; field_simp
  have hE : costExponent W d epsilon eta (2*eta/u)=P*epsilon+Q*eta := by
    dsimp [costExponent,P,Q]
    ring
  have hz : 2/u*eta ≤ g/2 := by
    have hh : 0 ≤ (Q+H+1)*eta := by positivity
    dsimp [Z] at ht
    nlinarith only [ht,hh]
  have hHeta : H*eta ≤ g/2 := by
    have hh : 0 ≤ (Q+1+2/u)*eta := by positivity
    dsimp [Z] at ht
    nlinarith only [ht,hh]
  have hnear : costExponent W d epsilon eta (2*eta/u)+eta ≤ g := by
    rw [hE,he]
    have hh : 0 ≤ (H+2/u)*eta := by positivity
    dsimp [Z] at ht
    nlinarith only [ht,hh]
  have hfar : costExponent W d epsilon eta (2*eta/u)+H*eta ≤ g := by
    rw [hE,he]
    have hh : 0 ≤ (1+2/u)*eta := by positivity
    dsimp [Z] at ht
    nlinarith only [ht,hh]
  refine ⟨epsilon,eta,g,heps,heta,hg,?_,?_,?_,?_⟩
  · calc
      2*eta/u = 2/u*eta := by ring
      _ ≤ g/2 := hz
      _ ≤ 1 := by linarith only [hg1]
  · change 0 < 1-H*eta
    linarith only [hHeta,hg1]
  · have hid : (gap/2)*u=4*g := by dsimp [g]; ring
    rw [hid]
    linarith only [hnear,hg]
  · change 2*g ≤ gap-gap/2-H*eta-costExponent W d epsilon eta (2*eta/u)
    have hgGap : 4*g ≤ gap/2 := by
      dsimp [g]
      nlinarith only [mul_le_mul_of_nonneg_right hu1 hgap.le]
    linarith only [hfar,hg,hgGap]

lemma original_normalization_exponent {u eta : ℝ} (hu : 0 < u) (d : ℕ) :
    (d:ℝ)*((2*eta*(1+u/2))/(u-u/2))=(4*(d:ℝ)*(1+u/2)/u)*eta := by
  field_simp
  ring

/-- One actual cutoff pays all three positive-power requirements. -/
theorem exists_original_weak_power_cutoff {eta a g C threshold : ℝ}
    (heta : 0 < eta) (ha : 0 < a) (hg : 0 < g) (hC : 0 < C)
    (hthreshold : 0 < threshold) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        delta^eta ≤ 1/2 ∧ 2*delta^a ≤ threshold ∧ C*delta^(2*g) ≤ 1/2 := by
  obtain ⟨d1,hd1,hd11,h1⟩ := NativeQuarterScaleParameters.exists_small_power_cutoff heta
    (by norm_num : (0:ℝ)<1/2)
  obtain ⟨d2,hd2,_hd21,h2⟩ := NativeQuarterScaleParameters.exists_small_power_cutoff ha
    (show 0<threshold/2 by positivity)
  obtain ⟨d3,hd3,_hd31,h3⟩ := NativeQuarterScaleParameters.exists_small_power_cutoff
    (show 0<2*g by positivity) (show 0<1/(2*C) by positivity)
  refine ⟨min d1 (min d2 d3),lt_min hd1 (lt_min hd2 hd3),(min_le_left _ _).trans hd11,?_⟩
  intro delta hd hsmall
  have hsmall1 := hsmall.trans (min_le_left _ _)
  have hsmall2 := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall3 := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨h1 delta hd hsmall1,?_,?_⟩
  · linarith only [h2 delta hd hsmall2]
  · have hh := (le_div_iff₀ (show 0<2*C by positivity)).mp (h3 delta hd hsmall3)
    nlinarith only [hh]

end OriginalWeakScalarPowerParameters
