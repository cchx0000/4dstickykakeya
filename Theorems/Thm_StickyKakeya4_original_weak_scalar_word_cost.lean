import Theorems.Thm_StickyKakeya4_original_polynomial_ring_cover
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
noncomputable section
open Classical

namespace OriginalWeakScalarWordCost
open OriginalPolynomialRingCover OriginalMonomialSmallCover

def wordCost (W d : ℕ) (R tau M : ℝ) : ℝ :=
  ((2*W+5:ℕ):ℝ)*(((W+1:ℕ):ℝ)*(8*signedBound R tau M d))^(W+1)

def costConstant (W d : ℕ) : ℝ :=
  ((2*W+5:ℕ):ℝ)*(((W+1:ℕ):ℝ)*8*259*1536*(6144:ℝ)^(d-1))^(W+1)

def costExponent (W d : ℕ) (epsilon eta zeta : ℝ) : ℝ :=
  ((W+1:ℕ):ℝ)*(((d+2:ℕ):ℝ)*epsilon+2*((d-1:ℕ):ℝ)*eta+(d:ℝ)*zeta)

lemma costConstant_pos (W d : ℕ) : 0 < costConstant W d := by
  unfold costConstant
  positivity

lemma original_self_cost_power {delta epsilon zeta : ℝ} (hd : 0 < delta) :
    selfBound (delta^zeta) (delta^(-epsilon))=1536*delta^(-(2*epsilon+zeta)) := by
  unfold selfBound
  rw [← Real.rpow_mul_natCast hd.le]
  calc
    _ = 1536*(delta^((-epsilon)*(2:ℝ))/delta^zeta) := by ring
    _ = _ := by
      rw [← Real.rpow_sub hd]
      congr 1
      ring

lemma original_monomial_cost_power (d : ℕ) {delta epsilon eta zeta : ℝ} (hd : 0 < delta) :
    monomialBound (productFactor (delta^(-eta)) (delta^zeta)) (delta^(-epsilon)) d =
      (6144:ℝ)^(d-1)*delta^(-(((d-1:ℕ):ℝ)*(2*eta+zeta)+(d:ℝ)*epsilon)) := by
  have hF : productFactor (delta^(-eta)) (delta^zeta)=6144*delta^(-(2*eta+zeta)) := by
    unfold productFactor
    rw [← Real.rpow_mul_natCast hd.le]
    calc
      _ = 6144*(delta^((-eta)*(2:ℝ))/delta^zeta) := by ring
      _ = _ := by
        rw [← Real.rpow_sub hd]
        congr 1
        ring
  unfold monomialBound
  rw [hF,mul_pow,← Real.rpow_mul_natCast hd.le,← Real.rpow_mul_natCast hd.le]
  rw [mul_assoc,← Real.rpow_add hd]
  congr 1
  ring

/-- The total small-power loss is polynomial because BOTH original degree
and the selected monomial word length are fixed. All constants are explicit. -/
theorem original_word_cost_power (W d : ℕ) {delta epsilon eta zeta : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heps : 0 ≤ epsilon)
    (heta : 0 ≤ eta) (hzeta : 0 ≤ zeta) (hdim : 1 ≤ d) :
    wordCost W d (delta^(-eta)) (delta^zeta) (delta^(-epsilon)) ≤
      costConstant W d*delta^(-costExponent W d epsilon eta zeta) := by
  let S := selfBound (delta^zeta) (delta^(-epsilon))
  let Q := monomialBound (productFactor (delta^(-eta)) (delta^zeta)) (delta^(-epsilon)) d
  let E := ((d+2:ℕ):ℝ)*epsilon+2*((d-1:ℕ):ℝ)*eta+(d:ℝ)*zeta
  have hS := original_self_cost_power (epsilon:=epsilon) (zeta:=zeta) hd
  have hQ := original_monomial_cost_power d (epsilon:=epsilon) (eta:=eta) (zeta:=zeta) hd
  have hS1 : 1 ≤ S := by
    rw [show S=selfBound (delta^zeta) (delta^(-epsilon)) from rfl,hS]
    exact one_le_mul_of_one_le_of_one_le (by norm_num) (Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hd hd1 (by linarith only [heps,hzeta]))
  have hQ1 : 1 ≤ Q := by
    rw [show Q=monomialBound (productFactor (delta^(-eta)) (delta^zeta)) (delta^(-epsilon)) d from rfl,hQ]
    apply one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1
    have hnon : 0 ≤ ((d-1:ℕ):ℝ)*(2*eta+zeta)+(d:ℝ)*epsilon := by positivity
    linarith only [hnon]
  have hS0 : 0 ≤ S := le_trans (by norm_num) hS1
  have hQ0 : 0 ≤ Q := le_trans (by norm_num) hQ1
  have h1 : 1 ≤ S*Q := one_le_mul_of_one_le_of_one_le hS1 hQ1
  have h2 : S ≤ S*Q := by nlinarith only [mul_le_mul_of_nonneg_left hQ1 hS0]
  have h3 : Q ≤ S*Q := by nlinarith only [mul_le_mul_of_nonneg_right hS1 hQ0]
  have hbound : signedBound (delta^(-eta)) (delta^zeta) (delta^(-epsilon)) d ≤ 259*S*Q := by
    change 1+S+Q+256*S*Q ≤ 259*S*Q
    linarith only [h1,h2,h3]
  have hnat : ((d-1:ℕ):ℝ)+1=d := by exact_mod_cast Nat.sub_add_cancel hdim
  have hSQ : S*Q=(1536*(6144:ℝ)^(d-1))*delta^(-E) := by
    change selfBound (delta^zeta) (delta^(-epsilon))*
      monomialBound (productFactor (delta^(-eta)) (delta^zeta)) (delta^(-epsilon)) d = _
    rw [hS,hQ]
    calc
      _ = (1536*(6144:ℝ)^(d-1))*(delta^(-(2*epsilon+zeta))*
          delta^(-(((d-1:ℕ):ℝ)*(2*eta+zeta)+(d:ℝ)*epsilon))) := by ring
      _ = _ := by
        rw [← Real.rpow_add hd]
        congr 1
        dsimp [E]
        push_cast
        rw [← hnat]
        ring
  have hbase := mul_le_mul_of_nonneg_left hbound
    (show 0≤((W+1:ℕ):ℝ)*8 by positivity)
  have hbase' : ((W+1:ℕ):ℝ)*(8*signedBound (delta^(-eta)) (delta^zeta) (delta^(-epsilon)) d) ≤
      (((W+1:ℕ):ℝ)*8*259*1536*(6144:ℝ)^(d-1))*delta^(-E) := by
    have heq : ((W+1:ℕ):ℝ)*8*(259*S*Q)=
        (((W+1:ℕ):ℝ)*8*259*1536*(6144:ℝ)^(d-1))*delta^(-E) := by
      calc
        _ = (((W+1:ℕ):ℝ)*8*259)*(S*Q) := by ring
        _ = _ := by rw [hSQ]; ring
    nlinarith only [hbase,heq]
  have hnon : 0 ≤ ((W+1:ℕ):ℝ)*(8*signedBound (delta^(-eta)) (delta^zeta) (delta^(-epsilon)) d) := by
    unfold signedBound selfBound monomialBound productFactor
    positivity
  have hp := pow_le_pow_left₀ hnon hbase' (W+1)
  have hm := mul_le_mul_of_nonneg_left hp (show 0≤((2*W+5:ℕ):ℝ) by positivity)
  change wordCost W d (delta^(-eta)) (delta^zeta) (delta^(-epsilon)) ≤ _ at hm
  rw [mul_pow,← Real.rpow_mul_natCast hd.le] at hm
  have he : (-E)*((W+1:ℕ):ℝ)= -costExponent W d epsilon eta zeta := by
    dsimp [E,costExponent]
    ring
  rw [he] at hm
  simpa only [costConstant,mul_assoc] using hm

end OriginalWeakScalarWordCost
