import Theorems.Thm_StickyKakeya4_original_rounded_ring_product
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalMonomialSmallCover
open OriginalRoundedRuzsaCover OriginalRoundedRingProduct

def productFactor (R tau : ℝ) : ℝ := 6144*R^2/tau

def monomialBound (F M : ℝ) (d : ℕ) : ℝ := F^(d-1)*M^d

lemma original_product_factor_bound {x R tau : ℝ} (hR : 1 ≤ R)
    (htau : 0 < tau) (hlower : tau ≤ |x|) (hupper : |x| ≤ R) :
    1536*(1+|x|)^2/|x| ≤ productFactor R tau := by
  have hx : 0 < |x| := htau.trans_le hlower
  have hs : 1536*(1+|x|)^2 ≤ 6144*R^2 := by
    nlinarith only [hR,hupper,abs_nonneg x]
  calc
    _ ≤ 6144*R^2/|x| := (div_le_div_iff_of_pos_right hx).mpr hs
    _ ≤ 6144*R^2/tau := div_le_div_of_nonneg_left (by positivity) htau hlower

/-- Multiplication by one ACTUAL original coefficient at every step avoids
reciprocal losses from intermediate monomials. All exponents count genuine
original factors, and are uniform for a fixed degree. -/
theorem original_monomial_small_cover (A D : Finset ℝ) {delta R tau M : ℝ}
    (hd : 0 < delta) (hA : A.Nonempty) (hR : 1 ≤ R) (htau : 0 < tau)
    (hM : 0 ≤ M) (hD : ∀ x∈D, tau ≤ |x| ∧ |x| ≤ R)
    (hsmall : ∀ x∈D, ((cells delta (A+dilate x A)).card:ℝ) ≤ M*(cells delta A).card)
    (d : ℕ) (hdim : 1 ≤ d) :
    ∀ y∈D^d, ((cells delta (A+dilate y A)).card:ℝ) ≤
      monomialBound (productFactor R tau) M d*(cells delta A).card := by
  have hF : 0 ≤ productFactor R tau := by unfold productFactor; positivity
  induction d, hdim using Nat.le_induction with
  | base =>
    intro y hy
    simp only [pow_one] at hy
    simpa only [monomialBound,Nat.sub_self,pow_zero,pow_one,one_mul] using hsmall y hy
  | succ d hdpos ih =>
    intro z hz
    rw [pow_succ] at hz
    obtain ⟨y,hy,x,hx,rfl⟩ := Finset.mem_mul.mp hz
    have hxD := hD x hx
    have hx0 : x≠0 := abs_pos.mp (htau.trans_le hxD.1)
    have hbound : 0 ≤ monomialBound (productFactor R tau) M d := by
      unfold monomialBound
      positivity
    have hh := original_product_small_cover A hd hx0 hA hM (hsmall x hx) (ih y hy)
    have hfactor := original_product_factor_bound hR htau hxD.1 hxD.2
    have hm := mul_le_mul_of_nonneg_right hfactor
      (show 0 ≤ M*monomialBound (productFactor R tau) M d*((cells delta A).card:ℝ) by positivity)
    have he : productFactor R tau*M*monomialBound (productFactor R tau) M d =
        monomialBound (productFactor R tau) M (d+1) := by
      unfold monomialBound
      rw [show d+1-1=d by omega]
      have hdid : d-1+1=d := by omega
      have hFp : (productFactor R tau)^(d-1)*productFactor R tau=
          (productFactor R tau)^d := by rw [← pow_succ,hdid]
      calc
        _ = ((productFactor R tau)^(d-1)*productFactor R tau)*(M^d*M) := by ring
        _ = _ := by rw [hFp,pow_succ]
    rw [mul_comm x y] at hh
    calc
      _ ≤ (productFactor R tau*M*monomialBound (productFactor R tau) M d)*
          ((cells delta A).card:ℝ) := by nlinarith only [hh,hm]
      _ = _ := by rw [he]

end OriginalMonomialSmallCover
