import Theorems.Thm_StickyKakeya4_original_monomial_small_cover
import Theorems.Thm_StickyKakeya4_original_signed_coefficient_cover
import Theorems.Thm_StickyKakeya4_original_selected_word_cover
import Theorems.Thm_StickyKakeya4_original_polynomial_word_length
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open Classical
open scoped Pointwise BigOperators

namespace OriginalPolynomialRingCover
open OriginalRoundedRuzsaCover OriginalRoundedRingProduct OriginalMonomialSmallCover
open OriginalSignedCoefficientCover OriginalSelectedWordCover OriginalPolynomialWordLength

def selfBound (tau M : ℝ) : ℝ := (1536/tau)*M^2

def signedBound (R tau M : ℝ) (d : ℕ) : ℝ :=
  1+selfBound tau M+monomialBound (productFactor R tau) M d+
    256*selfBound tau M*monomialBound (productFactor R tau) M d

/-- Every original signed degree-d monomial has a controlled actual linear
image. Zero and the original anchor are included with their proved costs. -/
theorem original_signed_monomial_covers (A D : Finset ℝ) {delta R tau M : ℝ}
    (hd : 0 < delta) (hA : A.Nonempty) (hD : D.Nonempty)
    (hR : 1 ≤ R) (htau : 0 < tau) (htau1 : tau ≤ 1) (hM : 0 ≤ M)
    (hDbox : ∀ x∈D, tau ≤ |x| ∧ |x| ≤ R)
    (hsmall : ∀ x∈D, ((cells delta (A+dilate x A)).card:ℝ) ≤ M*(cells delta A).card)
    (d : ℕ) (hdim : 1 ≤ d) :
    ((cells delta (A+A)).card:ℝ) ≤ signedBound R tau M d*(cells delta A).card ∧
    ∀ y∈signedMonomials D d, ((cells delta (A+dilate y A)).card:ℝ) ≤
      signedBound R tau M d*(cells delta A).card := by
  obtain ⟨x,hx⟩ := hD
  have hself := original_self_sum_small_cover A hd hA htau htau1 (hDbox x hx).1 (hsmall x hx)
  have hmono := original_monomial_small_cover A D hd hA hR htau hM hDbox hsmall d hdim
  have hS : 0 ≤ selfBound tau M := by unfold selfBound; positivity
  have hQ : 0 ≤ monomialBound (productFactor R tau) M d := by
    unfold monomialBound productFactor
    positivity
  have hSQ : 0 ≤ 256*selfBound tau M*monomialBound (productFactor R tau) M d := by positivity
  have hB1 : 1 ≤ signedBound R tau M d := by
    unfold signedBound
    linarith only [hS,hQ,hSQ]
  have hBS : selfBound tau M ≤ signedBound R tau M d := by
    unfold signedBound
    linarith only [hS,hQ,hSQ]
  have hBQ : monomialBound (productFactor R tau) M d ≤ signedBound R tau M d := by
    unfold signedBound
    linarith only [hS,hQ,hSQ]
  have hBN : 256*selfBound tau M*monomialBound (productFactor R tau) M d ≤
      signedBound R tau M d := by unfold signedBound; linarith only [hS,hQ]
  have hN : (0:ℝ) ≤ (cells delta A).card := Nat.cast_nonneg _
  refine ⟨hself.trans (mul_le_mul_of_nonneg_right hBS hN),?_⟩
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · have hzero : dilate 0 A=0 := by
      ext z
      constructor
      · intro hz
        obtain ⟨a,_ha,rfl⟩ := Finset.mem_image.mp hz
        simp
      · intro hz
        have hz0 : z=0 := by simpa only [Finset.mem_zero] using hz
        obtain ⟨a,ha⟩ := hA
        exact Finset.mem_image.mpr ⟨a,ha,by simp only [zero_mul,hz0]⟩
    rw [hzero,add_zero]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hB1 hN
  · rcases Finset.mem_union.mp hy with hy | hy
    · exact (hmono y hy).trans (mul_le_mul_of_nonneg_right hBQ hN)
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_neg.mp hy
      have hh := original_negative_small_cover A hd hA hS hself (hmono z hz)
      exact hh.trans (mul_le_mul_of_nonneg_right hBN hN)

/-- A bounded-degree, bounded-LENGTH original polynomial is controlled by
only its own actual monomial witnesses. The explicit exponent T+1 cannot
be treated as fixed unless T was chosen before the mesh and input data. -/
theorem original_polynomial_word_cover (A D : Finset ℝ) {delta R tau M : ℝ}
    (hd : 0 < delta) (hA : A.Nonempty) (hD : D.Nonempty)
    (hR : 1 ≤ R) (htau : 0 < tau) (htau1 : tau ≤ 1) (hM : 0 ≤ M)
    (hDbox : ∀ x∈D, tau ≤ |x| ∧ |x| ≤ R)
    (hsmall : ∀ x∈D, ((cells delta (A+dilate x A)).card:ℝ) ≤ M*(cells delta A).card)
    (T d : ℕ) (hdim : 1 ≤ d) {y : ℝ} (hy : y∈polynomialWords D T d) :
    ((cells delta (A+dilate y A)).card:ℝ) ≤
      ((2*T+5:ℕ):ℝ)*(((T+1:ℕ):ℝ)*(8*signedBound R tau M d))^(T+1)*(cells delta A).card := by
  obtain ⟨f,hf⟩ := Finset.mem_nsmul.mp hy
  have hsum : y=∑ i : Fin T,(f i:ℝ) := by simpa only [List.sum_ofFn] using hf.symm
  have hc := original_signed_monomial_covers A D hd hA hD hR htau htau1 hM hDbox hsmall d hdim
  have hB : 0 ≤ signedBound R tau M d := by
    unfold signedBound selfBound monomialBound productFactor
    positivity
  rw [hsum]
  exact original_selected_word_cover A T (fun i => (f i:ℝ)) hd hA hB hc.1
    (fun i => hc.2 (f i) (f i).2)

end OriginalPolynomialRingCover
