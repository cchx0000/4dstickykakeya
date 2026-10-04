import Theorems.Thm_StickyKakeya4_original_dense_polynomial_coefficients
import Theorems.Thm_StickyKakeya4_original_polynomial_ring_cover
import Theorems.Thm_StickyKakeya4_original_weak_scalar_word_cost
import Theorems.Thm_StickyKakeya4_original_dense_coefficient_projection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
noncomputable section
open Classical
open scoped Pointwise BigOperators

namespace OriginalWeakScalarFiniteComparison
open ActualRoundedAdditiveEnergy GKZOriginalGapEnergy GKZDilateRoundedSums
open OriginalRoundedRuzsaCover OriginalRoundedRingProduct OriginalPolynomialRingCover
open OriginalDensePolynomialCoefficients OriginalPolynomialWordLength
open OriginalDenseCoefficientCounts OriginalDenseCoefficientProjection OriginalWeakScalarWordCost

lemma original_sum_cover_eq (A : Finset ℝ) (delta x : ℝ) :
    sumCover A delta x=cells delta (A+dilate x A) := by
  have he : A+dilate x A=(A.product A).image (fun p => p.1+x*p.2) := by
    simpa only [dilate,Finset.image_id,Finset.image_id',id_eq] using
      image_add_image A A id (fun a => x*a)
  rw [cells,he,Finset.image_image]
  rfl

lemma original_cells_card_of_separated (A : Finset ℝ) {delta : ℝ} (hd : 0 < delta)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|) :
    (cells delta A).card=A.card := by
  exact Finset.card_image_iff.mpr (rounding_injOn A hd hsep)

/-- A certificate-free finite weak-scalar comparison on the ORIGINAL
coefficient and target carriers. The separated polynomial coefficients and
all their cover bounds are constructed from the same original inputs. -/
theorem exists_original_weak_scalar_comparison (n : ℕ) (kappa : ℝ)
    (hkappa : 0 < kappa) (hkappa1 : kappa ≤ 1)
    (hmu : 2 ≤ kappa*((n+1:ℕ):ℝ)) :
    ∃ W : ℕ, 0 < W ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (A D : Finset ℝ) (delta R tau q KA KD u v eta M : ℝ),
        A.Nonempty → D.Nonempty → 0 < delta → delta ≤ 1 → 1 ≤ R →
        0 < tau → tau ≤ 1 → delta ≤ q → q ≤ 1 → 0 ≤ KA → 0 ≤ M →
        kappa < v → 0 ≤ eta →
        (∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|) →
        (∀ x∈D, tau ≤ |x| ∧ |x| ≤ R) →
        ScalarFrostman A delta KA u → ScalarFrostman D delta KD v →
        KD*(2*R)^kappa ≤ delta^(-eta) →
        2*delta^(1-((2^n:ℕ):ℝ)*(eta/(v-kappa))) ≤ (1/4:ℝ)^(1/kappa) →
        (∀ x∈D, ((sumCover A delta x).card:ℝ) ≤ M*A.card) →
        1 ≤ wordCost W (2^n) R tau M*
          (4*KA*q^u+192*delta*A.card/(q*C*delta^(((2^n:ℕ):ℝ)*(eta/(v-kappa))))) := by
  obtain ⟨W,hW,C,hC,hproducer⟩ := exists_fixed_original_dense_polynomial_coefficients
    n kappa hkappa hkappa1 hmu
  refine ⟨W,hW,C,hC,?_⟩
  intro A D delta R tau q KA KD u v eta M hA hD hd hd1 hR htau htau1 hq hq1 hKA hM
    hgap heta hAsep hDbox hAprofile hDprofile hbudget hcutoff hsmall
  have hdiam : ∀ x∈D, ∀ y∈D, |x-y| ≤ 2*R := by
    intro x hx y hy
    have hh := abs_sub_le x 0 y
    simp only [sub_zero,zero_sub,abs_neg] at hh
    linarith only [hh,(hDbox x hx).2,(hDbox y hy).2]
  have hdR : delta ≤ 2*R := by linarith only [hd1,hR]
  obtain ⟨Xi,hXi,hXiNon,hXiSep,hpop⟩ := hproducer D delta (2*R) KD v eta hD hd hd1 hdR
    hgap heta hdiam hDprofile hbudget hcutoff
  have hcard := original_cells_card_of_separated A hd hAsep
  have hsmall' : ∀ x∈D, ((cells delta (A+dilate x A)).card:ℝ) ≤ M*(cells delta A).card := by
    intro x hx
    rw [← original_sum_cover_eq,hcard]
    exact hsmall x hx
  have hwords : ∀ x∈Xi, ((sumCover A delta x).card:ℝ) ≤ wordCost W (2^n) R tau M*A.card := by
    intro x hx
    rw [original_sum_cover_eq]
    have hh := original_polynomial_word_cover A D hd hA hD hR htau htau1 hM hDbox hsmall'
      W (2^n) (one_le_pow₀ (by norm_num : (1:ℕ)≤2)) (hXi hx)
    rw [hcard] at hh
    exact hh
  have hgain := original_common_small_sum_obstruction A Xi delta q KA u
    (wordCost W (2^n) R tau M) hA hXiNon hd hq hq1 hKA hAsep hXiSep hAprofile hwords
  have hN : (0:ℝ) ≤ A.card := Nat.cast_nonneg _
  have hX : (0:ℝ) < Xi.card := Nat.cast_pos.mpr hXiNon.card_pos
  have hqpos : 0 < q := hd.trans_le hq
  let power := delta^(((2^n:ℕ):ℝ)*(eta/(v-kappa)))
  have hpower : 0 < power := Real.rpow_pos_of_pos hd _
  have hfar : 6*(A.card:ℝ)/(q*Xi.card) ≤ 192*delta*A.card/(q*C*power) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hpop (show 0≤6*(A.card:ℝ)*q by positivity)
    nlinarith only [hh]
  have hcost : 0 ≤ wordCost W (2^n) R tau M := by
    unfold wordCost signedBound selfBound OriginalMonomialSmallCover.monomialBound
      OriginalMonomialSmallCover.productFactor
    positivity
  exact hgain.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl (4*KA*q^u)) hfar) hcost)

end OriginalWeakScalarFiniteComparison
