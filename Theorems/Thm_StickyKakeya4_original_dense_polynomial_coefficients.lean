import Theorems.Thm_StickyKakeya4_original_full_coefficient_normalization
import Theorems.Thm_StickyKakeya4_original_normalized_polynomial_cover
import Theorems.Thm_StickyKakeya4_original_polynomial_word_homogeneity
import Theorems.Thm_StickyKakeya4_original_polynomial_mesh_transfer
import Theorems.Thm_StickyKakeya4_original_coefficient_cover_net
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
noncomputable section
open Classical
open scoped Pointwise BigOperators

namespace OriginalDensePolynomialCoefficients
open ActualRoundedAdditiveEnergy GKZOriginalGapEnergy OriginalFullCoefficientNormalization
open OriginalPolynomialWordLength OriginalNormalizedPolynomialCover OriginalPolynomialWordHomogeneity
open OriginalPolynomialMeshTransfer OriginalCoefficientCoverNet

/-- The full original weak coefficient profile constructs a dense ACTUAL
separated polynomial coefficient carrier. Word length and degree are fixed
before the data. The profile normalization, initial projection, dimension
reduction, centering expansion, mesh transfer and final net are all derived. -/
theorem exists_fixed_original_dense_polynomial_coefficients (n : ℕ) (kappa : ℝ)
    (hkappa : 0 < kappa) (hkappa1 : kappa ≤ 1)
    (hmu : 2 ≤ kappa*((n+1:ℕ):ℝ)) :
    ∃ W : ℕ, 0 < W ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (D : Finset ℝ) (delta B K u eta : ℝ), D.Nonempty →
        0 < delta → delta ≤ 1 → delta ≤ B → kappa < u → 0 ≤ eta →
        (∀ x∈D, ∀ y∈D, |x-y| ≤ B) → ScalarFrostman D delta K u →
        K*B^kappa ≤ delta^(-eta) →
        2*delta^(1-((2^n:ℕ):ℝ)*(eta/(u-kappa))) ≤ (1/4:ℝ)^(1/kappa) →
        ∃ Xi : Finset ℝ, Xi⊆polynomialWords D W (2^n) ∧ Xi.Nonempty ∧
          (∀ x∈Xi, ∀ y∈Xi, x≠y → delta ≤ |x-y|) ∧
          C*delta^(((2^n:ℕ):ℝ)*(eta/(u-kappa))) ≤ 32*delta*Xi.card := by
  obtain ⟨T,hT,C,hC,hengine⟩ := exists_fixed_polynomial_cover_of_absolute_profile n kappa hkappa hmu
  refine ⟨T*2^(2^n),by positivity,C,hC,?_⟩
  intro D delta B K u eta hD hd hd1 hdB hgap heta hDbox hDprofile hbudget hcutoff
  let d : ℕ := 2^n
  let alpha := eta/(u-kappa)
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hdge : 1 ≤ d := hdpos
  have halpha : 0 ≤ alpha := div_nonneg heta (sub_pos.mpr hgap).le
  obtain ⟨S,c,R,hSD,hc,hdR,_hRB,_hcard,hbox,hprofile,_hmass,hradius⟩ :=
    exists_original_full_profile_normalization D hD hd hkappa.le hkappa1 hdB hDbox hDprofile
  have hR : 0 < R := hd.trans_le hdR
  let A := normalizedCarrier S c R
  have hA : A.Nonempty := (show S.Nonempty from ⟨c,hc⟩).image _
  have hlower : delta^alpha ≤ R := original_full_radius_power hd hd1 hR heta hgap hbudget hradius
  let base := max (delta/R) (delta/R^d)
  have hbasepos : 0 < base := (div_pos hd hR).trans_le (le_max_left _ _)
  have hbasetop : base ≤ delta^(1-(d:ℝ)*alpha) :=
    original_final_polynomial_mesh d hd hd1 halpha hdge hlower
  have hthreshold := OriginalCoefficientNormalization.absolute_diameter_threshold hkappa
  have hbase1 : base ≤ 1 := by
    change 2*delta^(1-(d:ℝ)*alpha) ≤ (1/4:ℝ)^(1/kappa) at hcutoff
    linarith only [hbasetop,hcutoff,hthreshold.2.1]
  obtain ⟨k,hbase,hbaseupper⟩ := exists_original_coarser_dyadic_mesh hbasepos hbase1
  let epsilon := ProjectionAnnulusEnergy.mesh k
  have he : 0 < epsilon := ProjectionAnnulusEnergy.mesh_pos k
  have henginecutoff : epsilon ≤ (1/4:ℝ)^(1/kappa) := by
    change 2*delta^(1-(d:ℝ)*alpha) ≤ (1/4:ℝ)^(1/kappa) at hcutoff
    linarith only [hbaseupper,hbasetop,hcutoff]
  have hAprofile : ScalarFrostman A epsilon 2 kappa := by
    intro center r hr hr1
    exact hprofile center r (((le_max_left _ _).trans hbase).trans hr) hr1
  have himage := hengine k A hA henginecutoff hbox hAprofile
  have hmesh := original_homogeneous_mesh R delta d hR hd
  change delta/R ≤ base ∧ delta ≤ base*R^d ∧ base*min R (R^d)=delta at hmesh
  have hpow : 0 < R^d := pow_pos hR d
  have hmin : 0 < min R (R^d) := lt_min hR hpow
  have hcoarse : delta ≤ epsilon*R^d := hmesh.2.1.trans
    (mul_le_mul_of_nonneg_right hbase hpow.le)
  have hupper : epsilon*min R (R^d) ≤ 2*delta := by
    have hh := mul_le_mul_of_nonneg_right hbaseupper hmin.le
    nlinarith only [hh,hmesh.2.2]
  let Q := polynomialWords A T d
  have hQimage : C ≤ epsilon*((Q.image (fun x => rounded epsilon (id x))).card:ℝ) := by
    simpa only [id_eq] using himage
  have htransfer := original_homogeneous_cover_transfer Q id d hR hd he hcoarse hupper hQimage
  have hhom := original_polynomial_word_homogeneity S D c R hSD (hSD hc) hR T d
  have hcount : ((Q.image (fun x => rounded delta (R^d*id x))).card:ℝ) ≤
      ((polynomialWords D (T*2^d) d).image (rounded delta)).card := by
    have hh := Nat.cast_le (α:=ℝ).mpr (Finset.card_le_card (Finset.image_subset_image
      (f:=rounded delta) hhom))
    simpa only [Finset.image_image,Function.comp_def,id_eq] using hh
  have hsmallpow : delta^((d:ℝ)*alpha) ≤ min R (R^d) := by
    apply le_min
    · have hdreal : (1:ℝ) ≤ d := by exact_mod_cast hdge
      have hexp : alpha ≤ (d:ℝ)*alpha := by nlinarith only [halpha,hdreal]
      exact (Real.rpow_le_rpow_of_exponent_ge hd hd1 hexp).trans hlower
    · have hh := pow_le_pow_left₀ (Real.rpow_nonneg hd.le alpha) hlower d
      simpa only [← Real.rpow_mul_natCast hd.le,mul_comm alpha (d:ℝ)] using hh
  have h1 := mul_le_mul_of_nonneg_right hsmallpow hC.le
  have h2 := mul_le_mul_of_nonneg_left hcount (show 0≤8*delta by positivity)
  have hcover : C*delta^((d:ℝ)*alpha)/8 ≤
      delta*((polynomialWords D (T*2^d) d).image (rounded delta)).card := by
    nlinarith only [h1,htransfer,h2]
  have hL : 0 < C*delta^((d:ℝ)*alpha)/8 := by positivity
  obtain ⟨Xi,hXi,hXiNon,hsep,hpop⟩ := exists_original_dense_coefficient_net
    (polynomialWords D (T*2^d) d) hd hL hcover
  refine ⟨Xi,hXi,hXiNon,hsep,?_⟩
  change C*delta^((d:ℝ)*alpha) ≤ 32*delta*Xi.card
  nlinarith only [hpop]

end OriginalDensePolynomialCoefficients
