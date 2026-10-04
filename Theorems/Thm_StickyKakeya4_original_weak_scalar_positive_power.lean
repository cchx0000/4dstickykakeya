import Theorems.Thm_StickyKakeya4_original_weak_scalar_finite_comparison
import Theorems.Thm_StickyKakeya4_original_weak_scalar_power_comparison
import Theorems.Thm_StickyKakeya4_original_weak_scalar_power_parameters
import Theorems.Thm_StickyKakeya4_original_coefficient_zero_removal
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace OriginalWeakScalarPositivePower
open ActualRoundedAdditiveEnergy GKZOriginalGapEnergy OriginalDenseCoefficientProjection
open OriginalWeakScalarFiniteComparison OriginalWeakScalarWordCost
open OriginalWeakScalarPowerComparison OriginalWeakScalarPowerParameters
open OriginalCoefficientZeroRemoval

/-- Genuine weak-profile scalar expansion. All exponents and the cutoff
precede the actual original target and coefficient sets. The target profile
exponent need not match its cardinality exponent. The selected coefficient
belongs to the ORIGINAL D, after the derived polynomial contradiction. -/
theorem exists_original_weak_scalar_growth (u gap : ℝ)
    (hu : 0 < u) (hu1 : u ≤ 1) (hgap : 0 < gap) (hgap1 : gap ≤ 1) :
    ∃ epsilon eta delta0 : ℝ, 0 < epsilon ∧ 0 < eta ∧ 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (A D : Finset ℝ) (delta : ℝ), A.Nonempty → D.Nonempty →
        0 < delta → delta ≤ delta0 →
        (∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|) →
        (A.card:ℝ) ≤ delta^(-1+gap) →
        ScalarFrostman A delta (delta^(-eta)) u →
        ScalarFrostman D delta (delta^(-eta)) u →
        (∀ x∈D, |x| ≤ delta^(-eta)) →
        ∃ x∈D, delta^(-epsilon)*A.card < (sumCover A delta x).card := by
  let kappa := u/2
  let n : ℕ := ⌈4/u⌉₊
  let d : ℕ := 2^n
  have hkappa : 0 < kappa := by dsimp [kappa]; positivity
  have hkappa1 : kappa ≤ 1 := by dsimp [kappa]; linarith only [hu1]
  have hkv : kappa < u := by dsimp [kappa]; linarith only [hu]
  have hmu : 2 ≤ kappa*((n+1:ℕ):ℝ) := by
    have hn : (4:ℝ)/u ≤ (n:ℝ) := Nat.le_ceil _
    have hh := (div_le_iff₀ hu).mp hn
    dsimp [kappa]
    push_cast
    nlinarith only [hh,hu]
  have hdim : 1 ≤ d := one_le_pow₀ (by norm_num : (1:ℕ)≤2)
  obtain ⟨W,hW,C,hC,hcompare⟩ := exists_original_weak_scalar_comparison n kappa hkappa hkappa1 hmu
  obtain ⟨epsilon,eta,g,heps,heta,hg,hzeta1,hmeshPower,hnear,hfar⟩ :=
    exists_original_weak_power_margins W d hu hu1 hgap hgap1
  let zeta := 2*eta/u
  let alpha := (4*(d:ℝ)*(1+u/2)/u)*eta
  let totalConstant := costConstant W d*(4+192/C)
  have hzeta : 0 ≤ zeta := by dsimp [zeta]; positivity
  have htotal : 0 < totalConstant := mul_pos (costConstant_pos W d) (by positivity)
  have hthreshold : 0 < (1/4:ℝ)^(1/kappa) := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_original_weak_power_cutoff heta hmeshPower hg htotal hthreshold
  refine ⟨epsilon,eta,delta0,heps,heta,hd0,hd01,?_⟩
  intro A D delta hA hD hd hsmall hAsep hNupper hAprofile hDprofile hDbox
  have hd1 : delta ≤ 1 := hsmall.trans hd01
  obtain ⟨hzero,henginecut,hfinalcut⟩ := hcut delta hd hsmall
  let R := delta^(-eta)
  let tau := delta^zeta
  let q := delta^(gap/2)
  let M := delta^(-epsilon)
  let D0 := D.filter (fun x => tau < |x|)
  have hRpos : 0 < R := Real.rpow_pos_of_pos hd _
  have hR1 : 1 ≤ R := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (by linarith only [heta])
  have htau : 0 < tau := Real.rpow_pos_of_pos hd _
  have htau1 : tau ≤ 1 := Real.rpow_le_one hd.le hd1 hzeta
  have htauLow : delta ≤ tau := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hd hd1 hzeta1
  have hq1 : q ≤ 1 := Real.rpow_le_one hd.le hd1 (by positivity : 0≤gap/2)
  have hqLow : delta ≤ q := by
    have hhalf : gap/2 ≤ 1 := by linarith only [hgap1]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hd hd1 hhalf
  have hM : 0 ≤ M := (Real.rpow_pos_of_pos hd _).le
  have hzeroCap : R*tau^u ≤ 1/2 := by
    change delta^(-eta)*(delta^(2*eta/u))^u ≤ 1/2
    rw [original_zero_removal_power hd hu]
    exact hzero
  have hmass := original_remove_zero_mass D htauLow htau1 hDprofile hzeroCap
  have hD0 : D0.Nonempty := by
    have hN : (0:ℝ) < D.card := Nat.cast_pos.mpr hD.card_pos
    have hp : (0:ℝ) < D0.card := (div_pos hN (by norm_num : (0:ℝ)<2)).trans_le hmass
    exact Finset.card_pos.mp (Nat.cast_pos.mp hp)
  have hD0profile : ScalarFrostman D0 delta (2*R) u :=
    original_remove_zero_profile D hd.le hRpos.le htauLow htau1 hDprofile hzeroCap
  have hD0box : ∀ x∈D0, tau ≤ |x| ∧ |x| ≤ R := by
    intro x hx
    exact ⟨(Finset.mem_filter.mp hx).2.le,hDbox x (Finset.mem_filter.mp hx).1⟩
  let etaN := 2*eta*(1+kappa)
  have hetaN : 0 ≤ etaN := by dsimp [etaN]; positivity
  have hbudget : (2*R)*(2*R)^kappa ≤ delta^(-etaN) :=
    original_profile_normalization_budget hd hkappa.le hzero
  have hnorm : (d:ℝ)*(etaN/(u-kappa))=alpha := original_normalization_exponent hu d
  have henginecut' : 2*delta^(1-((2^n:ℕ):ℝ)*(etaN/(u-kappa))) ≤ (1/4:ℝ)^(1/kappa) := by
    change 2*delta^(1-(d:ℝ)*(etaN/(u-kappa))) ≤ _
    rw [hnorm]
    exact henginecut
  by_contra hbad
  push Not at hbad
  have hsmallD0 : ∀ x∈D0, ((sumCover A delta x).card:ℝ) ≤ M*A.card := by
    intro x hx
    exact hbad x (Finset.mem_filter.mp hx).1
  have hcompare' := hcompare A D0 delta R tau q R (2*R) u u etaN M hA hD0 hd hd1 hR1
    htau htau1 hqLow hq1 hRpos.le hM hkv hetaN hAsep hD0box hAprofile hD0profile
    hbudget henginecut' hsmallD0
  change 1 ≤ wordCost W d R tau M*
    (4*R*q^u+192*delta*A.card/(q*C*delta^((d:ℝ)*(etaN/(u-kappa))))) at hcompare'
  rw [hnorm] at hcompare'
  have hupper := original_power_obstruction_upper W d hd hd1 heps.le heta.le hzeta hdim hC
    (Nat.cast_nonneg A.card) hNupper hnear hfar
  have hbig : 1 ≤ totalConstant*delta^(2*g) := hcompare'.trans hupper
  linarith only [hbig,hfinalcut]

end OriginalWeakScalarPositivePower
