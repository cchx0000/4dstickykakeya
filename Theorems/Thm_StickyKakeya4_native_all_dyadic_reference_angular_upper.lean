import Theorems.Thm_StickyKakeya4_native_conditional_reference_angular_upper
import Theorems.Thm_StickyKakeya4_native_conditional_grid_power_cost
import Theorems.Thm_StickyKakeya4_native_fixed_class_exponent_at_most_one

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeAllDyadicReferenceAngularUpper
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeLocalParentSource NativeRelativeCoarseReadback
open NativeGenericReferenceData NativeExtraQueriedRankConfiguration NativeConditionalReferenceMenu
open NativeSameSourceConditionalAngularUpper NativeSameSourceAngularBallUpper
open NativeLocalParentGeometry NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu
open NativeFixedCompactKakeyaExponent NativeMiddleGrainParentBudget

open NativeConditionalReferenceAngularUpper NativeConditionalGridCoverage
open NativeConditionalGridPowerCost NativeAngularDyadicInterpolation

lemma width_mono {c s : ℕ} (hcs : c≤ s) :
    (64:ℝ)/((2^s:ℕ):ℝ)≤ 64/((2^c:ℕ):ℝ) := by
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0< (2:ℕ)) hcs

/-- Every dyadic pair between Rho and1 is read from one fixed pre-E1 grid.
The exact physical ancestor and angular descendant maps pay interpolation
by16*r^(-2/K), with no spatial counting loss or extra core. -/
theorem exists_all_dyadic_angular_ball_upper (epsilon window budget : ℝ)
    (hepsilon : 0< epsilon) (hwindow : 0< window) (hbudget : 0< budget)
    (hWindowBudget : 3*window≤ budget) :
    ∃seedCap delta0 : ℝ,0< seedCap ∧ 0< delta0 ∧ delta0≤ 1/8 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta seed tau e : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0< tau) (L g K : ℕ),
        0≤ eta → 0≤ zeta → eta≤ seed/8 → zeta≤ seed/256 →
        seed≤ seedCap → D.thickness≤ delta0 → 0< K →
      ∀ref : Reference h tau htau seed e zeta L g,
        HasCallerUniformities ref (factory g K) →
      ∀i : Fin (g+1),6≤ (ref.schedule i).val →
      let m := middleDepth (ref.schedule i).val
      ∀s t : ℕ,6≤ t → t≤ s → s≤ m →
      ∀r power : ℝ,0< r → r≤ D.thickness^power → window≤ power →
        64*D.thickness≤ r^2 → 3072*r≤ ((64:ℝ)/((2^m:ℕ):ℝ))^2 →
      ∀(p : Parent) (E : Finset (Fin n × Index)),E⊆ ref.E1 →
        (∀z∈E,parentLabel D ref.a (2^m) z.1=p) →
      ∀(cell : Index) (center : EuclideanSpace ℝ (Fin 3)),
        (∀z∈E,physicalCell D ref.a (2^m) (2^s) p z.2=cell) →
        (∀z∈E,dist (localSlope D (2^m) p z.1) center≤ 64/((2^t:ℕ):ℝ)) →
        ((E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤
          (16*27*conditionalConstant)*r^(-((budget+seed/4)/power+epsilon/2+2/(K:ℝ)))*
            ((64/((2^t:ℕ):ℝ))/(64/((2^s:ℕ):ℝ)))^extremalExponent := by
  obtain ⟨seedCap,delta0,hSeed,hd0,hd08,Hupper⟩ :=
    exists_reference_angular_ball_upper epsilon window budget hepsilon hwindow hbudget hWindowBudget
  refine ⟨seedCap,delta0,hSeed,hd0,hd08,?_⟩
  intro n D eta zeta seed tau e h htau L g K heta hzeta hetaSeed hzseed hseed hsmall hK
    ref Hcaller i hstop m s t ht hts hsm r power hr hrscale hwa hdelta hMiddle
    p E hE hParent cell center hCell hBall
  have hm : 6≤ m := (middle_depth_bounds _ hstop).1
  obtain ⟨q,hqi,hqs,hqt,hgapS,hgapT⟩ := exists_query_predecessors ref.schedule i hK s t ht hts hsm
  have hqm : outerDepth ref.schedule q=m := by simp only [outerDepth,hqi,m]
  let s0 := rhoDepth ref.schedule q
  let t0 := sigmaDepth ref.schedule q
  let cell0 : Index := fun j => cell j/(2^(s-s0):ℕ)
  have hCell0 : ∀z∈E,physicalCell D ref.a (2^m) (2^s0) p z.2=cell0 := by
    intro z hz
    exact (physical_ancestor D ref.a (2^m) p hqs z.2).symm.trans
      (congrArg (fun v : Index => fun j => v j/(2^(s-s0):ℕ)) (hCell z hz))
  have hBall0 : ∀z∈E,dist (localSlope D (2^m) p z.1) center≤ 64/((2^t0:ℕ):ℝ) :=
    fun z hz => (hBall z hz).trans (width_mono hqt)
  have HH := Hupper n D eta zeta seed tau e h htau L g K heta hzeta hetaSeed hzseed hseed hsmall hK
    ref Hcaller q (by simpa only [hqi] using hstop)
  dsimp only at HH
  rw [hqm] at HH
  have hCoarse := HH r power hr hrscale hwa hdelta hMiddle p E hE hParent cell0 center hCell0 hBall0
  have hInterp := angular_image_interpolation D (2^m) p E hqs
  have hFine := hInterp.trans (mul_le_mul_of_nonneg_left hCoarse (Nat.cast_nonneg _))
  have hDelta : 0< (64:ℝ)/((2^m:ℕ):ℝ) := by positivity
  have hDelta1 : (64:ℝ)/((2^m:ℕ):ℝ)≤ 1 := by
    simpa using width_mono hm
  have hrDelta : r≤ ((64:ℝ)/((2^m:ℕ):ℝ))^2 := by nlinarith only [hMiddle,hr]
  have hSigma : ((64:ℝ)/((2^t0:ℕ):ℝ))/(64/((2^t:ℕ):ℝ))≤
      2*((64:ℝ)/((2^m:ℕ):ℝ))^(-(1/(K:ℝ))) := by
    rw [dyadic_width_ratio hqt]
    exact gap_cost m K t t0 hm hK hgapT
  have hPay := two_scale_cost K hK hDelta hDelta1 hr hrDelta
    (by positivity : 0< (64:ℝ)/((2^s:ℕ):ℝ))
    (by positivity : 0< (64:ℝ)/((2^t:ℕ):ℝ))
    (by positivity : 0< (64:ℝ)/((2^t0:ℕ):ℝ))
    (width_mono hqs) extremalExponent_nonneg NativeFixedClassExponentAtMostOne.extremalExponent_le_one
    (Nat.cast_nonneg (2^(s-s0))) (gap_cost m K s s0 hm hK hgapS) hSigma
  have hPaid := mul_le_mul_of_nonneg_left hPay
    (show 0≤ (27*conditionalConstant)*r^(-((budget+seed/4)/power+epsilon/2)) by
      dsimp [conditionalConstant]; positivity)
  have hFine' : ((E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤
      ((27*conditionalConstant)*r^(-((budget+seed/4)/power+epsilon/2)))*
        ((((2^(s-s0):ℕ):ℝ)^3)*((64/((2^t0:ℕ):ℝ))/(64/((2^s0:ℕ):ℝ)))^extremalExponent) := by
    simpa only [s0,t0,Nat.cast_pow,mul_assoc,mul_comm,mul_left_comm] using hFine
  have hFinal := hFine'.trans hPaid
  have hPower : r^(-((budget+seed/4)/power+epsilon/2))*r^(-(2/(K:ℝ)))=
      r^(-((budget+seed/4)/power+epsilon/2+2/(K:ℝ))) := by
    rw [←Real.rpow_add hr]
    congr 1
    ring
  apply hFinal.trans_eq
  rw [show (27*conditionalConstant*r^(-((budget+seed/4)/power+epsilon/2)))*
      (16*r^(-(2/(K:ℝ)))*(64/((2^t:ℕ):ℝ)/(64/((2^s:ℕ):ℝ)))^extremalExponent)=
      (16*27*conditionalConstant)*(r^(-((budget+seed/4)/power+epsilon/2))*r^(-(2/(K:ℝ))))*
        (64/((2^t:ℕ):ℝ)/(64/((2^s:ℕ):ℝ)))^extremalExponent by ring,hPower]

end NativeAllDyadicReferenceAngularUpper
