import Theorems.Thm_StickyKakeya4_native_angular_bottom_endpoint
import Theorems.Thm_StickyKakeya4_native_conditional_upper_parameters

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativePaidMeshAngularUpper
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeLocalParentSource NativeRelativeCoarseReadback
open NativeGenericReferenceData NativeExtraQueriedRankConfiguration NativeConditionalReferenceMenu
open NativeSameSourceConditionalAngularUpper NativeSameSourceAngularBallUpper
open NativeLocalParentGeometry NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu
open NativeFixedCompactKakeyaExponent NativeMiddleGrainParentBudget

open NativeConditionalReferenceAngularUpper NativeConditionalGridCoverage
open NativeConditionalGridPowerCost NativeAngularDyadicInterpolation

open NativeAllDyadicReferenceAngularUpper NativeAngularBottomEndpoint NativeConditionalUpperParameters

def meshAngularConstant : ℝ := (64:ℝ)^3*16*27*conditionalConstant

/-- One fixed menu and one pre-source cutoff give the requested small
r-loss for every dyadic angular ball throughout the actual final spatial
mesh range [Rho/64,1]. The selected stopping exponent is only required to
exceed the prechosen amin; no relative loss or radix budget remains unpaid. -/
theorem exists_paid_mesh_angular_ball_upper (amin loss : ℝ)
    (hamin : 0< amin) (hloss : 0< loss) (hloss1 : loss≤ 1) :
    ∃(K : ℕ) (seedCap delta0 : ℝ),0< K ∧ 0< seedCap ∧ 0< delta0 ∧ delta0≤ 1/8 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta seed tau e : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0< tau) (L g : ℕ),
        0≤ eta → 0≤ zeta → eta≤ seed/8 → zeta≤ seed/256 →
        seed≤ seedCap → D.thickness≤ delta0 →
      ∀ref : Reference h tau htau seed e zeta L g,
        HasCallerUniformities ref (factory g K) →
      ∀i : Fin (g+1),6≤ (ref.schedule i).val →
      let m := middleDepth (ref.schedule i).val
      ∀s t : ℕ,6≤ t → t≤ s → s≤ m+6 →
      ∀r power : ℝ,0< r → r≤ D.thickness^power → amin≤ power →
        64*D.thickness≤ r^2 → 3072*r≤ ((64:ℝ)/((2^m:ℕ):ℝ))^2 →
      ∀(p : Parent) (E : Finset (Fin n × Index)),E⊆ ref.E1 →
        (∀z∈E,parentLabel D ref.a (2^m) z.1=p) →
      ∀(cell : Index) (center : EuclideanSpace ℝ (Fin 3)),
        (∀z∈E,physicalCell D ref.a (2^m) (2^s) p z.2=cell) →
        (∀z∈E,dist (localSlope D (2^m) p z.1) center≤ 64/((2^t:ℕ):ℝ)) →
        ((E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤
          meshAngularConstant*r^(-loss)*
            ((64/((2^t:ℕ):ℝ))/(64/((2^s:ℕ):ℝ)))^extremalExponent := by
  obtain ⟨epsilon,window,budget,seedBound,K,he,hw,hb,hs,hK,hwb,hwa,Hloss⟩ :=
    exists_upper_parameters amin loss hamin hloss hloss1
  obtain ⟨seedCap,delta0,hSeed,hd0,hd08,Hupper⟩ :=
    exists_all_dyadic_angular_ball_upper epsilon window budget he hw hb hwb
  refine ⟨K,min seedCap seedBound,delta0,hK,lt_min hSeed hs,hd0,hd08,?_⟩
  intro n D eta zeta seed tau e h htau L g heta hzeta hetaSeed hzseed hseed hsmall
    ref Hcaller i hstop m s t ht hts hsm r power hr hrscale hpower hdelta hMiddle
    p E hE hParent cell center hCell hBall
  have hm : 6≤ m := (middle_depth_bounds _ hstop).1
  have hDelta1 : (64:ℝ)/((2^m:ℕ):ℝ)≤ 1 := by simpa using width_mono hm
  have hDelta0 : 0≤ (64:ℝ)/((2^m:ℕ):ℝ) := by positivity
  have hr1 : r≤ 1 := by nlinarith only [hMiddle,hr,hDelta1,hDelta0]
  have hpaid := Hloss power seed hpower (hseed.trans (min_le_right _ _))
  have hPower := Real.rpow_le_rpow_of_exponent_ge hr hr1 (neg_le_neg hpaid)
  let C : ℝ := (16*27*conditionalConstant)*r^(-loss)
  have hC : 0≤ C := by dsimp [C,conditionalConstant]; positivity
  have Hbase : ∀s t : ℕ,6≤ t → t≤ s → s≤ m →
      ∀(cell : Index) (center : EuclideanSpace ℝ (Fin 3)),
        (∀z∈E,physicalCell D ref.a (2^m) (2^s) p z.2=cell) →
        (∀z∈E,dist (localSlope D (2^m) p z.1) center≤ 64/((2^t:ℕ):ℝ)) →
        ((E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤
          C*((64/((2^t:ℕ):ℝ))/(64/((2^s:ℕ):ℝ)))^extremalExponent := by
    intro s t ht hts hsm cell center hCell hBall
    have hh := Hupper n D eta zeta seed tau e h htau L g K heta hzeta hetaSeed hzseed
      (hseed.trans (min_le_left _ _)) hsmall hK ref Hcaller i hstop s t ht hts hsm
      r power hr hrscale (hwa.trans hpower) hdelta hMiddle p E hE hParent cell center hCell hBall
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPower (by dsimp [conditionalConstant]; positivity)) (by positivity))
  have hh := extend_bottom D ref.a m hm p E C extremalExponent hC extremalExponent_nonneg
    Hbase s t ht hts hsm cell center hCell hBall
  simpa only [C,meshAngularConstant,mul_assoc] using hh

end NativePaidMeshAngularUpper
