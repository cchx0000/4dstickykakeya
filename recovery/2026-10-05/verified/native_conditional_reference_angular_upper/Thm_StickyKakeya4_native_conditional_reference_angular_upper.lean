import Theorems.Thm_StickyKakeya4_native_conditional_reference_menu
import Theorems.Thm_StickyKakeya4_native_same_source_angular_ball_upper

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeConditionalReferenceAngularUpper
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeLocalParentSource NativeRelativeCoarseReadback
open NativeGenericReferenceData NativeExtraQueriedRankConfiguration NativeConditionalReferenceMenu
open NativeSameSourceConditionalAngularUpper NativeSameSourceAngularBallUpper
open NativeLocalParentGeometry NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu
open NativeFixedCompactKakeyaExponent NativeMiddleGrainParentBudget

/-- The fixed pre-E1 two-parameter menu supplies every conditional equality
used by the actual angular-ball theorem. Source retention, the radix and its
cost are read from the same enlarged Reference, with its original big F1. -/
theorem exists_reference_angular_ball_upper (epsilon window budget : ℝ)
    (hepsilon : 0< epsilon) (hwindow : 0< window) (hbudget : 0< budget)
    (hWindowBudget : 3*window≤ budget) :
    ∃seedCap delta0 : ℝ,0< seedCap ∧ 0< delta0 ∧ delta0≤ 1/8 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta seed tau e : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0< tau) (L g K : ℕ),
        0≤ eta → 0≤ zeta → eta≤ seed/8 → zeta≤ seed/256 →
        seed≤ seedCap → D.thickness≤ delta0 → 0< K →
      ∀ref : Reference h tau htau seed e zeta L g,
        HasCallerUniformities ref (factory g K) →
      ∀i : Fin (queryCount g K),6≤ (ref.schedule (candidate i)).val →
      let m := outerDepth ref.schedule i
      let s := rhoDepth ref.schedule i
      let t := sigmaDepth ref.schedule i
      ∀r power : ℝ,0< r → r≤ D.thickness^power → window≤ power →
        64*D.thickness≤ r^2 → 3072*r≤ ((64:ℝ)/((2^m:ℕ):ℝ))^2 →
      ∀(p : Parent) (E : Finset (Fin n × Index)),E⊆ ref.E1 →
        (∀z∈E,parentLabel D ref.a (2^m) z.1=p) →
      ∀(cell : Index) (center : EuclideanSpace ℝ (Fin 3)),
        (∀z∈E,physicalCell D ref.a (2^m) (2^s) p z.2=cell) →
        (∀z∈E,dist (localSlope D (2^m) p z.1) center≤ 64/((2^t:ℕ):ℝ)) →
        ((E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤
          (27*conditionalConstant)*r^(-((budget+seed/4)/power+epsilon/2))*
            ((64/((2^t:ℕ):ℝ))/(64/((2^s:ℕ):ℝ)))^extremalExponent := by
  obtain ⟨seedCap,delta0,hSeed,hd0,hd08,Hupper⟩ :=
    exists_angular_ball_upper epsilon window budget hepsilon hwindow hbudget hWindowBudget
  refine ⟨seedCap,delta0,hSeed,hd0,hd08,?_⟩
  intro n D eta zeta seed tau e h htau L g K heta hzeta hetaSeed hzseed hseed hsmall hK
    ref Hcaller i hstop m s t r power hr hrscale hwa hdelta hMiddle p E hE hParent cell center hCell hBall
  have hm : 6≤ outerDepth ref.schedule i := (middle_depth_bounds _ hstop).1
  obtain ⟨ht,hts,hsm⟩ := query_bounds ref.schedule i hK hm
  have hlevel := query_phase_depth ref.schedule i hK hstop
  have hQ : 1≤ coreRadix ref.original ref.R L := by
    have hh := NativeSourceSizeBounds.radix_four_le (NativeOriginalParentDensityCore.retained ref.original ref.R).card L
    dsimp only [coreRadix]
    omega
  have HU := reference_uniformities ref Hcaller i
  exact Hupper n D eta zeta seed ref.a h heta hzeta hetaSeed hzseed hseed hsmall
    ref.original ref.R ref.level ref.backbone ref.E1 ref.core.1
    (factor ref.dimension (g+1) L) (coreRadix ref.original ref.R L) m s t r power
    hQ (NativeGenericReferenceData.factor_pos ref) ht hts hsm hlevel hr hrscale hwa hdelta hMiddle ref.core.2.2.1
    HU.1 ref.cost HU.2 p E hE hParent cell center hCell hBall

end NativeConditionalReferenceAngularUpper
