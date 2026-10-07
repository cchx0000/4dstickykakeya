import Theorems.Thm_StickyKakeya4_native_same_source_conditional_angular_upper
import Theorems.Thm_StickyKakeya4_native_conditional_angular_power_budget
import Theorems.Thm_StickyKakeya4_native_angular_ball_cell_cover

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 11000000

noncomputable section
namespace NativeSameSourceAngularBallUpper
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeMiddleWindowBalance NativeReferenceParentCompleteAngularUpper NativeRelativeCoarseReadback
open NativeJointUniformCoarseRelations NativeNormalizedCellAngularMenu NativeNormalizedCellRelativeMenu
open NativeFixedCompactKakeyaExponent NativeReferenceXYGridAngularCap
open NativeConditionalAngularCountTransfer NativeConditionalAngularScaleReadback

open NativeSameSourceConditionalAngularUpper NativeConditionalAngularPowerBudget
open NativeAngularBallCellCover

/-- Actual same-source angular ball upper with exponent exactly kappa.
All first-core and native relative-source losses are explicitly paid in
stopping r; seedCap and delta0 are selected before the source datum. -/
theorem exists_angular_ball_upper (epsilon window budget : ℝ)
    (hepsilon : 0< epsilon) (hwindow : 0< window) (hbudget : 0< budget)
    (hWindowBudget : 3*window≤ budget) :
    ∃seedCap delta0 : ℝ,0< seedCap ∧ 0< delta0 ∧ delta0≤ 1/8 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta seed a : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0≤ eta → 0≤ zeta → eta≤ seed/8 → zeta≤ seed/256 → seed≤ seedCap → D.thickness≤ delta0 →
      ∀(original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ),
        HasOriginalBackbone D original R a level zeta →
      ∀E1 : Finset (Fin n × Index),E1⊆ retained original R →
      ∀(F Q m s t : ℕ) (r power : ℝ),1≤ Q → 0< F → 6≤ t → t≤ s → s≤ m → m+s-6≤ level →
        0< r → r≤ D.thickness^power → window≤ power →
        64*D.thickness≤ r^2 → 3072*r≤ ((64:ℝ)/((2^m:ℕ):ℝ))^2 →
        (incidences original).card≤ F*E1.card →
        (∀x y,x∈E1 → y∈E1 →
          (parentEdges D a (2^(m+t-6)) E1 (parentLabel D a (2^(m+t-6)) x.1)).card≤ 
            Q^2*(parentEdges D a (2^(m+t-6)) E1 (parentLabel D a (2^(m+t-6)) y.1)).card) →
        (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*D.thickness^(-eta)≤ D.thickness^(-(seed/8)) →
        (∀q : Parent,∀hq : (parentLabels D R a (2^(m+t-6)) q).Nonempty,
          HasUniformFibers (parentEdges D a (2^(m+t-6)) E1 q) Q
            (doublePair h R a (m+t-6) q hq (2^(s-t+6))) ∧
          HasUniformFibers (parentEdges D a (2^(m+t-6)) E1 q) Q
            (fun z => (doublePair h R a (m+t-6) q hq (2^(s-t+6)) z).2)) →
      ∀(p : Parent) (E : Finset (Fin n × Index)),E⊆ E1 →
        (∀z∈E,parentLabel D a (2^m) z.1=p) →
      ∀(cell : Index) (center : EuclideanSpace ℝ (Fin 3)),
        (∀z∈E,physicalCell D a (2^m) (2^s) p z.2=cell) →
        (∀z∈E,dist (NativeLocalParentGeometry.localSlope D (2^m) p z.1) center≤ 64/((2^t:ℕ):ℝ)) →
        ((E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤ 
          (27*conditionalConstant)*r^(-((budget+seed/4)/power+epsilon/2))*
            ((64/((2^t:ℕ):ℝ))/(64/((2^s:ℕ):ℝ)))^extremalExponent := by
  obtain ⟨seedCap,delta0,hSeed,hd0,hd08,Hcell⟩ :=
    exists_conditional_angular_upper epsilon window budget hepsilon hwindow hbudget hWindowBudget
  refine ⟨seedCap,delta0,hSeed,hd0,hd08,?_⟩
  intro n D eta zeta seed a h heta0 hzeta heta hzseed hseed hsmall original R level HB E1 hE1
    F Q m s t r power hQ hF ht hts hsm hlevel hr hrscale hwa hdelta hMiddle hret Hparent Hcost Hrelative
    p E hEE1 hParent cell center hCell hBall
  have hpow : 0< power := hwindow.trans_le hwa
  have hseed0 : 0≤ seed := by linarith only [heta0,heta]
  have hb6 : 6≤ m+t-6 := by omega
  have hN : (64:ℝ)≤ ((2^(m+t-6):ℕ):ℝ) := by
    exact_mod_cast (show (64:ℕ)≤ 2^(m+t-6) by
      simpa only [show (2:ℕ)^6=64 by norm_num] using
        Nat.pow_le_pow_right (by norm_num : 0< (2:ℕ)) hb6)
  have hLocal : D.thickness≤ ((2^(m+t-6):ℕ):ℝ)*D.thickness/64 := by
    nlinarith only [hN,h.1.2.1]
  have hT : (64:ℝ)≤ ((2^t:ℕ):ℝ) := by
    exact_mod_cast (show (64:ℕ)≤ 2^t by
      simpa only [show (2:ℕ)^6=64 by norm_num] using
        Nat.pow_le_pow_right (by norm_num : 0< (2:ℕ)) ht)
  have hsigma : 0< (64:ℝ)/((2^t:ℕ):ℝ) := by positivity
  have hrho : 0< (64:ℝ)/((2^s:ℕ):ℝ) := by positivity
  have hDelta : 0< (64:ℝ)/((2^m:ℕ):ℝ) := by positivity
  have hsigma1 : (64:ℝ)/((2^t:ℕ):ℝ)≤ 1 := (div_le_one (by positivity)).mpr hT
  have hsmR : ((2^s:ℕ):ℝ)≤ ((2^m:ℕ):ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0< (2:ℕ)) hsm
  have hDeltaRho : (64:ℝ)/((2^m:ℕ):ℝ)≤ 64/((2^s:ℕ):ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hsmR
  have hrDelta : r≤ ((64:ℝ)/((2^m:ℕ):ℝ))^2 := by nlinarith only [hMiddle,hr]
  let B : ℝ := conditionalConstant*(Q:ℝ)^4*(((2^(m+t-6):ℕ):ℝ)*D.thickness/64)^(-budget)*
    ((64/((2^s:ℕ):ℝ))/(64/((2^t:ℕ):ℝ)))^(-extremalExponent-epsilon)
  have hB : 0≤ B := by dsimp [B,conditionalConstant]; have hd := h.1.2.1; positivity
  have hUpper := angular_ball_count D (2^m) (2^s) p E center _ hsigma hBall B hB (by
    intro v _hv
    exact Hcell n D eta zeta seed a h hzeta heta hzseed hseed hsmall original R level HB E1 hE1
      F Q m s t r power hQ ht hts hsm hlevel hr hrscale hwa hdelta hMiddle hret Hparent Hcost Hrelative
      p (E.filter (fun z => localAngle D (2^m) p (64/((2^t:ℕ):ℝ)) z.1=v))
      ((filter_subset _ _).trans hEE1)
      (fun z hz => hParent z (mem_filter.mp hz).1) cell v
      (fun z hz => hCell z (mem_filter.mp hz).1)
      (fun _ hz => (mem_filter.mp hz).2))
  have hPay := source_conditional_power_cost (kappa := extremalExponent) h.1.2.1 h.1.2.2.1 hr hpow hrscale heta0 hseed0
    hbudget.le hepsilon.le hLocal hrho hsigma hsigma1 hDelta hDeltaRho hrDelta F Q hF Hcost
  have hPay' := mul_le_mul_of_nonneg_left hPay (show 0≤ 27*conditionalConstant by
    norm_num [conditionalConstant])
  exact hUpper.trans (by simpa only [B,mul_assoc] using hPay')

end NativeSameSourceAngularBallUpper
