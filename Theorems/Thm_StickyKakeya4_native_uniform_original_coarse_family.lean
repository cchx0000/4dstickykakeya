import Theorems.Thm_StickyKakeya4_native_original_tube_family_caller
import Theorems.Thm_StickyKakeya4_native_original_pruning_loss
import Theorems.Thm_StickyKakeya4_native_original_nonempty_coarse_family
import Theorems.Thm_StickyKakeya4_original_profiled_coarse_shadings
import Theorems.Thm_StickyKakeya4_native_original_shading_width_cutoff
import Theorems.Thm_StickyKakeya4_original_densest_fiber_retention
import Theorems.Thm_StickyKakeya4_native_original_densest_scale_decay
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeUniformOriginalCoarseFamily
local instance : DecidableEq (ℤ×ℤ) := Classical.decEq _
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl OriginalDensestWideExtension
open OriginalAnnularGraphDeletion OriginalAnnularOffRootMass NativeAnnularParameterBudget
open NativeOriginalOffRootMass NativeOriginalRadialReduction OriginalRadialNearDiagonal
open NativeOriginalTubeFamilyCaller NativeRadialClassPruning OriginalUnitLineGrid
open OriginalWeightedLineColorSelection OriginalClippedUnitTube OriginalRepresentativeShading
open OriginalAdmissibleShadedFamily OriginalThickeningColorBudget OriginalArbitraryStripCapCharge
open OriginalProfiledCoarseShadings OriginalShadingCenterProfile OriginalShadingGridGeometry
open DyadicOriginalFiberSelection OriginalDensestFiberRetention

/-- Freeze one internal exponent before the external Frostman loss and
mesh. This gives the native original-source family with one delta cutoff
uniform over every allowed external eta, as required by the radial theorem's
quantifier order. The genuine small-s expansion is still separate. -/
theorem exists_uniform_original_nonempty_coarse_family (t sigma s zeta : ℝ)
    (ht : 0<t) (ht2 : t≤2) (hsigma : 0≤sigma) (hsigma1 : sigma≤1)
    (hsgap : sigma≤s) (ha : sigma<t) (hmargin : s-sigma<zeta) :
    ∀ etaUpper : ℝ, 0<etaUpper →
    ∃ etaI eta0 delta0 : ℝ,
      0<etaI ∧ etaI≤etaUpper ∧ etaI≤t/2 ∧ ((4+12/t)+1)*etaI≤zeta+sigma-s ∧
      4*((4+12/t)*etaI)/(t-sigma)≤(zeta+sigma-s)/4 ∧
      eta0=etaI/2 ∧ 0<eta0 ∧ 0<delta0 ∧ delta0≤1 ∧
      ∀ eta : ℝ, 0<eta → eta≤eta0 →
      ∀ delta : ℝ, 0<delta → delta≤delta0 →
    ∀ Pts : Finset Point, ∀ G : Finset Pair,
      G⊆Pts.product Pts →
      (∀ z∈Pts, |z.1|≤1 ∧ |z.2|≤1) →
      (∀ p∈Pts, ∀ q∈Pts, p≠q → delta≤euclideanDistance p q) →
      (∀ z∈G, ∃ R : ℝ, delta≤R ∧ R≤1 ∧
        delta^(-zeta)*R^s*Pts.card≤(physicalPairTube Pts R z).card) →
      (∀ q∈Pts, ∀ R : ℝ, delta≤R → R≤1 →
        ((Pts.filter (fun v => euclideanDistance q v≤R)).card : ℝ)≤delta^(-eta)*R^t*Pts.card) →
      (G.card : ℝ)≤delta^eta*(Pts.card : ℝ)^2 ∨
      ∃ n : ℕ, ∃ rho : ℝ, ∃ j : ℕ, ∃ G4 : Finset Pair,
        delta≤dyadicRadius n ∧ dyadicRadius n≤2*delta ∧
        rho∈scaleMenu n ∧ delta≤rho ∧ rho≤1 ∧ j<Nat.log 2 Pts.card+1 ∧
        G4⊆G ∧ G4.Nonempty ∧
        (G.card : ℝ)/2<(((n+1)*levelCount Pts:ℕ):ℝ)*G4.card ∧
        (G.card : ℝ)≤delta^etaI*(Pts.card : ℝ)^2+
          ((n+1)*(Nat.log 2 Pts.card+1):ℕ)*
            (G4.card+(delta^(2*etaI)+400*delta^(2*((4+12/t)*etaI)/(t-sigma)))*(Pts.card : ℝ)^2) ∧
        delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*(2^j:ℕ) ∧
        delta^(s-sigma-zeta)*rho^sigma≤2^sigma ∧
        rho≤delta^((zeta+sigma-s)/2) ∧ 3*rho≤1/448 ∧
        (∀ z∈G4, z.1≠z.2 ∧
          (delta^(2*((4+12/t)*etaI)/(t-sigma)))^2*(2^j:ℕ)≤
            ((G4.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
          (delta^(2*((4+12/t)*etaI)/(t-sigma)))^2*(2^j:ℕ)≤
            ((G4.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ)) ∧
        ∀ w h : ℝ, 3*rho≤w → w≤1/448 → rho≤h →
        let tau0 := delta^(2*((4+12/t)*etaI)/(t-sigma))
        let m : ℝ := (2^j:ℕ)
        let K := 8*shadingCoefficient n delta ((4+12/t)*etaI) tau0
        let b := min (t-sigma) 1
        let B := 2^(sigma+1)*6^sigma*m
        ∃ S : Finset Pair, ∃ j' k' : ℕ, S⊆G4 ∧ S.Nonempty ∧
          j'<levelCount Pts ∧ k'<levelCount Pts ∧
          (G4.card : ℝ)≤4*(thickeningModulus rho w:ℝ)^3*(levelCount Pts:ℝ)^2*B^2*S.card ∧
          Set.InjOn (lineCell rho) (↑S : Set Pair) ∧
          (∀ z∈S, ∀ u∈S, normalChart z=normalChart u) ∧
          (S.image (fun z => clippedTube z w)).card=S.card ∧
          (∀ z∈S, ∀ u∈S, z≠u → ∃ p∈clippedTube z w, 2*w< |scaledResidual u p|) ∧
          (∀ z∈S, tau0^2*m≤4*levelCount Pts*2^j'*2^k' ∧
            ∃ R : Finset Point,
              R⊆bin (originalShading Pts G4 rho z) (fun p => grid h (halfPoint p)) j' ∧
              R.Nonempty ∧ 2^k'≤9*R.card ∧ R.card<2^(k'+1) ∧
              (∀ p∈R, halfPoint p∈clippedTube z w) ∧
              (∀ p∈R, ∀ q∈R, p≠q →
                2*h<max |(halfPoint p).1-(halfPoint q).1| |(halfPoint p).2-(halfPoint q).2|) ∧
              (∀ (x : Point) (r : ℝ), h≤r →
                ((R.filter (fun p => InBox (halfPoint p) x r)).card : ℝ)≤
                  18*(levelCount Pts:ℝ)*(K*(2*r)^b)*R.card)) ∧
          (∀ R : Pair→Finset Point,
            (∀ z∈S, R z⊆bin (originalShading Pts G4 rho z) (fun p => grid h (halfPoint p)) j') →
            2^j'*(S.biUnion (fun z => (R z).image (fun p => grid h (halfPoint p)))).card≤Pts.card) ∧
          ∀ (W nx ny c : ℝ) (A : Set Point), rho≤W → W≤1/448 →
            nx^2+ny^2=1 → (∀ p∈A, |nx*p.1+ny*p.2-c|≤W) →
            ((containedInSet S w A).card : ℝ)≤
              539*(2^(sigma+1)*((432*W+16*rho)/rho)^sigma/tau0^2)^2 := by
  intro etaUpper hupper
  let a : ℝ := zeta+sigma-s
  let C : ℝ := 4+12/t
  have hap : 0<a := by dsimp [a]; linarith only [hmargin]
  have hCp : 0<C := by dsimp [C]; positivity
  have hden : 0<t-sigma := sub_pos.mpr ha
  let etaI : ℝ := min etaUpper (min (t/4) (min (a/(2*(C+1))) (a*(t-sigma)/(16*C))))
  have hIp : 0<etaI := by dsimp [etaI]; positivity
  have hIupper : etaI≤etaUpper := min_le_left _ _
  have hIt : etaI≤t/2 := ((min_le_right _ _).trans (min_le_left _ _)).trans (by linarith only [ht])
  have hIa : etaI≤a/(2*(C+1)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hIc : etaI≤a*(t-sigma)/(16*C) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hIeps : ((4+12/t)+1)*etaI≤zeta+sigma-s := by
    have hh := (le_div_iff₀ (by positivity : 0<2*(C+1))).mp hIa
    change (C+1)*etaI≤a
    nlinarith only [hh,mul_pos (by linarith only [hCp] : 0<C+1) hIp]
  have hcritical : 4*((4+12/t)*etaI)/(t-sigma)≤(zeta+sigma-s)/4 := by
    have hh := (le_div_iff₀ (by positivity : 0<16*C)).mp hIc
    apply (div_le_iff₀ hden).mpr
    change 4*(C*etaI)≤a/4*(t-sigma)
    nlinarith only [hh]
  obtain ⟨delta0,hd0,hd01,hfamily⟩ :=
    NativeOriginalNonemptyCoarseFamily.exists_native_original_nonempty_coarse_family_threshold
      t sigma s zeta etaI ht ht2 hsigma hsigma1 hsgap ha hmargin.le hIp hIt hIeps
  refine ⟨etaI,etaI/2,delta0,hIp,hIupper,hIt,hIeps,hcritical,rfl,by positivity,hd0,hd01,?_⟩
  intro eta _heta he delta hd hsmall Pts G hGP hbox hsep hviol hfrostman
  have hd1 := hsmall.trans hd01
  have heI : eta≤etaI := he.trans (by linarith only [hIp])
  have hpow : delta^(-eta)≤delta^(-etaI) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith only [heI])
  have hF : ∀ q∈Pts, ∀ R : ℝ, delta≤R → R≤1 →
      ((Pts.filter (fun v => euclideanDistance q v≤R)).card : ℝ)≤delta^(-etaI)*R^t*Pts.card := by
    intro q hq R hR hR1
    have hrp : 0≤R^t := Real.rpow_nonneg (hd.le.trans hR) _
    exact (hfrostman q hq R hR hR1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hrp) (Nat.cast_nonneg Pts.card))
  rcases hfamily delta hd hsmall Pts G hGP hbox hsep hviol hF with hsmallG|hlarge
  · left
    have htarget : delta^(etaI/2)≤delta^eta :=
      Real.rpow_le_rpow_of_exponent_ge hd hd1 he
    exact hsmallG.trans (mul_le_mul_of_nonneg_right htarget (sq_nonneg _))
  · exact Or.inr hlarge

end NativeUniformOriginalCoarseFamily
