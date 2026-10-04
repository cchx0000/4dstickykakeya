import Theorems.Thm_StickyKakeya4_native_uniform_original_coarse_family
import Theorems.Thm_StickyKakeya4_native_original_critical_query_range
import Theorems.Thm_StickyKakeya4_native_original_cap_fraction_budget
import Theorems.Thm_StickyKakeya4_native_a1_initial_radial_graph

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeA2CriticalTubeFamily
local instance : DecidableEq (ℤ×ℤ) := Classical.decEq _
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open FourUnitTubeBandCover NativeA1InitialRadialGraph NativeUniformOriginalCoarseFamily
open NativeRadialClassPruning OriginalUnitLineGrid OriginalClippedUnitTube OriginalRepresentativeShading
open OriginalArbitraryStripCapCharge OriginalShadingGridGeometry OriginalShadingCenterProfile
open OriginalPhysicalTubeScaleSelection DyadicOriginalFiberSelection OriginalGoodGraphCapFraction
open OriginalCriticalWidthBound NativeOriginalCriticalQueryRange NativeOriginalCapFractionBudget

/-- Original point and two-ends data construct the actual A.2 good graph.
Every sufficiently large original violation graph inside it yields actual
coarse physical shadings with a derived small critical-tube fraction.
The internal eta is fixed before the external eta and original mesh.
No A.3 expansion or critical cap certificate is supplied. -/
theorem exists_uniform_original_critical_tube_family
    (t sigma s zeta eps1 eps2 chi C0 : ℝ)
    (ht : 0<t) (ht2 : t≤2) (hsigma : 0≤sigma) (hsigma1 : sigma≤1)
    (hsgap : sigma≤s) (ha : sigma<t) (hgap : s-sigma<zeta)
    (he1 : 0<eps1) (he1small : eps1<1/8) (he2 : 0<eps2)
    (hchi : 0<chi) (hchimax : chi≤t*eps1/12) (hC0 : 1≤C0)
    (hgeometric : 4*eps1<3*(zeta+sigma-s)/4) :
    ∀ etaUpper : ℝ, 0<etaUpper →
    ∃ etaI eta0 delta0 : ℝ, 0<etaI ∧ etaI≤etaUpper ∧ eta0=etaI/2 ∧ 0<eta0 ∧ 0<delta0 ∧ delta0≤1 ∧
      etaI/2+8*((4+12/t)*etaI)/(t-sigma)<chi ∧
      ∀ eta : ℝ, 0<eta → eta≤eta0 →
      ∀ delta : ℝ, 0<delta → delta≤delta0 →
      ∀ Pts : Finset Point, Pts.Nonempty →
        (∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1) →
        (∀ p∈Pts, ∀ q∈Pts, p≠q → delta≤euclideanDistance p q) →
        (∀ p∈Pts, ∀ R : ℝ, delta≤R → R≤1 →
          ((Pts.filter (fun q => euclideanDistance p q≤R)).card : ℝ)≤delta^(-eta)*R^t*Pts.card) →
        (∀ nx ny c h : ℝ, nx^2+ny^2=1 →
          ((unitTube Pts nx ny c h (delta^eps1)).card : ℝ)≤delta^eps2*Pts.card) →
        ∃ G0 : Finset Pair, G0⊆Pts.product Pts ∧
          (1-delta^(min (t*eps1/2) (eps2/2)))*(Pts.card : ℝ)^2≤G0.card ∧
          (∀ z∈G0, z.1≠z.2 ∧
            ((physicalPairTube Pts (C0*delta^(4*eps1)) z).card : ℝ)<delta^chi*Pts.card) ∧
          ∀ G : Finset Pair, G⊆G0 →
            (∀ z∈G, ∃ R : ℝ, delta≤R ∧ R≤1 ∧
              delta^(-zeta)*R^s*Pts.card≤(physicalPairTube Pts R z).card) →
            (G.card : ℝ)≤delta^eta*(Pts.card : ℝ)^2 ∨
            ∃ n : ℕ, ∃ rho : ℝ, ∃ j : ℕ, ∃ G4 S : Finset Pair, ∃ j' k' : ℕ,
              delta≤dyadicRadius n ∧ dyadicRadius n≤2*delta ∧
              delta≤rho ∧ rho≤delta^((zeta+sigma-s)/2) ∧
              G4⊆G ∧ S⊆G4 ∧ S.Nonempty ∧
              (G.card : ℝ)/2<(((n+1)*levelCount Pts:ℕ):ℝ)*G4.card ∧
              let tau0 := delta^(2*((4+12/t)*etaI)/(t-sigma))
              let m : ℝ := (2^j:ℕ)
              let K := 8*shadingCoefficient n delta ((4+12/t)*etaI) tau0
              let b := min (t-sigma) 1
              (G4.card : ℝ)≤4*(110:ℝ)^3*(levelCount Pts:ℝ)^2*
                (2^(sigma+1)*6^sigma*m)^2*S.card ∧
              Set.InjOn (lineCell rho) (↑S : Set Pair) ∧
              (S.image (fun z => clippedTube z (3*rho))).card=S.card ∧
              (∀ z∈S, ∀ u∈S, z≠u → ∃ p∈clippedTube z (3*rho),
                2*(3*rho)< |scaledResidual u p|) ∧
              (∀ z∈S, tau0^2*m≤4*levelCount Pts*2^j'*2^k' ∧
                ∃ R : Finset Point,
                  R⊆bin (originalShading Pts G4 rho z) (fun p => grid (3*rho) (halfPoint p)) j' ∧
                  R.Nonempty ∧ 2^k'≤9*R.card ∧ R.card<2^(k'+1) ∧
                  (∀ p∈R, halfPoint p∈clippedTube z (3*rho)) ∧
                  (∀ p∈R, ∀ q∈R, p≠q →
                    2*(3*rho)<max |(halfPoint p).1-(halfPoint q).1| |(halfPoint p).2-(halfPoint q).2|) ∧
                  (∀ (x : Point) (r : ℝ), 3*rho≤r →
                    ((R.filter (fun p => InBox (halfPoint p) x r)).card : ℝ)≤
                      18*(levelCount Pts:ℝ)*(K*(2*r)^b)*R.card)) ∧
              (∀ R : Pair→Finset Point,
                (∀ z∈S, R z⊆bin (originalShading Pts G4 rho z)
                  (fun p => grid (3*rho) (halfPoint p)) j') →
                2^j'*(S.biUnion (fun z => (R z).image (fun p => grid (3*rho) (halfPoint p)))).card≤Pts.card) ∧
              criticalWidth rho S≤1/448 ∧
              432*criticalWidth rho S+16*rho≤C0*delta^(4*eps1) ∧
              ∀ (nx ny c : ℝ) (A : Set Point), nx^2+ny^2=1 →
                (∀ p∈A, |nx*p.1+ny*p.2-c|≤criticalWidth rho S) →
                ((containedInSet S (3*rho) A).card : ℝ)≤delta^chi*S.card := by
  intro etaUpper hEtaUpper
  let D := 1+16*(4+12/t)/(t-sigma)
  have hD1 : 1≤D := by
    have hden : 0<t-sigma := sub_pos.mpr ha
    have hterm : 0≤16*(4+12/t)/(t-sigma) := by positivity
    dsimp [D]
    linarith only [hterm]
  have hD : 0<D := lt_of_lt_of_le zero_lt_one hD1
  have hU : 0<min (chi/D) etaUpper := lt_min (div_pos hchi hD) hEtaUpper
  obtain ⟨etaI,eta0,dF,hI,hIUpper,_hIt,_hIgain,hIquery,heta0,heta0p,hdF,hdF1,hfamily⟩ :=
    exists_uniform_original_nonempty_coarse_family t sigma s zeta
      ht ht2 hsigma hsigma1 hsgap ha hgap (min (chi/D) etaUpper) hU
  have hIextra : etaI≤etaUpper := hIUpper.trans (min_le_right _ _)
  have hIbudget : etaI*D≤chi := (le_div_iff₀ hD).mp (hIUpper.trans (min_le_left _ _))
  have hIchi : etaI≤chi := by
    have hh := mul_le_mul_of_nonneg_left hD1 hI.le
    linarith only [hh,hIbudget]
  have hcapmargin : etaI/2+8*((4+12/t)*etaI)/(t-sigma)<chi := by
    have he : etaI*D=2*(etaI/2+8*((4+12/t)*etaI)/(t-sigma)) := by dsimp [D]; ring
    rw [he] at hIbudget
    linarith only [hIbudget,hchi]
  have hquerymargin : 4*eps1<(zeta+sigma-s)-4*((4+12/t)*etaI)/(t-sigma) := by
    linarith only [hIquery,hgeometric]
  obtain ⟨dA,hdA,hA2⟩ := exists_original_eta_dilated_radial_threshold
    t eps1 eps2 C0 ht ht2 he1 he1small he2 hC0
  obtain ⟨dQ,hdQ,_hdQ1,hquery⟩ := exists_original_critical_query_threshold
    (zeta+sigma-s) ((4+12/t)*etaI) (t-sigma) eps1 C0 (sub_pos.mpr ha) he1
    (lt_of_lt_of_le zero_lt_one hC0) hquerymargin
  obtain ⟨dB,hdB,_hdB1,hbudget⟩ := exists_native_original_cap_fraction_budget
    sigma etaI ((4+12/t)*etaI) (t-sigma) chi hsigma1 hcapmargin
  refine ⟨etaI,eta0,min (min dA dF) (min dQ dB),hI,hIextra,heta0,heta0p,
    lt_min (lt_min hdA hdF) (lt_min hdQ hdB),
    (min_le_left _ _).trans ((min_le_right _ _).trans hdF1),hcapmargin,?_⟩
  intro eta heta hetaSmall delta hd hsmall Pts hPts hbox hsep hfrostman htwoends
  have hsmallA := hsmall.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hsmallF := hsmall.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsmallQ := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallB := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd1 := hsmallF.trans hdF1
  have hetaI : eta≤etaI/2 := by simpa only [heta0] using hetaSmall
  have hetachi : eta≤chi := by linarith only [hetaI,hI,hIchi]
  obtain ⟨G0,hG0,hgood,hG0mass⟩ := hA2 delta chi eta hd hsmallA hetachi hchi hchimax
    Pts hPts hbox hfrostman htwoends
  refine ⟨G0,hG0,hG0mass,hgood,?_⟩
  intro G hGG0 hviol
  by_cases hsmallG : (G.card : ℝ)≤delta^eta*(Pts.card : ℝ)^2
  · exact Or.inl hsmallG
  · rcases hfamily eta heta hetaSmall delta hd hsmallF Pts G (hGG0.trans hG0)
      hbox hsep hviol hfrostman with hsmallOld|hlarge
    · exact (hsmallG hsmallOld).elim
    · right
      obtain ⟨n,rho,j,G4,hmesh,hbottom,_hrhomenu,hdrho,hrho1,_hj,hG4,_hG4n,hhalf,
        _hretain,hgain,_hscale,hdecay,hwidth,hgraph,hcoarse⟩ := hlarge
      have hrho : 0<rho := hd.trans_le hdrho
      let tau := delta^(2*((4+12/t)*etaI)/(t-sigma))
      let m : ℝ := (2^j:ℕ)
      have htau : 0<tau := Real.rpow_pos_of_pos hd _
      have hm : 0 < m := by dsimp [m]; positivity
      obtain ⟨S,j',k',hS,hSn,_hj',_hk',hmass,hinj,hchart,hsets,hphysical,hshading,hunion,_hdensecap⟩ :=
        hcoarse (3*rho) (3*rho) le_rfl hwidth (by linarith only [hrho])
      rw [minimal_thickening_modulus rho hrho] at hmass
      have hrich := fun z hz => (hgraph z hz).2
      have hgain' : delta^(-(zeta+sigma-s))*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m := by
        simpa only [show -(zeta+sigma-s)=s-sigma-zeta by ring] using hgain
      obtain ⟨hWsmall,_hRlow,_hRhigh,hRQ⟩ := hquery delta hd hsmallQ Pts G4 S rho sigma m
        hrho hrho1 hsigma1 hm hSn hS hinj (hG4.trans (hGG0.trans hG0)) hbox
        (fun z hz => (hgraph z hz).1) hrich hgain'
      refine ⟨n,rho,j,G4,S,j',k',hmesh,hbottom,hdrho,hdecay,hG4,hS,hSn,hhalf,hmass,hinj,hsets,
        hphysical,hshading,hunion,hWsmall,hRQ,?_⟩
      intro nx ny c A hunit hA
      have hpow := Real.rpow_le_rpow_of_exponent_ge hd hd1 hetaI
      have hdense : delta^(etaI/2)*(Pts.card : ℝ)^2≤G.card :=
        (mul_le_mul_of_nonneg_right hpow (sq_nonneg _)).trans (le_of_not_ge hsmallG)
      have hfinite := original_good_graph_cap_fraction Pts G0 G G4 S rho (3*rho)
        (criticalWidth rho S) (C0*delta^(4*eps1)) tau m (delta^chi) nx ny c
        (delta^(etaI/2)) (((n+1)*levelCount Pts:ℕ):ℝ) 110 (levelCount Pts)
        (2^(sigma+1)*6^sigma) A hrho (by positivity) (by linarith only [hWsmall])
        htau hm (by positivity) (by positivity) (by positivity) hRQ hS hG4 hGG0 hG0 hinj hchart hbox
        (fun z hz => ⟨(hgood z hz).1,(hgood z hz).2.le⟩) hrich hdense hhalf.le hmass hunit hA
      have hcoefficient := hbudget delta hd hsmallB n hmesh hbottom Pts hbox hsep
      exact hfinite.trans (mul_le_mul_of_nonneg_right hcoefficient (Nat.cast_nonneg S.card))

end NativeA2CriticalTubeFamily
