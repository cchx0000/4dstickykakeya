import Theorems.Thm_StickyKakeya4_native_a2_critical_tube_family
import Theorems.Thm_StickyKakeya4_native_original_shading_slack
import Theorems.Thm_StickyKakeya4_native_original_compact_family_parameters
import Theorems.Thm_StickyKakeya4_original_clipped_tube_representation
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeOriginalLengthTwoA3Data
local instance : DecidableEq (ℤ×ℤ) := Classical.decEq _
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open FourUnitTubeBandCover NativeA2CriticalTubeFamily NativeOriginalShadingSlack
open OriginalUnitLineGrid OriginalClippedUnitTube OriginalRepresentativeShading
open OriginalArbitraryStripCapCharge OriginalShadingGridGeometry OriginalShadingCenterProfile
open OriginalPhysicalTubeScaleSelection DyadicOriginalFiberSelection OriginalCriticalWidthBound
open NativeOriginalCompactFamilyParameters OriginalCriticalCapParameterTransfer
open OriginalClippedTubeRepresentation

/-- Primitive original point and two-ends hypotheses construct an actual
finite family with all the displayed geometric and shading inputs of a
length-two native A.3 engine. The actual rectangles have longitudinal
coordinate in [-1,1] and transverse coordinate in [-3rho,3rho]. The
original point is mapped by halfPoint exactly once. The fixed target e,
internal eta and all cutoffs precede the source, mesh and effective
population exponent. No Furstenberg gain is assumed or asserted. -/
theorem exists_uniform_original_length_two_family
    (t sigma s zeta eps1 eps2 chi C0 e : ℝ)
    (ht : 0<t) (ht2 : t≤2) (hsigma : 0≤sigma) (hsigma1 : sigma≤1)
    (hsgap : sigma≤s) (ha : sigma<t) (hgap : s-sigma<zeta)
    (he1 : 0<eps1) (he1small : eps1<1/8) (he2 : 0<eps2)
    (hchi : 0<chi) (hchimax : chi≤t*eps1/12) (hC0 : 1≤C0)
    (hgeometric : 4*eps1<3*(zeta+sigma-s)/4) (he : 0<e) :
    ∃ etaI eta0 delta0 : ℝ, 0<etaI ∧
      etaI≤((zeta+sigma-s)/2)*e/(4*(4+12/t)*(1+4/(t-sigma))) ∧
      eta0=etaI/2 ∧ 0<eta0 ∧ 0<delta0 ∧ delta0≤1 ∧
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
            ∃ tbar : ℝ, ∃ Y : Pair→Finset Point,
              delta≤dyadicRadius n ∧ dyadicRadius n≤2*delta ∧
              delta≤rho ∧ rho≤delta^((zeta+sigma-s)/2) ∧
              G4⊆G ∧ S⊆G4 ∧ S.Nonempty ∧ (∀ z∈S, z.1≠z.2) ∧
              (G.card : ℝ)/2<(((n+1)*levelCount Pts:ℕ):ℝ)*G4.card ∧
              let tau0 := delta^(2*((4+12/t)*etaI)/(t-sigma))
              let m : ℝ := (2^j:ℕ)
              let b := min (t-sigma) 1
              let u := min (chi/2) (7*eps1/2)
              0<b ∧ b≤1 ∧ 0<3*rho ∧ 3*rho≤1/2 ∧
              (3*rho)^(-tbar)=(S.card : ℝ) ∧ chi≤tbar ∧ tbar≤2-7*eps1 ∧
              0<tbar ∧ tbar<2 ∧ 0<u ∧ u≤min tbar (2-tbar) ∧
              (G4.card : ℝ)≤4*(110:ℝ)^3*(levelCount Pts:ℝ)^2*
                (2^(sigma+1)*6^sigma*m)^2*S.card ∧
              Set.InjOn (lineCell rho) (↑S : Set Pair) ∧
              (S.image (fun z => clippedTube z (3*rho))).card=S.card ∧
              (∀ z∈S, ∀ u∈S, z≠u → ∃ p∈clippedTube z (3*rho),
                2*(3*rho)< |scaledResidual u p|) ∧
              (∀ z∈S, tau0^2*m≤4*levelCount Pts*2^j'*2^k' ∧
                Y z⊆bin (originalShading Pts G4 rho z)
                  (fun p => grid (3*rho) (halfPoint p)) j' ∧
                Y z⊆Pts ∧ (Y z).Nonempty ∧ 2^k'≤9*(Y z).card ∧ (Y z).card<2^(k'+1) ∧
                ((Y z).image halfPoint).card=(Y z).card ∧
                (((Y z).image halfPoint).image (grid (3*rho))).card=(Y z).card ∧
                (∀ p∈(Y z).image halfPoint, p∈clippedTube z (3*rho)) ∧
                (∀ p∈(Y z).image halfPoint, ∀ q∈(Y z).image halfPoint, p≠q →
                  2*(3*rho)<max |p.1-q.1| |p.2-q.2|) ∧
                (∀ (x : Point) (r : ℝ), 3*rho≤r →
                  ((((Y z).image halfPoint).filter (fun p => InBox p x r)).card : ℝ)≤
                    (3*rho)^(-e)*r^b*((Y z).image halfPoint).card)) ∧
              2^j'*(S.biUnion (fun z => ((Y z).image halfPoint).image (grid (3*rho)))).card≤Pts.card ∧
              criticalWidth rho S≤1/448 ∧
              432*criticalWidth rho S+16*rho≤C0*delta^(4*eps1) ∧
              (∀ (nx ny c : ℝ) (A : Set Point), nx^2+ny^2=1 →
                (∀ p∈A, |nx*p.1+ny*p.2-c|≤criticalWidth rho S) →
                ((containedInSet S (3*rho) A).card : ℝ)≤delta^chi*S.card) ∧
              (∀ (nx ny c : ℝ) (A : Set Point), nx^2+ny^2=1 →
                (∀ p∈A, |nx*p.1+ny*p.2-c|≤criticalWidth rho S) →
                ((containedInSet S (3*rho) A).card : ℝ)≤(3*rho)^u*S.card) := by
  let kappa := (zeta+sigma-s)/2
  have hkappa : 0<kappa := by dsimp [kappa]; linarith only [hgap]
  have ha' : 0<t-sigma := sub_pos.mpr ha
  let etaUpper := kappa*e/(4*(4+12/t)*(1+4/(t-sigma)))
  have hupper : 0<etaUpper := by dsimp [etaUpper]; positivity
  obtain ⟨etaI,eta0,dF,hI,hIU,heta0,heta0p,hdF,hdF1,_hmargin,hfamily⟩ :=
    exists_uniform_original_critical_tube_family t sigma s zeta eps1 eps2 chi C0
      ht ht2 hsigma hsigma1 hsgap ha hgap he1 he1small he2 hchi hchimax hC0 hgeometric
      etaUpper hupper
  obtain ⟨dB,hdB,_hdB1,hbudget⟩ := exists_original_coarse_shading_slack
    t (t-sigma) kappa e ht ha' hkappa he
  obtain ⟨dP,hdP,_hdP1,hparameters⟩ := exists_original_compact_family_parameter_cutoff
    eps1 kappa C0 chi he1 hkappa (by linarith only [hC0]) hchi
  refine ⟨etaI,eta0,min dF (min dB dP),hI,hIU,heta0,heta0p,
    lt_min hdF (lt_min hdB hdP),(min_le_left _ _).trans hdF1,?_⟩
  intro eta heta hetaSmall delta hd hsmall Pts hPts hbox hsep hfrostman htwoends
  have hsmallF := hsmall.trans (min_le_left _ _)
  have hsmallB := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallP := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd1 := hsmallF.trans hdF1
  obtain ⟨G0,hG0,hG0mass,hgood,hgraphs⟩ := hfamily eta heta hetaSmall delta hd hsmallF
    Pts hPts hbox hsep hfrostman htwoends
  refine ⟨G0,hG0,hG0mass,hgood,?_⟩
  intro G hGG0 hviol
  rcases hgraphs G hGG0 hviol with hsmallG|hlarge
  · exact Or.inl hsmallG
  · right
    obtain ⟨n,rho,j,G4,S,j',k',hmesh,hbottom,hdrho,hdecay,hG4,hS,hSn,hhalf,
      hmass,hinj,hsets,hphysical,hshading,hunion,hWsmall,hquery,hcap⟩ := hlarge
    have hrho : 0<rho := hd.trans_le hdrho
    have hdistinct : ∀ z∈S, z.1≠z.2 := fun z hz => (hgood z (hGG0 (hG4 (hS hz)))).1
    obtain ⟨tbar,hr,hrhalf,hcard,htlo,hthi,htbar,htbar2,hu,huBound⟩ :=
      hparameters delta hd hsmallP rho S hdrho hdecay hSn hdistinct hquery hcap
    have hcoeff := hbudget etaI hI.le hIU delta hd hsmallB n hmesh hbottom Pts hbox hsep
      rho hdrho hdecay (min (t-sigma) 1) (min_le_right _ _)
    let tau0 := delta^(2*((4+12/t)*etaI)/(t-sigma))
    let m : ℝ := (2^j:ℕ)
    let b := min (t-sigma) 1
    have hchoose : ∀ z : Pair, ∃ R : Finset Point, z∈S →
        tau0^2*m≤4*levelCount Pts*2^j'*2^k' ∧
        R⊆bin (originalShading Pts G4 rho z) (fun p => grid (3*rho) (halfPoint p)) j' ∧
        R.Nonempty ∧ 2^k'≤9*R.card ∧ R.card<2^(k'+1) ∧
        (∀ p∈R, halfPoint p∈clippedTube z (3*rho)) ∧
        (∀ p∈R, ∀ q∈R, p≠q →
          2*(3*rho)<max |(halfPoint p).1-(halfPoint q).1| |(halfPoint p).2-(halfPoint q).2|) ∧
        (∀ (x : Point) (r : ℝ), 3*rho≤r →
          ((R.filter (fun p => InBox (halfPoint p) x r)).card : ℝ)≤
            (3*rho)^(-e)*r^b*R.card) := by
      intro z
      by_cases hz : z∈S
      · obtain ⟨hm,R,hRbin,hRn,hRlo,hRhi,hRphy,hRsep,hRF⟩ := hshading z hz
        refine ⟨R,fun _ => ⟨hm,hRbin,hRn,hRlo,hRhi,hRphy,hRsep,?_⟩⟩
        exact original_coarse_profile_with_slack Pts R n delta ((4+12/t)*etaI) (t-sigma)
          b rho e hcoeff hrho hRF
      · exact ⟨∅,fun hz' => (hz hz').elim⟩
    choose Y hY using hchoose
    have hYbin : ∀ z∈S, Y z⊆bin (originalShading Pts G4 rho z)
        (fun p => grid (3*rho) (halfPoint p)) j' := fun z hz => (hY z hz).2.1
    have hunionY := hunion Y hYbin
    have hcoarsecap := original_critical_cap_coarse_exponent S rho delta chi
      (min (chi/2) (7*eps1/2)) hd hd1 hdrho hu.le
      ((min_le_left _ _).trans (by linarith only [hchi])) hcap
    refine ⟨n,rho,j,G4,S,j',k',tbar,Y,hmesh,hbottom,hdrho,hdecay,hG4,hS,hSn,hdistinct,hhalf,
      lt_min ha' zero_lt_one,min_le_right _ _,hr,hrhalf,hcard,htlo,hthi,htbar,htbar2,hu,huBound,
      hmass,hinj,hsets,hphysical,?_,?_,hWsmall,hquery,hcap,hcoarsecap⟩
    · intro z hz
      obtain ⟨hm,hRbin,hRn,hRlo,hRhi,hRphy,hRsep,hRF⟩ := hY z hz
      have hYP : Y z⊆Pts := by
        intro p hp
        exact (Finset.mem_filter.mp ((Finset.mem_filter.mp (hRbin hp)).1)).1
      have hgridinj : Set.InjOn (fun p => grid (3*rho) (halfPoint p)) (↑(Y z)) := by
        intro p hp q hq heq
        by_contra hpq
        have hfar := hRsep p hp q hq hpq
        have hpbox := point_in_own_cell hr (halfPoint p)
        have hqbox := point_in_own_cell hr (halfPoint q)
        change grid (3*rho) (halfPoint p)=grid (3*rho) (halfPoint q) at heq
        rw [← heq] at hqbox
        have hx : |(halfPoint p).1-(halfPoint q).1|≤3*rho+3*rho :=
          (abs_sub_le _ (corner (3*rho) (grid (3*rho) (halfPoint p))).1 _).trans
            (add_le_add hpbox.1 (by simpa only [abs_sub_comm] using hqbox.1))
        have hy : |(halfPoint p).2-(halfPoint q).2|≤3*rho+3*rho :=
          (abs_sub_le _ (corner (3*rho) (grid (3*rho) (halfPoint p))).2 _).trans
            (add_le_add hpbox.2 (by simpa only [abs_sub_comm] using hqbox.2))
        have hmax := max_le hx hy
        linarith only [hfar,hmax]
      refine ⟨hm,hRbin,hYP,hRn,hRlo,hRhi,original_half_shading_card (Y z),?_,?_,?_,?_⟩
      · simpa only [Finset.image_image,Function.comp_def] using Finset.card_image_of_injOn hgridinj
      · intro p hp
        obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
        exact hRphy q hq
      · intro p hp q hq hpq
        obtain ⟨p',hp',rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨q',hq',rfl⟩ := Finset.mem_image.mp hq
        exact hRsep p' hp' q' hq' (fun h => hpq (congrArg halfPoint h))
      · intro x r hr'
        rw [Finset.filter_image,original_half_shading_card,original_half_shading_card]
        exact hRF x r hr'
    · simpa only [Finset.image_image,Function.comp_def] using hunionY

end NativeOriginalLengthTwoA3Data
