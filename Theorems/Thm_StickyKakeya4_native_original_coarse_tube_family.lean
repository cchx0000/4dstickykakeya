import Theorems.Thm_StickyKakeya4_native_original_tube_family_caller
import Theorems.Thm_StickyKakeya4_original_profiled_coarse_shadings
import Theorems.Thm_StickyKakeya4_native_original_shading_width_cutoff
import Theorems.Thm_StickyKakeya4_original_densest_fiber_retention
import Theorems.Thm_StickyKakeya4_native_original_densest_scale_decay
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeOriginalCoarseTubeFamily
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

/-- A single original-input caller constructs the actual coarse physical
shadings and their pair-mass, occupancy, separation, Frostman, cap and union
bounds. All intermediate angular and annular inputs are derived internally.
The remaining positive Furstenberg gain is not assumed or concluded. -/
theorem exists_native_original_coarse_family_threshold (t sigma s zeta eta : ℝ)
    (ht : 0<t) (ht2 : t≤2) (hsigma : 0≤sigma) (hsigma1 : sigma≤1)
    (hsgap : sigma≤s) (ha : sigma<t) (hgap : s-sigma≤zeta)
    (heta : 0<eta) (hetat : eta≤t/2)
    (heps : ((4+12/t)+1)*eta≤zeta+sigma-s) :
    ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧
    ∀ delta : ℝ, 0<delta → delta≤delta0 →
    ∀ Pts : Finset Point, ∀ G : Finset Pair,
      G⊆Pts.product Pts →
      (∀ z∈Pts, |z.1|≤1 ∧ |z.2|≤1) →
      (∀ z∈G, ∃ R : ℝ, delta≤R ∧ R≤1 ∧
        delta^(-zeta)*R^s*Pts.card≤(physicalPairTube Pts R z).card) →
      (∀ q∈Pts, ∀ R : ℝ, delta≤R → R≤1 →
        ((Pts.filter (fun v => euclideanDistance q v≤R)).card : ℝ)≤delta^(-eta)*R^t*Pts.card) →
      (G.card : ℝ)≤delta^eta*(Pts.card : ℝ)^2 ∨
      ∃ n : ℕ, ∃ rho : ℝ, ∃ j : ℕ, ∃ G4 : Finset Pair,
        delta≤dyadicRadius n ∧ dyadicRadius n≤2*delta ∧
        rho∈scaleMenu n ∧ delta≤rho ∧ rho≤1 ∧ j<Nat.log 2 Pts.card+1 ∧
        G4⊆G ∧
        (G.card : ℝ)≤delta^eta*(Pts.card : ℝ)^2+
          ((n+1)*(Nat.log 2 Pts.card+1):ℕ)*
            (G4.card+(delta^(2*eta)+400*delta^(2*((4+12/t)*eta)/(t-sigma)))*(Pts.card : ℝ)^2) ∧
        delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*(2^j:ℕ) ∧
        delta^(s-sigma-zeta)*rho^sigma≤2^sigma ∧
        rho≤delta^((zeta+sigma-s)/2) ∧ 3*rho≤1/448 ∧
        (∀ z∈G4, z.1≠z.2 ∧
          (delta^(2*((4+12/t)*eta)/(t-sigma)))^2*(2^j:ℕ)≤
            ((G4.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
          (delta^(2*((4+12/t)*eta)/(t-sigma)))^2*(2^j:ℕ)≤
            ((G4.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ)) ∧
        ∀ w h : ℝ, 3*rho≤w → w≤1/448 → rho≤h → G4.Nonempty →
        let tau0 := delta^(2*((4+12/t)*eta)/(t-sigma))
        let m : ℝ := (2^j:ℕ)
        let K := 8*shadingCoefficient n delta ((4+12/t)*eta) tau0
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
  obtain ⟨delta1,hd1,hd11,hfamily⟩ := exists_native_original_tube_family_threshold
    t sigma s zeta eta ht ht2 hsigma hsigma1 hsgap ha hgap heta hetat heps
  obtain ⟨delta2,hd2,_hd21,hwidthcut⟩ :=
    NativeOriginalShadingWidthCutoff.exists_native_shading_width_cutoff t eta ht heta
  have hmargin : 0<zeta+sigma-s := by
    have hp : 0<((4+12/t)+1)*eta := by positivity
    exact hp.trans_le heps
  obtain ⟨delta3,hd3,_hd31,hscalecut⟩ :=
    NativeOriginalDensestScaleDecay.exists_original_densest_scale_cutoff _ hmargin
  refine ⟨min (min delta1 delta2) delta3,lt_min (lt_min hd1 hd2) hd3,
    (min_le_left _ _).trans ((min_le_left _ _).trans hd11),?_⟩
  intro delta hd hsmall Pts G hGP hbox hviol hfrostman
  have hsmall12 := hsmall.trans (min_le_left (min delta1 delta2) delta3)
  have hsmall1 := hsmall12.trans (min_le_left delta1 delta2)
  have hsmall2 := hsmall12.trans (min_le_right delta1 delta2)
  have hsmall3 := hsmall.trans (min_le_right (min delta1 delta2) delta3)
  have hdle1 := hsmall1.trans hd11
  rcases hfamily delta hd hsmall1 Pts G hGP hbox hviol hfrostman with hsmallG|hlarge
  · exact Or.inl hsmallG
  · right
    obtain ⟨n,rho,j,G4,hmesh,hbottom,hrhomenu,hdrho,hrho1,hj,hG4,hretain,hgain,hscale,hdata,hphysical⟩ := hlarge
    have hscale' : delta^(-(zeta+sigma-s))*rho^sigma≤(2:ℝ)^sigma := by
      simpa only [show s-sigma-zeta= -(zeta+sigma-s) by ring] using hscale
    obtain ⟨hsmallrho,hwidthrange⟩ := hscalecut delta rho sigma hd hsmall3
      (hd.trans_le hdrho) hrho1 hsigma1 hscale'
    have hclasses : ∀ z∈G4, z.1≠z.2 ∧
        (delta^(2*((4+12/t)*eta)/(t-sigma)))^2*(2^j:ℕ)≤
          ((G4.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
        (delta^(2*((4+12/t)*eta)/(t-sigma)))^2*(2^j:ℕ)≤
          ((G4.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ) := by
      intro z hz
      obtain ⟨hsep,_hlo,_hhi,_hwide,_hann,_hoff,hf,hr⟩ := hdata z hz
      refine ⟨?_,hf,hr⟩
      intro he
      have he0 : euclideanDistance z.1 z.2=0 := by rw [he]; simp [euclideanDistance]
      rw [he0] at hsep
      exact (not_le_of_gt (Real.rpow_pos_of_pos hd _)) hsep
    refine ⟨n,rho,j,G4,hmesh,hbottom,hrhomenu,hdrho,hrho1,hj,hG4,hretain,hgain,hscale,
      hsmallrho,hwidthrange,hclasses,?_⟩
    intro w h hwidth hwsmall hmeshcoarse hG4n
    let tau0 : ℝ := delta^(2*((4+12/t)*eta)/(t-sigma))
    let m : ℝ := (2^j:ℕ)
    have hm : 0<m := by dsimp [m]; positivity
    have hrho : 0<rho := hd.trans_le hdrho
    have htau : 0<tau0 := Real.rpow_pos_of_pos hd _
    have hexp : 0<2*((4+12/t)*eta)/(t-sigma) := div_pos (by positivity) (sub_pos.mpr ha)
    have htau1 : tau0≤1 := Real.rpow_le_one hd.le hdle1 hexp.le
    have hne : ∀ z∈G4, z.1≠z.2 := by
      intro z hz he
      have hh := (hdata z hz).1
      have he0 : euclideanDistance z.1 z.2=0 := by rw [he]; simp [euclideanDistance]
      rw [he0] at hh
      exact (not_le_of_gt (Real.rpow_pos_of_pos hd _)) hh
    obtain ⟨T,hT,hfiber,hweight,_hM,hinj,hchart,hsets,hsep,_hshading,hcap⟩ := hphysical w hwidth
    have hTn : T.Nonempty := by
      by_contra hnot
      have hTe := Finset.not_nonempty_iff_eq_empty.mp hnot
      have hzero : (originalCellGraph G4 T rho).card=0 := by
        simp [originalCellGraph,hTe]
      rw [hzero,mul_zero] at hweight
      have hpos := Finset.card_pos.mpr hG4n
      omega
    have hwide : ∀ z∈G4, ∀ R : ℝ, rho≤R → R≤1 →
        ((physicalPairTube Pts R z).card : ℝ)≤2^(sigma+1)*(R/rho)^sigma*m := by
      intro z hz
      exact (hdata z hz).2.2.2.1
    have hann := fun z hz => (hdata z hz).2.2.2.2.1
    have hreverse := fun z hz => (hdata z hz).2.2.2.2.2.2.2
    have hwidthAnn : 24*rho≤(delta^(2*eta/t))^(-3:ℝ)*rho :=
      mul_le_mul_of_nonneg_right (hwidthcut delta hd hsmall2) hrho.le
    have heta' : 0≤(4+12/t)*eta := by positivity
    have heps' : -((4+12/t)*eta)≤zeta+sigma-s-eta := by nlinarith only [heps,heta']
    obtain ⟨j',k',S,hST,hSn,hj',hk',hcount,hcoarsedata,hunion⟩ :=
      exists_original_profiled_coarse_shadings Pts G4 T n delta eta ((4+12/t)*eta)
        t sigma s zeta rho m ((delta^(2*eta/t))^(-3:ℝ)*rho) tau0 h w
        hd hdle1 (by positivity) ha.le hsigma1 hm hrhomenu hdrho htau htau1
        hwidthAnn heps' hmeshcoarse hwidth hTn hT (hG4.trans hGP) hbox hne hgain
        hfrostman hann hreverse
    have hpop : ∀ z∈T, ((physicalPairTube Pts (6*rho) z).card : ℝ)≤
        2^(sigma+1)*6^sigma*m := by
      intro z hz
      have hq : 6*rho/rho=6 := by field_simp
      have hh := hwide z (hT hz) (6*rho) (by linarith only [hrho])
        (by linarith only [hwidth,hwsmall])
      simpa only [hq] using hh
    have hmass := original_pair_mass_after_coarse_selection Pts G4 T S rho
      (2^(sigma+1)*6^sigma*m) (thickeningModulus rho w) (levelCount Pts)
      hrho hT hinj (hG4.trans hGP) hbox hne hpop hweight hcount
    have hSinj : Set.InjOn (lineCell rho) (↑S : Set Pair) :=
      fun _ hz _ hu heq => hinj (hST hz) (hST hu) heq
    have hphysicalInj : Set.InjOn (fun z => clippedTube z w) (↑S : Set Pair) := by
      intro z hz u hu heq
      by_contra hneq
      obtain ⟨p,hp,hfar⟩ := hsep z (hST hz) u (hST hu) hneq
      change clippedTube z w=clippedTube u w at heq
      rw [heq] at hp
      linarith only [hp.1,hfar,hrho,hwidth]
    refine ⟨S,j',k',hST.trans hT,hSn,hj',hk',hmass,hSinj,(fun z hz u hu => hchart z (hST hz) u (hST hu)),
      Finset.card_image_iff.mpr hphysicalInj,
      (fun z hz u hu => hsep z (hST hz) u (hST hu)),hcoarsedata,hunion,?_⟩
    intro W nx ny c A hWlo hWhi hunit hA
    have hsub : containedInSet S w A⊆containedInSet T w A := by
      intro z hz
      obtain ⟨hz,hcontain⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hST hz,hcontain⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (hcap W nx ny c A hWlo hWhi hunit hA)

end NativeOriginalCoarseTubeFamily
