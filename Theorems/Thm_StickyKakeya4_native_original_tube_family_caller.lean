import Theorems.Thm_StickyKakeya4_native_original_step3_caller
import Theorems.Thm_StickyKakeya4_original_dense_family_cap
import Theorems.Thm_StickyKakeya4_original_thickening_color_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeOriginalTubeFamilyCaller
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl OriginalDensestWideExtension
open OriginalAnnularGraphDeletion OriginalAnnularOffRootMass NativeAnnularParameterBudget
open NativeOriginalOffRootMass NativeOriginalRadialReduction OriginalRadialNearDiagonal
open NativeOriginalStep3Caller NativeRadialClassPruning OriginalUnitLineGrid
open OriginalWeightedLineColorSelection OriginalClippedUnitTube OriginalRepresentativeShading
open OriginalAdmissibleShadedFamily OriginalThickeningColorBudget OriginalArbitraryStripCapCharge
open OriginalDenseFamilyCap

/-- Actual original Frostman and violation data construct the physical
shaded family, with explicit original pair retention, essential separation,
and an external-strip cap derived from the original dense wide-tube profile.
No angular class counts, tube overlaps, or radial cap are assumed as output certificates. -/
theorem exists_native_original_tube_family_threshold (t sigma s zeta eta : ℝ)
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
        (∀ z∈G4,
          delta^(2*eta/t)≤euclideanDistance z.1 z.2 ∧
          2^j≤(physicalPairTube Pts rho z).card ∧
          (physicalPairTube Pts rho z).card<2^(j+1) ∧
          (∀ R : ℝ, rho≤R → R≤1 → ((physicalPairTube Pts R z).card : ℝ)≤
            2^(sigma+1)*(R/rho)^sigma*(2^j:ℕ)) ∧
          (∀ tau∈annularScales n rho (delta^(2*((4+12/t)*eta)/(t-sigma))),
            ((OriginalAnnularRowCover.annularSupport Pts z.1 z.2
              ((delta^(2*eta/t))^(-3:ℝ)*rho) tau).card : ℝ)<
                delta^(-((4+12/t)*eta))*tau^(t-sigma)*(2^j:ℕ) ∧
            ((OriginalAnnularRowCover.annularSupport Pts z.2 z.1
              ((delta^(2*eta/t))^(-3:ℝ)*rho) tau).card : ℝ)<
                delta^(-((4+12/t)*eta))*tau^(t-sigma)*(2^j:ℕ)) ∧
          ((2^j:ℕ):ℝ)/2≤(offRootSupport Pts z rho
            (delta^(2*((4+12/t)*eta)/(t-sigma)))).card ∧
          (delta^(2*((4+12/t)*eta)/(t-sigma)))^2*(2^j:ℕ)≤
            ((G4.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
          (delta^(2*((4+12/t)*eta)/(t-sigma)))^2*(2^j:ℕ)≤
            ((G4.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ)) ∧
        ∀ w : ℝ, 3*rho≤w → ∃ S : Finset Pair,
          S⊆G4 ∧ originalCellGraph G4 S rho⊆G4 ∧
          G4.card≤4*(thickeningModulus rho w)^3*(originalCellGraph G4 S rho).card ∧
          (thickeningModulus rho w:ℝ)≤37*w/rho ∧
          Set.InjOn (lineCell rho) (↑S : Set Pair) ∧
          (∀ z∈S, ∀ u∈S, normalChart z=normalChart u) ∧
          (S.image (fun z => clippedTube z w)).card=S.card ∧
          (∀ z∈S, ∀ u∈S, z≠u → ∃ p∈clippedTube z w, 2*w< |scaledResidual u p|) ∧
          (∀ z∈S,
            (delta^(2*((4+12/t)*eta)/(t-sigma)))^2*(2^j:ℕ)≤
              (((originalShading Pts G4 rho z).image halfPoint).card : ℝ) ∧
            ↑((originalShading Pts G4 rho z).image halfPoint)⊆clippedTube z w) ∧
          ∀ (W nx ny c : ℝ) (A : Set Point), rho≤W → W≤1/448 →
            nx^2+ny^2=1 → (∀ p∈A, |nx*p.1+ny*p.2-c|≤W) →
            ((containedInSet S w A).card : ℝ)≤539*
              (2^(sigma+1)*((432*W+16*rho)/rho)^sigma/
                (delta^(2*((4+12/t)*eta)/(t-sigma)))^2)^2 := by
  obtain ⟨delta0,hd0,hd01,hstep3⟩ := exists_native_original_step3_threshold
    t sigma s zeta eta ht ht2 hsigma hsigma1 hsgap ha hgap heta hetat heps
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall Pts G hGP hbox hviol hfrostman
  rcases hstep3 delta hd hsmall Pts G hGP hbox hviol hfrostman with hsmallG|hlarge
  · exact Or.inl hsmallG
  · right
    obtain ⟨n,rho,j,G4,hmesh,hbottom,hrhomenu,hdrho,hrho1,hj,hG4,hretain,hgain,hscale,hdata⟩ := hlarge
    refine ⟨n,rho,j,G4,hmesh,hbottom,hrhomenu,hdrho,hrho1,hj,hG4,hretain,hgain,hscale,hdata,?_⟩
    intro w hwidth
    let tau : ℝ := delta^(2*((4+12/t)*eta)/(t-sigma))
    let m : ℝ := (2^j:ℕ)
    let k : ℝ := tau^2*m/2
    have htau : 0<tau := Real.rpow_pos_of_pos hd _
    have hm : 0<m := by dsimp [m]; positivity
    have hrho : 0<rho := hd.trans_le hdrho
    have hk : 0≤k := by dsimp [k]; positivity
    have hne : ∀ z∈G4, z.1≠z.2 := by
      intro z hz he
      have hh := (hdata z hz).1
      have he0 : euclideanDistance z.1 z.2=0 := by rw [he]; simp [euclideanDistance]
      rw [he0] at hh
      exact (not_le_of_gt (Real.rpow_pos_of_pos hd _)) hh
    have hwide : ∀ z∈G4, ∀ R : ℝ, rho≤R → R≤1 →
        ((physicalPairTube Pts R z).card : ℝ)≤2^(sigma+1)*(R/rho)^sigma*m := by
      intro z hz
      exact (hdata z hz).2.2.2.1
    have hrich : ∀ z∈G4,
        2*k≤((G4.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
        2*k≤((G4.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ) := by
      intro z hz
      obtain ⟨_hsep,_hlo,_hhi,_hwide,_hann,_hoff,hforward,hreverse⟩ := hdata z hz
      have he : 2*k=tau^2*m := by dsimp [k]; ring
      rw [he]
      exact ⟨hforward,hreverse⟩
    obtain ⟨hM,hmeshM,hMbound⟩ := original_thickening_color_budget rho w hrho hwidth
    obtain ⟨S,hS,hfiber,hweight,hinj,hchart,hsets,hsep,hshade,_hcharge,_hcap⟩ :=
      exists_original_admissible_shaded_family Pts G4 rho w k (thickeningModulus rho w)
        hrho hwidth hk hM hmeshM (hG4.trans hGP) hbox hne hrich
    refine ⟨S,hS,hfiber,hweight,hMbound,hinj,hchart,hsets,hsep,?_,?_⟩
    · intro z hz
      have he : 2*k=tau^2*m := by dsimp [k]; ring
      simpa only [he] using hshade z hz
    · intro W nx ny c A hWlo hWhi hunit hA
      have hW : W≤1/4 := by linarith only [hWhi]
      have hRlo : rho≤432*W+16*rho := by linarith only [hrho,hWlo]
      have hRhi : 432*W+16*rho≤1 := by linarith only [hWlo,hWhi]
      have hcap := original_dense_external_cap Pts G4 S rho w W k (2^(sigma+1)) m sigma nx ny c A
        hrho (by linarith only [hrho,hwidth]) hW hk hunit hA hS hinj hchart
        (hG4.trans hGP) hbox hne hrich hRlo hRhi hwide
      exact normalize_original_dense_cap _ _ tau m htau hm hcap

end NativeOriginalTubeFamilyCaller
