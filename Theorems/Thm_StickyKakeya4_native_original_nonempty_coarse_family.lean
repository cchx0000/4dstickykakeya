import Theorems.Thm_StickyKakeya4_native_original_tube_family_caller
import Theorems.Thm_StickyKakeya4_native_original_pruning_loss
import Theorems.Thm_StickyKakeya4_original_profiled_coarse_shadings
import Theorems.Thm_StickyKakeya4_native_original_shading_width_cutoff
import Theorems.Thm_StickyKakeya4_original_densest_fiber_retention
import Theorems.Thm_StickyKakeya4_native_original_densest_scale_decay
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeOriginalNonemptyCoarseFamily
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

/-- The source separation pays all scale-menu and occupancy logarithms.
Above the target original graph error, the same actual coarse family is
nonempty and retains an explicit positive original-pair charge. No
nonempty-return or logarithmic-budget certificate is an input. -/
theorem exists_native_original_nonempty_coarse_family_threshold (t sigma s zeta eta : ℝ)
    (ht : 0<t) (ht2 : t≤2) (hsigma : 0≤sigma) (hsigma1 : sigma≤1)
    (hsgap : sigma≤s) (ha : sigma<t) (hgap : s-sigma≤zeta)
    (heta : 0<eta) (hetat : eta≤t/2)
    (heps : ((4+12/t)+1)*eta≤zeta+sigma-s) :
    ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧
    ∀ delta : ℝ, 0<delta → delta≤delta0 →
    ∀ Pts : Finset Point, ∀ G : Finset Pair,
      G⊆Pts.product Pts →
      (∀ z∈Pts, |z.1|≤1 ∧ |z.2|≤1) →
      (∀ p∈Pts, ∀ q∈Pts, p≠q → delta≤euclideanDistance p q) →
      (∀ z∈G, ∃ R : ℝ, delta≤R ∧ R≤1 ∧
        delta^(-zeta)*R^s*Pts.card≤(physicalPairTube Pts R z).card) →
      (∀ q∈Pts, ∀ R : ℝ, delta≤R → R≤1 →
        ((Pts.filter (fun v => euclideanDistance q v≤R)).card : ℝ)≤delta^(-eta)*R^t*Pts.card) →
      (G.card : ℝ)≤delta^(eta/2)*(Pts.card : ℝ)^2 ∨
      ∃ n : ℕ, ∃ rho : ℝ, ∃ j : ℕ, ∃ G4 : Finset Pair,
        delta≤dyadicRadius n ∧ dyadicRadius n≤2*delta ∧
        rho∈scaleMenu n ∧ delta≤rho ∧ rho≤1 ∧ j<Nat.log 2 Pts.card+1 ∧
        G4⊆G ∧ G4.Nonempty ∧
        (G.card : ℝ)/2<(((n+1)*levelCount Pts:ℕ):ℝ)*G4.card ∧
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
        ∀ w h : ℝ, 3*rho≤w → w≤1/448 → rho≤h →
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
  obtain ⟨delta1,hd1,hd11,hcoarse⟩ :=
    NativeOriginalCoarseTubeFamily.exists_native_original_coarse_family_threshold
      t sigma s zeta eta ht ht2 hsigma hsigma1 hsgap ha hgap heta hetat heps
  obtain ⟨delta2,hd2,_hd21,hloss⟩ :=
    NativeOriginalPruningLoss.exists_original_pruning_loss_cutoff t sigma eta ht ht2 hsigma ha heta
  refine ⟨min delta1 delta2,lt_min hd1 hd2,(min_le_left _ _).trans hd11,?_⟩
  intro delta hd hsmall Pts G hGP hbox hsep hviol hfrostman
  have hsmall1 := hsmall.trans (min_le_left delta1 delta2)
  have hsmall2 := hsmall.trans (min_le_right delta1 delta2)
  have hdle1 := hsmall1.trans hd11
  by_cases hsmallG : (G.card : ℝ)≤delta^(eta/2)*(Pts.card : ℝ)^2
  · exact Or.inl hsmallG
  · have hlargeG := lt_of_not_ge hsmallG
    have hgpos : (0:ℝ)<G.card :=
      (mul_nonneg (Real.rpow_pos_of_pos hd _).le (sq_nonneg _)).trans_lt hlargeG
    rcases hcoarse delta hd hsmall1 Pts G hGP hbox hviol hfrostman with hsmallOld|hlarge
    · have hpow : delta^eta≤delta^(eta/2) :=
        Real.rpow_le_rpow_of_exponent_ge hd hdle1 (by linarith only [heta])
      exact (hsmallG (hsmallOld.trans (mul_le_mul_of_nonneg_right hpow (sq_nonneg _)))).elim
    · right
      obtain ⟨n,rho,j,G4,hmesh,hbottom,hrhomenu,hdrho,hrho1,hj,hG4,hretain,hgain,hscale,
        hdecay,hwidthrange,hclasses,hfamily⟩ := hlarge
      have herr := hloss delta hd hsmall2 n hmesh hbottom Pts hbox hsep
      let H : ℝ := (((n+1)*levelCount Pts:ℕ):ℝ)
      let err : ℝ := delta^eta+H*(delta^(2*eta)+400*delta^(2*((4+12/t)*eta)/(t-sigma)))
      have he : err≤delta^(eta/2)/2 := herr
      have hretain' : (G.card : ℝ)≤H*G4.card+err*(Pts.card : ℝ)^2 := by
        dsimp [H,err,levelCount]
        nlinarith only [hretain]
      have hhalf := NativeOriginalPruningLoss.original_retained_graph_half
        (G.card : ℝ) G4.card ((Pts.card : ℝ)^2) H err (delta^(eta/2))
        (sq_nonneg _) he hlargeG hretain'
      have hG4n : G4.Nonempty := by
        apply Finset.card_pos.mp
        have hnonneg : 0≤H := by dsimp [H]; positivity
        have hc : (0:ℝ)<G4.card := by
          by_contra hc
          have hp := mul_nonpos_of_nonneg_of_nonpos hnonneg (le_of_not_gt hc)
          linarith only [hhalf,hgpos,hp]
        exact_mod_cast hc
      refine ⟨n,rho,j,G4,hmesh,hbottom,hrhomenu,hdrho,hrho1,hj,hG4,hG4n,hhalf,hretain,
        hgain,hscale,hdecay,hwidthrange,hclasses,?_⟩
      intro w h hw hws hh
      exact hfamily w h hw hws hh hG4n

end NativeOriginalNonemptyCoarseFamily
