import Theorems.Thm_StickyKakeya4_native_original_step2_caller
import Theorems.Thm_StickyKakeya4_original_angular_pruning_from_physical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

noncomputable section
namespace NativeOriginalStep3Caller
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl OriginalDensestWideExtension
open OriginalAnnularGraphDeletion OriginalAnnularOffRootMass NativeAnnularParameterBudget
open NativeOriginalOffRootMass NativeOriginalRadialReduction OriginalRadialNearDiagonal
open NativeOriginalStep2Caller OriginalAngularPruningFromPhysical NativeRadialClassPruning

lemma off_root_le_endpoint_counts (P : Finset Point) (z : Pair) (rho tau : ℝ) :
    (offRootSupport P z rho tau).card≤
      ((physicalPairTube P rho z).filter (fun v => tau≤euclideanDistance z.1 v)).card ∧
    (offRootSupport P z rho tau).card≤
      ((physicalPairTube P rho z).filter (fun v => tau≤euclideanDistance z.2 v)).card := by
  constructor
  · apply Finset.card_le_card
    intro v hv
    obtain ⟨hv,h1,_h2⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hv,h1.le⟩
  · apply Finset.card_le_card
    intro v hv
    obtain ⟨hv,_h1,h2⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hv,h2.le⟩

/-- Closed original-input Steps1--3: the angular class populations are
proved from actual physical far mass before pruning the same original graph.
All old scale, tube and annular data survive; no class budget is an input. -/
theorem exists_native_original_step3_threshold (t sigma s zeta eta : ℝ)
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
        ∀ z∈G4,
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
            ((G4.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ) := by
  obtain ⟨delta0,hd0,hd01,hstep2⟩ := exists_native_original_step2_threshold
    t sigma s zeta eta ht ht2 hsigma hsigma1 hsgap ha hgap heta hetat heps
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall Pts G hGP hbox hviol hfrostman
  rcases hstep2 delta hd hsmall Pts G hGP hbox hviol hfrostman with hsmallG|hlarge
  · exact Or.inl hsmallG
  · right
    obtain ⟨n,rho,j,G3,hmesh,hbottom,hrho,hdrho,hrho1,hj,hG3G,hretain,hgain,hscale,hdata⟩ := hlarge
    let tau := delta^(2*((4+12/t)*eta)/(t-sigma))
    let M : ℝ := (2^j:ℕ)
    have htau : 0<tau := by dsimp [tau]; positivity
    have hexp : 0<2*((4+12/t)*eta)/(t-sigma) := by
      apply div_pos
      · positivity
      · exact sub_pos.mpr ha
    have htau1 : tau≤1 := Real.rpow_le_one hd.le (hsmall.trans hd01) hexp.le
    have hne : ∀ z∈G3, z.1≠z.2 := by
      intro z hz he
      have hh := (hdata z hz).1
      have he0 : euclideanDistance z.1 z.2=0 := by rw [he]; simp [euclideanDistance]
      rw [he0] at hh
      exact (not_le_of_gt (Real.rpow_pos_of_pos hd _)) hh
    have hfar : ∀ z∈G3,
        M/2≤(((physicalPairTube Pts rho z).filter (fun v => tau≤euclideanDistance z.1 v)).card : ℝ) ∧
        M/2≤(((physicalPairTube Pts rho z).filter (fun v => tau≤euclideanDistance z.2 v)).card : ℝ) := by
      intro z hz
      obtain ⟨_hsep,_hmlo,_hmhi,_hwide,_hann,hoff⟩ := hdata z hz
      have hb := off_root_le_endpoint_counts Pts z rho tau
      exact ⟨hoff.trans (Nat.cast_le.mpr hb.1),hoff.trans (Nat.cast_le.mpr hb.2)⟩
    obtain ⟨G4,hG4G3,hcharge,hdegree⟩ := exists_original_angular_core Pts G3
      (hd.trans_le hdrho) htau htau1 (show 0≤M/2 by dsimp [M]; positivity)
      (hG3G.trans hGP) hne hfar
    refine ⟨n,rho,j,G4,hmesh,hbottom,hrho,hdrho,hrho1,hj,hG4G3.trans hG3G,
      ?_,hgain,hscale,?_⟩
    · have hinner : (G3.card : ℝ)+delta^(2*eta)*(Pts.card : ℝ)^2≤
          G4.card+(delta^(2*eta)+400*tau)*(Pts.card : ℝ)^2 := by
        nlinarith only [hcharge]
      have hh := mul_le_mul_of_nonneg_left hinner
        (show (0:ℝ)≤((n+1)*(Nat.log 2 Pts.card+1):ℕ) by positivity)
      change (G.card : ℝ)≤delta^eta*(Pts.card : ℝ)^2+
        ((n+1)*(Nat.log 2 Pts.card+1):ℕ)*
          (G4.card+(delta^(2*eta)+400*tau)*(Pts.card : ℝ)^2)
      linarith only [hretain,hh]
    · intro z hz
      obtain ⟨hsep,hmlo,hmhi,hwide,hann,hoff⟩ := hdata z (hG4G3 hz)
      refine ⟨hsep,hmlo,hmhi,hwide,hann,hoff,?_,?_⟩
      · have hh := (hdegree z hz).1
        have heq : 2*tau^2*(M/2)=tau^2*M := by ring
        rw [heq] at hh
        exact hh
      · have hh := (hdegree z hz).2
        have heq : 2*tau^2*(M/2)=tau^2*M := by ring
        rw [heq] at hh
        exact hh

end NativeOriginalStep3Caller
