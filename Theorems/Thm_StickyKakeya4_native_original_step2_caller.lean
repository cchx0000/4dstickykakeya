import Theorems.Thm_StickyKakeya4_native_original_off_root_mass
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

noncomputable section
namespace NativeOriginalStep2Caller
open OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl OriginalDensestWideExtension
open OriginalAnnularGraphDeletion OriginalAnnularOffRootMass NativeAnnularParameterBudget
open NativeOriginalOffRootMass NativeOriginalRadialReduction OriginalRadialNearDiagonal

/-- Closed original-input A.1 Steps 1--2. Remove the actual near diagonal,
construct the actual densest graph, and delete every bad dyadic annulus in
both orientations. The remaining ORIGINAL pairs retain at least half of
their ORIGINAL tube points away from both endpoints. All deletion budgets
and the small-scale cutoff are derived, rather than supplied as certificates. -/
theorem exists_native_original_step2_threshold (t sigma s zeta eta : ℝ)
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
      ∃ n : ℕ, ∃ rho : ℝ, ∃ j : ℕ, ∃ G3 : Finset Pair,
        delta≤dyadicRadius n ∧ dyadicRadius n≤2*delta ∧
        rho∈scaleMenu n ∧ delta≤rho ∧ rho≤1 ∧ j<Nat.log 2 Pts.card+1 ∧
        G3⊆G ∧
        (G.card : ℝ)≤delta^eta*(Pts.card : ℝ)^2+
          ((n+1)*(Nat.log 2 Pts.card+1):ℕ)*
            (G3.card+delta^(2*eta)*(Pts.card : ℝ)^2) ∧
        delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*(2^j:ℕ) ∧
        delta^(s-sigma-zeta)*rho^sigma≤2^sigma ∧
        ∀ z∈G3,
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
            (delta^(2*((4+12/t)*eta)/(t-sigma)))).card := by
  classical
  let eta' := (4+12/t)*eta
  have heta' : 0<eta' := by dsimp [eta']; positivity
  obtain ⟨d1,hd1,_hd11,hmenu1⟩ := exists_original_menu_power_cutoff 1216 (by norm_num) heta
  obtain ⟨d2,hd2,hd21,hmenu2⟩ := exists_original_menu_power_cutoff 4 (by norm_num) heta'
  obtain ⟨d3,hd3,hpower⟩ := NativeA2PowerBudget.exists_power_threshold
    (2*eta'/(t-sigma)) (1/2)
    (div_pos (mul_pos (by norm_num) heta') (sub_pos.mpr ha)) (by norm_num)
  let delta0 := min d1 (min d2 d3)
  have hdelta0 : 0<delta0 := lt_min hd1 (lt_min hd2 hd3)
  have hdelta01 : delta0≤1 := (min_le_right d1 (min d2 d3)).trans
    ((min_le_left d2 d3).trans hd21)
  refine ⟨delta0,hdelta0,hdelta01,?_⟩
  intro delta hd hsmall Pts G hGP hbox hviol hfrostman
  have hdd1 : delta≤d1 := hsmall.trans (min_le_left _ _)
  have hdd2 : delta≤d2 := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdd3 : delta≤d3 := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdle1 : delta≤1 := hsmall.trans hdelta01
  let r := delta^(2*eta/t)
  let tau0 := delta^(2*eta'/(t-sigma))
  have hr : 0<r := by dsimp [r]; positivity
  obtain ⟨_hrlow,hr1,_hrcoef⟩ := original_separation_radius delta t eta hd hdle1 ht heta.le hetat
  have htauhalf : tau0≤1/2 := hpower delta hd hdd3
  obtain ⟨G1,hG1G,hsep,hnear⟩ := remove_original_near_diagonal Pts G delta t eta
    hd hdle1 ht heta.le hetat hGP hfrostman
  by_cases hG1 : G1.Nonempty
  · right
    have hG1P : G1⊆Pts.product Pts := hG1G.trans hGP
    have hdistinct (z : Pair) (hz : z∈G1) : z.1≠z.2 := by
      intro he
      have hs := hsep z hz
      have hzero : euclideanDistance z.1 z.2=0 := by rw [he]; simp [euclideanDistance]
      rw [hzero] at hs
      exact (not_le_of_gt hr) hs
    obtain ⟨n,rho,j,G2,hmesh,hbottom,hrho,hdrho,hrho1,hj,hG2G1,_hG2,
        hmass,hgain,hscale,hdata,_hrows⟩ :=
      exists_original_densest_graph_with_annular_control Pts G1 delta eta eta' t sigma s zeta r
        hd hdle1 ht2 hsigma hsigma1 hsgap hgap hr hr1 hG1 hG1P hbox hdistinct
        (fun z hz => hviol z (hG1G hz)) hfrostman
    let S := annularScales n rho tau0
    let G3 := retainedAnnularGraph Pts G2 S (r^(-3:ℝ)*rho)
      (fun tau => delta^(-eta')*tau^(t-sigma)*(2^j:ℕ))
    have hS (tau : ℝ) (htau : tau∈S) : 0<tau ∧ tau≤1/2 ∧ delta≤2*tau := by
      obtain ⟨htauS,hlow,hhigh⟩ := Finset.mem_filter.mp htau
      have htaupos := ((scale_menu_bounds n).2.2 tau htauS).1
      exact ⟨htaupos,hhigh.trans htauhalf,by linarith only [hdrho,hlow,htaupos]⟩
    have hsource := original_source_density_of_native_gain Pts delta sigma s zeta rho (2^j:ℕ)
      hd hdle1 (((scale_menu_bounds n).2.2 rho hrho).1.le) hgap hgain
    obtain ⟨hG3G2,hgood,hdelete⟩ := native_original_annular_graph_deletion
      Pts G2 S n delta eta eta' t sigma rho (2^j:ℕ) r hd ht2 hsigma hsigma1 (by positivity)
      hr hr1 hrho hS (hG2G1.trans hG1P) hbox (fun z hz => hdistinct z (hG2G1 hz))
      (fun z hz => (hdata z hz).2.2) hsource hfrostman
    have hScard : (S.card : ℝ)≤(n:ℝ)+5 := by
      have hh : (S.card : ℝ)≤(n+1:ℕ) := by
        exact_mod_cast annular_scales_card n rho tau0
      push_cast at hh
      linarith only [hh]
    have hcoeff : 1216*(S.card:ℝ)*delta^eta≤1 := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hScard (by norm_num : (0:ℝ)≤1216))
        (Real.rpow_nonneg hd.le eta)
      exact hh.trans (hmenu1 delta hd hdd1 n hmesh hbottom)
    have hlosspow := native_annular_loss_power delta eta t sigma hd hdle1 heta.le ht hsigma1
    have hloss : 1216*(S.card:ℝ)*r^(-3*sigma)*delta^(eta'-eta)≤delta^(2*eta) := by
      calc
        _ = 1216*(S.card:ℝ)*((delta^(2*eta/t))^(-3*sigma)*delta^((4+12/t)*eta-eta)) := by
          dsimp [r,eta']
          ring
        _ ≤ 1216*(S.card:ℝ)*delta^(3*eta) :=
          mul_le_mul_of_nonneg_left hlosspow (by positivity)
        _ = (1216*(S.card:ℝ)*delta^eta)*delta^(2*eta) := by
          have hpow : delta^(3*eta)=delta^eta*delta^(2*eta) := by
            rw [← Real.rpow_add hd]
            congr 1
            ring
          rw [hpow]
          ring
        _ ≤ 1*delta^(2*eta) := mul_le_mul_of_nonneg_right hcoeff (by positivity)
        _ = _ := one_mul _
    have hretention : (G2.card:ℝ)≤G3.card+delta^(2*eta)*(Pts.card:ℝ)^2 := by
      change (G2.card:ℝ)≤G3.card+
        1216*S.card*r^(-3*sigma)*delta^(eta'-eta)*(Pts.card:ℝ)^2 at hdelete
      have hh := mul_le_mul_of_nonneg_right hloss (sq_nonneg (Pts.card:ℝ))
      nlinarith only [hdelete,hh]
    refine ⟨n,rho,j,G3,hmesh,hbottom,hrho,hdrho,hrho1,hj,hG3G2.trans (hG2G1.trans hG1G),
      ?_,hgain,hscale,?_⟩
    · have hmassR : (G1.card:ℝ)≤((n+1)*(Nat.log 2 Pts.card+1):ℕ)*(G2.card:ℝ) := by
        exact_mod_cast hmass
      have hh := mul_le_mul_of_nonneg_left hretention
        (Nat.cast_nonneg ((n+1)*(Nat.log 2 Pts.card+1)) : (0:ℝ)≤_)
      nlinarith only [hnear,hmassR,hh]
    · intro z hz
      have hzG2 := hG3G2 hz
      obtain ⟨hmlo,hmhi,hwide⟩ := hdata z hzG2
      refine ⟨hsep z (hG2G1 hzG2),hmlo,hmhi,hwide,hgood z hz,?_⟩
      exact native_original_off_root_half Pts G2 n z delta eta eta' t sigma s zeta rho (2^j:ℕ) r
        hd hdle1 ha hsigma1 hr hr1 (by positivity) hrho hdrho
        (by linarith only [htauhalf]) (by dsimp [eta']; linarith only [heps])
        (hmenu2 delta hd hdd2 n hmesh hbottom) (hG1P (hG2G1 hzG2)) hgain
        (Nat.cast_le.mpr hmlo) hfrostman hz
  · left
    have hG1empty := Finset.not_nonempty_iff_eq_empty.mp hG1
    simpa only [hG1empty,Finset.card_empty,Nat.cast_zero,zero_add] using hnear

end NativeOriginalStep2Caller
