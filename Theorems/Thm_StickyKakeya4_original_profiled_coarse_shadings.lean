import Theorems.Thm_StickyKakeya4_original_shading_box_profile
import Theorems.Thm_StickyKakeya4_original_coarse_shading_preparation
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
namespace OriginalProfiledCoarseShadings
local instance : DecidableEq (ℤ×ℤ) := Classical.decEq _
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open NativeRadialClassPruning OriginalRepresentativeShading OriginalShadingCenterProfile
open OriginalShadingBoxProfile OriginalShadingGridGeometry OriginalClippedUnitTube
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl
open OriginalAnnularRowCover OriginalAnnularOffRootMass
open OriginalCoarseShadingPreparation DyadicOriginalFiberSelection

/-- Native original input gives the precise half-coordinate box profile
consumed by the existing coarse-shading selection. -/
theorem original_shading_half_box_frostman
    (Pts : Finset Point) (G : Finset Pair) (n : ℕ) (z : Pair)
    (delta eta eta' t sigma s zeta rho m w tau0 : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (heta' : 0≤eta')
    (ha : sigma≤t) (hsigma1 : sigma≤1) (hm : 0 ≤ m)
    (hrho : rho∈scaleMenu n) (hquery : delta≤rho)
    (htau : 0<tau0) (htop : tau0≤1)
    (hwidth : 24*rho≤w) (heps : -eta'≤zeta+sigma-s-eta)
    (hz : z∈G) (hGP : G⊆Pts.product Pts)
    (hbox : ∀ x∈Pts, |x.1|≤1 ∧ |x.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2)
    (hgain : delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m)
    (hfrostman : ∀ q∈Pts, ∀ L : ℝ, delta≤L → L≤1 →
      ((Pts.filter (fun v => euclideanDistance q v≤L)).card : ℝ)≤delta^(-eta)*L^t*Pts.card)
    (hann : ∀ u∈G, ∀ tau∈annularScales n rho tau0,
      ((annularSupport Pts u.1 u.2 w tau).card : ℝ)<delta^(-eta')*tau^(t-sigma)*m ∧
      ((annularSupport Pts u.2 u.1 w tau).card : ℝ)<delta^(-eta')*tau^(t-sigma)*m)
    (hreverse : tau0^2*m≤((G.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ))
    (x : Point) (R : ℝ) (hR : rho≤R) :
    (((originalShading Pts G rho z).filter (fun p => InBox (halfPoint p) x R)).card : ℝ)≤
      (8*shadingCoefficient n delta eta' tau0)*R^(min (t-sigma) 1)*(originalShading Pts G rho z).card := by
  exact original_half_box_profile_from_centers (originalShading Pts G rho z) rho
    (shadingCoefficient n delta eta' tau0) (min (t-sigma) 1)
    ((scale_menu_bounds n).2.2 rho hrho).1
    (original_shading_coefficient_one_le n delta eta' tau0 hd hd1 heta' htau htop)
    (le_min (sub_nonneg.mpr ha) (by norm_num)) (min_le_right _ _)
    (fun p hp L hL => original_shaded_center_frostman Pts G n z p delta eta eta' t sigma s zeta
      rho m w tau0 L hd hd1 heta' ha hsigma1 hm hrho hquery htau htop hL hwidth heps
      hz hGP hbox hdistinct hgain hfrostman hann hreverse hp) x R hR

/-- Actual original Frostman data and surviving annuli produce coarse
shadings directly. No shading Frostman certificate is supplied. Original
labels, physical memberships, common occupancy, and original union mass
are all retained. -/
theorem exists_original_profiled_coarse_shadings
    (Pts : Finset Point) (G T : Finset Pair) (n : ℕ)
    (delta eta eta' t sigma s zeta rho m w tau0 h W : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (heta' : 0≤eta')
    (ha : sigma≤t) (hsigma1 : sigma≤1) (hm : 0 < m)
    (hrho : rho∈scaleMenu n) (hquery : delta≤rho)
    (htau : 0<tau0) (htop : tau0≤1)
    (hwidth : 24*rho≤w) (heps : -eta'≤zeta+sigma-s-eta)
    (hmesh : rho≤h) (hphysical : 3*rho≤W)
    (hT : T.Nonempty) (hTG : T⊆G) (hGP : G⊆Pts.product Pts)
    (hbox : ∀ x∈Pts, |x.1|≤1 ∧ |x.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2)
    (hgain : delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m)
    (hfrostman : ∀ q∈Pts, ∀ L : ℝ, delta≤L → L≤1 →
      ((Pts.filter (fun v => euclideanDistance q v≤L)).card : ℝ)≤delta^(-eta)*L^t*Pts.card)
    (hann : ∀ u∈G, ∀ tau∈annularScales n rho tau0,
      ((annularSupport Pts u.1 u.2 w tau).card : ℝ)<delta^(-eta')*tau^(t-sigma)*m ∧
      ((annularSupport Pts u.2 u.1 w tau).card : ℝ)<delta^(-eta')*tau^(t-sigma)*m)
    (hreverse : ∀ z∈G,
      tau0^2*m≤((G.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ)) :
    let K := 8*shadingCoefficient n delta eta' tau0
    let b := min (t-sigma) 1
    ∃ j k : ℕ, ∃ S : Finset Pair, S⊆T ∧ S.Nonempty ∧
      j<levelCount Pts ∧ k<levelCount Pts ∧ T.card≤(levelCount Pts)^2*S.card ∧
      (∀ z∈S, tau0^2*m≤4*levelCount Pts*2^j*2^k ∧
        ∃ R : Finset Point, R⊆bin (originalShading Pts G rho z) (fun p => grid h (halfPoint p)) j ∧
          R.Nonempty ∧ 2^k≤9*R.card ∧ R.card<2^(k+1) ∧
          (∀ p∈R, halfPoint p∈clippedTube z W) ∧
          (∀ p∈R, ∀ q∈R, p≠q →
            2*h<max |(halfPoint p).1-(halfPoint q).1| |(halfPoint p).2-(halfPoint q).2|) ∧
          (∀ (x : Point) (r : ℝ), h≤r →
            ((R.filter (fun p => InBox (halfPoint p) x r)).card : ℝ)≤
              18*(levelCount Pts : ℝ)*(K*(2*r)^b)*R.card)) ∧
      (∀ R : Pair→Finset Point,
        (∀ z∈S, R z⊆bin (originalShading Pts G rho z) (fun p => grid h (halfPoint p)) j) →
        2^j*(S.biUnion (fun z => (R z).image (fun p => grid h (halfPoint p)))).card≤Pts.card) := by
  let K := 8*shadingCoefficient n delta eta' tau0
  let b := min (t-sigma) 1
  let Y := fun z => originalShading Pts G rho z
  have hrhop := ((scale_menu_bounds n).2.2 rho hrho).1
  have hh : 0<h := hrhop.trans_le hmesh
  have hK : 1≤K := by
    have hk := original_shading_coefficient_one_le n delta eta' tau0 hd hd1 heta' htau htop
    dsimp [K]
    linarith only [hk]
  have hb : 0≤b := le_min (sub_nonneg.mpr ha) (by norm_num)
  have hmass (z : Pair) (hz : z∈G) : tau0^2*m≤((Y z).card : ℝ) := by
    have hrev := hreverse z hz
    have hlow := original_representative_shading_lower Pts G rho (tau0^2*m/2) z hrhop hz
      hGP hbox hdistinct (by nlinarith only [hrev])
    dsimp [Y]
    nlinarith only [hlow]
  have hY : ∀ z∈T, (Y z).Nonempty := by
    intro z hz
    apply Finset.card_pos.mp
    have hl := hmass z (hTG hz)
    have hp : 0<tau0^2*m := mul_pos (sq_pos_of_pos htau) hm
    exact_mod_cast hp.trans_le hl
  have hpoint : ∀ z∈T, ∀ (x : Point) (r : ℝ), h≤r → r≤1 →
      (((Y z).filter (fun p => InBox (halfPoint p) x r)).card : ℝ)≤K*r^b*(Y z).card := by
    intro z hz x r hr _hr1
    exact original_shading_half_box_frostman Pts G n z delta eta eta' t sigma s zeta rho m w tau0
      hd hd1 heta' ha hsigma1 hm.le hrho hquery htau htop hwidth heps (hTG hz)
      hGP hbox hdistinct hgain hfrostman hann (hreverse z (hTG hz)) x r (hmesh.trans hr)
  obtain ⟨j,k,S,hST,hS,hj,hk,hretain,hdata,hunion⟩ := exists_original_coarse_shadings
    Pts T Y halfPoint hh hK hb hT (fun _ _ => Finset.filter_subset _ _) hY hpoint
  refine ⟨j,k,S,hST,hS,hj,hk,hretain,?_,hunion⟩
  intro z hz
  obtain ⟨hupper,R,hRY,hRn,hRlo,hRhi,hRsep,hRF⟩ := hdata z hz
  have hlow := hmass z (hTG (hST hz))
  refine ⟨?_,R,hRY,hRn,hRlo,hRhi,?_,hRsep,hRF⟩
  · have hh : ((Y z).card : ℝ)≤4*levelCount Pts*2^j*2^k := by exact_mod_cast hupper
    exact hlow.trans hh
  · intro p hp
    have hpY : p∈Y z := (Finset.mem_filter.mp (hRY hp)).1
    have hpT := original_shading_half_mem_clipped Pts G rho z p
      (hdistinct z (hTG (hST hz))) hbox hpY
    exact ⟨hpT.1.trans hphysical,hpT.2⟩

end OriginalProfiledCoarseShadings
