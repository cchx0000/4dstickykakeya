import Theorems.Thm_StickyKakeya4_original_annular_row_cover
import Theorems.Thm_StickyKakeya4_original_densest_wide_extension
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace OriginalAnnularRowCharge
open OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl OriginalDensestWideExtension
open OriginalAnnularRowCover

theorem original_annular_row_charge
    (Pts : Finset Point) (G : Finset Pair) (p : Point) (n : ℕ)
    (sigma rho m w tau H : ℝ)
    (hsigma : 0≤sigma) (hm : 0≤m) (hw : 0≤w) (htau : 0<tau) (htau1 : tau≤1)
    (hH : 0<H) (hrho : rho∈scaleMenu n) (hwidth : rho≤38*w/tau)
    (hpP : p∈Pts) (hbox : ∀ z∈Pts, |z.1|≤1 ∧ |z.2|≤1)
    (hdistinct : ∀ z∈G, z.1≠z.2)
    (hlocal : ∀ z∈G, ∀ R : ℝ, rho≤R → R≤1 →
      ((physicalPairTube Pts R z).card : ℝ)≤2^(sigma+1)*(R/rho)^sigma*m)
    (hsource : rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m) :
    H*((badPartners Pts G p w tau H).card : ℝ)≤
      (2^(sigma+1)*((38*w/tau)/rho)^sigma*m)*
        (Pts.filter (fun q => euclideanDistance p q≤2*tau)).card := by
  classical
  obtain ⟨F,hFI,_hdis,hmass,_hcover,hcard⟩ :=
    exists_original_annular_row_cover Pts G p w tau H hw htau htau1 hH hpP hbox hdistinct
  let B := 2^(sigma+1)*((38*w/tau)/rho)^sigma*m
  have hrhopos := ((scale_menu_bounds n).2.2 rho hrho).1
  have hB : 0≤B := by dsimp [B]; positivity
  have hf (b : Point) (hb : b∈F) :
      ((physicalPairTube Pts (38*w/tau) (p,b)).card : ℝ)≤B := by
    have hbG := (Finset.mem_filter.mp (hFI hb)).2.1
    exact original_all_larger_width_control Pts (p,b) sigma rho (38*w/tau) m
      hsigma hm hrhopos (hlocal (p,b) hbG) hsource hwidth
  have hcardR : ((badPartners Pts G p w tau H).card : ℝ)≤
      ∑ b∈F, ((physicalPairTube Pts (38*w/tau) (p,b)).card : ℝ) := by exact_mod_cast hcard
  have hrow : ((badPartners Pts G p w tau H).card : ℝ)≤(F.card : ℝ)*B := by
    calc
      _ ≤ _ := hcardR
      _ ≤ ∑ _b∈F, B := Finset.sum_le_sum hf
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left hrow hH.le
  have h2 := mul_le_mul_of_nonneg_left hmass hB
  change H*((badPartners Pts G p w tau H).card : ℝ)≤B*
    (Pts.filter (fun q => euclideanDistance p q≤2*tau)).card
  nlinarith only [h1,h2]

/-- Query the ORIGINAL Euclidean Frostman profile at the explicit legal radius 2tau. -/
theorem original_annular_row_frostman_charge
    (Pts : Finset Point) (G : Finset Pair) (p : Point) (n : ℕ)
    (delta eta t sigma rho m w tau H : ℝ)
    (_hd : 0<delta) (hsigma : 0≤sigma) (hm : 0≤m) (hw : 0≤w)
    (htau : 0<tau) (htau1 : tau≤1) (hH : 0<H)
    (hquerylow : delta≤2*tau) (hqueryhigh : 2*tau≤1)
    (hrho : rho∈scaleMenu n) (hwidth : rho≤38*w/tau)
    (hpP : p∈Pts) (hbox : ∀ z∈Pts, |z.1|≤1 ∧ |z.2|≤1)
    (hdistinct : ∀ z∈G, z.1≠z.2)
    (hlocal : ∀ z∈G, ∀ R : ℝ, rho≤R → R≤1 →
      ((physicalPairTube Pts R z).card : ℝ)≤2^(sigma+1)*(R/rho)^sigma*m)
    (hsource : rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m)
    (hfrostman : ∀ q∈Pts, ∀ R : ℝ, delta≤R → R≤1 →
      ((Pts.filter (fun v => euclideanDistance q v≤R)).card : ℝ)≤delta^(-eta)*R^t*Pts.card) :
    H*((badPartners Pts G p w tau H).card : ℝ)≤
      (2^(sigma+1)*((38*w/tau)/rho)^sigma*m)*
        (delta^(-eta)*(2*tau)^t*Pts.card) := by
  have hrow := original_annular_row_charge Pts G p n sigma rho m w tau H
    hsigma hm hw htau htau1 hH hrho hwidth hpP hbox hdistinct hlocal hsource
  have hrhopos := ((scale_menu_bounds n).2.2 rho hrho).1
  exact hrow.trans (mul_le_mul_of_nonneg_left
    (hfrostman p hpP (2*tau) hquerylow hqueryhigh) (by positivity))
end OriginalAnnularRowCharge
