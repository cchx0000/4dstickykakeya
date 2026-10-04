import Theorems.Thm_StickyKakeya4_original_annular_off_root_mass
import Theorems.Thm_StickyKakeya4_native_annular_parameter_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open scoped BigOperators
noncomputable section
namespace NativeOriginalOffRootMass
open OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl OriginalAnnularRowCover
open OriginalAnnularGraphDeletion OriginalAnnularOffRootMass NativeAnnularParameterBudget

def offRootSupport (Pts : Finset Point) (z : Pair) (rho tau0 : ℝ) : Finset Point := by
  classical
  exact (physicalPairTube Pts rho z).filter
    (fun q => tau0<euclideanDistance z.1 q ∧ tau0<euclideanDistance z.2 q)

/-- The retained original pair has at least half its original tube mass
outside BOTH endpoint balls. Every near point is charged to original
Frostman balls or actual annuli; no off-root mass premise is used. -/
theorem native_original_off_root_half
    (Pts : Finset Point) (G : Finset Pair) (n : ℕ) (z : Pair)
    (delta eta eta' t sigma s zeta rho m r : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (ha : sigma<t) (hsigma1 : sigma≤1)
    (hr : 0<r) (hr1 : r≤1) (hm : 0 ≤ m)
    (hrho : rho∈scaleMenu n) (hquery : delta≤rho)
    (htop : delta^(2*eta'/(t-sigma))≤1)
    (heps : eta'≤zeta+sigma-s-eta)
    (hsmall : 4*((n:ℝ)+5)*delta^eta'≤1)
    (hzP : z∈Pts.product Pts)
    (hgain : delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m)
    (hmass : m≤((physicalPairTube Pts rho z).card : ℝ))
    (hfrostman : ∀ p∈Pts, ∀ R : ℝ, delta≤R → R≤1 →
      ((Pts.filter (fun v => euclideanDistance p v≤R)).card : ℝ)≤delta^(-eta)*R^t*Pts.card)
    (hz : z∈retainedAnnularGraph Pts G
      (annularScales n rho (delta^(2*eta'/(t-sigma)))) (r^(-3:ℝ)*rho)
      (fun tau => delta^(-eta')*tau^(t-sigma)*m)) :
    m/2≤((offRootSupport Pts z rho (delta^(2*eta'/(t-sigma)))).card : ℝ) := by
  classical
  let tau0 := delta^(2*eta'/(t-sigma))
  let w := r^(-3:ℝ)*rho
  let A := delta^eta'*m
  have hb := (scale_menu_bounds n).2.2 rho hrho
  have hA : 0≤A := by dsimp [A]; positivity
  have hwidth : rho≤w := by
    have hh : 1≤r^(-3:ℝ) := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hr hr1
        (by norm_num : (-3:ℝ)≤0)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh hb.1.le
  have hinner := original_inner_ball_budget Pts delta eta eta' rho t sigma s zeta m
    hd hd1 hb.1 hb.2.2 ha.le hsigma1 hm heps hgain
  have hthreshold (tau : ℝ) (htau : tau∈annularScales n rho tau0) :
      delta^(-eta')*tau^(t-sigma)*m≤A := by
    obtain ⟨htauS,_hlo,hhi⟩ := Finset.mem_filter.mp htau
    have htaupos := ((scale_menu_bounds n).2.2 tau htauS).1
    have hp := Real.rpow_le_rpow htaupos.le hhi (sub_pos.mpr ha).le
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (by positivity : 0≤delta^(-eta'))) hm
    have hid := native_annular_top_power delta eta' (t-sigma) hd (sub_pos.mpr ha)
    simpa only [tau0,A,← mul_assoc,hid] using hh
  have hret := (Finset.mem_filter.mp hz).2
  have hball (p : Point) (hp : p∈Pts) :
      ((Pts.filter (fun v => euclideanDistance p v≤rho)).card : ℝ)≤4*A := by
    simpa only [A,mul_assoc] using (hfrostman p hp rho hquery hb.2.2).trans hinner
  have hnear1 := original_near_root_card Pts z.1 z.2 n rho tau0 w (4*A) A hrho htop
    (hball z.1 (Finset.mem_product.mp hzP).1)
    hA (fun tau htau => ((hret tau htau).1.le).trans (hthreshold tau htau))
  have hnear2 := original_near_root_card Pts z.2 z.1 n rho tau0 w (4*A) A hrho htop
    (hball z.2 (Finset.mem_product.mp hzP).2)
    hA (fun tau htau => ((hret tau htau).2.le).trans (hthreshold tau htau))
  let Near1 := (physicalPairTube Pts w z).filter (fun q => euclideanDistance z.1 q≤tau0)
  let Near2 := (physicalPairTube Pts w z.swap).filter (fun q => euclideanDistance z.2 q≤tau0)
  let Away := offRootSupport Pts z rho tau0
  have hcover : physicalPairTube Pts rho z⊆Away∪(Near1∪Near2) := by
    intro q hq
    have hqw := physical_tube_mono Pts z hwidth hq
    by_cases h1 : tau0<euclideanDistance z.1 q
    · by_cases h2 : tau0<euclideanDistance z.2 q
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hq,h1,h2⟩))
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_filter.mpr
        exact ⟨by simpa only [physical_pair_tube_swap] using hqw,le_of_not_gt h2⟩
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hqw,le_of_not_gt h1⟩))))
  have hcard : ((physicalPairTube Pts rho z).card : ℝ)≤Away.card+Near1.card+Near2.card := by
    have hc := (Finset.card_le_card hcover).trans
      ((Finset.card_union_le Away (Near1∪Near2)).trans
        (Nat.add_le_add_left (Finset.card_union_le Near1 Near2) Away.card))
    have hcR : ((physicalPairTube Pts rho z).card : ℝ)≤Away.card+(Near1.card+Near2.card) := by
      exact_mod_cast hc
    simpa only [add_assoc] using hcR
  have hnear1' : (Near1.card : ℝ)≤((n:ℝ)+5)*A := by
    change (Near1.card : ℝ)≤4*A+(n+1:ℕ)*A at hnear1
    push_cast at hnear1
    nlinarith only [hnear1]
  have hnear2' : (Near2.card : ℝ)≤((n:ℝ)+5)*A := by
    change (Near2.card : ℝ)≤4*A+(n+1:ℕ)*A at hnear2
    push_cast at hnear2
    nlinarith only [hnear2]
  have hsmallm := mul_le_mul_of_nonneg_right hsmall hm
  change m/2≤(Away.card : ℝ)
  dsimp [A] at hnear1' hnear2'
  nlinarith only [hmass,hcard,hnear1',hnear2',hsmallm]

end NativeOriginalOffRootMass
