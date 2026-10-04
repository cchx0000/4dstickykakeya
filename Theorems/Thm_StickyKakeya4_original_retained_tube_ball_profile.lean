import Theorems.Thm_StickyKakeya4_native_original_off_root_mass
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalRetainedTubeBallProfile
open OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl OriginalAnnularRowCover
open OriginalAnnularGraphDeletion OriginalAnnularOffRootMass

/-- Source-side input for A.1 (232): all original points of the retained
wide tube in either actual endpoint ball satisfy the expected power law.
The inner ball and every intermediate annulus are counted explicitly. -/
theorem retained_original_wide_tube_ball_profile
    (Pts : Finset Point) (G : Finset Pair) (n : ℕ) (z : Pair)
    (delta eta eta' t sigma s zeta rho m w tau0 R : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (ha : sigma≤t) (hsigma1 : sigma≤1)
    (hm : 0 ≤ m) (hrho : rho∈scaleMenu n) (hquery : delta≤rho)
    (hRlow : rho≤R) (hRhigh : R≤tau0) (htop : tau0≤1)
    (heps : -eta'≤zeta+sigma-s-eta)
    (hzP : z∈Pts.product Pts)
    (hgain : delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m)
    (hfrostman : ∀ p∈Pts, ∀ L : ℝ, delta≤L → L≤1 →
      ((Pts.filter (fun v => euclideanDistance p v≤L)).card : ℝ)≤delta^(-eta)*L^t*Pts.card)
    (hz : z∈retainedAnnularGraph Pts G (annularScales n rho tau0) w
      (fun tau => delta^(-eta')*tau^(t-sigma)*m)) :
    (((physicalPairTube Pts w z).filter (fun q => euclideanDistance z.1 q≤R)).card : ℝ)≤
      ((n:ℝ)+5)*delta^(-eta')*R^(t-sigma)*m ∧
    (((physicalPairTube Pts w z).filter (fun q => euclideanDistance z.2 q≤R)).card : ℝ)≤
      ((n:ℝ)+5)*delta^(-eta')*R^(t-sigma)*m := by
  classical
  let A := delta^(-eta')*R^(t-sigma)*m
  let F := delta^(zeta+sigma-s-eta)*rho^(t-sigma)
  have hb := (scale_menu_bounds n).2.2 rho hrho
  have hR : 0<R := hb.1.trans_le hRlow
  have hA : 0≤A := mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hR.le _)) hm
  have hF : 0≤F := mul_nonneg (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hb.1.le _)
  have hFp : F≤delta^(-eta')*R^(t-sigma) := by
    apply mul_le_mul
    · exact Real.rpow_le_rpow_of_exponent_ge hd hd1 heps
    · exact Real.rpow_le_rpow hb.1.le hRlow (sub_nonneg.mpr ha)
    · exact Real.rpow_nonneg hb.1.le _
    · exact Real.rpow_nonneg hd.le _
  have htwo : (2:ℝ)^(sigma+1)≤4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show sigma+1≤2 by linarith only [hsigma1])
    norm_num only [Real.rpow_two,show (2:ℝ)^2=4 by norm_num] at hh
    exact hh
  have hid : F*(delta^(s-sigma-zeta)*rho^sigma)=delta^(-eta)*rho^t := by
    dsimp [F]
    calc
      _ = (delta^(zeta+sigma-s-eta)*delta^(s-sigma-zeta))*(rho^(t-sigma)*rho^sigma) := by ring
      _ = _ := by rw [← Real.rpow_add hd,← Real.rpow_add hb.1]; congr 2 <;> ring
  have hinner : delta^(-eta)*rho^t*(Pts.card:ℝ)≤4*A := by
    have hh := mul_le_mul_of_nonneg_left hgain hF
    rw [← mul_assoc,hid] at hh
    have hp := mul_le_mul hFp htwo (by positivity) (by positivity)
    have hmultiply := mul_le_mul_of_nonneg_right hp hm
    dsimp [A]
    nlinarith only [hh,hmultiply]
  have hball (p : Point) (hp : p∈Pts) :
      ((Pts.filter (fun v => euclideanDistance p v≤rho)).card:ℝ)≤4*A :=
    (hfrostman p hp rho hquery hb.2.2).trans hinner
  have hret := (Finset.mem_filter.mp hz).2
  have hann (tau : ℝ) (htau : tau∈annularScales n rho R) :
      ((annularSupport Pts z.1 z.2 w tau).card : ℝ)≤A ∧
      ((annularSupport Pts z.2 z.1 w tau).card : ℝ)≤A := by
    obtain ⟨htauS,htaurho,htauR⟩ := Finset.mem_filter.mp htau
    have htaupos := ((scale_menu_bounds n).2.2 tau htauS).1
    have htauS' : tau∈annularScales n rho tau0 :=
      Finset.mem_filter.mpr ⟨htauS,htaurho,htauR.trans hRhigh⟩
    have hthreshold : delta^(-eta')*tau^(t-sigma)*m≤A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow htaupos.le htauR (sub_nonneg.mpr ha)) (by positivity)) hm
    exact ⟨(hret tau htauS').1.le.trans hthreshold,(hret tau htauS').2.le.trans hthreshold⟩
  have hfirst := original_near_root_card Pts z.1 z.2 n rho R w (4*A) A hrho
    (hRhigh.trans htop) (hball z.1 (Finset.mem_product.mp hzP).1) hA
    (fun tau htau => (hann tau htau).1)
  have hsecond := original_near_root_card Pts z.2 z.1 n rho R w (4*A) A hrho
    (hRhigh.trans htop) (hball z.2 (Finset.mem_product.mp hzP).2) hA
    (fun tau htau => (hann tau htau).2)
  have hconvert : 4*A+(n+1:ℕ)*A=((n:ℝ)+5)*delta^(-eta')*R^(t-sigma)*m := by
    dsimp [A]
    push_cast
    ring
  rw [hconvert] at hfirst hsecond
  refine ⟨hfirst,?_⟩
  change (((physicalPairTube Pts w z.swap).filter
    (fun q => euclideanDistance z.2 q≤R)).card : ℝ)≤_ at hsecond
  simpa only [physical_pair_tube_swap] using hsecond

end OriginalRetainedTubeBallProfile
