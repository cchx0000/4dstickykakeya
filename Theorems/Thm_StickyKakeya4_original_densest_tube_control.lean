import Theorems.Thm_StickyKakeya4_original_physical_tube_scale_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace OriginalDensestTubeControl
open OriginalPairStripGeometry OriginalPhysicalPairTube OriginalPhysicalTubeScaleSelection

/-- The menu is finite and retains both the unit radius and the mesh scale. -/
theorem scale_menu_bounds (n : ℕ) :
    (scaleMenu n).Nonempty ∧ (scaleMenu n).card≤n+1 ∧
    ∀ q∈scaleMenu n, 0<q ∧ dyadicRadius n≤q ∧ q≤1 := by
  classical
  refine ⟨?_,?_,?_⟩
  · refine ⟨dyadicRadius 0,Finset.mem_image.mpr ⟨0,Finset.mem_range.mpr (by omega),rfl⟩⟩
  · exact (Finset.card_image_le).trans_eq (Finset.card_range _)
  · intro q hq
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
    have hjn : j≤n := by have := Finset.mem_range.mp hj; omega
    refine ⟨by unfold dyadicRadius; positivity,?_,?_⟩
    · exact pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤1/2) (by norm_num) hjn
    · exact pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num)

/-- Maximal density on the explicit menu controls EVERY larger physical
radius, using original P throughout, including nondyadic radii. -/
theorem original_larger_width_control
    (Pts : Finset Point) (z : Pair) (n : ℕ) (sigma rho R : ℝ)
    (hsigma : 0≤sigma) (hrho : rho∈scaleMenu n)
    (hmax : ∀ q∈scaleMenu n, score Pts sigma q z≤score Pts sigma rho z)
    (hRlow : rho≤R) (hRhigh : R≤1) :
    ((physicalPairTube Pts R z).card : ℝ)≤
      2^sigma*(R/rho)^sigma*(physicalPairTube Pts rho z).card := by
  have hb := (scale_menu_bounds n).2.2 rho hrho
  have hR : 0<R := hb.1.trans_le hRlow
  obtain ⟨j,hjn,hRq,hqR⟩ := dyadic_radius_cover n R (by linarith only [hb.2.1,hRlow,hR]) hRhigh
  have hqS : dyadicRadius j∈scaleMenu n := Finset.mem_image.mpr
    ⟨j,Finset.mem_range.mpr (by omega),rfl⟩
  have hqpos := ((scale_menu_bounds n).2.2 _ hqS).1
  have hp := hmax _ hqS
  dsimp [score] at hp
  have hraw := (div_le_div_iff₀ (Real.rpow_pos_of_pos hqpos sigma)
    (Real.rpow_pos_of_pos hb.1 sigma)).mp hp
  have hcard : ((physicalPairTube Pts R z).card : ℝ)≤
      (physicalPairTube Pts (dyadicRadius j) z).card :=
    Nat.cast_le.mpr (Finset.card_le_card (physical_tube_mono Pts z hRq))
  have hpowers := Real.rpow_le_rpow hqpos.le hqR hsigma
  have h1 := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hb.1.le sigma)
  have h2 := mul_le_mul_of_nonneg_left hpowers (Nat.cast_nonneg (physicalPairTube Pts rho z).card)
  calc
    _ ≤ ((physicalPairTube Pts rho z).card : ℝ)*(2*R)^sigma/rho^sigma :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hb.1 sigma)).mpr (h1.trans (hraw.trans h2))
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hR.le,
        Real.div_rpow hR.le hb.1.le]
      ring

/-- A continuous-radius violation yields a large densest original score.
The factor 2^sigma is the complete rounding cost. -/
theorem original_violation_forces_large_score
    (Pts : Finset Point) (z : Pair) (n : ℕ) (sigma s delta zeta : ℝ)
    (hd : 0<delta) (hbottom : dyadicRadius n≤2*delta)
    (hsigma : 0≤sigma) (hsgap : sigma≤s)
    (hviol : ∃ R : ℝ, delta≤R ∧ R≤1 ∧
      delta^(-zeta)*R^s*Pts.card≤(physicalPairTube Pts R z).card) :
    delta^(s-sigma-zeta)*(Pts.card : ℝ)≤
      2^sigma*score Pts sigma
        (chosenScale Pts (scaleMenu n) (scale_menu_bounds n).1 sigma z) z := by
  obtain ⟨R,hRlow,hRhigh,hlarge⟩ := hviol
  have hRpos : 0<R := hd.trans_le hRlow
  obtain ⟨j,hjn,hRq,hqR⟩ := dyadic_radius_cover n R (by linarith only [hbottom,hRlow]) hRhigh
  have hqS : dyadicRadius j∈scaleMenu n := Finset.mem_image.mpr
    ⟨j,Finset.mem_range.mpr (by omega),rfl⟩
  have hqpos := ((scale_menu_bounds n).2.2 _ hqS).1
  have hcard : ((physicalPairTube Pts R z).card : ℝ)≤
      (physicalPairTube Pts (dyadicRadius j) z).card :=
    Nat.cast_le.mpr (Finset.card_le_card (physical_tube_mono Pts z hRq))
  have hp := (chosen_scale_spec Pts (scaleMenu n) (scale_menu_bounds n).1 sigma z).2 _ hqS
  have hgap := Real.rpow_le_rpow hd.le hRlow (sub_nonneg.mpr hsgap)
  have hgap' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgap (Real.rpow_nonneg hd.le (-zeta))) (Nat.cast_nonneg Pts.card)
  have hiden : delta^(-zeta)*delta^(s-sigma)=delta^(s-sigma-zeta) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hsmall : delta^(-zeta)*R^(s-sigma)*Pts.card≤
      ((physicalPairTube Pts (dyadicRadius j) z).card : ℝ)/R^sigma := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hRpos sigma)).mpr
    have heq : R^(s-sigma)*R^sigma=R^s := by
      rw [← Real.rpow_add hRpos,sub_add_cancel]
    calc
      _ = delta^(-zeta)*(R^(s-sigma)*R^sigma)*Pts.card := by ring
      _ = delta^(-zeta)*R^s*Pts.card := by rw [heq]
      _ ≤ _ := hlarge.trans hcard
  have hqpow : (dyadicRadius j)^sigma≤2^sigma*R^sigma := by
    simpa only [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hRpos.le]
      using Real.rpow_le_rpow hqpos.le hqR hsigma
  have hqcontrol : ((physicalPairTube Pts (dyadicRadius j) z).card : ℝ)/R^sigma≤
      2^sigma*score Pts sigma (dyadicRadius j) z := by
    unfold score
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hRpos sigma)).mpr
    have hh := mul_le_mul_of_nonneg_left hqpow
      (div_nonneg (Nat.cast_nonneg (physicalPairTube Pts (dyadicRadius j) z).card)
        (Real.rpow_nonneg hqpos.le sigma))
    have heq : ((physicalPairTube Pts (dyadicRadius j) z).card : ℝ)/(dyadicRadius j)^sigma*
        (dyadicRadius j)^sigma=(physicalPairTube Pts (dyadicRadius j) z).card :=
      div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hqpos sigma))
    rw [heq] at hh
    nlinarith only [hh]
  rw [hiden] at hgap'
  exact hgap'.trans (hsmall.trans (hqcontrol.trans
    (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by norm_num) sigma))))

end OriginalDensestTubeControl
