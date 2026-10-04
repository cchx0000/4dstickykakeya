import Theorems.Thm_StickyKakeya4_original_densest_tube_control

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeRadialDensestGraph
open OriginalPairStripGeometry OriginalPhysicalPairTube
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl

/-- A literal finite dyadic menu with bottom scale comparable to the
original arbitrary positive mesh. -/
theorem exists_original_dyadic_mesh (delta : ℝ) (hd : 0<delta) (hd1 : delta≤1) :
    ∃ n : ℕ, delta≤dyadicRadius n ∧ dyadicRadius n≤2*delta := by
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one hd (by norm_num : (1/2:ℝ)<1)
  obtain ⟨n,_hn,hlo,hhi⟩ := dyadic_radius_cover N delta (by
    change (1/2:ℝ)^N≤2*delta
    linarith only [hN,hd]) hd1
  exact ⟨n,hlo,hhi⟩

/-- Source Step1 performed on the actual violating ORIGINAL pair graph:
select one densest radius and one actual occupancy bin. The graph loss uses
the exact finite menu and the logarithm of ORIGINAL |P|. The output controls
every larger physical radius against the SAME original point set. -/
theorem exists_native_densest_original_graph
    (Pts : Finset Point) (G : Finset Pair) (n : ℕ)
    (delta sigma s zeta : ℝ) (hd : 0<delta) (hmesh : delta≤dyadicRadius n)
    (hbottom : dyadicRadius n≤2*delta)
    (hsigma : 0≤sigma) (hsgap : sigma≤s)
    (hG : G.Nonempty) (hGP : G⊆Pts.product Pts)
    (hviol : ∀ z∈G, ∃ R : ℝ, delta≤R ∧ R≤1 ∧
      delta^(-zeta)*R^s*Pts.card≤(physicalPairTube Pts R z).card) :
    ∃ rho∈scaleMenu n, delta≤rho ∧ ∃ j : ℕ, j<Nat.log 2 Pts.card+1 ∧
      ∃ H : Finset Pair, H⊆G ∧ H.Nonempty ∧
      G.card≤(n+1)*(Nat.log 2 Pts.card+1)*H.card ∧
      delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*(2^j:ℕ) ∧
      delta^(s-sigma-zeta)*rho^sigma≤2^sigma ∧
      ∀ z∈H,
        2^j≤(physicalPairTube Pts rho z).card ∧
        (physicalPairTube Pts rho z).card<2^(j+1) ∧
        ∀ R : ℝ, rho≤R → R≤1 →
          ((physicalPairTube Pts R z).card : ℝ)≤
            2^(sigma+1)*(R/rho)^sigma*(2^j:ℕ) := by
  classical
  have hm := scale_menu_bounds n
  obtain ⟨rho,hrho,j,hj,H,hHG,hH,hmass,hdata⟩ :=
    exists_original_densest_graph_bin Pts G (scaleMenu n) sigma hG hGP hm.1
      (fun q hq => (hm.2.2 q hq).1)
  have hrhopos := (hm.2.2 rho hrho).1
  have hpowpos := Real.rpow_pos_of_pos hrhopos sigma
  have htwo : (2:ℝ)^(sigma+1)=2^sigma*2 := by rw [Real.rpow_add (by norm_num),Real.rpow_one]
  have hlabel (z : Pair) (hz : z∈H) :
      delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤
        2^sigma*(physicalPairTube Pts rho z).card := by
    have hh := original_violation_forces_large_score Pts z n sigma s delta zeta
      hd hbottom hsigma hsgap (hviol z (hHG hz))
    rw [(hdata z hz).1] at hh
    dsimp [score] at hh
    rw [← mul_div_assoc] at hh
    have hh' := mul_le_mul_of_nonneg_right hh hpowpos.le
    have heq : 2^sigma*((physicalPairTube Pts rho z).card : ℝ)/rho^sigma*rho^sigma=
        2^sigma*(physicalPairTube Pts rho z).card := div_mul_cancel₀ _ (ne_of_gt hpowpos)
    rw [heq] at hh'
    nlinarith only [hh']
  obtain ⟨z0,hz0⟩ := hH
  have hNpos : 0<(Pts.card : ℝ) := by
    have hp := (Finset.mem_product.mp (hGP (hHG hz0))).1
    exact_mod_cast Finset.card_pos.mpr ⟨z0.1,hp⟩
  have htop := (original_tube_card_bounds Pts z0 rho
    (Finset.mem_product.mp (hGP (hHG hz0))).1 hrhopos.le).2
  have hlower := hlabel z0 hz0
  have hbinR : ((physicalPairTube Pts rho z0).card : ℝ)≤2*(2^j:ℕ) := by
    have h := (hdata z0 hz0).2.2.1.le
    rw [pow_succ,Nat.mul_comm] at h
    exact_mod_cast h
  have hlarge : delta^(s-sigma-zeta)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*(2^j:ℕ) := by
    rw [htwo]
    have hh := mul_le_mul_of_nonneg_left hbinR (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) sigma)
    nlinarith only [hlower,hh]
  have hscale : delta^(s-sigma-zeta)*rho^sigma≤2^sigma := by
    apply (mul_le_mul_iff_of_pos_right hNpos).mp
    exact hlower.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr htop)
      (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) sigma))
  refine ⟨rho,hrho,hmesh.trans ((hm.2.2 rho hrho).2.1),j,hj,H,hHG,⟨z0,hz0⟩,?_,hlarge,hscale,?_⟩
  · exact hmass.trans (Nat.mul_le_mul_right H.card
      (Nat.mul_le_mul_right (Nat.log 2 Pts.card+1) hm.2.1))
  · intro z hz
    refine ⟨(hdata z hz).2.1,(hdata z hz).2.2.1,?_⟩
    intro R hRlow hRhigh
    have hcontrol := original_larger_width_control Pts z n sigma rho R hsigma hrho
      (hdata z hz).2.2.2 hRlow hRhigh
    have hbin : ((physicalPairTube Pts rho z).card : ℝ)≤2*(2^j:ℕ) := by
      have h := (hdata z hz).2.2.1.le
      rw [pow_succ,Nat.mul_comm] at h
      exact_mod_cast h
    have hRpos : 0<R := hrhopos.trans_le hRlow
    have hfactor : 0≤(2:ℝ)^sigma*(R/rho)^sigma := by positivity
    have hh := mul_le_mul_of_nonneg_left hbin hfactor
    rw [htwo]
    nlinarith only [hcontrol,hh]

end NativeRadialDensestGraph
