import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_cover
import Theorems.Thm_StickyKakeya4_native_original_shading_width_cutoff
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalTubeFrostman
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeCover NativeQuarterScaleParameters

/-- Original 2-Frostman ball counts imply the genuine bounded physical
tube count. All ball centers are original points; no pair-length loss
or tube-count certificate is used. -/
theorem original_tube_two_frostman_count (P : Finset Point3) (z : Pair3)
    (delta eta rho : ℝ) (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta)
    (hquery : delta≤rho) (hrho1 : rho≤1)
    (hbox : ∀ p∈P, ∀ i, |p i|≤1)
    (hfrostman : ∀ p∈P, ∀ R : ℝ, delta≤R → R≤1 →
      ((P.filter (fun q => distance3 p q≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card) :
    ((physicalPairTube3 P rho z).card : ℝ)≤400*delta^(-eta)*rho*P.card := by
  have hrho : 0<rho := hd.trans_le hquery
  have hK : 1≤delta^(-eta) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hd hd1
      (show -eta≤0 by linarith only [heta])
  by_cases hsmall : 10*rho≤1
  · obtain ⟨C,hCT,hC,hcover⟩ := exists_original_tube_ball_centers P z rho hrho hrho1 hbox
    let B := fun p : Point3 => P.filter (fun q => distance3 p q≤10*rho)
    have hsub : physicalPairTube3 P rho z⊆C.biUnion B := by
      intro x hx
      obtain ⟨p,hp,hpx⟩ := hcover x hx
      exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,hpx⟩⟩
    have hcount : ((physicalPairTube3 P rho z).card : ℝ)≤∑ p∈C, ((B p).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
    have hsum : (∑ p∈C, ((B p).card : ℝ))≤(C.card : ℝ)*(delta^(-eta)*(10*rho)^2*P.card) := by
      calc
        _ ≤ ∑ _p∈C, (delta^(-eta)*(10*rho)^2*P.card) := by
          apply Finset.sum_le_sum
          intro p hp
          exact hfrostman p (Finset.mem_filter.mp (hCT hp)).1 (10*rho)
            (by linarith only [hquery,hrho]) hsmall
        _ = _ := by simp
    have hC' := mul_le_mul_of_nonneg_right hC
      (show 0≤100*delta^(-eta)*rho*P.card by positivity)
    have hfinal : (C.card : ℝ)*(delta^(-eta)*(10*rho)^2*P.card)≤400*delta^(-eta)*rho*P.card := by
      nlinarith only [hC']
    exact hcount.trans (hsum.trans hfinal)
  · have hcard : ((physicalPairTube3 P rho z).card : ℝ)≤P.card :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
    have hmult := mul_le_mul_of_nonneg_right hK hrho.le
    have hfactor : 1≤400*delta^(-eta)*rho := by
      have hh : 1<10*rho := lt_of_not_ge hsmall
      nlinarith only [hh,hmult]
    exact hcard.trans (by
      have hh := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg P.card)
      simpa only [one_mul] using hh)

/-- The actual original rich tube gain and original 2-Frostman input give
the scale inequality behind (243), with a fixed explicit constant. -/
theorem original_rich_tube_scale_bound (P : Finset Point3) (z : Pair3)
    (delta eta rho zeta gamma A : ℝ) (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta)
    (hquery : delta≤rho) (hrho1 : rho≤1) (hA : 0≤A) (hP : P.Nonempty)
    (hbox : ∀ p∈P, ∀ i, |p i|≤1)
    (hfrostman : ∀ p∈P, ∀ R : ℝ, delta≤R → R≤1 →
      ((P.filter (fun q => distance3 p q≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card)
    (hgain : delta^(-(zeta-gamma))*rho^(2-gamma)*P.card≤A*(physicalPairTube3 P rho z).card) :
    rho^(1-gamma)≤400*A*delta^(zeta-gamma-eta) := by
  have hrho : 0<rho := hd.trans_le hquery
  have hcount := original_tube_two_frostman_count P z delta eta rho hd hd1 heta hquery hrho1 hbox hfrostman
  have h1 := hgain.trans (mul_le_mul_of_nonneg_left hcount hA)
  have hPp : 0<(P.card : ℝ) := by exact_mod_cast hP.card_pos
  have h2 : delta^(-(zeta-gamma))*rho^(2-gamma)≤400*A*delta^(-eta)*rho := by
    apply (mul_le_mul_iff_of_pos_right hPp).mp
    nlinarith only [h1]
  have hrpow : rho^(2-gamma)=rho^(1-gamma)*rho := by
    calc
      _ = rho^((1-gamma)+1) := by congr 1; ring
      _ = rho^(1-gamma)*rho^((1:ℝ)) := Real.rpow_add hrho _ _
      _ = _ := by rw [Real.rpow_one]
  rw [hrpow] at h2
  have h3 : delta^(-(zeta-gamma))*rho^(1-gamma)≤400*A*delta^(-eta) := by
    apply (mul_le_mul_iff_of_pos_right hrho).mp
    nlinarith only [h2]
  have he : delta^(-(zeta-gamma))*delta^(zeta-gamma-eta)=delta^(-eta) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  apply (mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos hd (-(zeta-gamma)))).mp
  calc
    _ ≤ 400*A*delta^(-eta) := h3
    _ = _ := by rw [← he]; ring

/-- A genuine source-independent cutoff makes the actual maximizing tube
width a positive power of the original mesh, uniformly for external eta
below half the fixed gain margin. -/
theorem exists_original_rich_tube_scale_cutoff (zeta gamma A : ℝ)
    (hgap : gamma<zeta) (hgamma : gamma<1) (hA : 0<A) :
    ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧
      ∀ delta : ℝ, 0<delta → delta≤delta0 → ∀ eta : ℝ, 0≤eta → eta≤(zeta-gamma)/2 →
      ∀ (P : Finset Point3) (z : Pair3) (rho : ℝ), P.Nonempty → delta≤rho → rho≤1 →
        (∀ p∈P, ∀ i, |p i|≤1) →
        (∀ p∈P, ∀ R : ℝ, delta≤R → R≤1 →
          ((P.filter (fun q => distance3 p q≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card) →
        delta^(-(zeta-gamma))*rho^(2-gamma)*P.card≤A*(physicalPairTube3 P rho z).card →
        rho≤delta^((zeta-gamma)/(4*(1-gamma))) := by
  have hg : 0<zeta-gamma := sub_pos.mpr hgap
  have hb : 0<1-gamma := sub_pos.mpr hgamma
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_small_power_cutoff
    (show 0<(zeta-gamma)/4 by positivity) (show 0<1/(400*A) by positivity)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall eta heta hetaMax P z rho hP hquery hrho1 hbox hfrostman hgain
  have hd1 := hsmall.trans hd01
  have hrho := hd.trans_le hquery
  have hscale := original_rich_tube_scale_bound P z delta eta rho zeta gamma A hd hd1 heta
    hquery hrho1 hA.le hP hbox hfrostman hgain
  have hpower := Real.rpow_le_rpow_of_exponent_ge hd hd1
    (show (zeta-gamma)/2≤zeta-gamma-eta by linarith only [hetaMax])
  have hconst := mul_le_mul_of_nonneg_left (hcut delta hd hsmall) (show 0≤400*A by positivity)
  have hid : (400*A)*(1/(400*A))=1 := by field_simp
  rw [hid] at hconst
  have hpowSplit : delta^((zeta-gamma)/2)=delta^((zeta-gamma)/4)*delta^((zeta-gamma)/4) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hbound : rho^(1-gamma)≤delta^((zeta-gamma)/4) := by
    have hh := hscale.trans (mul_le_mul_of_nonneg_left hpower (show 0≤400*A by positivity))
    rw [hpowSplit] at hh
    have hh' := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hd.le ((zeta-gamma)/4))
    nlinarith only [hh,hh']
  apply (Real.rpow_le_rpow_iff hrho.le (Real.rpow_nonneg hd.le _) hb).mp
  rw [← Real.rpow_mul hd.le]
  have he : (zeta-gamma)/(4*(1-gamma))*(1-gamma)=(zeta-gamma)/4 := by field_simp
  rw [he]
  exact hbound

end OriginalThreeDimensionalTubeFrostman
