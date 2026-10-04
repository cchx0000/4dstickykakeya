import Theorems.Thm_StickyKakeya4_original_three_dimensional_native_reinforcement_budget
import Theorems.Thm_StickyKakeya4_native_original_grid_balanced_fibers
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

noncomputable section
namespace OriginalThreeDimensionalOwnerCoefficientBudget
open OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalAveragedSliceEnergy OriginalThreeDimensionalRegularizedMarkedSlice
open OriginalThreeDimensionalSliceParameterChoice OriginalPhysicalTubeScaleSelection
open OriginalThreeDimensionalGridBalancedFibers OriginalThreeDimensionalCoverBallUniformity
open OriginalThreeDimensionalGridUniformity OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalUniformBallCover NativeQuarterScaleParameters

/-- The actual original graph and original logarithmic menu bound control
E/L. This calculation retains every Delta/rho and original mass factor. -/
theorem original_owner_energy_ratio_bound (P : Finset Point3) (G : Finset Pair3)
    (delta rho eta : ℝ) (N : ℕ) (hd : 0 < delta) (hrho : 0 < rho) (hP : P.Nonempty)
    (hdense : delta^(2*eta)*(P.card : ℝ)^2 ≤ G.card)
    (hmenu : (N:ℝ)+1 ≤ delta^(-eta)) :
    let Delta := 54*rho/delta^(2*eta)
    let E := energyBudget P rho Delta (delta^(-eta)) N
    let L := (1/(8*rho))*(G.card : ℝ)
    E/L ≤ 67184640000*delta^(-8*eta) := by
  let r := delta^(2*eta)
  let Delta := 54*rho/r
  let E := energyBudget P rho Delta (delta^(-eta)) N
  let L := (1/(8*rho))*(G.card : ℝ)
  let C : ℝ := 67184640000
  have hpc : (0:ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hgc : (0:ℝ) < G.card := (show 0 < delta^(2*eta)*(P.card : ℝ)^2 by positivity).trans_le hdense
  have hr : 0 < r := by dsimp [r]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have he : E*(8*rho*r^2)=C*((N:ℝ)+1)*delta^(-eta)*(P.card : ℝ)^2 := by
    dsimp [E,energyBudget,Delta,C]
    field_simp
    ring
  have hp0 : delta^(-eta)*delta^(-eta)=delta^(-2*eta) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hp1 : delta^(-8*eta)*r^2=delta^(-4*eta) := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast hd.le,← Real.rpow_add hd]
    congr 1
    ring
  have hp2 : delta^(-4*eta)*delta^(2*eta)=delta^(-2*eta) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hupper : E*(8*rho*r^2) ≤ C*delta^(-2*eta)*(P.card : ℝ)^2 := by
    rw [he]
    calc
      _ ≤ C*delta^(-eta)*delta^(-eta)*(P.card : ℝ)^2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmenu (by dsimp [C]; norm_num))
            (Real.rpow_nonneg hd.le (-eta))) (sq_nonneg (P.card : ℝ))
      _ = _ := by rw [mul_assoc C, hp0]
  have hlower : C*delta^(-2*eta)*(P.card : ℝ)^2 ≤ C*delta^(-4*eta)*G.card := by
    have hh := mul_le_mul_of_nonneg_left hdense (show 0 ≤ C*delta^(-4*eta) by dsimp [C]; positivity)
    calc
      _ = (C*delta^(-4*eta))*(delta^(2*eta)*(P.card : ℝ)^2) := by rw [← hp2]; ring
      _ ≤ _ := hh
  have hright : (C*delta^(-8*eta)*L)*(8*rho*r^2)=C*delta^(-4*eta)*G.card := by
    calc
      _ = C*(delta^(-8*eta)*r^2)*G.card := by dsimp [L]; field_simp
      _ = _ := by rw [hp1]
  apply (div_le_iff₀ hL).mpr
  apply (mul_le_mul_iff_of_pos_right (show 0 < 8*rho*r^2 by positivity)).mp
  change E*(8*rho*r^2) ≤ (C*delta^(-8*eta)*L)*(8*rho*r^2)
  rw [hright]
  exact hupper.trans hlower

/-- The exact factors occurring in the constructed owner output have
explicit power losses once the two genuine source coefficients are paid. -/
theorem original_owner_power_coefficients (delta eta A R : ℝ) (hd : 0 < delta)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hAb : A ≤ delta^(-2*eta))
    (hRb : R ≤ delta^(-9*eta)) (hconst : 4096*delta^eta ≤ 1) :
    32*A*R ≤ delta^(-12*eta) ∧ 4096*A*R^2 ≤ delta^(-21*eta) ∧
      32*R*A^2 ≤ delta^(-14*eta) := by
  have absorb (C b : ℝ) (hC : C ≤ 4096) : C*delta^b ≤ delta^(b-eta) := by
    have hs := (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hd.le eta)).trans hconst
    have hh := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hd.le (b-eta))
    have he : delta^eta*delta^(b-eta)=delta^b := by rw [← Real.rpow_add hd]; congr 1; ring
    simpa only [mul_assoc,he,one_mul] using hh
  have hAR : A*R ≤ delta^(-11*eta) := by
    calc
      _ ≤ delta^(-2*eta)*delta^(-9*eta) := mul_le_mul hAb hRb hR (by positivity)
      _ = _ := by rw [← Real.rpow_add hd]; congr 1; ring
  have hAR2 : A*R^2 ≤ delta^(-20*eta) := by
    calc
      _ ≤ delta^(-2*eta)*(delta^(-9*eta))^2 :=
        mul_le_mul hAb (pow_le_pow_left₀ hR hRb 2) (sq_nonneg R) (by positivity)
      _ = _ := by rw [← Real.rpow_mul_natCast hd.le,← Real.rpow_add hd]; congr 1; ring
  have hRA2 : R*A^2 ≤ delta^(-13*eta) := by
    calc
      _ ≤ delta^(-9*eta)*(delta^(-2*eta))^2 :=
        mul_le_mul hRb (pow_le_pow_left₀ hA hAb 2) (sq_nonneg A) (by positivity)
      _ = _ := by rw [← Real.rpow_mul_natCast hd.le,← Real.rpow_add hd]; congr 1; ring
  refine ⟨?_,?_,?_⟩
  · have hh := (mul_le_mul_of_nonneg_left hAR (by norm_num : (0:ℝ) ≤ 32)).trans
      (absorb 32 (-11*eta) (by norm_num))
    have he : -11*eta-eta= -12*eta := by ring
    simpa only [mul_assoc,he] using hh
  · have hh := (mul_le_mul_of_nonneg_left hAR2 (by norm_num : (0:ℝ) ≤ 4096)).trans
      (absorb 4096 (-20*eta) le_rfl)
    have he : -20*eta-eta= -21*eta := by ring
    simpa only [mul_assoc,he] using hh
  · have hh := (mul_le_mul_of_nonneg_left hRA2 (by norm_num : (0:ℝ) ≤ 32)).trans
      (absorb 32 (-13*eta) (by norm_num))
    have he : -13*eta-eta= -14*eta := by ring
    simpa only [mul_assoc,he] using hh

/-- Fixed positive internal eta is chosen BEFORE this mesh cutoff. No
uniform cutoff is claimed while eta tends to zero. The original graph
and actual original-scale menu pay both the energy and full-fiber factors. -/
theorem exists_original_owner_coefficient_cutoff (eta : ℝ) (heta : 0 < eta) :
    ∃ delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ,0 < delta → delta ≤ delta0 →
      ∀ (P : Finset Point3) (G : Finset Pair3) (rho : ℝ) (N : ℕ),
        P.Nonempty → 0 < rho → delta ≤ dyadicRadius N →
        delta^(2*eta)*(P.card : ℝ)^2 ≤ G.card →
        let Delta := 54*rho/delta^(2*eta)
        let E := energyBudget P rho Delta (delta^(-eta)) N
        let L := (1/(8*rho))*(G.card : ℝ)
        E/L ≤ delta^(-9*eta) ∧
          uniformFiberConstant (delta^(-eta)) ≤ delta^(-2*eta) ∧
          4096*delta^eta ≤ 1 := by
  let C : ℝ := 67184640000+uniformFiberConstant 1+4096
  have hA : 0 ≤ uniformFiberConstant 1 := by unfold uniformFiberConstant; positivity
  have hC : 0 < C := by dsimp [C]; linarith only [hA]
  obtain ⟨dM,hdM,hdM1,hM⟩ := exists_original_coarse_menu_cutoff eta heta
  obtain ⟨dC,hdC,_hdC1,hCut⟩ := exists_small_power_cutoff heta (one_div_pos.mpr hC)
  refine ⟨min dM dC,lt_min hdM hdC,(min_le_left _ _).trans hdM1,?_⟩
  intro delta hd hsmall P G rho N hP hrho hquery hdense
  have hconst : C*delta^eta ≤ 1 := by
    have hh := (le_div_iff₀ hC).mp (hCut delta hd (hsmall.trans (min_le_right _ _)))
    nlinarith only [hh]
  have hC1 : 67184640000 ≤ C := by dsimp [C]; linarith only [hA]
  have hC2 : uniformFiberConstant 1 ≤ C := by dsimp [C]; linarith
  have hC3 : 4096 ≤ C := by dsimp [C]; linarith only [hA]
  have hpower (a b : ℝ) (ha : a ≤ C) : a*delta^b ≤ delta^(b-eta) := by
    have hs := (mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hd.le eta)).trans hconst
    have hh := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hd.le (b-eta))
    have he : delta^eta*delta^(b-eta)=delta^b := by rw [← Real.rpow_add hd]; congr 1; ring
    simpa only [mul_assoc,he,one_mul] using hh
  have hraw := original_owner_energy_ratio_bound P G delta rho eta N hd hrho hP hdense
    (hM delta hd (hsmall.trans (min_le_left _ _)) N hquery)
  refine ⟨hraw.trans ?_,?_,(mul_le_mul_of_nonneg_right hC3 (Real.rpow_nonneg hd.le eta)).trans hconst⟩
  · convert hpower 67184640000 (-8*eta) hC1 using 1; congr 1; ring
  · have he : uniformFiberConstant (delta^(-eta))=uniformFiberConstant 1*delta^(-eta) := by
      unfold uniformFiberConstant
      ring
    rw [he]
    convert hpower (uniformFiberConstant 1) (-eta) hC2 using 1; congr 1; ring


/-- Every smaller EXTERNAL source exponent is dominated by one fixed
internal exponent. The original grid convention, pair labels, pair gap,
and graph mass are all retained; the mesh cutoff can therefore depend
on that fixed internal exponent without varying with the source. -/
theorem original_source_to_fixed_internal_eta (P : Finset Point3) (G : Finset Pair3)
    (delta etaSource etaInternal : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (heta : etaSource ≤ etaInternal)
    (huniform : OriginalGridUniform P delta (delta^(-etaSource)))
    (hfrostman : ∀ p∈P,∀ R : ℝ,delta ≤ R → R ≤ 1 →
      ((P.filter (fun x => distance3 p x ≤ R)).card : ℝ) ≤ delta^(-etaSource)*R^2*P.card)
    (hdense : delta^etaSource*(P.card : ℝ)^2 ≤ G.card)
    (hsep : ∀ z∈G,delta^(2*etaSource) ≤ distance3 z.1 z.2) :
    OriginalGridUniform P delta (delta^(-etaInternal)) ∧
      (∀ p∈P,∀ R : ℝ,delta ≤ R → R ≤ 1 →
        ((P.filter (fun x => distance3 p x ≤ R)).card : ℝ) ≤ delta^(-etaInternal)*R^2*P.card) ∧
      delta^etaInternal*(P.card : ℝ)^2 ≤ G.card ∧
      ∀ z∈G,delta^(2*etaInternal) ≤ distance3 z.1 z.2 := by
  have hcoefficient : delta^(-etaSource) ≤ delta^(-etaInternal) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith only [heta])
  refine ⟨?_,?_,?_,?_⟩
  · intro a ha b hb R hR hR1
    exact (huniform a ha b hb R hR hR1).trans
      (mul_le_mul_of_nonneg_right hcoefficient (Nat.cast_nonneg _))
  · intro p hp R hR hR1
    exact (hfrostman p hp R hR hR1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg R))
        (Nat.cast_nonneg P.card))
  · exact (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 heta) (sq_nonneg (P.card : ℝ))).trans hdense
  · intro z hz
    exact (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith only [heta])).trans (hsep z hz)

end OriginalThreeDimensionalOwnerCoefficientBudget
