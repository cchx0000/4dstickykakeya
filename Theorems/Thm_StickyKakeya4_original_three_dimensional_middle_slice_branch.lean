import Theorems.Thm_StickyKakeya4_original_three_dimensional_slice_maximizer
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
namespace OriginalThreeDimensionalMiddleSliceBranch
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalUnitSlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalSliceMaximizer OriginalPhysicalTubeScaleSelection

private theorem middle_radius_ratio (D tau q L e1 alpha : ℝ)
    (hD : 0 < D) (htau : 0 < tau) (hq : 0 < q) (hL : 1  ≤  L) (htop : tau  ≤  L*D)
    (ha : 0  ≤  alpha) (ha1 : alpha  ≤  1) (hqtop : q  ≤  2*D^e1) :
    D^(alpha*(1-e1))*tau  ≤  2*L*D*(tau/q)^alpha := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have htp := Real.rpow_le_rpow_of_nonpos htau htop (show alpha-1  ≤  0 by linarith only [ha1])
  have hLpow : 1/L  ≤  L^(alpha-1) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hL (show (-1:ℝ)  ≤  alpha-1 by linarith only [ha])
    simpa only [Real.rpow_neg_one,one_div] using hh
  have hprod := mul_le_mul_of_nonneg_right hLpow (Real.rpow_nonneg hD.le (alpha-1))
  rw [← Real.mul_rpow hLp.le hD.le] at hprod
  have hprod' := hprod.trans htp
  have hscaled := mul_le_mul_of_nonneg_left hprod' hLp.le
  have he : L*((1/L)*D^(alpha-1))=D^(alpha-1) := by field_simp
  rw [he,Real.rpow_sub_one hD.ne',Real.rpow_sub_one htau.ne',← mul_div_assoc] at hscaled
  have htcross := (div_le_div_iff₀ hD htau).mp hscaled
  have htwo : (2:ℝ)^alpha  ≤  2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)  ≤  2) ha1
  have hqp : q^alpha  ≤  2*D^(e1*alpha) := by
    have hh := Real.rpow_le_rpow hq.le hqtop ha
    rw [Real.mul_rpow (by norm_num : (0:ℝ)  ≤  2) (Real.rpow_nonneg hD.le e1),← Real.rpow_mul hD.le] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hD.le (e1*alpha)))
  rw [Real.div_rpow htau.le hq.le,← mul_div_assoc]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hq alpha)).mpr
  have hp := mul_le_mul_of_nonneg_left hqp (show 0  ≤  D^(alpha*(1-e1))*tau by positivity)
  have heq : (D^(alpha*(1-e1))*tau)*(2*D^(e1*alpha))=2*tau*D^alpha := by
    calc
      _ = 2*tau*(D^(alpha*(1-e1))*D^(e1*alpha)) := by ring
      _ = _ := by rw [← Real.rpow_add hD]; congr 2; ring
  rw [heq] at hp
  nlinarith only [hp,htcross]

private theorem middle_radius_density (rho r D tau q L eta1 e1 e2 alpha : ℝ)
    (hrho : 0 < rho) (hr : 0 < r) (hr1 : r  ≤  1) (hD : 0 < D) (hL : 1  ≤  L)
    (hDrel : D=54*rho/r) (htau : 0 < tau) (hq : 0 < q) (htop : tau  ≤  L*D)
    (ha : 0  ≤  alpha) (ha1 : alpha  ≤  1) (hqtop : q  ≤  2*D^e1) :
    (r^2/(108*L)*rho^eta1*D^(e2+alpha*(1-e1)))*tau  ≤  
      D^e2*rho^(1+eta1)*(tau/q)^alpha := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hratio := middle_radius_ratio D tau q L e1 alpha hD htau hq hL htop ha ha1 hqtop
  have hscaled := mul_le_mul_of_nonneg_left hratio (show 0  ≤  r/(108*L)*rho^eta1*D^e2 by positivity)
  have hDr : r*D=54*rho := by rw [hDrel]; field_simp
  have hpow : rho^(1+eta1)=rho*rho^eta1 := by rw [Real.rpow_add hrho,Real.rpow_one]
  have hpowD : D^(e2+alpha*(1-e1))=D^e2*D^(alpha*(1-e1)) := Real.rpow_add hD _ _
  have hmiddle : (r/(108*L)*rho^eta1*D^(e2+alpha*(1-e1)))*tau  ≤  
      D^e2*rho^(1+eta1)*(tau/q)^alpha := by
    rw [hpow,hpowD]
    have hid : (r/(108*L)*rho^eta1*D^e2)*(2*L*D*(tau/q)^alpha)=
        D^e2*(rho*rho^eta1)*(tau/q)^alpha := by
      calc
        _ = (r*D)/54*(D^e2*rho^eta1*(tau/q)^alpha) := by field_simp; ring
        _ = _ := by rw [hDr]; ring
    rw [hid] at hscaled
    nlinarith only [hscaled]
  have hr2 : r^2  ≤  r := by nlinarith only [hr1,hr.le]
  have hh := mul_le_mul_of_nonneg_right hr2
    (show 0  ≤  rho^eta1*D^(e2+alpha*(1-e1))*tau/(108*L) by positivity)
  have hweak : (r^2/(108*L)*rho^eta1*D^(e2+alpha*(1-e1)))*tau  ≤  
      (r/(108*L)*rho^eta1*D^(e2+alpha*(1-e1)))*tau := by
    simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  exact hweak.trans hmiddle

/-- The actual finite maximum also closes every fixed multiple of the
small-radius range. In particular L=300/c_alpha covers the region where
the sharp angular threshold exceeds the cap theorem's upper range. -/
theorem original_selected_middle_slice_population
    (P : Finset Point3) (z : Pair3) (rho r eta1 e1 e2 L : ℝ)
    (d : DirectionLabel) (k : ℤ) (n j : ℕ)
    (hrho : 0 < rho) (hr : 0 < r) (hr1 : r  ≤  1) (he1 : 0 < e1) (he11 : e1  ≤  1)
    (he2 : 0 < e2) (halpha : 200*e2/e1  ≤  1) (hL : 1  ≤  L)
    (hmesh : rho=dyadicRadius n) (hDelta : 54*rho/r  ≤  1)
    (hheavy : rho^(1+eta1)*(P.card : ℝ)  ≤  (slabPoints P rho d k).card)
    (hconcentration : (54*rho/r)^e2*((enlargedSlice P rho d k (54*rho/r)).card : ℝ)  ≤  
      (physicalPairTube3 (enlargedSlice P rho d k (54*rho/r)) ((54*rho/r)^e1) z).card)
    (hmax : ∀ i  ≤  n, sliceScore (enlargedSlice P rho d k (54*rho/r)) z (200*e2/e1) (dyadicRadius i)  ≤  
      sliceScore (enlargedSlice P rho d k (54*rho/r)) z (200*e2/e1) (dyadicRadius j))
    (hmiddle : dyadicRadius j  ≤  L*(54*rho/r)) :
    (r^2/(108*L)*rho^eta1*(54*rho/r)^(e2+(200*e2/e1)*(1-e1)))*dyadicRadius j*P.card  ≤  
      (physicalPairTube3 P (dyadicRadius j) z).card := by
  let D := 54*rho/r
  let Q := enlargedSlice P rho d k D
  let alpha := 200*e2/e1
  have hD : 0 < D := by dsimp [D]; positivity
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hp (i : ℕ) : 0 < dyadicRadius i := by dsimp [dyadicRadius]; positivity
  have hDr : D*r=54*rho := by dsimp [D]; field_simp
  have hrhoD : 3*rho  ≤  D := by nlinarith only [hDr,mul_le_mul_of_nonneg_left hr1 hD.le,hrho.le]
  have hsub : slabPoints P rho d k⊆Q := by
    intro p hps
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hps).1,
      (original_slab_in_unit_slab P rho d k hrho.le p hps).trans hrhoD⟩
  have hmass : rho^(1+eta1)*(P.card : ℝ)  ≤  Q.card :=
    hheavy.trans (Nat.cast_le.mpr (Finset.card_le_card hsub))
  have hq : 0 < D^e1 := Real.rpow_pos_of_pos hD e1
  have hq1 : D^e1  ≤  1 := Real.rpow_le_one hD.le hDelta he1.le
  have hDq : D  ≤  D^e1 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hD hDelta he11
  obtain ⟨j0,hj0,hqj0,hj0q⟩ := dyadic_radius_cover n (D^e1)
    (by rw [← hmesh]; linarith only [hrhoD,hDq,hq.le]) hq1
  have hconc : D^e2*(Q.card : ℝ)  ≤  (physicalPairTube3 Q (dyadicRadius j0) z).card :=
    hconcentration.trans (Nat.cast_le.mpr (Finset.card_le_card (original_physical_tube3_mono Q z hqj0)))
  have hcross := (div_le_div_iff₀ (Real.rpow_pos_of_pos (hp j0) alpha)
    (Real.rpow_pos_of_pos (hp j) alpha)).mp (hmax j0 hj0)
  have hpop := mul_le_mul_of_nonneg_right hconc (Real.rpow_nonneg (hp j).le alpha)
  have hlower : D^e2*(Q.card : ℝ)*(dyadicRadius j/dyadicRadius j0)^alpha  ≤  
      (physicalPairTube3 Q (dyadicRadius j) z).card := by
    rw [Real.div_rpow (hp j).le (hp j0).le,← mul_div_assoc]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (hp j0) alpha)).mpr
    exact hpop.trans hcross
  have hscalar := middle_radius_density rho r D (dyadicRadius j) (dyadicRadius j0) L eta1 e1 e2 alpha
    hrho hr hr1 hD hL rfl (hp j) (hp j0) hmiddle ha.le halpha hj0q
  have h1 := mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg P.card)
  have h2 := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg (Real.rpow_nonneg hD.le e2) (Real.rpow_nonneg (div_nonneg (hp j).le (hp j0).le) alpha))
  have hfull : ((physicalPairTube3 Q (dyadicRadius j) z).card : ℝ)  ≤  (physicalPairTube3 P (dyadicRadius j) z).card := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro p hp'
    obtain ⟨hpQ,hptube⟩ := Finset.mem_filter.mp hp'
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpQ).1,hptube⟩
  have hh : D^e2*rho^(1+eta1)*(dyadicRadius j/dyadicRadius j0)^alpha*P.card  ≤  
      (physicalPairTube3 Q (dyadicRadius j) z).card := by nlinarith only [h2,hlower]
  exact h1.trans (hh.trans hfull)

end OriginalThreeDimensionalMiddleSliceBranch
