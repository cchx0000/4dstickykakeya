import Theorems.Thm_StickyKakeya4_original_three_dimensional_slice_maximizer
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
namespace OriginalThreeDimensionalSmallSliceBranch
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalUnitSlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalSliceMaximizer
open OriginalPhysicalTubeScaleSelection

private theorem small_radius_ratio (D tau q e1 alpha : ℝ)
    (hD : 0<D) (htau : 0<tau) (hq : 0<q) (htop : tau≤D)
    (ha : 0≤alpha) (ha1 : alpha≤1) (hqtop : q≤2*D^e1) :
    D^(alpha*(1-e1))*tau≤2*D*(tau/q)^alpha := by
  have htp := Real.rpow_le_rpow_of_nonpos htau htop (show alpha-1≤0 by linarith only [ha1])
  rw [Real.rpow_sub_one hD.ne',Real.rpow_sub_one htau.ne'] at htp
  have htcross := (div_le_div_iff₀ hD htau).mp htp
  have htwo : (2:ℝ)^alpha≤2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) ha1
  have hqp : q^alpha≤2*D^(e1*alpha) := by
    have hh := Real.rpow_le_rpow hq.le hqtop ha
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hD.le e1),
      ← Real.rpow_mul hD.le] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hD.le (e1*alpha)))
  rw [Real.div_rpow htau.le hq.le,← mul_div_assoc]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hq alpha)).mpr
  have hp := mul_le_mul_of_nonneg_left hqp
    (show 0≤D^(alpha*(1-e1))*tau by positivity)
  have heq : (D^(alpha*(1-e1))*tau)*(2*D^(e1*alpha))=2*tau*D^alpha := by
    calc
      _ = 2*tau*(D^(alpha*(1-e1))*D^(e1*alpha)) := by ring
      _ = _ := by rw [← Real.rpow_add hD]; congr 2; ring
  rw [heq] at hp
  nlinarith only [hp,htcross]

private theorem small_radius_density (rho r D tau q eta1 e1 e2 alpha : ℝ)
    (hrho : 0<rho) (hr : 0<r) (hr1 : r≤1) (hD : 0<D)
    (hDrel : D=54*rho/r) (htau : 0<tau) (hq : 0<q) (htop : tau≤D)
    (ha : 0≤alpha) (ha1 : alpha≤1) (hqtop : q≤2*D^e1) :
    (r^2/108*rho^eta1*D^(e2+alpha*(1-e1)))*tau≤
      D^e2*rho^(1+eta1)*(tau/q)^alpha := by
  have hratio := small_radius_ratio D tau q e1 alpha hD htau hq htop ha ha1 hqtop
  have hscaled := mul_le_mul_of_nonneg_left hratio
    (show 0≤r/108*rho^eta1*D^e2 by positivity)
  have hDr : r*D=54*rho := by rw [hDrel]; field_simp
  have hpow : rho^(1+eta1)=rho*rho^eta1 := by rw [Real.rpow_add hrho,Real.rpow_one]
  have hpowD : D^(e2+alpha*(1-e1))=D^e2*D^(alpha*(1-e1)) := Real.rpow_add hD _ _
  have hmiddle : (r/108*rho^eta1*D^(e2+alpha*(1-e1)))*tau≤
      D^e2*rho^(1+eta1)*(tau/q)^alpha := by
    rw [hpow,hpowD]
    have hid : (r/108*rho^eta1*D^e2)*(2*D*(tau/q)^alpha)=
        D^e2*(rho*rho^eta1)*(tau/q)^alpha := by
      calc
        _ = (r*D)/54*(D^e2*rho^eta1*(tau/q)^alpha) := by ring
        _ = _ := by rw [hDr]; ring
    rw [hid] at hscaled
    nlinarith only [hscaled]
  have hr2 : r^2≤r := by nlinarith only [hr1,hr.le]
  have hh := mul_le_mul_of_nonneg_right hr2
    (show 0≤rho^eta1*D^(e2+alpha*(1-e1))*tau/108 by positivity)
  have hweak : (r^2/108*rho^eta1*D^(e2+alpha*(1-e1)))*tau≤
      (r/108*rho^eta1*D^(e2+alpha*(1-e1)))*tau := by nlinarith only [hh]
  exact hweak.trans hmiddle

/-- Original heavy-slab mass and actual concentrated slice points close
the small-radius branch of the genuine finite maximum. The large-radius
branch keeps its legal original annular half-mass. The explicit r squared
is retained for compatibility with the current direction extraction loss. -/
theorem exists_original_concentrated_slice_radius
    (P : Finset Point3) (z : Pair3) (rho r eta1 e1 e2 : ℝ)
    (d : DirectionLabel) (k : ℤ) (n M : ℕ)
    (hrho : 0<rho) (hr : 0<r) (hr1 : r≤1) (he1 : 0<e1) (he11 : e1≤1) (he2 : 0<e2)
    (halpha : 200*e2/e1≤1) (hmesh : rho=dyadicRadius n)
    (hcontract : (dyadicRadius M)^(200*e2/e1)≤1/2)
    (hrcut : r≤54*dyadicRadius M) (hDelta : 54*rho/r≤1) (hP : P.Nonempty)
    (hheavy : rho^(1+eta1)*(P.card : ℝ)≤(slabPoints P rho d k).card)
    (hconcentration :
      (54*rho/r)^e2*((enlargedSlice P rho d k (54*rho/r)).card : ℝ)≤
        (physicalPairTube3 (enlargedSlice P rho d k (54*rho/r)) ((54*rho/r)^e1) z).card) :
    let D := 54*rho/r
    let Q := enlargedSlice P rho d k D
    let alpha := 200*e2/e1
    let nu := r^2/108*rho^eta1*D^(e2+alpha*(1-e1))
    ∃ j : ℕ, j≤n ∧
      (∀ i≤n, sliceScore Q z alpha (dyadicRadius i)≤ sliceScore Q z alpha (dyadicRadius j)) ∧
      D^e2*(dyadicRadius j)^alpha≤(2*D^e1)^alpha ∧
      (dyadicRadius j≤D → nu*dyadicRadius j*P.card≤(physicalPairTube3 P (dyadicRadius j) z).card) ∧
      (D<dyadicRadius j → j+M≤n ∧
        ((physicalPairTube3 Q (dyadicRadius j) z).card : ℝ)/2≤
          ((physicalPairTube3 Q (dyadicRadius j) z\physicalPairTube3 Q (dyadicRadius (j+M)) z).card : ℝ)) := by
  let D := 54*rho/r
  let Q := enlargedSlice P rho d k D
  let alpha := 200*e2/e1
  have hD : 0<D := by dsimp [D]; positivity
  have hD1 : D≤1 := hDelta
  have ha : 0<alpha := by dsimp [alpha]; positivity
  have hDr : D*r=54*rho := by dsimp [D]; field_simp
  have hrhoD : 3*rho≤D := by nlinarith only [hDr,mul_le_mul_of_nonneg_left hr1 hD.le,hrho.le]
  have hslabQ : slabPoints P rho d k⊆Q := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
      (original_slab_in_unit_slab P rho d k hrho.le p hp).trans hrhoD⟩
  have hmass : rho^(1+eta1)*(P.card : ℝ)≤Q.card :=
    hheavy.trans (Nat.cast_le.mpr (Finset.card_le_card hslabQ))
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    have hPp : 0<(P.card : ℝ) := by exact_mod_cast hP.card_pos
    have hh : 0<(Q.card : ℝ) := (mul_pos (Real.rpow_pos_of_pos hrho _) hPp).trans_le hmass
    exact_mod_cast hh
  have hq : 0<D^e1 := Real.rpow_pos_of_pos hD e1
  have hq1 : D^e1≤1 := Real.rpow_le_one hD.le hD1 he1.le
  have hDq : D≤D^e1 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hD hD1 he11
  obtain ⟨j0,hj0,hqj0,hj0q⟩ := dyadic_radius_cover n (D^e1)
    (by rw [← hmesh]; linarith only [hrhoD,hDq,hq.le]) hq1
  have hconc : D^e2*(Q.card : ℝ)≤(physicalPairTube3 Q (dyadicRadius j0) z).card := by
    exact hconcentration.trans (Nat.cast_le.mpr (Finset.card_le_card
      (original_physical_tube3_mono Q z hqj0)))
  have hbottom : dyadicRadius n≤dyadicRadius M*D := by
    rw [← hmesh]
    have hh := mul_le_mul_of_nonneg_right hrcut hD.le
    nlinarith only [hh,hDr]
  obtain ⟨j,hj,hmax,hlower,hupper,hcases⟩ := exists_original_slice_maximizer_with_boundary
    P rho D d k z n M j0 alpha (D^e2) hj0 (Real.rpow_nonneg hD.le e2)
      hcontract hbottom hQ hconc
  have hp (i : ℕ) : 0<dyadicRadius i := by dsimp [dyadicRadius]; positivity
  refine ⟨j,hj,hmax,hupper.trans (Real.rpow_le_rpow (hp j0).le hj0q ha.le),?_,?_⟩
  · intro hsmall
    have hscalar := small_radius_density rho r D (dyadicRadius j) (dyadicRadius j0)
      eta1 e1 e2 alpha hrho hr hr1 hD rfl (hp j) (hp j0) hsmall ha.le halpha hj0q
    have h1 := mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg P.card)
    have h2 := mul_le_mul_of_nonneg_left hmass
      (mul_nonneg (Real.rpow_nonneg hD.le e2)
        (Real.rpow_nonneg (div_nonneg (hp j).le (hp j0).le) alpha))
    have hfull : ((physicalPairTube3 Q (dyadicRadius j) z).card : ℝ)≤
        (physicalPairTube3 P (dyadicRadius j) z).card := by
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro p hp'
      obtain ⟨hpQ,hptube⟩ := Finset.mem_filter.mp hp'
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpQ).1,hptube⟩
    have hl : D^e2*rho^(1+eta1)*(dyadicRadius j/dyadicRadius j0)^alpha*P.card≤
        (physicalPairTube3 Q (dyadicRadius j) z).card := by nlinarith only [h2,hlower]
    exact h1.trans (hl.trans hfull)
  · intro hlarge
    rcases hcases with hsmall|hgood
    · exact (not_le_of_gt hlarge hsmall).elim
    · exact hgood

end OriginalThreeDimensionalSmallSliceBranch
