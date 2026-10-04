import Theorems.Thm_StickyKakeya4_original_three_dimensional_annular_slab_charge
import Theorems.Thm_StickyKakeya4_original_three_dimensional_separated_normals
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000

noncomputable section
open scoped Matrix BigOperators
namespace OriginalThreeDimensionalLargeSlicePopulation
open Classical Matrix OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalUnitSlabs OriginalThreeDimensionalUnitNormals
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalSliceMaximizer OriginalThreeDimensionalSeparatedNormals
open OriginalThreeDimensionalAnnularSlabCharge OriginalPhysicalTubeScaleSelection

private theorem large_baseline_ratio (D tau q e1 alpha : ℝ)
    (hD : 0 < D) (htau : 0 < tau) (hq : 0 < q) (hlarge : D ≤ tau)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hqtop : q ≤ 2*D^e1) :
    D^(alpha*(1-e1)) ≤ 2*(tau/q)^alpha := by
  have htwo : (2:ℝ)^alpha ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ha1
  have hqp : q^alpha ≤ 2*D^(e1*alpha) := by
    have hh := Real.rpow_le_rpow hq.le hqtop ha
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hD.le e1),← Real.rpow_mul hD.le] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hD.le (e1*alpha)))
  have htp := Real.rpow_le_rpow hD.le hlarge ha
  rw [Real.div_rpow htau.le hq.le,← mul_div_assoc]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hq alpha)).mpr
  have hh := mul_le_mul_of_nonneg_left hqp (Real.rpow_nonneg hD.le (alpha*(1-e1)))
  have he : D^(alpha*(1-e1))*(2*D^(e1*alpha))=2*D^alpha := by
    calc
      _ = 2*(D^(alpha*(1-e1))*D^(e1*alpha)) := by ring
      _ = _ := by rw [← Real.rpow_add hD]; congr 2; ring
  rw [he] at hh
  linarith only [hh,htp]

/-- Actual original concentration and the two genuine maximizing-radius
comparisons force an annular source population. No annular mass is an
input; the original heavy slab and original point set are retained. -/
theorem original_common_radius_annular_population
    (P : Finset Point3) (z : Pair3) (d : DirectionLabel) (k : ℤ)
    (rho D tau c q eta1 e1 e2 alpha : ℝ)
    (hrho : 0 < rho) (hD : 0 < D) (htau : 0 < tau) (hc : 0 < c) (hc1 : c ≤ 1)
    (hq : 0 < q) (hwidth : 3*rho ≤ D) (hlarge : D ≤ tau)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hcontract : c^alpha ≤ 1/2)
    (hqlo : D^e1 ≤ q) (hqtop : q ≤ 2*D^e1)
    (hheavy : rho^(1+eta1)*(P.card : ℝ) ≤ (slabPoints P rho d k).card)
    (hconc : D^e2*((enlargedSlice P rho d k D).card : ℝ) ≤
      (physicalPairTube3 (enlargedSlice P rho d k D) (D^e1) z).card)
    (hmax : sliceScore (enlargedSlice P rho d k D) z alpha q ≤
      sliceScore (enlargedSlice P rho d k D) z alpha tau)
    (hinner : sliceScore (enlargedSlice P rho d k D) z alpha (tau*c) ≤
      sliceScore (enlargedSlice P rho d k D) z alpha tau) :
    rho^(1+eta1)*D^(e2+alpha*(1-e1))*P.card ≤
      4*((sliceAnnulus P rho D tau (tau*c) z d k).card : ℝ) := by
  let Q := enlargedSlice P rho d k D
  have hsub : slabPoints P rho d k ⊆ Q := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
      (original_slab_in_unit_slab P rho d k hrho.le p hp).trans hwidth⟩
  have hmass : rho^(1+eta1)*(P.card : ℝ) ≤ Q.card :=
    hheavy.trans (Nat.cast_le.mpr (Finset.card_le_card hsub))
  have hconc' : D^e2*(Q.card : ℝ) ≤ (physicalPairTube3 Q q z).card :=
    hconc.trans (Nat.cast_le.mpr (Finset.card_le_card (original_physical_tube3_mono Q z hqlo)))
  have hcross := (div_le_div_iff₀ (Real.rpow_pos_of_pos hq alpha) (Real.rpow_pos_of_pos htau alpha)).mp hmax
  have hpop := mul_le_mul_of_nonneg_right hconc' (Real.rpow_nonneg htau.le alpha)
  have hlower : D^e2*(Q.card : ℝ)*(tau/q)^alpha ≤ (physicalPairTube3 Q tau z).card := by
    rw [Real.div_rpow htau.le hq.le,← mul_div_assoc]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hq alpha)).mpr
    exact hpop.trans hcross
  have hratio := large_baseline_ratio D tau q e1 alpha hD htau hq hlarge ha ha1 hqtop
  have h1 := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg (Real.rpow_nonneg hD.le e2) (Real.rpow_nonneg (div_nonneg htau.le hq.le) alpha))
  have h2 := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ D^e2*rho^(1+eta1)*P.card by positivity)
  have hhalf := original_slice_annular_half_mass Q z alpha tau c htau hc hc1 hcontract hinner
  have hpow : D^(e2+alpha*(1-e1))=D^e2*D^(alpha*(1-e1)) := Real.rpow_add hD _ _
  change rho^(1+eta1)*D^(e2+alpha*(1-e1))*P.card ≤ 4*((physicalPairTube3 Q tau z\physicalPairTube3 Q (tau*c) z).card : ℝ)
  rw [hpow]
  nlinarith only [h1,h2,hlower,hhalf]

/-- An actual common-radius incidence subfamily gives an actual original
tube population. The cap and angular subfamily are constructed here from
the literal pair band. The cardinality of that original incidence family
is retained explicitly for the subsequent genuine menu pigeonhole. -/
theorem original_large_common_slice_population
    (P : Finset Point3) (z : Pair3) (S : Finset DirectionLabel) (k : DirectionLabel→ℤ)
    (rho r eta1 e1 e2 : ℝ) (n M j : ℕ)
    (hrho : 0 < rho) (hr : 0 < r) (hr1 : r ≤ 1) (he1 : 0 < e1) (he11 : e1 ≤ 1)
    (he2 : 0 < e2) (halpha : 200*e2/e1 ≤ 1) (hmesh : rho=dyadicRadius n)
    (hcontract : (dyadicRadius M)^(200*e2/e1) ≤ 1/2) (hDelta : 54*rho/r ≤ 1)
    (hlarge : 300*(54*rho/r)/dyadicRadius M ≤ dyadicRadius j)
    (hbox : ∀ p∈P, ∀ i, |p i| ≤ 1) (hzP : z∈P.product P) (hsep : r ≤ distance3 z.1 z.2)
    (hS : S ⊆ pairBand rho z.1 z.2)
    (hslabs : ∀ d∈S, z.1∈slabPoints P rho d (k d) ∧ z.2∈slabPoints P rho d (k d))
    (hheavy : ∀ d∈S, rho^(1+eta1)*(P.card : ℝ) ≤ (slabPoints P rho d (k d)).card)
    (hconc : ∀ d∈S, (54*rho/r)^e2*((enlargedSlice P rho d (k d) (54*rho/r)).card : ℝ) ≤
      (physicalPairTube3 (enlargedSlice P rho d (k d) (54*rho/r)) ((54*rho/r)^e1) z).card)
    (hmax : ∀ d∈S, ∀ i ≤ n,
      sliceScore (enlargedSlice P rho d (k d) (54*rho/r)) z (200*e2/e1) (dyadicRadius i) ≤
      sliceScore (enlargedSlice P rho d (k d) (54*rho/r)) z (200*e2/e1) (dyadicRadius j)) :
    (S.card : ℝ)*rho*(dyadicRadius M*r^2/4665600000*rho^eta1*
      (54*rho/r)^(e2+(200*e2/e1)*(1-e1)))*dyadicRadius j*P.card ≤
      (physicalPairTube3 P (dyadicRadius j) z).card := by
  let D := 54*rho/r
  let tau := dyadicRadius j
  let c := dyadicRadius M
  let alpha := 200*e2/e1
  let E := e2+alpha*(1-e1)
  let g := 30*D/(tau*c)
  have hD : 0 < D := by dsimp [D]; positivity
  have htau : 0 < tau := by dsimp [tau,dyadicRadius]; positivity
  have hc : 0 < c := by dsimp [c,dyadicRadius]; positivity
  have htau1 : tau ≤ 1 := by dsimp [tau,dyadicRadius]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hc1 : c ≤ 1 := by dsimp [c,dyadicRadius]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hDr : D*r=54*rho := by dsimp [D]; field_simp
  have hwidth : 3*rho ≤ D := by nlinarith only [hDr,mul_le_mul_of_nonneg_left hr1 hD.le,hrho.le]
  have hlarge' : 300*D ≤ tau*c := (div_le_iff₀ hc).mp hlarge
  have htc : tau*c ≤ 1 := mul_le_one₀ htau1 hc.le hc1
  have hDlt : D < tau := by
    have hh := mul_le_mul_of_nonneg_left hc1 htau.le
    nlinarith only [hlarge',hh,hD]
  have hinnerIndex : j+M ≤ n := by
    by_contra hh
    have hp : dyadicRadius (j+M) ≤ dyadicRadius n := by
      dsimp [dyadicRadius]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have he : dyadicRadius (j+M)=tau*c := pow_add _ _ _
    rw [he,← hmesh] at hp
    nlinarith only [hp,hlarge',hwidth,hrho]
  have hg : 0 < g := by dsimp [g]; positivity
  have hgrho : rho ≤ g := by
    dsimp [g]
    apply (le_div_iff₀ (mul_pos htau hc)).mpr
    have hh := mul_le_mul_of_nonneg_left htc hrho.le
    nlinarith only [hh,hwidth,hrho.le]
  have hgsmall : g ≤ 1/10 := by
    dsimp [g]
    apply (div_le_iff₀ (mul_pos htau hc)).mpr
    linarith only [hlarge']
  obtain ⟨hpP,hqP⟩ := Finset.mem_product.mp hzP
  obtain ⟨C,hCS,hCsep,hcover⟩ := actual_unoriented_net S rho g hg
  have hcover' : S ⊆ C.biUnion (fun d => doubleCap S rho g (unitNormal rho d)) := by
    intro e he
    obtain ⟨d,hd,hclose⟩ := hcover e he
    exact Finset.mem_biUnion.mpr ⟨d,hd,Finset.mem_filter.mpr ⟨he,hclose.imp le_of_lt le_of_lt⟩⟩
  have hcaps : ∀ d∈C, ((doubleCap S rho g (unitNormal rho d)).card : ℝ)*(rho*r) ≤ 720000*g := by
    intro d _hd
    have hh := original_double_cap_count S rho g r z.1 z.2 (unitNormal rho d)
      hrho hgrho hgsmall hr hsep (hbox _ hpP) (hbox _ hqP) (original_unit_normal_square rho d) hS
    nlinarith only [hh]
  have hnet := weighted_cover_count S C (fun d => doubleCap S rho g (unitNormal rho d))
    (rho*r) (720000*g) (by positivity) hcover' hcaps
  have hq : 0 < D^e1 := Real.rpow_pos_of_pos hD e1
  have hq1 : D^e1 ≤ 1 := Real.rpow_le_one hD.le hDelta he1.le
  have hDq : D ≤ D^e1 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hD hDelta he11
  obtain ⟨j0,hj0,hqj0,hj0q⟩ := dyadic_radius_cover n (D^e1)
    (by rw [← hmesh]; linarith only [hwidth,hDq,hq.le]) hq1
  have hp (i : ℕ) : 0 < dyadicRadius i := by dsimp [dyadicRadius]; positivity
  have hinnerEq : dyadicRadius (j+M)=tau*c := pow_add _ _ _
  have hAnn (d : DirectionLabel) (hd : d∈C) :
      rho^(1+eta1)*D^E*P.card ≤ 4*((sliceAnnulus P rho D tau (tau*c) z d (k d)).card : ℝ) := by
    exact original_common_radius_annular_population P z d (k d) rho D tau c (dyadicRadius j0)
      eta1 e1 e2 alpha hrho hD htau hc hc1 (hp j0) hwidth hDlt.le ha.le halpha hcontract hqj0 hj0q
      (hheavy d (hCS hd)) (hconc d (hCS hd)) (hmax d (hCS hd) j0 hj0)
      (by simpa only [hinnerEq] using hmax d (hCS hd) (j+M) hinnerIndex)
  have hcharge := original_separated_annular_slab_sum P z C k rho D r tau (tau*c)
    hrho.le hD hr (mul_pos htau hc) hwidth hDr.ge hbox hsep
    (fun d hd => hslabs d (hCS hd)) (fun d hd e he hde => hCsep d hd e he hde)
  have hchargeR : (∑ d∈C, ((sliceAnnulus P rho D tau (tau*c) z d (k d)).card : ℝ)) ≤
      (physicalPairTube3 P tau z).card := by exact_mod_cast hcharge
  have hsum : (C.card : ℝ)*(rho^(1+eta1)*D^E*P.card) ≤ 4*(physicalPairTube3 P tau z).card := by
    calc
      _ = ∑ _d∈C, (rho^(1+eta1)*D^E*P.card) := by simp
      _ ≤ ∑ d∈C, 4*((sliceAnnulus P rho D tau (tau*c) z d (k d)).card : ℝ) := Finset.sum_le_sum hAnn
      _ = 4*∑ d∈C, ((sliceAnnulus P rho D tau (tau*c) z d (k d)).card : ℝ) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hchargeR (by norm_num)
  have hnet' := mul_le_mul_of_nonneg_right hnet (show 0 ≤ rho^(1+eta1)*D^E*P.card by positivity)
  have hsum' := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 720000*g by positivity)
  have hfinite : (S.card : ℝ)*(rho*r)*(rho^(1+eta1)*D^E*P.card) ≤
      (2880000*g)*(physicalPairTube3 P tau z).card := by nlinarith only [hnet',hsum']
  have hscale := mul_le_mul_of_nonneg_right hfinite (show 0 ≤ r*c*tau/(4665600000*rho) by positivity)
  have hpow : rho^(1+eta1)=rho*rho^eta1 := by rw [Real.rpow_add hrho,Real.rpow_one]
  have hleft : ((S.card : ℝ)*(rho*r)*(rho^(1+eta1)*D^E*P.card))*(r*c*tau/(4665600000*rho))=
      (S.card : ℝ)*rho*(c*r^2/4665600000*rho^eta1*D^E)*tau*P.card := by rw [hpow]; field_simp
  have hright : ((2880000*g)*(physicalPairTube3 P tau z).card)*(r*c*tau/(4665600000*rho))=
      (physicalPairTube3 P tau z).card := by dsimp [g,D]; field_simp; ring
  rw [hleft,hright] at hscale
  exact hscale

end OriginalThreeDimensionalLargeSlicePopulation
