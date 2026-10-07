import Theorems.Thm_StickyKakeya4_native_normalized_population_admission_budget
import Theorems.Thm_StickyKakeya4_native_reference_slice_budget_costs
import Theorems.Thm_StickyKakeya4_native_sharp_parent_graph_data
import Theorems.Thm_StickyKakeya4_native_rank_exponent_hierarchy

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

noncomputable section
namespace NativeSharpPopulationAdmission
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeNormalizedPopulationAdmissionBudget NativeReferenceSliceBudgetCosts
open NativeRankExponentHierarchy NativeQuarterScaleParameters
open NativeSharpParentGraphData NativeQueriedVertexWeights NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeSpatialAngularGeometry

/-- The first and second costs stored by the source pay the actual product
F1*G. There is no separate population or retention-power hypothesis. -/
theorem original_refinement_cost {delta eta c1 c2 : ℝ}
    (hd : 0< delta) (hd1 : delta≤ 1) (heta : 0≤ eta)
    (F1 F2 G Q1 Q2 : ℕ) (hQ1 : 1≤ Q1) (hQ2 : 1≤ Q2) (hGF : G≤ F2)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta)≤ delta^(-c1))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta)≤ delta^(-c2)) :
    (F1:ℝ)*G≤ delta^(-(c1+c2)) := by
  have hpow : (1:ℝ)≤ delta^(-eta) := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_nonpos.mpr heta))
  have hF := first_retention_density_cost hd F1 Q1 hQ1 H1
  have hG := first_retention_density_cost hd F2 Q2 hQ2 H2
  have hf' : (F1:ℝ)≤ (F1:ℝ)*delta^(-eta) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg F1)
  have hg' : (F2:ℝ)≤ (F2:ℝ)*delta^(-eta) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg F2)
  have hf := hf'.trans hF
  have hg : (G:ℝ)≤ delta^(-c2) := (Nat.cast_le.mpr hGF).trans (hg'.trans hG)
  have hh := mul_le_mul hf hg (Nat.cast_nonneg G) (Real.rpow_nonneg hd.le (-c1))
  rw [←Real.rpow_add hd] at hh
  convert hh using 1
  congr 1
  ring

/-- Literal readback of theta*delta^eta in HasSharpCurveParentProfiles,
including any subsequent same-source retention cost. -/
theorem sharp_population_readback (delta r eta loss : ℝ) (g F1 G : ℕ)
    (mass count extra : ℝ) :
    ((r^loss/(4*((g:ℝ)+1)))*mass/(2*(F1:ℝ)*G*count))*delta^eta/extra =
      populationValue delta r eta loss g mass count ((F1:ℝ)*G*extra) := by
  unfold populationValue
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The actual rank hierarchy leaves half the local-admission margin for
the later graph, quotient and third-core costs. -/
theorem hierarchy_admission_margins {eta0 c tau seed eta zeta c2 localEta profileExp : ℝ}
    (he : 0< eta0) (hc : 0≤ c) (hc1 : c≤ 1)
    (hlocal : eta0≤ localEta/80) (hprofile : eta0≤ profileExp/4)
    (htau : tau≤ commonBudget eta0 c/1024) (hseed : seed≤ tau/16384)
    (heta : eta≤ seed/8) (hzeta : zeta≤ seed/256) (hc2 : c2=commonBudget eta0 c/4)
    (rank : Fin 4) (ell : ℕ) (hell : ell≤ 3) :
    eta+(2*(ell:ℝ)+1)*rankLoss eta0 c rank+rankLoss eta0 c rank+seed/8+c2≤ localEta/8 ∧
      eta+zeta≤ localEta/4 ∧ zeta≤ profileExp/4 := by
  have hbudget : commonBudget eta0 c≤ eta0 := by
    have hp := pow_le_one₀ hc hc1 (n:=3)
    unfold commonBudget
    nlinarith only [hp,he]
  have hrank := rankLoss_le_initial he.le hc hc1 rank
  have hrank0 : 0≤ rankLoss eta0 c rank := by unfold rankLoss; positivity
  have hellr : (ell:ℝ)≤ 3 := by exact_mod_cast hell
  have hmass : (2*(ell:ℝ)+1)*rankLoss eta0 c rank≤ 7*eta0 := by
    nlinarith only [hellr,hrank,hrank0]
  rw [hc2]
  constructor
  · linarith only [hmass,hrank,heta,hseed,htau,hbudget,hlocal,he]
  constructor
  · linarith only [heta,hzeta,hseed,htau,hbudget,hlocal,he]
  · linarith only [hzeta,hseed,htau,hbudget,hprofile,he]

/-- The local-source cutoff and all four admission budgets are selected
together before the original source. The remaining costs are the actual
graph/quotient/third-core product, not a new source population. -/
theorem exists_sharp_admission_cutoff (localEta profileExp eps0 : ℝ)
    (he : 0< localEta) (hp : 0< profileExp) (heps : 0< eps0) (g : ℕ) :
    ∃delta0 : ℝ,0< delta0 ∧ delta0≤ 1/8 ∧
      ∀delta Delta r eta zeta loss c1 c2 extraPower mass count extra : ℝ,
      ∀F1 F2 G Q1 Q2 : ℕ,
        0< delta → delta≤ delta0 → 0< Delta → delta≤ Delta^2 → delta≤ r →
        0≤ eta → 0≤ loss → 0< count → 0< F1 → 0< G → 0< extra →
        1≤ Q1 → 1≤ Q2 → G≤ F2 →
        r^(7*loss)*count≤ mass →
        eta+8*loss+c1+c2≤ localEta/8 → extraPower≤ localEta/8 →
        eta+zeta≤ localEta/4 → zeta≤ profileExp/4 →
        (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta)≤ delta^(-c1) →
        (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta)≤ delta^(-c2) →
        extra≤ delta^(-extraPower) →
        let localThickness := delta/Delta
        let mu := ((r^loss/(4*((g:ℝ)+1)))*mass/(2*(F1:ℝ)*G*count))*delta^eta
        localThickness≤ eps0 ∧
        (2048:ℝ)^3*localThickness^localEta≤ delta^zeta ∧
        (373248*512^4:ℝ)*localThickness^localEta≤ delta^(eta+zeta) ∧
        (1024*175616*NativeOriginalPrunedMass.volumeConstant)*localThickness^localEta≤ mu/extra ∧
        (64:ℝ)^3*localThickness^profileExp≤ delta^zeta := by
  obtain ⟨d0,hd0,hd01,hBudget⟩ := exists_original_population_admission_cutoff localEta profileExp he hp g
  obtain ⟨d1,hd1,_hd11,hSmall⟩ := exists_small_power_cutoff (by norm_num : (0:ℝ)< 1/2) heps
  refine ⟨min d0 d1,lt_min hd0 hd1,(min_le_left _ _).trans hd01,?_⟩
  intro delta Delta r eta zeta loss c1 c2 extraPower mass count extra F1 F2 G Q1 Q2
    hd hsmall hDelta hsquare hr heta hloss hcount hF1 hG hextra hQ1 hQ2 hGF
    hmass hbase hExtraPower hcw hprofile H1 H2 hExtra
  have hd0' := hsmall.trans (min_le_left _ _)
  have hd1' : delta≤ 1 := (hd0'.trans hd01).trans (by norm_num)
  have hcost := original_refinement_cost hd hd1' heta F1 F2 G Q1 Q2 hQ1 hQ2 hGF H1 H2
  have htotalCost : (F1:ℝ)*G*extra≤ delta^(-(c1+c2+extraPower)) := by
    have hh := mul_le_mul hcost hExtra hextra.le (Real.rpow_nonneg hd.le _)
    rw [←Real.rpow_add hd] at hh
    convert hh using 1
    congr 1
    ring
  have hcostPos : 0< (F1:ℝ)*G*extra := by positivity
  have htotal : eta+7*loss+loss+(c1+c2+extraPower)≤ localEta/4 := by
    linarith only [hbase,hExtraPower]
  obtain ⟨hAd,hCw,hDen,hProf⟩ := hBudget delta Delta r eta zeta (7*loss) loss
    (c1+c2+extraPower) mass count ((F1:ℝ)*G*extra) hd hd0' hDelta hsquare hr
    heta (by positivity) hloss htotal hcw hprofile hcount hcostPos hmass htotalCost
  have hLocal := (local_scale_root hd hDelta hsquare).trans
    (hSmall delta hd (hsmall.trans (min_le_right _ _)))
  rw [←sharp_population_readback] at hDen
  exact ⟨hLocal,hAd,hCw,hDen,hProf⟩

end NativeSharpPopulationAdmission
