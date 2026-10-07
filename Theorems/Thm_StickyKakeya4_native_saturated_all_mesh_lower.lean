import Theorems.Thm_StickyKakeya4_native_angular_test_source_window
import Theorems.Thm_StickyKakeya4_native_scheduled_angular_ancestor
import Theorems.Thm_StickyKakeya4_native_generic_reference_data
import Theorems.Thm_StickyKakeya4_native_history_dimension_range
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000
noncomputable section
namespace NativeSaturatedAllMeshLower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeLocalMenuInterpolation
open NativeJointUniformCoarseRelations NativeMiddleWindowBalance NativeFixedSizeScaleMenu
open NativeActualMesoscopicRankConfiguration NativeAllTwoScaleConfiguration NativeRankExponentHierarchy
open NativeMiddleGrainParentBudget NativeGeneralRankScalarBudget NativeOriginalPointSaturation
open NativeSaturatedSourceAngularRankLower NativeScheduledAngularAncestor NativeGenericReferenceData
open NativeSourceSizeBounds NativeActivePhasePopulation NativeQueriedVertexWeights
open NativeOriginalPointAngularLower NativeSaturatedAngularPowerLower NativeFixedCompactKakeyaExponent
theorem all_mesh_depth_window {delta r a tau : ℝ}
    (hd : 0< delta) (ha : 0≤ a) (htau : 0< tau) (htauHalf : tau≤ 1/2)
    (level stop s : ℕ) (hdy : delta=(2:ℝ)⁻¹^level)
    (hstop18 : 18≤ stop) (hstopCap : stop≤ level/4)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1) (hrdelta : r≤ delta^a)
    (hsmall : delta^(a/2)≤ 1/48) (htauCut : tau≤ 4*a)
    (hs6 : 6≤ s) (hsm : s≤ middleDepth stop+6) :
    middleDepth stop+s-3≤ level ∧
      rankWindow tau*(level:ℝ)≤ ((middleDepth stop+s-3:ℕ):ℝ) ∧
      ((middleDepth stop+s-3:ℕ):ℝ)≤ (1-rankWindow tau)*(level:ℝ) := by
  have hstop6 : 6 ≤ stop := by omega
  have hsmstop : middleDepth stop+6 ≤ stop := by dsimp [middleDepth]; omega
  have hlo := NativeGeneralRankScalarBudget.middle_lower hd ha level stop hdy hidentity hrdelta hsmall htauCut
  have hboundary : boundaryWindow tau=tau/1000 := min_eq_left (by linarith only [htauHalf])
  have hw : 2*rankWindow tau≤ boundaryWindow tau := by
    have hh : rankWindow tau≤ (tau/16)/1000 := min_le_right _ _
    rw [hboundary]
    linarith only [hh,htau]
  obtain ⟨hm6,hms,_hphaseLow,_hphaseHigh⟩ := middle_depth_bounds stop hstop6
  have hstopm : stop≤ 2*middleDepth stop := by dsimp [middleDepth]; omega
  have hN : middleDepth stop+s-3≤ 2*stop := by omega
  have hNm : middleDepth stop≤ middleDepth stop+s-3 := by omega
  have hcap : 4*stop≤ level := by omega
  have hstopmR : (stop:ℝ)≤ 2*(middleDepth stop:ℝ) := by exact_mod_cast hstopm
  have hNR : ((middleDepth stop+s-3:ℕ):ℝ)≤ 2*(stop:ℝ) := by exact_mod_cast hN
  have hNmR : (middleDepth stop:ℝ)≤ ((middleDepth stop+s-3:ℕ):ℝ) := by exact_mod_cast hNm
  have hcapR : 4*(stop:ℝ)≤ (level:ℝ) := by exact_mod_cast hcap
  have hwindowHalf : rankWindow tau≤ 1/2 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (by norm_num))
  have hlevel0 := Nat.cast_nonneg (α:=ℝ) level
  refine ⟨by omega,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hw hlevel0
    nlinarith only [hh,hlo,hstopmR,hNmR]
  · have hh := mul_le_mul_of_nonneg_right hwindowHalf hlevel0
    nlinarith only [hNR,hcapR,hh]


/-- Every dyadic mesh from the unit scale down to Rho/64 uses an actual
already-installed E1 ancestor. No point-degree or angular lower certificate
is added after the saturated pre-third source has been chosen. -/
theorem actual_all_mesh_point_lower {n g J : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta eta0 c c2 r : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau) (L : ℕ)
    (ref : Reference h tau htau seed e zeta L g)
    (E2 S : Finset (Fin n × Index)) (points : Finset Index) (h21 : E2⊆ref.E1) (hE2n : E2.Nonempty)
    (rank : Fin 4) (hi : 1 ≤ rank.val) (hell : rank.val+1 ≤ 3)
    (heta : 0 ≤ eta) (he0 : 0 < eta0) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcUnit : c ≤ 1/(eta0+1)) (hr : 0 < r) (hr1 : r ≤ 1)
    (hrdelta : r ≤ D.thickness^(cutoff c rank))
    (hmass : r^((2*((rank.val+1:ℕ):ℝ)+1)*rankLoss eta0 c rank)*(E2.card:ℝ) ≤
      (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ))
    (htauHalf : tau ≤ 1/2) (hTau : tau ≤ commonBudget eta0 c/1024)
    (hTauHistory : tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1)))
    (hseed : seed ≤ tau/16384) (hc2 : c2=commonBudget eta0 c/4)
    (hg : 0 < g) (hgrid : 1/(g:ℝ) < rankWindow tau/4)
    (F2 G Q2 : ℕ) (hG : 0 < G) (hGF : G ≤ F2)
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2))
    (j : Fin (g+1)) (hstop18 : 18 ≤ (ref.schedule j).val)
    (hstopCap : (ref.schedule j).val ≤ ref.level/4)
    (hidentity : 48*((2^(ref.schedule j).val:ℕ):ℝ)*r=1)
    (hsmall : D.thickness ≤ NativeHistoryDimensionRange.extraCutoff c hc hc1 g)
    (p : Parent)
    (HS : Saturated (parentEdges D ref.a (2^(middleDepth (ref.schedule j).val)) E2 p) S Prod.snd)
    (HPoint : HasUniformFibers (parentEdges D ref.a (2^(middleDepth (ref.schedule j).val)) E2 p) Q2 Prod.snd)
    (hret :
      let lambda := r^(rankLoss eta0 c rank)/(4*((g:ℝ)+1))
      let W : ℝ := (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)
      let mu := (lambda*W/(2*(factor ref.dimension (g+1) L:ℝ)*G*(E2.card:ℝ)))*D.thickness^eta
      (mu/rowConstant)*(parentEdges D ref.a (2^(middleDepth (ref.schedule j).val)) ref.E1 p).card ≤
        (parentEdges D ref.a (2^(middleDepth (ref.schedule j).val)) E2 p).card)
    (s : ℕ) (hs : 6 ≤ s) (hsm : s ≤ middleDepth (ref.schedule j).val+6)
    (k : Index) (hk : k∈S.image Prod.snd) :
    (64/((2^s:ℕ):ℝ))^(-extremalExponent) ≤
      (2744*rowConstant*((g:ℝ)+1))*r^(-(9*rankLoss eta0 c rank))*
        (pointMenu D (middleDepth (ref.schedule j).val) s p S k).card := by
  have hstop6 : 6 ≤ (ref.schedule j).val := by omega
  have hTauCut := tau_le_cutoff he0.le hc hc1 hcUnit rank hi htau.le J hTauHistory
  have hcut := (NativeHistoryDimensionRange.extraCutoff_spec c hc hc1 g).2.2 D.thickness h.1.2.1 hsmall rank
  obtain ⟨hf,hlo,hhi⟩ := all_mesh_depth_window h.1.2.1 (cutoff_bounds hc hc1 rank).1.le htau htauHalf
    ref.level (ref.schedule j).val s ref.backbone.2.1 hstop18 hstopCap hidentity hrdelta hcut.1 hTauCut hs hsm
  obtain ⟨hgap0,hgapTau,jA,hAncestor,hGap,HAncestor⟩ := exists_actual_angular_ancestor D ref.E1 ref.a tau htau
    g ref.level (middleDepth (ref.schedule j).val+s-3) (coreRadix ref.original ref.R L) hg ref.grid_depth
    hgrid ref.schedule ref.schedule_eq ref.parent_point hlo hhi
  have hmLevel : middleDepth (ref.schedule j).val ≤ ref.level :=
    (middle_depth_bounds _ hstop6).2.1.trans (Nat.le_of_lt_succ (ref.schedule j).isLt)
  have hQ1 : 1 ≤ coreRadix ref.original ref.R L := (by norm_num : 1 ≤ (4:ℕ)).trans (radix_four_le _ _)
  exact actual_saturated_angular_rank_lower h ref.original ref.R ref.level ref.backbone ref.E1 E2 S points
    ref.core.1 h21 hE2n rank (rank.val+1) hell heta he0 hc hr hr1 hrdelta hmass
    htau hTau hseed hc2 hgap0 hgapTau g (factor ref.dimension (g+1) L) F2 G (coreRadix ref.original ref.R L) Q2
    hg ref.grid_depth (NativeGenericReferenceData.factor_pos ref) hG hQ1 hGF hgrid ref.cost H2 ref.middle
    (middleDepth (ref.schedule j).val) s (ref.schedule jA).val hmLevel (by omega) hf hAncestor hGap
    p HS HAncestor HPoint hret k hk

end NativeSaturatedAllMeshLower
