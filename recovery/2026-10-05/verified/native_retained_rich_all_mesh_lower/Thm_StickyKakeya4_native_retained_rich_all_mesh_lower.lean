import Theorems.Thm_StickyKakeya4_native_saturated_all_mesh_lower
import Theorems.Thm_StickyKakeya4_native_retained_rich_angular_rank_lower
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000
noncomputable section
namespace NativeRetainedRichAllMeshLower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeLocalMenuInterpolation
open NativeJointUniformCoarseRelations NativeMiddleWindowBalance NativeFixedSizeScaleMenu
open NativeActualMesoscopicRankConfiguration NativeAllTwoScaleConfiguration NativeRankExponentHierarchy
open NativeMiddleGrainParentBudget NativeGeneralRankScalarBudget NativeOriginalPointSaturation
open NativeSaturatedSourceAngularRankLower NativeScheduledAngularAncestor NativeGenericReferenceData
open NativeSourceSizeBounds NativeActivePhasePopulation NativeQueriedVertexWeights
open NativeOriginalPointAngularLower NativeSaturatedAngularPowerLower NativeFixedCompactKakeyaExponent
open NativeSaturatedAllMeshLower NativeRetainedRichAngularRankLower
open NativeNormalizedCellAngularMenu RichDirectionalLayers
/-- Every dyadic fine scale through the final mesh uses its already
installed original E1 ancestor. The actual rich class belongs to the same
one-third selection, with its original per-point edge weights preserved. -/
theorem actual_all_mesh_rich_class_lower {n g J Jangle : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta eta0 c c2 r : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau) (L : ℕ)
    (ref : Reference h tau htau seed e zeta L g)
    (E2 S I T : Finset (Fin n × Index)) (points : Finset Index) (h21 : E2⊆ref.E1) (hE2n : E2.Nonempty)
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
    (hIS : I⊆ S) (hTI : T⊆ I) (F3 Q3 : ℕ) (hF3 : 0< F3)
    (hret3 : S.card≤ F3*I.card) (HPoint3 : HasUniformFibers I Q3 Prod.snd)
    (hret :
      let lambda := r^(rankLoss eta0 c rank)/(4*((g:ℝ)+1))
      let W : ℝ := (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)
      let mu := (lambda*W/(2*(factor ref.dimension (g+1) L:ℝ)*G*(E2.card:ℝ)))*D.thickness^eta
      (mu/rowConstant)*(parentEdges D ref.a (2^(middleDepth (ref.schedule j).val)) ref.E1 p).card ≤
        (parentEdges D ref.a (2^(middleDepth (ref.schedule j).val)) E2 p).card)
    (s : ℕ) (hs : 6 ≤ s) (hsm : s ≤ middleDepth (ref.schedule j).val+6)
    (sigmaDepth : Fin Jangle → ℕ) (jangle : Fin Jangle)
    (k : Index) (hk : k∈I.image Prod.snd) (q : Fin 3 → ℤ)
    (hRich : ((I.filter (fun z => z.2=k)).card:ℝ)/
        (2*(Jangle:ℝ)*(((I.filter (fun z => z.2=k)).image
          (fun z => angularCell D (2^(middleDepth (ref.schedule j).val))
            (2^(sigmaDepth jangle)) p z.1)).card:ℝ)) <
      ((classFiber (T.filter (fun z => z.2=k))
        (fun z => angularCell D (2^(middleDepth (ref.schedule j).val))
          (2^(sigmaDepth jangle)) p z.1) q).card:ℝ)) :
    (64/((2^s:ℕ):ℝ))^(-extremalExponent)≤
      ((2744*rowConstant*((g:ℝ)+1))*r^(-(9*rankLoss eta0 c rank)))*
      ((F3:ℝ)*(Q3:ℝ)^2*
        (2*(Jangle:ℝ)*(((I.filter (fun z => z.2=k)).image
          (fun z => angularCell D (2^(middleDepth (ref.schedule j).val))
            (2^(sigmaDepth jangle)) p z.1)).card:ℝ))*
        (((classFiber (T.filter (fun z => z.2=k))
          (fun z => angularCell D (2^(middleDepth (ref.schedule j).val))
            (2^(sigmaDepth jangle)) p z.1) q).image
          (fun z => angularCell D (2^(middleDepth (ref.schedule j).val)) (2^s) p z.1)).card:ℝ)) := by
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
  exact actual_retained_rich_angular_rank_lower h ref.original ref.R ref.level ref.backbone ref.E1 E2 S I T points
    ref.core.1 h21 hE2n rank (rank.val+1) hell heta he0 hc hr hr1 hrdelta hmass
    htau hTau hseed hc2 hgap0 hgapTau g (factor ref.dimension (g+1) L) F2 G (coreRadix ref.original ref.R L) Q2
    hg ref.grid_depth (NativeGenericReferenceData.factor_pos ref) hG hQ1 hGF hgrid ref.cost H2 ref.middle
    (middleDepth (ref.schedule j).val) s (ref.schedule jA).val hmLevel (by omega) hf hAncestor hGap
    p HS hIS hTI F3 Q3 hF3 hret3 HPoint3 HAncestor HPoint hret sigmaDepth jangle k hk q hRich


end NativeRetainedRichAllMeshLower
