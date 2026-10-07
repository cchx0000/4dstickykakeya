import Theorems.Thm_StickyKakeya4_native_reference_parent_grain_cleanup

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

noncomputable section
namespace NativeOriginalParentGrainCleanup
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeSpatialAngularGeometry NativeSquaredGrainQueries NativeActualProjectedGrainCount
open NativeQueriedVertexWeights NativeOriginalPacketReference NativeCompatibleNodeDirections
open NativeDirectionRankDichotomy NativeActualGrainHistory NativeHistoryGrainCount NativeHistoryGrainCleanup
open NativeParentGrainIncidenceCleanup NativeParentVertexMassCap NativeSpatialParentCount
open NativeConditionedPairMenu NativeAllTwoScaleConfiguration NativeTwoScaleConfiguration
open NativeMiddleWindowBalance NativeFixedCompactKakeyaExponent NativeFullCoarseShadow
open NativeRetainedFinePairDensity RichDirectionalLayers WeightedRichDirectionalLayers
open scoped BigOperators

open NativeSourceParentGrainCleanup

open NativeReferenceParentGrainCleanup

/-- Choose the parent against FULL original incidences after the same mixed
cleanup. Original, retained-R, E1 and E2 parent retention all hold on one p;
the exact source-derived grain lower survives this stronger choice. -/
theorem source_original_parent_grain_cleanup {n d g level J : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed tau q c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1) (hE2 : E2.Nonempty) (L : ℕ)
    (schedule : Fin (g+1) → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (htau : 0 < tau) (heta : 0 ≤ eta) (hseed : seed ≤ tau/16384)
    (hg : 0 < g) (hgl : g ≤ level)
    (hgrid : 1/(g:ℝ) < min (boundaryWindow tau) ((tau/16)/1000)/4)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (hschedule : schedule=fullSchedule tau htau g level)
    (Hcore : IsCore D original R a eta zeta d (g+1) L Rel
      (fun j => 2^(schedule j).val) E1)
    (hcost : (125*175616*16384:ℝ)*(factor d (g+1) L:ℝ)*(coreRadix original R L:ℝ)^2*
      D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (hconditioned : ∀i j,HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
      HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val))
    (hreference : ∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E1 a level m f tau)
    (G : ℕ) (hG : 0 < G) (lambda : ℝ) (hlambda : 0 < lambda)
    (hret : lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card)
    (_hJ : 0 < J) (m : Fin J → ℕ) (hm6 : ∀i,6 ≤ m i) (ell : ℕ) (hell : ell ≤ 4)
    (S0 : Finset Index) (hS0 : S0⊆E2.image Prod.snd) (Q2 : ℕ)
    (HU : ∀i,HasUniformFibers E2 Q2 (fun z => spatialLabel D (2^(phaseDepth (m i))) z.2))
    (hq : 0 < q) (hq1 : q ≤ 1)
    (point : Fin J → Index → Index)
    (tuple : Fin J → Index → Fin ell → (Fin n × Index))
    (anchor : Fin J → Index → Fin ell → Fin n)
    (Hsys : ∀i,IsNodeDirectionSystem D a (m i) E2 S0 q ell (point i) (tuple i) (anchor i))
    (Hhistory : HasGrainHistory D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 Q2 lambda c1 c2)
    (i : Fin J) (hf : phaseDepth (m i) ≤ level) (hsmall : D.thickness ≤ 1/8)
    (HP : HasUniformFibers E2 Q2 (physicalPair h R a level (phaseDepth (m i))))
    (K : Finset Index)
    (hK : K⊆history D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 J)
    (hKn : K.Nonempty) :
    let plane := fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node))
    let Lgrain := predecessorProduct D (m i) E2 Q2
      (scaleThreshold D E2 (m i)
        (history D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 i.val)
        ell (natStageDirectionIndex h (tuple i))) ell
    let theta := lambda*(mass K (pointWeight E2):ℝ)/(2*(factor d (g+1) L:ℝ)*(G:ℝ)*(E2.card:ℝ))
    0 < theta ∧ ∃H⊆cutEdges E2 K,H.Nonempty ∧ mass K (pointWeight E2) ≤ 2*H.card ∧
      ∃p : Parent,(parentEdges D a (2^(m i)) H p).Nonempty ∧
        theta*(parentEdges D a (2^(m i)) (incidences original) p).card ≤
          (parentEdges D a (2^(m i)) H p).card ∧
        theta*(parentEdges D a (2^(m i)) (retained original R) p).card ≤
          (parentEdges D a (2^(m i)) H p).card ∧
        theta*(parentEdges D a (2^(m i)) E1 p).card ≤ (parentEdges D a (2^(m i)) H p).card ∧
        theta*(parentEdges D a (2^(m i)) E1 p).card ≤ (parentEdges D a (2^(m i)) E2 p).card ∧
        theta*(parentEdges D a (2^(m i)) E2 p).card ≤ (parentEdges D a (2^(m i)) H p).card ∧
        ∀x∈parentEdges D a (2^(m i)) H p,
          lambda*D.thickness^(2*eta+3*zeta+7*tau)*(mass K (pointWeight E2):ℝ)*Lgrain <
            parentGrainConstant*transverseCost q ell*(Q2:ℝ)^2*(factor d (g+1) L:ℝ)*G*E2.card*
              (mixedVertices D a (m i) (phaseDepth (m i)) plane ell (parentEdges D a (2^(m i)) H p)
                (mixedLabel D a (m i) plane ell x)).card := by
  intro plane Lgrain theta
  obtain ⟨H,hHJ,hHn,hhalf,hgrain⟩ := source_mixed_grain_core h original R E1 E2 h21 hE2 L schedule Rel
    htau heta hseed hg hgl hgrid Hbackbone hschedule Hcore hcost hconditioned hreference
    G hG lambda hlambda hret _hJ m hm6 ell hell S0 hS0 Q2 HU hq hq1 point tuple anchor Hsys Hhistory
    i hf hsmall HP K hK hKn
  have hHE2 : H⊆E2 := hHJ.trans (cutEdges_subset E2 K)
  have hHE1 : H⊆E1 := hHE2.trans h21
  have hE1I : E1⊆incidences original := Hcore.1.trans (filter_subset _ _)
  have hHI : H⊆incidences original := hHE1.trans hE1I
  have hF1 : (0:ℝ)<factor d (g+1) L := by dsimp [factor,NativeLocalPairUniformCore.retentionCost]; positivity
  have hEcard : (0:ℝ)<E2.card := by exact_mod_cast card_pos.mpr hE2
  have hGr : (0:ℝ)<G := by exact_mod_cast hG
  have hW : (0:ℝ) < mass K (pointWeight E2) := by
    rw [←cutEdges_card E2 K]
    exact_mod_cast card_pos.mpr (hHn.mono hHJ)
  have hden : 0 < 2*(factor d (g+1) L:ℝ)*(G:ℝ)*(E2.card:ℝ) := by positivity
  have htheta : 0 < theta := by dsimp [theta]; positivity
  have hhalfR : (mass K (pointWeight E2):ℝ) ≤ 2*(H.card:ℝ) := by exact_mod_cast hhalf
  have hI : ((incidences original).card:ℝ) ≤ (factor d (g+1) L:ℝ)*E1.card := by
    exact_mod_cast Hcore.2.2.1
  have hh : lambda*(mass K (pointWeight E2):ℝ)*(incidences original).card ≤
      (H.card:ℝ)*(2*(factor d (g+1) L:ℝ)*(G:ℝ)*(E2.card:ℝ)) := by
    calc
      _ ≤ lambda*(mass K (pointWeight E2):ℝ)*((factor d (g+1) L:ℝ)*E1.card) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
      _ = ((factor d (g+1) L:ℝ)*(mass K (pointWeight E2):ℝ))*(lambda*E1.card) := by ring
      _ ≤ ((factor d (g+1) L:ℝ)*(mass K (pointWeight E2):ℝ))*((G:ℝ)*E2.card) :=
        mul_le_mul_of_nonneg_left hret (by positivity)
      _ = ((factor d (g+1) L:ℝ)*(G:ℝ)*E2.card)*(mass K (pointWeight E2):ℝ) := by ring
      _ ≤ ((factor d (g+1) L:ℝ)*(G:ℝ)*E2.card)*(2*(H.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hhalfR (by positivity)
      _ = _ := by ring
  have hthetaRet : theta*((incidences original).card:ℝ) ≤ (H.card:ℝ) := by
    dsimp [theta]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hden).mpr hh
  obtain ⟨p,_hp,_hIp,hHp,hlocal⟩ := NativeDensePhaseParentRetention.exists_retained_fiber
    (incidences original) H hHI (hHn.mono hHI) (fun z => parentLabel D a (2^(m i)) z.1) theta 1 htheta
      (by simpa only [one_mul] using hthetaRet)
  have hmain : theta*(parentEdges D a (2^(m i)) (incidences original) p).card ≤
      (parentEdges D a (2^(m i)) H p).card := by simpa only [one_mul,parentEdges] using hlocal
  have hmon (A B : Finset (Fin n × Index)) (hAB : A⊆B) :
      theta*(parentEdges D a (2^(m i)) A p).card ≤ theta*(parentEdges D a (2^(m i)) B p).card :=
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card (filter_subset_filter _ hAB))) htheta.le
  have hE1ret := (hmon E1 (incidences original) hE1I).trans hmain
  have hHparent : ((parentEdges D a (2^(m i)) H p).card:ℝ) ≤
      (parentEdges D a (2^(m i)) E2 p).card := by
    exact_mod_cast card_le_card (filter_subset_filter _ hHE2)
  refine ⟨htheta,H,hHJ,hHn,hhalf,p,hHp,hmain,
    (hmon (retained original R) (incidences original) (filter_subset _ _)).trans hmain,
    hE1ret,hE1ret.trans hHparent,(hmon E2 E1 h21).trans hE1ret,?_⟩
  intro x hx
  have hxH := (mem_filter.mp hx).1
  have hxp := (mem_filter.mp hx).2
  have he : mixedLabel D a (m i) plane ell x=(p,taggedLabel D (m i) plane ell x.2) := Prod.ext hxp rfl
  have hdense : lambda*D.thickness^(2*eta+3*zeta+7*tau)*(mass K (pointWeight E2):ℝ)*Lgrain <
      parentGrainConstant*transverseCost q ell*(Q2:ℝ)^2*(factor d (g+1) L:ℝ)*G*E2.card*
        (mixedVertices D a (m i) (phaseDepth (m i)) plane ell H
          (mixedLabel D a (m i) plane ell x)).card := hgrain x hxH
  simpa only [he,mixedVertices,parent_mixed_fiber_eq] using hdense

end NativeOriginalParentGrainCleanup
