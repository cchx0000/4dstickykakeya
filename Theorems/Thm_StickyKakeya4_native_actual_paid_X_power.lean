import Theorems.Thm_StickyKakeya4_native_actual_sharp_X_power
import Theorems.Thm_StickyKakeya4_native_sharp_X_budget_actual
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeActualPaidXPower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeSpatialAngularGeometry NativeSquaredGrainQueries NativeActualProjectedGrainCount
open NativeQueriedVertexWeights NativeOriginalPacketReference NativeCompatibleNodeDirections
open NativeDirectionRankDichotomy NativeActualGrainHistory NativeHistoryGrainCount NativeHistoryGrainCleanup
open NativeParentGrainIncidenceCleanup NativeParentVertexMassCap NativeSpatialParentCount
open NativeConditionedPairMenu NativeAllTwoScaleConfiguration NativeTwoScaleConfiguration
open NativeMiddleWindowBalance NativeFixedCompactKakeyaExponent NativeFullCoarseShadow
open NativeRetainedFinePairDensity RichDirectionalLayers WeightedRichDirectionalLayers
open NativeSourceParentGrainCleanup NativeHistoryGrainPowerDensity
open scoped BigOperators

open NativeSharpXCapCancellation

open NativeSharpXSourceCount NativeSharpXPowerAlgebra NativeTranslatedGrainHeightFibers
open NativeTranslatedGrainHeightSelection NativeWeightedGrainQuotientGeometry NativeHorizontalGrainSlice
open NativeGrainHeightProjectionFibers NativeGrainQuotientFibers

open NativeActualSharpXLower NativeSharpXHistoryPower NativeRetainedSliceBudgetAlgebra

open NativeActualSharpXPower NativeSharpXBudgetActual NativeSharpXBudgetCutoff NativeRankExponentHierarchy
open NativeRetainedSliceBudgetSource

theorem source_reference_X_small_power {n d g level J : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed tau q c2 : ℝ}
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
    (Hhistory : HasGrainHistory D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 Q2 lambda (seed/8) c2)
    (i : Fin J) (hf : phaseDepth (m i) ≤ level) (hsmall : D.thickness ≤ 1/8)
    (HP : HasUniformFibers E2 Q2 (physicalPair h R a level (phaseDepth (m i))))
    (K : Finset Index)
    (hK : K⊆history D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 J)
    (hKn : K.Nonempty)
    (Hgraph T : Finset (Fin n × Index)) (hHE2 : Hgraph⊆E2)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell1 : 1 ≤ ell)
    (hdim : Module.finrank ℝ P=ell-1)
    (hT : T⊆second D a (m i) ell
      (fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node)))
      (NativeWeightedGrainQuotientGeometry.retained D a (m i) ell
        (fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node)))
        Hgraph P hP hell1 hell hdim (physicalMesh (m i) (phaseDepth (m i))/8)))
    (F3 Q3 : ℕ)
    (hthreshold : ∀x∈T,
      ((cutEdges E2 K).card:ℝ)/(2*((((cutEdges E2 K).image
        (mixedLabel D a (m i)
          (fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node))) ell)).card):ℝ)) ≤
        (quotientCost q*(F3:ℝ)*(Q3:ℝ)^2)*(mixedFiber D a (m i)
          (fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node))) ell T
          (mixedLabel D a (m i)
            (fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node))) ell x)).card)
    (eta0 c epsilon r : ℝ) (rank : Fin 4) (hellRank : ell=rank.val+1) (hRank3 : rank.val+1 ≤ 3)
    (he : 0 < epsilon) (he0 : 0 < eta0) (he01 : eta0 ≤ 1) (heSmall : eta0 ≤ epsilon/2048)
    (hc : 0 < c) (hc1 : c ≤ 1) (hcQ : c ≤ quotientTolerance (epsilon/4)/24)
    (hSourceCut : D.thickness ≤ sourceCutoff epsilon c g he hc)
    (hetaSeed : eta ≤ seed/8) (hseed0 : 0 ≤ seed)
    (F2 : ℕ) (hGF : G ≤ F2) (hQ3 : 1 ≤ Q3)
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2))
    (H3 : (F3:ℝ)*(Q3:ℝ)^4 ≤ D.thickness^(-(commonBudget eta0 c/4)))
    (hTau : tau ≤ commonBudget eta0 c/1024) (hzeta : zeta ≤ seed/256) (hc2 : c2=commonBudget eta0 c/4)
    (hr : 0 < r) (hr1 : r ≤ 1) (hrdelta : r ≤ D.thickness^(cutoff c rank))
    (hlambdaEq : lambda=r^(rankLoss eta0 c rank)/(4*((g:ℝ)+1)))
    (hMass : r^((2*((rank.val+1:ℕ):ℝ)+1)*rankLoss eta0 c rank)*(E2.card:ℝ) ≤
      (mass K (pointWeight E2):ℝ))
    (hqraw : r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q)
    (hscale : ((64:ℝ)/((2^(m i):ℕ):ℝ))^2 ≤ 6144*r) :
    let plane := fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node))
    let mu := physicalMesh (m i) (phaseDepth (m i))/8
    let rho := (64:ℝ)/((2^(m i):ℕ):ℝ)
    ∀x∈T,rho^epsilon*rho^(-((ell:ℝ)-1)) ≤
      (referenceX D a (m i) ell plane T P hP hell1 hell hdim mu
        (referenceKey D a (m i) ell plane P hP hell1 hell hdim mu x)).card := by
  intro plane mu rho x hx
  have hRaw := source_reference_X_power_lower h original R E1 E2 h21 hE2 L schedule Rel htau heta hseed hg hgl hgrid
    Hbackbone hschedule Hcore hcost hconditioned hreference G hG lambda hlambda hret _hJ m hm6 ell hell
    S0 hS0 Q2 HU hq hq1 point tuple anchor Hsys Hhistory i hf hsmall HP K hK hKn
    Hgraph T hHE2 P hP hell1 hdim hT F3 Q3 hthreshold x hx
  have hEcard : (0:ℝ)<E2.card := by exact_mod_cast card_pos.mpr hE2
  have hMassRatio : r^((2*((rank.val+1:ℕ):ℝ)+1)*rankLoss eta0 c rank) ≤
      (mass K (pointWeight E2):ℝ)/(E2.card:ℝ) := (le_div_iff₀ hEcard).mpr hMass
  have hQ1 : 1 ≤ coreRadix original R L :=
    (by norm_num : 1 ≤ (4:ℕ)).trans (NativeSourceSizeBounds.radix_four_le _ _)
  have hCost := actual_fiber_coefficient_le_power he he0 he01 heSmall hc hc1 hcQ
    (factor d (g+1) L) F2 G (coreRadix original R L) Q2 F3 Q3 g (m i) rank (hm6 i) hRank3
    h.1.2.1 hSourceCut heta hetaSeed hseed0 hQ1 hQ3 hGF hcost H2 H3 htau.le hTau hseed hzeta hc2
    hr hr1 hrdelta hlambdaEq hMassRatio hq hq1 hgrid hqraw hscale
  have hCost' : fiberCoefficient D.thickness eta zeta tau (seed/8) c2 lambda
      ((mass K (pointWeight E2):ℝ)/(E2.card:ℝ)) (factor d (g+1) L) G Q2 F3 Q3 q ell ≤ rho^(-epsilon) := by
    simpa only [hellRank] using hCost
  exact paid_X_lower (by dsimp [rho]; positivity) (Nat.cast_nonneg _) hRaw hCost'

end NativeActualPaidXPower
