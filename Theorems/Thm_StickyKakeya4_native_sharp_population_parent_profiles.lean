import Theorems.Thm_StickyKakeya4_native_sharp_mixed_grain_core
import Theorems.Thm_StickyKakeya4_native_population_parent_selection
import Theorems.Thm_StickyKakeya4_native_combined_parent_profiles

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeSharpPopulationParentProfiles
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeSpatialAngularGeometry NativeSquaredGrainQueries NativeActualProjectedGrainCount
open NativeQueriedVertexWeights NativeOriginalPacketReference NativeCompatibleNodeDirections
open NativeDirectionRankDichotomy NativeActualGrainHistory NativeHistoryGrainCount NativeHistoryGrainCleanup
open NativeParentGrainIncidenceCleanup NativeSourceParentGrainCleanup NativeSharpMixedGrainCore
open NativeConditionedPairMenu NativeAllTwoScaleConfiguration NativeTwoScaleConfiguration
open NativeMiddleWindowBalance NativeFixedCompactKakeyaExponent NativeFullCoarseShadow
open NativeRetainedFinePairDensity RichDirectionalLayers WeightedRichDirectionalLayers
open NativeCoarseShadingUniformity NativeCoarseDirectionThinning NativeActivePhasePopulation
open NativeCombinedParentProfiles NativeLocalPairFibers
open NativeSharpMixedGrainCore
open scoped BigOperators

/-- One actual population-rich parent, its unchanged mixed grain fibers,
and all requested reference profiles on the SAME E1/E2/global-R source. -/
def HasSharpPopulationParentProfiles {n K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 E2 : Finset (Fin n × Index)) (a : ℝ) (level m : ℕ)
    (plane : Index → Submodule ℝ E4) (points : Finset Index) (q : ℝ) (ell Q2 F1 G Lgrain : ℕ)
    (lambda zeta tau seed c2 : ℝ) (depths : Fin K → ℕ) : Prop :=
  let W := mass points (pointWeight E2)
  let theta := lambda*(W:ℝ)/(2*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ))
  let mu := theta*D.thickness^eta
  let retain := mu/rowConstant
  0 < theta ∧ 0 < mu ∧ 0 < retain ∧
    ∃H⊆cutEdges E2 points,H.Nonempty ∧ W ≤ 2*H.card ∧
      ∃p∈R.image (parentLabel D a (2^m)),(parentEdges D a (2^m) H p).Nonempty ∧
        mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤ D.thickness*(parentEdges D a (2^m) H p).card ∧
        (∀I⊆retained original R,retain*(parentEdges D a (2^m) I p).card ≤ (parentEdges D a (2^m) H p).card) ∧
        (∀x∈parentEdges D a (2^m) H p,
          lambda*D.thickness^(2*eta+3*zeta+7*tau)*(W:ℝ)*Lgrain <
            parentGrainConstant*transverseCost q ell*(Q2:ℝ)^2*(F1:ℝ)*G*E2.card*
              (mixedVertices D a m (phaseDepth m) plane ell (parentEdges D a (2^m) H p)
                (mixedLabel D a m plane ell x)).card) ∧
        HasMixedIncidenceThreshold D a m plane ell E2 points (parentEdges D a (2^m) H p) ∧
        (∀u,HasParentProfiles h R E1 E2 a level m (depths u) p retain lambda tau seed c2) ∧
        ∀u,
          let relative := (64/((2^(depths u):ℕ):ℝ))/(64/((2^m:ℕ):ℝ))
          let M := (NativeFiniteKakeyaCounts.multiplicity
            (fullSource h R a level (depths u) (parentEdges D a (2^m) H p))).toReal
          retain*D.thickness^(tau+seed/8+10*min (boundaryWindow tau) ((tau/16)/1000))*relative^(-extremalExponent) ≤ M ∧
            M ≤ D.thickness^(-(3*tau))*relative^(-extremalExponent)

/-- The actual mixed core is selected once; averaging against the complete
R backbone constructs the parent. The same parent carries original-population
retention, exact grains and all reference/cleaned conditional profiles. -/
theorem source_sharp_population_parent_profiles {n d g level J Kmenu : ℕ} {D : FiniteScaleSource n}
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
    (hKn : K.Nonempty)
    (F2 : ℕ) (hQ2 : 0 < Q2) (hGF : G ≤ F2)
    (hRich : ∀e,e∈E2 → D.thickness^eta*(2^level:ℕ)/
      (16384*(((factor d (g+1) L:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E2 (localPair D a (2^level) e)).card)
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2))
    (depths : Fin Kmenu → ℕ)
    (hdepths : ∀u,m i ≤ depths u ∧ depths u ≤ phaseDepth (m i))
    (hhalfDepth : ∀u,(depths u:ℝ) ≤ (level:ℝ)/2)
    (HQ : ∀u,HasUniformFibers E2 Q2
      (fixedPair D a level (depths u) (depths u) (representative h R a (2^(depths u)))) ∧
      HasUniformFibers E2 Q2 (fixedPair D a level (depths u) (m i) (representative h R a (2^(depths u))))) :
    let plane := fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node))
    let Lgrain := predecessorProduct D (m i) E2 Q2
      (scaleThreshold D E2 (m i)
        (history D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 i.val)
        ell (natStageDirectionIndex h (tuple i))) ell
    HasSharpPopulationParentProfiles h original R E1 E2 a level (m i) plane K q ell Q2
      (factor d (g+1) L) G Lgrain lambda zeta tau seed c2 depths := by
  intro plane Lgrain
  obtain ⟨H,hHJ,hHn,hhalf,hmin,hgrain⟩ := source_sharp_mixed_grain_core h original R E1 E2 h21 hE2 L schedule Rel
    htau heta hseed hg hgl hgrid Hbackbone hschedule Hcore hcost hconditioned hreference
    G hG lambda hlambda hret _hJ m hm6 ell hell S0 hS0 Q2 HU hq hq1 point tuple anchor Hsys Hhistory
    i hf hsmall HP K hK hKn
  change HasMixedIncidenceThreshold D a (m i) plane ell E2 K H at hmin
  have hHE2 : H⊆E2 := hHJ.trans (cutEdges_subset E2 K)
  have hHE1 : H⊆E1 := hHE2.trans h21
  have hF1 : 0 < factor d (g+1) L := by dsimp [factor,NativeLocalPairUniformCore.retentionCost]; positivity
  have hW : 0 < mass K (pointWeight E2) := by
    rw [←cutEdges_card E2 K]
    exact card_pos.mpr (hHn.mono hHJ)
  let theta := lambda*(mass K (pointWeight E2):ℝ)/(2*(factor d (g+1) L:ℝ)*(G:ℝ)*(E2.card:ℝ))
  let mu := theta*D.thickness^eta
  let retain := mu/rowConstant
  obtain ⟨htheta,hmu,p,hpR,hHp,hpop,hIret⟩ := NativePopulationParentSelection.source_population_parent
    h original Hbackbone.1 hsmall R E1 E2 H Hcore.1 h21 hHE2 hHn
    (factor d (g+1) L) G (mass K (pointWeight E2)) hF1 hG hW Hcore.2.2.1
    lambda hlambda hret hhalf (m i)
  have hretain : 0 < retain := div_pos hmu rowConstant_pos
  have hp2 : (parentEdges D a (2^(m i)) E2 p).Nonempty := hHp.mono (filter_subset_filter _ hHE2)
  have hp1 : (parentEdges D a (2^(m i)) E1 p).Nonempty := hHp.mono (filter_subset_filter _ hHE1)
  have hE1ret : retain*(parentEdges D a (2^(m i)) E1 p).card ≤
      (parentEdges D a (2^(m i)) H p).card := hIret E1 Hcore.1
  have hE2ret : retain*(parentEdges D a (2^(m i)) E1 p).card ≤
      (parentEdges D a (2^(m i)) E2 p).card := hE1ret.trans
        (Nat.cast_le.mpr (card_le_card (filter_subset_filter _ hHE2)))
  have hE1 : E1⊆incidences original := Hcore.1.trans (filter_subset _ _)
  have hER1 : ∀z∈E1,z.1∈R := fun z hz => (mem_filter.mp (Hcore.1 hz)).2
  have hHer := NativeReferenceHereditaryUpper.from_master_reference h original R E1 schedule Rel
    htau heta hseed hg hgl hgrid Hbackbone hschedule Hcore hcost hconditioned hreference
  refine ⟨htheta,hmu,hretain,H,hHJ,hHn,hhalf,p,hpR,hHp,hpop,hIret,?_,?_,?_,?_⟩
  · intro x hx
    have hxH := (mem_filter.mp hx).1
    have hxp := (mem_filter.mp hx).2
    have he : mixedLabel D a (m i) plane ell x=(p,taggedLabel D (m i) plane ell x.2) := Prod.ext hxp rfl
    have hdense : lambda*D.thickness^(2*eta+3*zeta+7*tau)*(mass K (pointWeight E2):ℝ)*Lgrain <
        parentGrainConstant*transverseCost q ell*(Q2:ℝ)^2*(factor d (g+1) L:ℝ)*G*E2.card*
          (mixedVertices D a (m i) (phaseDepth (m i)) plane ell H
            (mixedLabel D a (m i) plane ell x)).card := hgrain x hxH
    simpa only [he,mixedVertices,parent_mixed_fiber_eq] using hdense
  · intro x hx
    have hxH := (mem_filter.mp hx).1
    have hxp := (mem_filter.mp hx).2
    have he : mixedLabel D a (m i) plane ell x=(p,taggedLabel D (m i) plane ell x.2) := Prod.ext hxp rfl
    simpa only [he,parent_mixed_fiber_eq] using hmin x hxH
  · intro u
    exact source_parent_profiles h original R E1 E2 h21 L schedule Rel htau heta hseed hg hgl hgrid
      Hbackbone hschedule Hcore hcost hconditioned hreference F2 G Q2 hG hQ2 hGF hlambda hRich hcost2
      (m i) (depths u) (hm6 i) (hdepths u).1 (hdepths u).2 (hhalfDepth u)
      (HQ u).1 (HQ u).2 p hp2 hretain hE2ret
  · intro u
    have hfL : depths u ≤ level := (hdepths u).2.trans hf
    exact ⟨NativeWindowPaidParentLower.master_parent_power_lower h heta htau original Hbackbone.1
      Hbackbone.2.2.1 R E1 H hE1 hER1 hHE1 level (m i) (depths u) Hbackbone.2.1
      (hdepths u).1 (hhalfDepth u) g hg hgrid hgl (coreRadix original R L)
      (factor d (g+1) L) hF1 hcost (by simpa only [hschedule] using hconditioned)
      hreference p hp1 hretain hE1ret,
      hHer H hHE1 (m i) (depths u) (hdepths u).1 hfL p⟩

end NativeSharpPopulationParentProfiles
