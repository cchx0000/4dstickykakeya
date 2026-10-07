import Theorems.Thm_StickyKakeya4_native_source_parent_grain_cleanup

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

noncomputable section
namespace NativeReferenceParentGrainCleanup
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

/-- Construct a genuine source-derived incidence core with quantitative grain
bounds for EVERY mixed fiber, before any parent is selected. -/
theorem source_mixed_grain_core {n d g level J : ℕ} {D : FiniteScaleSource n}
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
    ∃H⊆cutEdges E2 K,H.Nonempty ∧ mass K (pointWeight E2) ≤ 2*H.card ∧
      ∀x∈H,
          lambda*D.thickness^(2*eta+3*zeta+7*tau)*(mass K (pointWeight E2):ℝ)*Lgrain <
            parentGrainConstant*transverseCost q ell*(Q2:ℝ)^2*(factor d (g+1) L:ℝ)*G*E2.card*
              (mixedVertices D a (m i) (phaseDepth (m i)) plane ell H
                (mixedLabel D a (m i) plane ell x)).card := by
  intro plane Lgrain
  let F := history D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 J
  let M := vertexCap E2 (spatialLabel D (2^(phaseDepth (m i)))) Q2
  let B := 2401*((373248*D.thickness^(-zeta))*(D.thickness^(-(3*tau))*
    (1/((2^(m i):ℕ):ℝ))^(-extremalExponent)))
  let T := 625*transverseCost q ell*(Q2:ℝ)^2*E2.card
  let U := parentCapConstant*(factor d (g+1) L:ℝ)*G
  let A := lambda*D.thickness^(2*eta+2*zeta+4*tau)*(1/((2^(m i):ℕ):ℝ))^(-extremalExponent)
  have hd := h.1.2.1
  have hKE : K⊆E2.image Prod.snd := hK.trans ((Hhistory.2.2.1 J le_rfl).2.1.trans hS0)
  have hcf : m i ≤ phaseDepth (m i) := by dsimp [phaseDepth]; have hh := hm6 i; omega
  have hc : m i ≤ level := hcf.trans hf
  have hf6 : 6 ≤ phaseDepth (m i) := (hm6 i).trans hcf
  have hM : (0:ℝ)<M := by exact_mod_cast vertexCap_pos E2 hE2 (spatialLabel D (2^(phaseDepth (m i)))) Q2 (HU i)
  have hcounts := history_grain_counts h E2 hE2 m hm6 ell hell S0 hS0 Q2 HU hq hq1 point tuple anchor Hsys Hhistory
  have hLgrain : (0:ℝ)<Lgrain := by exact_mod_cast (hcounts i).1
  have hgrain : (M:ℝ)*Lgrain*(K.image (taggedLabel D (m i) plane ell)).card ≤ T := by
    calc
      _ ≤ (M:ℝ)*Lgrain*(F.image (taggedLabel D (m i) plane ell)).card :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card (image_subset_image hK))) (by positivity)
      _ ≤ _ := (hcounts i).2
  have hcount : (((cutEdges E2 K).image (mixedLabel D a (m i) plane ell)).card:ℝ) ≤
      B*(K.image (taggedLabel D (m i) plane ell)).card := by
    apply mixed_label_count D a (m i) plane ell E2 K hKE B
    intro S hSE v hv
    exact source_spatial_parent_count h original R E1 L schedule Rel htau heta hseed hg hgl hgrid
      Hbackbone hschedule Hcore hcost hconditioned hreference S (hSE.trans h21) (m i) hc v hv
  obtain ⟨H,hHJ,hHn,hhalf,hmin0⟩ := exists_mixed_dense_core D a (m i) plane ell E2 K hKE hKn
  have hHE : H⊆E2 := hHJ.trans (cutEdges_subset E2 K)
  have hN : (0:ℝ)<((cutEdges E2 K).image (mixedLabel D a (m i) plane ell)).card := by
    exact_mod_cast card_pos.mpr ((hHn.mono hHJ).image _)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT : 0 ≤ T := by dsimp [T]; exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (transverseCost_pos hq ell).le) (sq_nonneg _)) (Nat.cast_nonneg _)
  refine ⟨H,hHJ,hHn,by rwa [←cutEdges_card E2 K],?_⟩
  intro x hx
  have hcap : A*((mixedFiber D a (m i) plane ell H
      (mixedLabel D a (m i) plane ell x)).card:ℝ) ≤
      (U*(M:ℝ))*(mixedVertices D a (m i) (phaseDepth (m i)) plane ell
        H (mixedLabel D a (m i) plane ell x)).card := by
    apply mixed_vertex_cross D a (m i) (phaseDepth (m i)) plane ell E2 _ hHE _ A (U*(M:ℝ))
    intro S hSE v hparent hspace
    exact source_parent_vertex_cap h original R E1 E2 h21 hE2 L schedule Rel htau heta hseed hg hgl hgrid
      Hbackbone hschedule Hcore hcost hconditioned hreference G hG lambda hlambda.le hret
      (m i) (phaseDepth (m i)) Q2 hcf hf6 hf hsmall HP (HU i) S hSE _ v hparent hspace
  have hh := density_cap_cancellation hM hLgrain hN hA hB hT
    (Nat.cast_nonneg (mixedFiber D a (m i) plane ell H
      (mixedLabel D a (m i) plane ell x)).card)
    ((K.image (taggedLabel D (m i) plane ell)).card:ℝ) hcount hgrain (hmin0 x hx).2 hcap
  have hcancel := cancel_depth_and_taxes hd
    (by positivity : 0 < (1/((2^(m i):ℕ):ℝ))^(-extremalExponent)) hh
  rw [cutEdges_card E2 K] at hcancel
  convert hcancel using 1
  dsimp [parentGrainConstant,T,U]
  ring

/-- Choose the parent against original E1 after the same mixed cleanup.
The additional lambda/G tax is explicit and gives both retention comparisons
needed by the later conditional lower transfer. -/
theorem source_reference_parent_grain_cleanup {n d g level J : ℕ} {D : FiniteScaleSource n}
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
    let theta := lambda*(mass K (pointWeight E2):ℝ)/(2*(G:ℝ)*(E2.card:ℝ))
    0 < theta ∧ ∃H⊆cutEdges E2 K,H.Nonempty ∧ mass K (pointWeight E2) ≤ 2*H.card ∧
      ∃p : Parent,(parentEdges D a (2^(m i)) H p).Nonempty ∧
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
  have hEcard : (0:ℝ)<E2.card := by exact_mod_cast card_pos.mpr hE2
  have hGr : (0:ℝ)<G := by exact_mod_cast hG
  have hW : (0:ℝ) < mass K (pointWeight E2) := by
    rw [←cutEdges_card E2 K]
    exact_mod_cast card_pos.mpr (hHn.mono hHJ)
  have hden : 0 < 2*(G:ℝ)*(E2.card:ℝ) := by positivity
  have htheta : 0 < theta := by dsimp [theta]; positivity
  have hhalfR : (mass K (pointWeight E2):ℝ) ≤ 2*(H.card:ℝ) := by exact_mod_cast hhalf
  have hh : lambda*(mass K (pointWeight E2):ℝ)*E1.card ≤
      (H.card:ℝ)*(2*(G:ℝ)*(E2.card:ℝ)) := by
    calc
      _ = (mass K (pointWeight E2):ℝ)*(lambda*E1.card) := by ring
      _ ≤ (mass K (pointWeight E2):ℝ)*((G:ℝ)*E2.card) := mul_le_mul_of_nonneg_left hret hW.le
      _ = ((G:ℝ)*E2.card)*(mass K (pointWeight E2):ℝ) := by ring
      _ ≤ ((G:ℝ)*E2.card)*(2*(H.card:ℝ)) := mul_le_mul_of_nonneg_left hhalfR (by positivity)
      _ = _ := by ring
  have hthetaRet : theta*(E1.card:ℝ) ≤ (H.card:ℝ) := by
    dsimp [theta]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hden).mpr hh
  obtain ⟨p,_hp,_hE1p,hHp,hlocal⟩ := NativeDensePhaseParentRetention.exists_retained_fiber
    E1 H hHE1 (hE2.mono h21) (fun z => parentLabel D a (2^(m i)) z.1) theta 1 htheta
      (by simpa only [one_mul] using hthetaRet)
  have hmain : theta*(parentEdges D a (2^(m i)) E1 p).card ≤
      (parentEdges D a (2^(m i)) H p).card := by simpa only [one_mul,parentEdges] using hlocal
  have hHparent : ((parentEdges D a (2^(m i)) H p).card:ℝ) ≤
      (parentEdges D a (2^(m i)) E2 p).card := by
    exact_mod_cast card_le_card (filter_subset_filter _ hHE2)
  have hEparent : ((parentEdges D a (2^(m i)) E2 p).card:ℝ) ≤
      (parentEdges D a (2^(m i)) E1 p).card := by
    exact_mod_cast card_le_card (filter_subset_filter _ h21)
  refine ⟨htheta,H,hHJ,hHn,hhalf,p,hHp,hmain,hmain.trans hHparent,
    (mul_le_mul_of_nonneg_left hEparent htheta.le).trans hmain,?_⟩
  intro x hx
  have hxH := (mem_filter.mp hx).1
  have hxp := (mem_filter.mp hx).2
  have he : mixedLabel D a (m i) plane ell x=(p,taggedLabel D (m i) plane ell x.2) := Prod.ext hxp rfl
  have hdense : lambda*D.thickness^(2*eta+3*zeta+7*tau)*(mass K (pointWeight E2):ℝ)*Lgrain <
      parentGrainConstant*transverseCost q ell*(Q2:ℝ)^2*(factor d (g+1) L:ℝ)*G*E2.card*
        (mixedVertices D a (m i) (phaseDepth (m i)) plane ell H
          (mixedLabel D a (m i) plane ell x)).card := hgrain x hxH
  simpa only [he,mixedVertices,parent_mixed_fiber_eq] using hdense

end NativeReferenceParentGrainCleanup
