import Theorems.Thm_StickyKakeya4_native_sharp_mixed_grain_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

noncomputable section
namespace NativeSaturatedMixedGrainCore
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

open NativeSharpMixedGrainCore NativeSimultaneousWeightedGrainCore NativeAutomaticWeightedGrainCore

/-- The actual deletion core keeps entire equivalence classes of all maps. -/
def SaturatedMaps {α : Type*} {J : ℕ} {β : Fin J → Type*}
    (A K : Finset α) (f : (j : Fin J) → α → β j) : Prop :=
  ∀x∈K,∀y∈A,(∀j,f j y=f j x) → y∈K

/-- Original incidences at a surviving old point are kept without thinning. -/
def HasPointSaturation {n : ℕ} (E H : Finset (Fin n × Index)) : Prop :=
  ∀x∈H,∀y∈E,y.2=x.2 → y∈H

def HasMixedSaturation {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (plane : Index → Submodule ℝ E4) (ell : ℕ) (E : Finset (Fin n × Index))
    (K : Finset Index) (H : Finset (Fin n × Index)) : Prop :=
  ∀x∈H,∀y∈cutEdges E K,mixedLabel D a m plane ell y=mixedLabel D a m plane ell x → y∈H

theorem exists_simultaneous_saturated_core {α : Type*} {J : ℕ} {β : Fin J → Type*}
    (A : Finset α) (f : (j : Fin J) → α → β j) (w : α → ℕ) (k : Fin J → ℕ) :
    ∃K⊆A, SaturatedMaps A K f ∧ (∀j,∀c∈K.image (f j), k j ≤ mass (classFiber K (f j) c) w) ∧
      mass A w ≤ mass K w+classBudget A f k := by
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hgood : ∀j,∀c∈A.image (f j), k j ≤ mass (classFiber A (f j) c) w
    · exact ⟨A,Subset.refl _,(fun _ _ y hy _ => hy),hgood,Nat.le_add_right _ _⟩
    · push Not at hgood
      obtain ⟨j,c,hc,hbad⟩ := hgood
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hc
      let B := eraseFiber A (f j) (f j x)
      have hBA : B⊂A := by
        apply filter_ssubset.mpr
        exact ⟨x,hx,by simp⟩
      obtain ⟨K,hKB,hsat,hmin,hmass⟩ := ih B hBA
      have hcost := eraseFiber_budget A f k j x hx
      have hsplit := eraseFiber_mass A (f j) w (f j x)
      have hsmall : mass (classFiber A (f j) (f j x)) w ≤ k j-1 := by omega
      have hsatA : SaturatedMaps A K f := by
        intro u hu y hy heq
        have huB := hKB hu
        have hyB : y∈B := by
          apply mem_filter.mpr
          refine ⟨hy,?_⟩
          rw [heq j]
          exact (mem_filter.mp huB).2
        exact hsat u hu y hyB heq
      refine ⟨K,hKB.trans (eraseFiber_subset A (f j) (f j x)),hsatA,hmin,?_⟩
      change mass B w ≤ mass K w+classBudget B f k at hmass
      change classBudget B f k+(k j-1) ≤ classBudget A f k at hcost
      change mass A w=mass B w+mass (classFiber A (f j) (f j x)) w at hsplit
      omega


theorem exists_automatic_saturated_core {α : Type*} {J : ℕ} {β : Fin J → Type*}
    (hJ : 0 < J) (A : Finset α) (f : (j : Fin J) → α → β j) (w : α → ℕ)
    (hpos : 0 < mass A w) :
    ∃K⊆A, K.Nonempty ∧ SaturatedMaps A K f ∧ mass A w ≤ 2*mass K w ∧
      mass (A\K) w ≤ classBudget A f (fun j => threshold (mass A w) J (A.image (f j)).card) ∧
      ∀j,∀c∈K.image (f j),
        threshold (mass A w) J (A.image (f j)).card ≤ mass (classFiber K (f j) c) w ∧
        (mass A w:ℝ)/(2*(J:ℝ)*((A.image (f j)).card:ℝ)) <
          (mass (classFiber K (f j) c) w:ℝ) := by
  let k := fun j => threshold (mass A w) J (A.image (f j)).card
  have hbudget : 2*classBudget A f k ≤ mass A w :=
    threshold_budget (mass A w) J hJ (fun j => (A.image (f j)).card)
  obtain ⟨K,hKA,hsat,hmin,hmass⟩ := exists_simultaneous_saturated_core A f w k
  have hhalf : mass A w ≤ 2*mass K w := by omega
  have hKpos : 0 < mass K w := by omega
  have hKne : K.Nonempty := by
    by_contra hne
    have hz : mass K w=0 := by rw [not_nonempty_iff_eq_empty.mp hne]; simp [WeightedRichDirectionalLayers.mass]
    omega
  have hloss := removed_mass_le A K w _ hKA hmass
  refine ⟨K,hKA,hKne,hsat,hhalf,hloss,?_⟩
  intro j c hc
  have hC : 0 < (A.image (f j)).card :=
    card_pos.mpr ⟨c,(image_subset_image hKA) hc⟩
  have hmin' := hmin j c hc
  refine ⟨hmin',?_⟩
  have hcast : (threshold (mass A w) J (A.image (f j)).card:ℝ) ≤
      (mass (classFiber K (f j) c) w:ℝ) := by exact_mod_cast hmin'
  exact (threshold_real (mass A w) J (A.image (f j)).card hJ hC).trans_le hcast

theorem exists_saturated_mixed_dense_core {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (E : Finset (Fin n × Index))
    (K : Finset Index) (hK : K⊆E.image Prod.snd) (hKn : K.Nonempty) :
    ∃H⊆cutEdges E K,H.Nonempty ∧ HasMixedSaturation D a m P ell E K H ∧ (cutEdges E K).card ≤ 2*H.card ∧
      ∀x∈H,
        threshold (cutEdges E K).card 1 ((cutEdges E K).image (mixedLabel D a m P ell)).card ≤
          (mixedFiber D a m P ell H (mixedLabel D a m P ell x)).card ∧
        ((cutEdges E K).card:ℝ)/(2*((((cutEdges E K).image (mixedLabel D a m P ell)).card):ℝ)) <
          ((mixedFiber D a m P ell H (mixedLabel D a m P ell x)).card:ℝ) := by
  have hJ : (cutEdges E K).Nonempty := by
    have hh : ((cutEdges E K).image Prod.snd).Nonempty := by rwa [cutEdges_points E K hK]
    exact hh.of_image
  have hunit (S : Finset (Fin n × Index)) : mass S (fun _ => 1)=S.card := by simp [WeightedRichDirectionalLayers.mass]
  have hpos : 0 < mass (cutEdges E K) (fun _ => 1) := by rw [hunit]; exact card_pos.mpr hJ
  obtain ⟨H,hHJ,hHn,hsat,hhalf,_hloss,hmin⟩ :=
    exists_automatic_saturated_core (β:=fun _ : Fin 1 => Parent × (Index × Index))
      (by norm_num) (cutEdges E K) (fun _ => mixedLabel D a m P ell) (fun _ => 1) hpos
  have hsatMixed : HasMixedSaturation D a m P ell E K H := by
    intro x hx y hy hxy
    exact hsat x hx y hy (fun _ => hxy)
  refine ⟨H,hHJ,hHn,hsatMixed,by simpa only [hunit] using hhalf,?_⟩
  intro x hx
  have hm := hmin (0:Fin 1) (mixedLabel D a m P ell x) (by
    simp only [mem_image]
    exact ⟨x,hx,rfl⟩)
  simpa only [hunit,classical_image_eq,Nat.cast_one,mul_one,mixedFiber] using hm


theorem source_saturated_mixed_grain_core {n d g level J : ℕ} {D : FiniteScaleSource n}
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
      HasMixedIncidenceThreshold D a (m i) plane ell E2 K H ∧
      HasMixedSaturation D a (m i) plane ell E2 K H ∧
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
  obtain ⟨H,hHJ,hHn,hsat,hhalf,hmin0⟩ := exists_saturated_mixed_dense_core D a (m i) plane ell E2 K hKE hKn
  have hHE : H⊆E2 := hHJ.trans (cutEdges_subset E2 K)
  have hN : (0:ℝ)<((cutEdges E2 K).image (mixedLabel D a (m i) plane ell)).card := by
    exact_mod_cast card_pos.mpr ((hHn.mono hHJ).image _)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT : 0 ≤ T := by dsimp [T]; exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (transverseCost_pos hq ell).le) (sq_nonneg _)) (Nat.cast_nonneg _)
  refine ⟨H,hHJ,hHn,by rwa [←cutEdges_card E2 K],hmin0,hsat,?_⟩
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


end NativeSaturatedMixedGrainCore
