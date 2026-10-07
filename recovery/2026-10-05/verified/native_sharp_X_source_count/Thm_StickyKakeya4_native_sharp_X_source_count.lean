import Theorems.Thm_StickyKakeya4_native_sharp_X_cap_cancellation
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeSharpXSourceCount
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

lemma cancel_depth_and_taxes_le {delta eta zeta tau lambda depthPower W L T U V : ℝ}
    (hd : 0 < delta) (hp : 0 < depthPower)
    (H : (lambda*delta^(2*eta+2*zeta+4*tau)*depthPower)*W*L ≤
      2*(2401*((373248*delta^(-zeta))*(delta^(-(3*tau))*depthPower)))*T*U*V) :
    lambda*delta^(2*eta+3*zeta+7*tau)*W*L ≤ 2*(2401*373248)*T*U*V := by
  have hh : depthPower*(lambda*delta^(2*eta+2*zeta+4*tau)*W*L) ≤
      depthPower*(2*(2401*373248)*delta^(-zeta)*delta^(-(3*tau))*T*U*V) := by
    convert H using 1 <;> ring
  have hc := (mul_le_mul_iff_right₀ hp).mp hh
  have ht := mul_le_mul_of_nonneg_right hc (Real.rpow_pos_of_pos hd (zeta+3*tau)).le
  have hl : delta^(2*eta+2*zeta+4*tau)*delta^(zeta+3*tau)=delta^(2*eta+3*zeta+7*tau) := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  have hr : delta^(-zeta)*delta^(-(3*tau))*delta^(zeta+3*tau)=1 := by
    rw [←Real.rpow_add hd,←Real.rpow_add hd]
    rw [show -zeta + -(3*tau) + (zeta+3*tau)=0 by ring,Real.rpow_zero]
  calc
    _ = (lambda*delta^(2*eta+2*zeta+4*tau)*W*L)*delta^(zeta+3*tau) := by rw [←hl]; ring
    _ ≤ (2*(2401*373248)*delta^(-zeta)*delta^(-(3*tau))*T*U*V)*delta^(zeta+3*tau) := ht
    _ = (2*(2401*373248)*T*U*V)*(delta^(-zeta)*delta^(-(3*tau))*delta^(zeta+3*tau)) := by ring
    _ = _ := by rw [hr,mul_one]

theorem source_threshold_cross_cancellation {n d g level J : ℕ} {D : FiniteScaleSource n}
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
    (G : ℕ) (hG : 0 < G) (lambda : ℝ) (_hlambda : 0 < lambda)
    (_hret : lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card)
    (_hJ : 0 < J) (m : Fin J → ℕ) (hm6 : ∀i,6 ≤ m i) (ell : ℕ) (hell : ell ≤ 4)
    (S0 : Finset Index) (hS0 : S0⊆E2.image Prod.snd) (Q2 : ℕ)
    (HU : ∀i,HasUniformFibers E2 Q2 (fun z => spatialLabel D (2^(phaseDepth (m i))) z.2))
    (hq : 0 < q) (hq1 : q ≤ 1)
    (point : Fin J → Index → Index)
    (tuple : Fin J → Index → Fin ell → (Fin n × Index))
    (anchor : Fin J → Index → Fin ell → Fin n)
    (Hsys : ∀i,IsNodeDirectionSystem D a (m i) E2 S0 q ell (point i) (tuple i) (anchor i))
    (Hhistory : HasGrainHistory D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 Q2 lambda c1 c2)
    (i : Fin J) (hf : phaseDepth (m i) ≤ level) (_hsmall : D.thickness ≤ 1/8)
    (_HP : HasUniformFibers E2 Q2 (physicalPair h R a level (phaseDepth (m i))))
    (K : Finset Index)
    (hK : K⊆history D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 J)
    (hKn : K.Nonempty) :
    let plane := fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple i node))
    let Lgrain := predecessorProduct D (m i) E2 Q2
      (scaleThreshold D E2 (m i)
        (history D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 i.val)
        ell (natStageDirectionIndex h (tuple i))) ell
    let M := vertexCap E2 (spatialLabel D (2^(phaseDepth (m i)))) Q2
    let N := ((cutEdges E2 K).image (mixedLabel D a (m i) plane ell)).card
    let A := lambda*D.thickness^(2*eta+2*zeta+4*tau)*(1/((2^(m i):ℕ):ℝ))^(-extremalExponent)
    let U := parentCapConstant*(factor d (g+1) L:ℝ)*G
    ∀loss Ht X : ℝ,0 ≤ loss → 0 ≤ Ht → 0 ≤ X →
      A*(((cutEdges E2 K).card:ℝ)/(2*(N:ℝ))) ≤ loss*(U*(M:ℝ))*Ht*X →
      lambda*D.thickness^(2*eta+3*zeta+7*tau)*(mass K (pointWeight E2):ℝ)*Lgrain ≤
        parentGrainConstant*transverseCost q ell*(Q2:ℝ)^2*(factor d (g+1) L:ℝ)*G*E2.card*loss*Ht*X := by
  intro plane Lgrain M N A U loss Ht X hloss hHt hX hcross
  let F := history D E2 m ell (fun i => natStageDirectionIndex h (tuple i)) S0 J
  let B := 2401*((373248*D.thickness^(-zeta))*(D.thickness^(-(3*tau))*
    (1/((2^(m i):ℕ):ℝ))^(-extremalExponent)))
  let T := 625*transverseCost q ell*(Q2:ℝ)^2*E2.card
  have hd := h.1.2.1
  have hKE : K⊆E2.image Prod.snd := hK.trans ((Hhistory.2.2.1 J le_rfl).2.1.trans hS0)
  have hcf : m i ≤ phaseDepth (m i) := by dsimp [phaseDepth]; have hh := hm6 i; omega
  have hc : m i ≤ level := hcf.trans hf
  have _hf6 : 6 ≤ phaseDepth (m i) := (hm6 i).trans hcf
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
  have hN : (0:ℝ)<N := by
    have hcut : (cutEdges E2 K).Nonempty := by
      have hh : ((cutEdges E2 K).image Prod.snd).Nonempty := by rwa [cutEdges_points E2 K hKE]
      exact hh.of_image
    exact_mod_cast card_pos.mpr (hcut.image _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hU : 0 ≤ U := by
    have hh := parentCapConstant_pos
    dsimp [U]
    positivity
  have hh := cross_cap_cancellation hM.le hLgrain.le hN hB hU hloss hHt hX hcount hgrain hcross
  have hh' : A*(cutEdges E2 K).card*Lgrain ≤ 2*B*T*U*(loss*Ht*X) := by
    convert hh using 1
    ring
  have hcancel := cancel_depth_and_taxes_le hd
    (by positivity : 0 < (1/((2^(m i):ℕ):ℝ))^(-extremalExponent)) hh'
  rw [cutEdges_card E2 K] at hcancel
  convert hcancel using 1
  dsimp [parentGrainConstant,T,U]
  ring

end NativeSharpXSourceCount
