import Theorems.Thm_StickyKakeya4_native_parent_grain_incidence_cleanup
import Theorems.Thm_StickyKakeya4_native_parent_vertex_mass_cap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

noncomputable section
namespace NativeSourceParentGrainCleanup
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

/-- Sum the actual parent/vertex cross bound over the raw vertices of one mixed fiber. -/
lemma mixed_vertex_cross {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (E H : Finset (Fin n × Index)) (hHE : H⊆E)
    (c : Parent × (Index × Index)) (A C : ℝ)
    (HC : ∀S⊆E,∀v : Index,(∀z∈S,parentLabel D a (2^m) z.1=c.1) →
      (∀z∈S,spatialLabel D (2^f) z.2=v) → A*(S.card:ℝ) ≤ C) :
    A*((mixedFiber D a m P ell H c).card:ℝ) ≤ C*(mixedVertices D a m f P ell H c).card := by
  let F := mixedFiber D a m P ell H c
  let raw := fun z : Fin n × Index => spatialLabel D (2^f) z.2
  have hs : (F.card:ℝ)=∑v∈F.image raw,((F.filter (fun z => raw z=v)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image raw F
  calc
    _ = ∑v∈F.image raw,A*((F.filter (fun z => raw z=v)).card:ℝ) := by rw [←mul_sum,←hs]
    _ ≤ ∑_v∈F.image raw,C := by
      apply sum_le_sum
      intro v _hv
      have hsub : F.filter (fun z => raw z=v) ⊆ E := by
        intro z hz
        have hh := (mem_filter.mp hz).1
        simp only [F,mixedFiber,classFiber,mem_filter] at hh
        exact hHE hh.1
      apply HC (F.filter (fun z => raw z=v)) hsub v
      · intro z hz
        have hh := (mem_filter.mp hz).1
        simp only [F,mixedFiber,classFiber,mem_filter] at hh
        exact congrArg Prod.fst hh.2
      · exact fun z hz => (mem_filter.mp hz).2
    _ = _ := by simp only [sum_const,nsmul_eq_mul,mixedVertices,F,raw]; ring

/-- Cancel the computed global fine-vertex cap between actual grain counts
and actual parent-grain incidence masses. -/
lemma density_cap_cancellation {W M L N B T U A F V : ℝ}
    (hM : 0 < M) (hL : 0 < L) (hN : 0 < N) (hA : 0 < A)
    (hB : 0 ≤ B) (hT : 0 ≤ T) (hF : 0 ≤ F)
    (G : ℝ) (hcount : N ≤ B*G) (hgrain : M*L*G ≤ T)
    (hdense : W/(2*N) < F) (hcap : A*F ≤ U*M*V) :
    A*W*L < 2*B*T*U*V := by
  have hd : W < 2*N*F := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 2*N)).mp hdense
    nlinarith only [hh]
  have hfirst : W*M*L < 2*B*T*F := by
    calc
      _ < (2*N*F)*(M*L) := by
        simpa only [mul_assoc] using mul_lt_mul_of_pos_right hd (mul_pos hM hL)
      _ ≤ (2*(B*G)*F)*(M*L) := by gcongr
      _ = (2*B*F)*(M*L*G) := by ring
      _ ≤ (2*B*F)*T := mul_le_mul_of_nonneg_left hgrain (by positivity)
      _ = _ := by ring
  have hsecond : A*(W*M*L) < (2*B*T)*(U*M*V) := by
    calc
      _ < A*(2*B*T*F) := mul_lt_mul_of_pos_left hfirst hA
      _ = (2*B*T)*(A*F) := by ring
      _ ≤ (2*B*T)*(U*M*V) := mul_le_mul_of_nonneg_left hcap (by positivity)
  have hh : M*(A*W*L) < M*(2*B*T*U*V) := by
    convert hsecond using 1 <;> ring
  exact (mul_lt_mul_iff_right₀ hM).mp hh

/-- The coarse depth power cancels exactly, leaving only the displayed source taxes. -/
lemma cancel_depth_and_taxes {delta eta zeta tau lambda depthPower W L T U V : ℝ}
    (hd : 0 < delta) (hp : 0 < depthPower)
    (H : (lambda*delta^(2*eta+2*zeta+4*tau)*depthPower)*W*L <
      2*(2401*((373248*delta^(-zeta))*(delta^(-(3*tau))*depthPower)))*T*U*V) :
    lambda*delta^(2*eta+3*zeta+7*tau)*W*L < 2*(2401*373248)*T*U*V := by
  have hh : depthPower*(lambda*delta^(2*eta+2*zeta+4*tau)*W*L) <
      depthPower*(2*(2401*373248)*delta^(-zeta)*delta^(-(3*tau))*T*U*V) := by
    convert H using 1 <;> ring
  have hc := (mul_lt_mul_iff_right₀ hp).mp hh
  have ht := mul_lt_mul_of_pos_right hc (Real.rpow_pos_of_pos hd (zeta+3*tau))
  have hl : delta^(2*eta+2*zeta+4*tau)*delta^(zeta+3*tau)=delta^(2*eta+3*zeta+7*tau) := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  have hr : delta^(-zeta)*delta^(-(3*tau))*delta^(zeta+3*tau)=1 := by
    rw [←Real.rpow_add hd,←Real.rpow_add hd]
    rw [show -zeta + -(3*tau) + (zeta+3*tau)=0 by ring,Real.rpow_zero]
  calc
    _ = (lambda*delta^(2*eta+2*zeta+4*tau)*W*L)*delta^(zeta+3*tau) := by rw [←hl]; ring
    _ < (2*(2401*373248)*delta^(-zeta)*delta^(-(3*tau))*T*U*V)*delta^(zeta+3*tau) := ht
    _ = (2*(2401*373248)*T*U*V)*(delta^(-zeta)*delta^(-(3*tau))*delta^(zeta+3*tau)) := by ring
    _ = _ := by rw [hr,mul_one]

def parentGrainConstant : ℝ := 2*(2401*373248)*625*parentCapConstant

/-- Clean ORIGINAL INCIDENCES over a prescribed final point core. All global
grain counts and both parent bounds are derived from the actual history and
original source. A parent is chosen only after mixed-fiber cleanup. -/
theorem source_parent_grain_cleanup {n d g level J : ℕ} {D : FiniteScaleSource n}
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
      ∃p : Parent,(parentEdges D a (2^(m i)) H p).Nonempty ∧
        (mass K (pointWeight E2):ℝ)*(parentEdges D a (2^(m i)) E2 p).card ≤
          2*(E2.card:ℝ)*(parentEdges D a (2^(m i)) H p).card ∧
        ∀x∈parentEdges D a (2^(m i)) H p,
          lambda*D.thickness^(2*eta+3*zeta+7*tau)*(mass K (pointWeight E2):ℝ)*Lgrain <
            parentGrainConstant*transverseCost q ell*(Q2:ℝ)^2*(factor d (g+1) L:ℝ)*G*E2.card*
              (mixedVertices D a (m i) (phaseDepth (m i)) plane ell (parentEdges D a (2^(m i)) H p)
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
  have hEcard : (0:ℝ)<E2.card := by exact_mod_cast card_pos.mpr hE2
  have hW : (0:ℝ)<(cutEdges E2 K).card := by exact_mod_cast card_pos.mpr (hHn.mono hHJ)
  obtain ⟨p,_hpE,_hEp,hp,hretLocal⟩ := NativeDensePhaseParentRetention.exists_retained_fiber
    E2 H hHE hE2 (fun z => parentLabel D a (2^(m i)) z.1)
    ((cutEdges E2 K).card/(E2.card:ℝ)) 2 (div_pos hW hEcard) (by
      rw [div_mul_cancel₀ _ hEcard.ne']
      exact_mod_cast hhalf)
  have hretp : (mass K (pointWeight E2):ℝ)*(parentEdges D a (2^(m i)) E2 p).card ≤
      2*(E2.card:ℝ)*(parentEdges D a (2^(m i)) H p).card := by
    have hh : ((cutEdges E2 K).card/(E2.card:ℝ))*(parentEdges D a (2^(m i)) E2 p).card ≤
        2*(parentEdges D a (2^(m i)) H p).card := by
      simpa only [parentEdges] using hretLocal
    rw [←cutEdges_card E2 K]
    calc
      _ = (E2.card:ℝ)*(((cutEdges E2 K).card/(E2.card:ℝ))*(parentEdges D a (2^(m i)) E2 p).card) := by
        field_simp
      _ ≤ (E2.card:ℝ)*(2*(parentEdges D a (2^(m i)) H p).card) := mul_le_mul_of_nonneg_left hh hEcard.le
      _ = _ := by ring
  have hmin : ∀x∈parentEdges D a (2^(m i)) H p,
      ((cutEdges E2 K).card:ℝ)/(2*((((cutEdges E2 K).image (mixedLabel D a (m i) plane ell)).card):ℝ)) <
        ((mixedFiber D a (m i) plane ell (parentEdges D a (2^(m i)) H p)
          (mixedLabel D a (m i) plane ell x)).card:ℝ) := by
    intro x hx
    have hxH := (mem_filter.mp hx).1
    have hxp := (mem_filter.mp hx).2
    have he : mixedLabel D a (m i) plane ell x=(p,taggedLabel D (m i) plane ell x.2) := Prod.ext hxp rfl
    rw [he,parent_mixed_fiber_eq]
    simpa only [he] using (hmin0 x hxH).2
  have hPE : parentEdges D a (2^(m i)) H p⊆E2 := (filter_subset _ _).trans hHE
  have hN : (0:ℝ)<((cutEdges E2 K).image (mixedLabel D a (m i) plane ell)).card := by
    exact_mod_cast card_pos.mpr ((hHn.mono hHJ).image _)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT : 0 ≤ T := by dsimp [T]; exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (transverseCost_pos hq ell).le) (sq_nonneg _)) (Nat.cast_nonneg _)
  refine ⟨H,hHJ,hHn,by rwa [←cutEdges_card E2 K],p,hp,hretp,?_⟩
  intro x hx
  have hcap : A*((mixedFiber D a (m i) plane ell (parentEdges D a (2^(m i)) H p)
      (mixedLabel D a (m i) plane ell x)).card:ℝ) ≤
      (U*(M:ℝ))*(mixedVertices D a (m i) (phaseDepth (m i)) plane ell
        (parentEdges D a (2^(m i)) H p) (mixedLabel D a (m i) plane ell x)).card := by
    apply mixed_vertex_cross D a (m i) (phaseDepth (m i)) plane ell E2 _ hPE _ A (U*(M:ℝ))
    intro S hSE v hparent hspace
    exact source_parent_vertex_cap h original R E1 E2 h21 hE2 L schedule Rel htau heta hseed hg hgl hgrid
      Hbackbone hschedule Hcore hcost hconditioned hreference G hG lambda hlambda.le hret
      (m i) (phaseDepth (m i)) Q2 hcf hf6 hf hsmall HP (HU i) S hSE _ v hparent hspace
  have hh := density_cap_cancellation hM hLgrain hN hA hB hT
    (Nat.cast_nonneg (mixedFiber D a (m i) plane ell (parentEdges D a (2^(m i)) H p)
      (mixedLabel D a (m i) plane ell x)).card)
    ((K.image (taggedLabel D (m i) plane ell)).card:ℝ) hcount hgrain (hmin x hx) hcap
  have hcancel := cancel_depth_and_taxes hd
    (by positivity : 0 < (1/((2^(m i):ℕ):ℝ))^(-extremalExponent)) hh
  rw [cutEdges_card E2 K] at hcancel
  convert hcancel using 1
  dsimp [parentGrainConstant,T,U]
  ring

end NativeSourceParentGrainCleanup
