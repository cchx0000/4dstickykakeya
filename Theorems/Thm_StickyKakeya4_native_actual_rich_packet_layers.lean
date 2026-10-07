import Theorems.Thm_StickyKakeya4_native_tagged_reference_density
import Theorems.Thm_StickyKakeya4_native_packet_retained_layers

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000

noncomputable section
namespace NativeActualRichPacketLayers
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeSpatialAngularGeometry
open NativeCoarseShadingUniformity NativeCoarseDirectionThinning NativeOriginalParentDensityCore
open NativeLocalPairFibers NativeShortRowPackets NativeSquaredGrainQueries NativeNodalReferenceLift
open NativeOriginalPacketReference NativeTaggedPacketRows NativeQueriedVertexWeights
open NativeTaggedReferenceDensity NativeJointUniformCoarseRelations NativeDirectionRankDichotomy
open RichDirectionalLayers WeightedRichDirectionalLayers NativeWeightedPacketLayers NativePacketRetainedLayers
open scoped BigOperators

/-- The entire reference budget is a fixed geometric constant times the
unchanged E2 incidence mass. -/
def referenceConstant : ℕ := 8193^4*(257^4*1025)

lemma referenceConstant_pos : 0 < referenceConstant := by norm_num [referenceConstant]

lemma packetMass_eq_of_subset {A B : Type*} (R : Finset A) (packet : B → Finset A)
    (w : A → ℕ) (c : B) (hc : packet c⊆R) :
    packetMass R packet w c=mass (packet c) w := by
  unfold packetMass
  rw [inter_eq_right.mpr hc]

/-- The real lower bound is evaluated at an ACTUAL minimizing packet. -/
lemma real_le_referenceMinimum {A B : Type*} (R U : Finset A) (packet : B → Finset A)
    (label : A → B) (w : A → ℕ) (hU : U.Nonempty) (lower : ℝ)
    (H : ∀u∈U,lower ≤ (packetMass R packet w (label u):ℝ)) :
    lower ≤ (referenceMinimum R U packet label w:ℝ) := by
  rw [referenceMinimum,dif_pos hU]
  obtain ⟨u,hu,he⟩ := mem_image.mp
    (min'_mem (U.image (fun u => packetMass R packet w (label u))) (hU.image _))
  rw [←he]
  exact H u hu

lemma original_point_mass_positive {n : ℕ} (E : Finset (Fin n × Index))
    (S : Finset Index) (hS : S⊆E.image Prod.snd) (hSn : S.Nonempty) :
    0 < mass S (pointWeight E) := by
  obtain ⟨k,hk⟩ := hSn
  obtain ⟨z,hz,hzk⟩ := mem_image.mp (hS hk)
  have hp : 0 < pointWeight E k := card_pos.mpr ⟨z,mem_filter.mpr ⟨hz,hzk⟩⟩
  have hs : pointWeight E k ≤ mass S (pointWeight E) :=
    single_le_sum (fun _ _ => Nat.zero_le _) hk
  exact hp.trans_le hs

/-- Actual packet membership bounds every overlap count; no overlap
certificate or auxiliary small parameter is supplied. -/
lemma packet_overlap_le {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (S : Finset Index) (T : Finset (Index × (Index × ℤ)))
    (dir : Index → Fin n) :
    overlapCount (reference D m E S) T
      (packetSet D m E S dir) ≤ 257^4*1025 := by
  apply Finset.sup_le
  intro u _hu
  have hsub : T.filter (fun c => u∈packetSet D m E S dir c) ⊆
      T.filter
        (fun c => taggedPacket (fun node => slopeVector D (dir node))
          (64/((2^(phaseDepth m):ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) (rawVertex D (phaseDepth m)) c u) := by
    intro c hc
    exact mem_filter.mpr ⟨(mem_filter.mp hc).1,(mem_filter.mp (mem_filter.mp hc).2).2⟩
  convert (card_le_card hsub).trans (tagged_packet_overlap _ _ _ _ _ u) using 1
  congr

lemma computed_reference_budget_le {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (S : Finset Index)
    (U : Finset (Index × Index)) (dir : ℕ → Index → Fin n) (ell : ℕ) :
    referenceBudget (reference D m E S) U (fun i => packetSet D m E S (dir i))
      (fun i => assignedLabel D m (dir i)) (tagWeight E) ell ≤ referenceConstant*E.card := by
  unfold referenceBudget
  apply max_le
  · exact Nat.succ_le_of_lt (Nat.mul_pos referenceConstant_pos (card_pos.mpr hE))
  · calc
      _ ≤ (257^4*1025)*(8193^4*E.card) := by
        apply Nat.mul_le_mul _ (reference_mass_le D m E S)
        apply Finset.sup_le
        intro i _hi
        exact packet_overlap_le D m E S _ (dir i)
      _ = referenceConstant*E.card := by unfold referenceConstant; ring

/-- The actual initial/reference mass ratio is retained in the threshold
estimate. The reference minimum and budget are never independently normalized. -/
lemma threshold_ratio_lower (W N ell B total M C : ℕ) (hN : 0 < N) (hell : 0 < ell)
    (htotal : 0 < total) (hM : 0 < M) (hC : 0 < C)
    (hbudget : N ≤ C*total) (a : ℝ) (_ha : 0 ≤ a) (hB : (M:ℝ)*a ≤ B) :
    ((W:ℝ)/(total:ℝ))*a/(2*(ell:ℝ)*(C:ℝ)) <
      (richThreshold W N ell B:ℝ)/(M:ℝ) := by
  have htot : (0:ℝ)<total := by exact_mod_cast htotal
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hCr : (0:ℝ)<C := by exact_mod_cast hC
  have hellr : (0:ℝ)<ell := by exact_mod_cast hell
  let beta : ℝ := (W:ℝ)/((C:ℝ)*(total:ℝ))
  have hbeta : 0 ≤ beta := by dsimp [beta]; positivity
  have hbN : beta*(N:ℝ) ≤ W := by
    calc
      _ ≤ beta*((C:ℝ)*(total:ℝ)) := mul_le_mul_of_nonneg_left (by exact_mod_cast hbudget) hbeta
      _ = _ := by dsimp [beta]; field_simp
  have ht := richThreshold_density W N ell B hN hell beta hbN
  have hlo : beta*((M:ℝ)*a)/(2*(ell:ℝ)) ≤ beta*(B:ℝ)/(2*(ell:ℝ)) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB hbeta) (by positivity)
  have hlt := hlo.trans_lt ht
  apply (lt_div_iff₀ hMr).mpr
  calc
    _ = beta*((M:ℝ)*a)/(2*(ell:ℝ)) := by dsimp [beta]; field_simp
    _ < _ := hlt

/-- Build the literal rich packet layers from one original E2 source and its
queried relations. Every reference lower bound, overlap budget and predecessor
threshold is derived here; the actual retained-point mass ratio stays explicit. -/
theorem construct_rich_packet_layers {n level : ℕ} {D : FiniteScaleSource n}
    {eta eta2 a lambda c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (hER : ∀z∈E,z.1∈R)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2)
    (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2) (heta2 : 0 ≤ eta2)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hlambda : 0 < lambda)
    (hRich : ∀e,e∈E → D.thickness^eta*(2^level:ℕ)/
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E (localPair D a (2^level) e)).card)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta2) ≤ D.thickness^(-c2))
    (m : ℕ) (hm6 : 6 ≤ m) (hpL : phaseDepth m ≤ level)
    (hscale : D.thickness ≤ (64/((2^m:ℕ):ℝ))^2)
    (HF : HasUniformFibers E Q2
      (fixedPair D a level (phaseDepth m) (phaseDepth m) (representative h R a (2^(phaseDepth m)))))
    (HC : HasUniformFibers E Q2
      (fixedPair D a level (phaseDepth m) m (representative h R a (2^(phaseDepth m)))))
    (HV : HasUniformFibers E Q2 (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (S : Finset Index) (hSE : S⊆E.image Prod.snd) (hSn : S.Nonempty)
    (ell : ℕ) (hell : 0 < ell) (dir : ℕ → Index → Fin n)
    (hanchor : ∀i<ell,∀k∈S,∃j : Fin n,(j,k)∈E ∧
      (parentLabel D a (2^m) j).1=(parentLabel D a (2^m) (dir i (spatialLabel D (2^m) k))).1) :
    let A := reference D m E S
    let U := currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ))
    let packet := fun i => packetSet D m E S (dir i)
    let label := fun i => assignedLabel D m (dir i)
    let w := tagWeight E
    let M := vertexCap E (spatialLabel D (2^(phaseDepth m))) Q2
    let N := referenceBudget A U packet label w ell
    let b := fun i => referenceMinimum A U (packet i) (label i) w
    let k := fun i => richThreshold (mass U w) N ell (b i)
    let Omega := NativeWeightedPacketLayers.layers U packet label w k
    U⊆A ∧ mass U w=mass S (pointWeight E) ∧ N ≤ referenceConstant*E.card ∧
      (∀i<ell,(M:ℝ)*lambda*D.thickness^(c1+5*c2)/(64/((2^m:ℕ):ℝ)) ≤ (b i:ℝ)) ∧
      Omega 0=U ∧ (∀i,Omega (i+1)⊆Omega i) ∧ (∀i,Omega i⊆A) ∧
      mass U w ≤ 2*mass (Omega ell) w ∧ 0 < mass (Omega ell) w ∧
      (∀i<ell,∀u∈Omega (i+1),k i ≤ packetMass (Omega i) (packet i) w (label i u)) ∧
      0 < ∏i∈range ell,k i ∧
      ∀i<ell,((mass S (pointWeight E):ℝ)/(E.card:ℝ))*lambda*D.thickness^(c1+5*c2)/
        (2*(ell:ℝ)*(referenceConstant:ℝ)*(64/((2^m:ℕ):ℝ))) < (k i:ℝ)/(M:ℝ) := by
  intro A U packet label w M N b k Omega
  have hEne : E.Nonempty := by
    obtain ⟨z,hz⟩ := hSn
    obtain ⟨e,he,_heq⟩ := mem_image.mp (hSE hz)
    exact ⟨e,he⟩
  have hU : U.Nonempty := by
    apply card_pos.mp
    change 0 < (currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ))).card
    rw [currentLift_card]
    exact card_pos.mpr hSn
  have hmass : mass U w=mass S (pointWeight E) := by
    exact currentLift_mass S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ)) (pointWeight E)
  have hW : 0 < mass U w := by rw [hmass]; exact original_point_mass_positive E S hSE hSn
  have hmp : m ≤ phaseDepth m := by dsimp [phaseDepth]; omega
  have hlarge := NativeCoarseShadingPruning.coarse_thickness_le_one m hm6
  have hcover : ∀i<ell,∀u∈U,u∈packet i (label i u) := by
    intro i hi u hu
    simp only [U,currentLift,mem_image] at hu
    obtain ⟨z,hz,rfl⟩ := hu
    obtain ⟨j,hjk,hja⟩ := hanchor i hi z hz
    have hmemb := NativeFullVertexFiberDensity.anchor_mem_short_closure D a level (phaseDepth m) m
      (representative h R a (2^(phaseDepth m))) E (j,z) hjk
    have hs := short_closure_tag_subset h original horiginal ha level m hdy (hmp.trans hpL) hm6 hlarge hscale
      (representative h R a (2^(phaseDepth m))) E hE S (dir i) (j,z) hjk hz hja
    exact hs (mem_image_of_mem _ hmemb)
  have hUA : U⊆A := by
    intro u hu
    exact (mem_filter.mp (hcover 0 hell u hu)).1
  have hbudget : N ≤ referenceConstant*E.card := computed_reference_budget_le D m E hEne S U dir ell
  have hminimum : ∀i<ell,(M:ℝ)*lambda*D.thickness^(c1+5*c2)/(64/((2^m:ℕ):ℝ)) ≤ (b i:ℝ) := by
    intro i hi
    apply real_le_referenceMinimum A U (packet i) (label i) w hU
    intro u hu
    simp only [U,currentLift,mem_image] at hu
    obtain ⟨z,hz,rfl⟩ := hu
    obtain ⟨j,hjk,hja⟩ := hanchor i hi z hz
    have hh := queried_tagged_packet_lower h original horiginal ha R E hE hER F1 F2 G Q1 Q2
      hF1 hG hQ2 hQ1 hGF heta2 hdy hlambda hRich hcost1 hcost2 m hm6 hpL hscale HF HC HV
      S (dir i) (j,z) hjk hz hja
    rw [packetMass_eq_of_subset A (packet i) w (label i _) (filter_subset _ _)]
    exact hh
  have hcore := construct_actual_packet_layers A U hUA packet label w ell hW hcover
  have hN : 0 < N := referenceBudget_positive A U packet label w ell
  have hM : 0 < M := vertexCap_pos E hEne _ Q2 HV
  refine ⟨hUA,hmass,hbudget,hminimum,hcore.1,hcore.2.1,hcore.2.2.1,hcore.2.2.2.1,
    hcore.2.2.2.2.1,hcore.2.2.2.2.2.1,hcore.2.2.2.2.2.2,?_⟩
  intro i hi
  have hd : 0 < D.thickness := h.1.2.1
  have ha0 : 0 ≤ lambda*D.thickness^(c1+5*c2)/(64/((2^m:ℕ):ℝ)) := by positivity
  have hbi : (M:ℝ)*(lambda*D.thickness^(c1+5*c2)/(64/((2^m:ℕ):ℝ))) ≤ (b i:ℝ) := by
    simpa only [mul_div_assoc,mul_assoc] using hminimum i hi
  have ht := threshold_ratio_lower (mass U w) N ell (b i) E.card M referenceConstant hN hell
    (card_pos.mpr hEne) hM referenceConstant_pos hbudget _ ha0 hbi
  rw [hmass] at ht
  have he : ((mass S (pointWeight E):ℝ)/(E.card:ℝ))*
      (lambda*D.thickness^(c1+5*c2)/(64/((2^m:ℕ):ℝ)))/(2*(ell:ℝ)*(referenceConstant:ℝ)) =
      ((mass S (pointWeight E):ℝ)/(E.card:ℝ))*lambda*D.thickness^(c1+5*c2)/
        (2*(ell:ℝ)*(referenceConstant:ℝ)*(64/((2^m:ℕ):ℝ))) := by ring
  rw [he] at ht
  simpa only [k,hmass] using ht

end NativeActualRichPacketLayers
