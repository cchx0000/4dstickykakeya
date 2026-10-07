import Theorems.Thm_StickyKakeya4_native_rank_four_packet_count
import Theorems.Thm_StickyKakeya4_native_actual_rich_packet_layers

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeActualRankFourCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeSpatialAngularGeometry
open NativeCoarseShadingUniformity NativeCoarseDirectionThinning NativeOriginalParentDensityCore
open NativeLocalPairFibers NativeSquaredGrainQueries NativeNodalReferenceLift
open NativeOriginalPacketReference NativeTaggedPacketRows NativeQueriedVertexWeights
open NativeTaggedReferenceDensity NativeJointUniformCoarseRelations NativeDirectionRankDichotomy
open NativeCompatibleAngularCandidates NativeCompatibleNodeDirections NativeRankFourPacketCount
open RichDirectionalLayers WeightedRichDirectionalLayers NativeWeightedPacketLayers NativePacketRetainedLayers
open NativeActualRichPacketLayers
open scoped BigOperators

def rankFourConstant : ℝ :=
  2*(8*(referenceConstant:ℝ))^4*(41*(256*258):ℝ)^16

lemma rankFourConstant_pos : 0 < rankFourConstant := by
  have hC : (0:ℝ)<referenceConstant := by exact_mod_cast referenceConstant_pos
  unfold rankFourConstant
  positivity

lemma clear_four_count (Vc Vf beta lambda d Q C Delta A q : ℝ)
    (hC : 0 < C) (hD : 0 < Delta) (hq : 0 < q)
    (H : beta*Vc*(beta*lambda*d/(8*C*Delta))^4 ≤ 2*Q^2*Vf*((A/q)^4)^4) :
    Vc*beta^5*lambda^4*d^4*q^16 ≤ 2*Q^2*(8*C)^4*A^16*Delta^4*Vf := by
  have hh := mul_le_mul_of_nonneg_right H
    (show 0 ≤ (8*C*Delta)^4*q^16 by positivity)
  have heL : beta*Vc*(beta*lambda*d/(8*C*Delta))^4*((8*C*Delta)^4*q^16)=
      Vc*beta^5*lambda^4*d^4*q^16 := by
    field_simp [hC.ne',hD.ne']
    ring
  have heR : (2*Q^2*Vf*((A/q)^4)^4)*((8*C*Delta)^4*q^16)=
      2*Q^2*(8*C)^4*A^16*Delta^4*Vf := by
    rw [←pow_mul]
    field_simp [hq.ne']
    ring
  rwa [heL,heR] at hh

/-- The rank-four count on the literal source. Actual compatible tuples,
local incident anchors, rich thresholds and half-weight layers are constructed
inside this proof. No predecessor-density or occupied-node certificate is input. -/
theorem actual_rank_four_count {n level : ℕ} {D : FiniteScaleSource n}
    {eta eta2 a lambda c1 c2 q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hER : ∀z∈E,z.1∈R)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2)
    (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2) (heta2 : 0 ≤ eta2)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hlambda : 0 < lambda)
    (hRich : ∀e,e∈E → D.thickness^eta*(2^level:ℕ)/
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E (localPair D a (2^level) e)).card)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta2) ≤ D.thickness^(-c2))
    (stop m : ℕ) (hms : m ≤ stop) (hm6 : 6 ≤ m) (hpL : phaseDepth m ≤ level)
    (hscale : D.thickness ≤ (64/((2^m:ℕ):ℝ))^2)
    (HF : HasUniformFibers E Q2
      (fixedPair D a level (phaseDepth m) (phaseDepth m) (representative h R a (2^(phaseDepth m)))))
    (HC : HasUniformFibers E Q2
      (fixedPair D a level (phaseDepth m) m (representative h R a (2^(phaseDepth m)))))
    (HV : HasUniformFibers E Q2 (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (HVcoarse : HasUniformFibers E Q2 (fun z => spatialLabel D (2^m) z.2))
    (hq : 0 < q) (hq1 : q ≤ 1)
    (P : Finset (Index × List (Fin 3 → ℤ))) (hPn : P.Nonempty)
    (hP : P⊆terminalFamily D a stop E q 4)
    (hcompatible : ∀x y,x∈P → y∈P → spatialLabel D (2^m) x.1=spatialLabel D (2^m) y.1 →
      projectWord stop m x.2=projectWord stop m y.2) :
    let S := P.image Prod.fst
    let beta := (mass S (pointWeight E):ℝ)/(E.card:ℝ)
    let Delta := 64/((2^m:ℕ):ℝ)
    (vertices E (spatialLabel D (2^m))).card*beta^5*lambda^4*(D.thickness^(c1+5*c2))^4*q^16 ≤
      rankFourConstant*(Q2:ℝ)^2*Delta^4*(vertices E (spatialLabel D (2^(phaseDepth m)))).card := by
  intro S beta Delta
  have hSE : S⊆E.image Prod.snd := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
    exact ((CompatibleTupleSelection.mem_goodPairs _ _ p).mp (hP hp)).1
  have hSn : S.Nonempty := hPn.image Prod.fst
  have hEne : E.Nonempty := by
    obtain ⟨k,hk⟩ := hSn
    obtain ⟨z,hz,_⟩ := mem_image.mp (hSE hk)
    exact ⟨z,hz⟩
  obtain ⟨point,tuple,anchor,HS,_hwords,_hsame⟩ :=
    exists_node_direction_system h a stop m hms E q hq 4 P hP hcompatible
  let dir := natStageDirectionIndex h tuple
  have hanchor : ∀i<4,∀k∈S,∃j : Fin n,(j,k)∈E ∧
      (parentLabel D a (2^m) j).1=(parentLabel D a (2^m) (dir i (spatialLabel D (2^m) k))).1 := by
    intro i hi k hk
    exact ⟨natStageAnchorIndex h anchor i k,nat_stage_anchor_readback h HS k hk i hi⟩
  let A := reference D m E S
  let U := currentLift S (cellCenter (mesh D)) Delta
  let packet := fun i => packetSet D m E S (dir i)
  let label := fun i => assignedLabel D m (dir i)
  let w := tagWeight E
  let M := vertexCap E (spatialLabel D (2^(phaseDepth m))) Q2
  let N := referenceBudget A U packet label w 4
  let b := fun i => referenceMinimum A U (packet i) (label i) w
  let k := fun i => richThreshold (mass U w) N 4 (b i)
  let Omega := NativeTaggedPacketFiberIteration.layers D m E S U dir k
  let L : ℝ := beta*lambda*D.thickness^(c1+5*c2)/(8*(referenceConstant:ℝ)*Delta)
  have hdata := construct_rich_packet_layers h original horiginal ha R E hE hER
    F1 F2 G Q1 Q2 hF1 hG hQ2 hQ1 hGF heta2 hdy hlambda hRich hcost1 hcost2
    m hm6 hpL hscale HF HC HV S hSE hSn 4 (by norm_num) dir hanchor
  obtain ⟨_hUA,hmass,_hbudget,_hminimum,_hzero,_hstep,_hsub,hhalf,_hpositive,_hpred,_hprod,hthreshold⟩ := hdata
  have hhalf' : mass S (pointWeight E) ≤ 2*mass (Omega 4) (fun u => pointWeight E u.2) := by
    rw [←hmass]
    exact hhalf
  have hcurrent : Omega 4⊆U := by
    exact NativeWeightedPacketLayers.layers_subset_start U packet label w k 4
  have hnodes := retained_node_cross D m E hEne S hSE Q2 HVcoarse (Omega 4) hcurrent hhalf'
  have hd : 0 < D.thickness := h.1.2.1
  have hL : 0 ≤ L := by dsimp [L,beta,Delta]; positivity
  have hk : ∀i<4,L ≤ (k i:ℝ)/(M:ℝ) := by
    intro i hi
    have ht := (hthreshold i hi).le
    norm_num only [Nat.cast_ofNat,show (2:ℝ)*4=8 by norm_num] at ht
    exact ht
  have hvertices := four_stage_vertex_count h m hm6 E hEne S hSE Q2 HV
    point tuple anchor HS hq hq1 k L hL hk
  have hfactor : beta*(vertices E (spatialLabel D (2^m))).card*L^4 ≤
      2*(Q2:ℝ)^2*(vertices E (spatialLabel D (2^(phaseDepth m)))).card*((41*(256*258)/q)^4)^4 := by
    calc
      _ ≤ (2*(Q2:ℝ)^2*((Omega 4).image Prod.fst).card)*L^4 :=
        mul_le_mul_of_nonneg_right hnodes (pow_nonneg hL 4)
      _ = 2*(Q2:ℝ)^2*(((Omega 4).image Prod.fst).card*L^4) := by ring
      _ ≤ 2*(Q2:ℝ)^2*((vertices E (spatialLabel D (2^(phaseDepth m)))).card*((41*(256*258)/q)^4)^4) :=
        mul_le_mul_of_nonneg_left hvertices (by positivity)
      _ = _ := by ring
  have hC : (0:ℝ)<referenceConstant := by exact_mod_cast referenceConstant_pos
  have hD : 0 < Delta := by dsimp [Delta]; positivity
  have hfinal := clear_four_count ((vertices E (spatialLabel D (2^m))).card)
    ((vertices E (spatialLabel D (2^(phaseDepth m)))).card) beta lambda (D.thickness^(c1+5*c2))
    Q2 referenceConstant Delta (41*(256*258)) q hC hD hq hfactor
  calc
    _ ≤ 2*(Q2:ℝ)^2*(8*(referenceConstant:ℝ))^4*(41*(256*258):ℝ)^16*Delta^4*
        (vertices E (spatialLabel D (2^(phaseDepth m)))).card := hfinal
    _ = _ := by unfold rankFourConstant; ring

end NativeActualRankFourCount
