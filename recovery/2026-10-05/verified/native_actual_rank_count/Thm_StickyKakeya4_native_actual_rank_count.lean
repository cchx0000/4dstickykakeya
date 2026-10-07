import Theorems.Thm_StickyKakeya4_native_rank_packet_count
import Theorems.Thm_StickyKakeya4_native_general_rank_scalar_budget
import Theorems.Thm_StickyKakeya4_native_actual_rich_packet_layers

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeActualRankCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeSpatialAngularGeometry
open NativeCoarseShadingUniformity NativeCoarseDirectionThinning NativeOriginalParentDensityCore
open NativeLocalPairFibers NativeSquaredGrainQueries NativeNodalReferenceLift
open NativeOriginalPacketReference NativeTaggedPacketRows NativeQueriedVertexWeights
open NativeTaggedReferenceDensity NativeJointUniformCoarseRelations NativeDirectionRankDichotomy
open NativeCompatibleAngularCandidates NativeCompatibleNodeDirections NativeRankFourPacketCount
open RichDirectionalLayers WeightedRichDirectionalLayers NativeWeightedPacketLayers NativePacketRetainedLayers
open NativeActualRichPacketLayers NativeRankPacketCount NativeGeneralRankScalarBudget
open scoped BigOperators

lemma loss_power {delta : ℝ} (hd : 0 ≤ delta) (s : ℝ) (ell : ℕ) :
    (delta^s)^ell=delta^((ell:ℝ)*s) := by
  rw [←Real.rpow_mul_natCast hd]
  congr 1
  ring

lemma clear_count (ell : ℕ) (Vc Vf beta lambda d Q C Delta A q : ℝ)
    (hC : 0 < C) (hD : 0 < Delta) (hq : 0 < q)
    (H : beta*Vc*(beta*lambda*d/(8*C*Delta))^ell ≤ 2*Q^2*Vf*((A/q)^4)^ell) :
    Vc*beta^(ell+1)*lambda^ell*d^ell*q^(4*ell) ≤
      2*Q^2*(8*C)^ell*A^(4*ell)*Delta^ell*Vf := by
  have hh := mul_le_mul_of_nonneg_right H
    (show 0 ≤ (8*C*Delta)^ell*q^(4*ell) by positivity)
  have hden : (8*C*Delta)^ell≠0 := (pow_pos (by positivity : 0 < 8*C*Delta) ell).ne'
  have heL : beta*Vc*(beta*lambda*d/(8*C*Delta))^ell*((8*C*Delta)^ell*q^(4*ell))=
      Vc*beta^(ell+1)*lambda^ell*d^ell*q^(4*ell) := by
    rw [div_pow]
    calc
      _ = beta*Vc*(((beta*lambda*d)^ell/(8*C*Delta)^ell)*(8*C*Delta)^ell)*q^(4*ell) := by ring
      _ = beta*Vc*(beta*lambda*d)^ell*q^(4*ell) := by rw [div_mul_cancel₀ _ hden]
      _ = _ := by rw [pow_succ beta]; simp only [mul_pow]; ring
  have hdiv : ((A/q)^4)^ell*q^(4*ell)=A^(4*ell) := by
    rw [←pow_mul,div_pow]
    exact div_mul_cancel₀ _ (pow_ne_zero (4*ell) hq.ne')
  have heR : (2*Q^2*Vf*((A/q)^4)^ell)*((8*C*Delta)^ell*q^(4*ell))=
      2*Q^2*(8*C)^ell*A^(4*ell)*Delta^ell*Vf := by
    calc
      _ = 2*Q^2*Vf*(8*C*Delta)^ell*(((A/q)^4)^ell*q^(4*ell)) := by ring
      _ = 2*Q^2*Vf*(8*C*Delta)^ell*A^(4*ell) := by rw [hdiv]
      _ = _ := by simp only [mul_pow]; ring
  rwa [heL,heR] at hh

/-- The general-rank count on the literal source. Actual compatible tuples,
local incident anchors, rich thresholds and half-weight layers are constructed
inside this proof. No predecessor-density or occupied-node certificate is input. -/
theorem actual_rank_count {n level : ℕ} {D : FiniteScaleSource n}
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
    (ell : ℕ) (hell : 0 < ell) (hell4 : ell ≤ 4)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (P : Finset (Index × List (Fin 3 → ℤ))) (hPn : P.Nonempty)
    (hP : P⊆terminalFamily D a stop E q ell)
    (hcompatible : ∀x y,x∈P → y∈P → spatialLabel D (2^m) x.1=spatialLabel D (2^m) y.1 →
      projectWord stop m x.2=projectWord stop m y.2) :
    let S := P.image Prod.fst
    let beta := (mass S (pointWeight E):ℝ)/(E.card:ℝ)
    let Delta := 64/((2^m:ℕ):ℝ)
    (vertices E (spatialLabel D (2^m))).card*beta^(ell+1)*lambda^ell*D.thickness^((ell:ℝ)*(c1+5*c2))*q^(4*ell) ≤
      geometricConstant ell*(Q2:ℝ)^2*Delta^ell*(vertices E (spatialLabel D (2^(phaseDepth m)))).card := by
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
    exists_node_direction_system h a stop m hms E q hq ell P hP hcompatible
  let dir := natStageDirectionIndex h tuple
  have hanchor : ∀i<ell,∀k∈S,∃j : Fin n,(j,k)∈E ∧
      (parentLabel D a (2^m) j).1=(parentLabel D a (2^m) (dir i (spatialLabel D (2^m) k))).1 := by
    intro i hi k hk
    exact ⟨natStageAnchorIndex h anchor i k,nat_stage_anchor_readback h HS k hk i hi⟩
  let A := reference D m E S
  let U := currentLift S (cellCenter (mesh D)) Delta
  let packet := fun i => packetSet D m E S (dir i)
  let label := fun i => assignedLabel D m (dir i)
  let w := tagWeight E
  let M := vertexCap E (spatialLabel D (2^(phaseDepth m))) Q2
  let N := referenceBudget A U packet label w ell
  let b := fun i => referenceMinimum A U (packet i) (label i) w
  let k := fun i => richThreshold (mass U w) N ell (b i)
  let Omega := NativeTaggedPacketFiberIteration.layers D m E S U dir k
  let L : ℝ := beta*lambda*D.thickness^(c1+5*c2)/(8*(referenceConstant:ℝ)*Delta)
  have hdata := construct_rich_packet_layers h original horiginal ha R E hE hER
    F1 F2 G Q1 Q2 hF1 hG hQ2 hQ1 hGF heta2 hdy hlambda hRich hcost1 hcost2
    m hm6 hpL hscale HF HC HV S hSE hSn ell hell dir hanchor
  obtain ⟨_hUA,hmass,_hbudget,_hminimum,_hzero,_hstep,_hsub,hhalf,_hpositive,_hpred,_hprod,hthreshold⟩ := hdata
  have hhalf' : mass S (pointWeight E) ≤ 2*mass (Omega ell) (fun u => pointWeight E u.2) := by
    rw [←hmass]
    exact hhalf
  have hcurrent : Omega ell⊆U := by
    exact NativeWeightedPacketLayers.layers_subset_start U packet label w k ell
  have hnodes := retained_node_cross D m E hEne S hSE Q2 HVcoarse (Omega ell) hcurrent hhalf'
  have hd : 0 < D.thickness := h.1.2.1
  have hL : 0 ≤ L := by dsimp [L,beta,Delta]; positivity
  have hC : (0:ℝ)<referenceConstant := by exact_mod_cast referenceConstant_pos
  have hD : 0 < Delta := by dsimp [Delta]; positivity
  have hellR : (0:ℝ)<ell := by exact_mod_cast hell
  have hell4R : (ell:ℝ) ≤ 4 := by exact_mod_cast hell4
  have hk : ∀i<ell,L ≤ (k i:ℝ)/(M:ℝ) := by
    intro i hi
    have hnum : 0 ≤ beta*lambda*D.thickness^(c1+5*c2) := by dsimp [beta]; positivity
    have hden : 0 < 2*(ell:ℝ)*(referenceConstant:ℝ)*Delta := by positivity
    have hdenle : 2*(ell:ℝ)*(referenceConstant:ℝ)*Delta ≤ 8*(referenceConstant:ℝ)*Delta := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : 2*(ell:ℝ) ≤ 8) hC.le) hD.le
    have hweak : L ≤ beta*lambda*D.thickness^(c1+5*c2)/(2*(ell:ℝ)*(referenceConstant:ℝ)*Delta) :=
      div_le_div_of_nonneg_left hnum hden hdenle
    exact hweak.trans (hthreshold i hi).le
  have hvertices := stage_vertex_count h m hm6 ell hell4 E hEne S hSE Q2 HV
    point tuple anchor HS hq hq1 k L hL hk
  have hfactor : beta*(vertices E (spatialLabel D (2^m))).card*L^ell ≤
      2*(Q2:ℝ)^2*(vertices E (spatialLabel D (2^(phaseDepth m)))).card*((41*(256*258)/q)^4)^ell := by
    calc
      _ ≤ (2*(Q2:ℝ)^2*((Omega ell).image Prod.fst).card)*L^ell :=
        mul_le_mul_of_nonneg_right hnodes (pow_nonneg hL ell)
      _ = 2*(Q2:ℝ)^2*(((Omega ell).image Prod.fst).card*L^ell) := by ring
      _ ≤ 2*(Q2:ℝ)^2*((vertices E (spatialLabel D (2^(phaseDepth m)))).card*((41*(256*258)/q)^4)^ell) :=
        mul_le_mul_of_nonneg_left hvertices (by positivity)
      _ = _ := by ring
  have hfinal := clear_count ell ((vertices E (spatialLabel D (2^m))).card)
    ((vertices E (spatialLabel D (2^(phaseDepth m)))).card) beta lambda (D.thickness^(c1+5*c2))
    Q2 referenceConstant Delta (41*(256*258)) q hC hD hq hfactor
  rw [loss_power hd.le (c1+5*c2) ell] at hfinal
  calc
    _ ≤ 2*(Q2:ℝ)^2*(8*(referenceConstant:ℝ))^ell*(41*(256*258):ℝ)^(4*ell)*Delta^ell*
        (vertices E (spatialLabel D (2^(phaseDepth m)))).card := hfinal
    _ = _ := by unfold geometricConstant; ring


end NativeActualRankCount
