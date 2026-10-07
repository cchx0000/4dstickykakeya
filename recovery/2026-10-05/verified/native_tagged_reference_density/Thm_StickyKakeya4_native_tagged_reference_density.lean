import Theorems.Thm_StickyKakeya4_native_tagged_packet_rows
import Theorems.Thm_StickyKakeya4_native_full_vertex_fiber_density

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4200000

noncomputable section
namespace NativeTaggedReferenceDensity
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeSpatialAngularGeometry
open NativeCoarseShadingUniformity NativeCoarseDirectionThinning NativeOriginalParentDensityCore
open NativeLocalPairFibers NativeShortRowPackets NativeSquaredGrainQueries NativeNodalReferenceLift
open NativeOriginalPacketReference NativeTaggedPacketRows NativeQueriedVertexWeights
open NativeFullVertexFiberDensity NativeJointUniformCoarseRelations
open RichDirectionalLayers WeightedRichDirectionalLayers
open scoped BigOperators

/-- A node tag leaves the actual E2 microcell incidence weight unchanged. -/
def tagWeight {n : ℕ} (E : Finset (Fin n × Index)) (u : Index × Index) : ℕ := pointWeight E u.2

lemma tag_mass {A N : Type*} [DecidableEq A] [DecidableEq N]
    (B : Finset A) (w : A → ℕ) (node : N) :
    mass (B.image (fun k => (node,k))) (fun u => w u.2)=mass B w := by
  unfold mass
  exact sum_image (fun _ _ _ _ he => congrArg Prod.snd he)

/-- The one tagged reference universe is independent of the direction choices.
Its total mass pays only the proved spatial-node duplication. -/
theorem reference_mass_le {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (S : Finset Index) :
    mass (reference D m E S) (tagWeight E) ≤ 8193^4*E.card := by
  have hh := boxReference_mass (S.image (spatialLabel D (2^m))) (64/((2^m:ℕ):ℝ))
    (E.image Prod.snd) (rawVertex D (phaseDepth m)) (pointWeight E)
  change mass (reference D m E S) (tagWeight E) ≤ 8193^4*mass (E.image Prod.snd) (pointWeight E) at hh
  rwa [reference_mass] at hh

/-- A single node's vertex fiber has the original computed cap; the global
node-duplication factor is absent from this local predecessor estimate. -/
theorem reference_vertex_cap {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (S : Finset Index) (Q : ℕ)
    (HV : HasUniformFibers E Q (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (node v : Index) :
    mass ((reference D m E S).filter
      (fun u => u.1=node ∧ spatialLabel D (2^(phaseDepth m)) u.2=v)) (tagWeight E) ≤
        vertexCap E (spatialLabel D (2^(phaseDepth m))) Q := by
  have hh := fixed_node_vertex_mass (S.image (spatialLabel D (2^m))) (64/((2^m:ℕ):ℝ))
    (E.image Prod.snd) (rawVertex D (phaseDepth m)) (pointWeight E)
    (spatialLabel D (2^(phaseDepth m))) node v
  have hc := vertex_mass_le_cap E (spatialLabel D (2^(phaseDepth m))) Q HV v
  have hb : mass ((reference D m E S).filter
      (fun u => u.1=node ∧ spatialLabel D (2^(phaseDepth m)) u.2=v)) (tagWeight E) ≤
        mass (classFiber (E.image Prod.snd) (spatialLabel D (2^(phaseDepth m))) v) (pointWeight E) := by
    dsimp only [reference,mass,tagWeight,classFiber]
    convert hh using 1
    all_goals congr
  exact hb.trans hc

/-- The genuine short-row closure carries its full original weight into the
actual packet on the same node; no packet-density premise is supplied. -/
theorem tagged_packet_mass_ge_closure {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmL : m ≤ level) (hm6 : 6 ≤ m)
    (hlarge : 64/((2^m:ℕ):ℝ) ≤ 1)
    (hscale : D.thickness ≤ (64/((2^m:ℕ):ℝ))^2)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (S : Finset Index) (directionIndex : Index → Fin n)
    (anchor : Fin n × Index) (hanchor : anchor∈E) (hS : anchor.2∈S)
    (hangular : (parentLabel D a (2^m) anchor.1).1=
      (parentLabel D a (2^m) (directionIndex (spatialLabel D (2^m) anchor.2))).1) :
    mass (shortVertexClosure D a level (phaseDepth m) m rep E anchor) (pointWeight E) ≤
      mass (packetSet D m E S directionIndex
        (assignedLabel D m directionIndex (spatialLabel D (2^m) anchor.2,anchor.2))) (tagWeight E) := by
  have hsub := short_closure_tag_subset h original horiginal ha level m hdy hmL hm6 hlarge hscale
    rep E hE S directionIndex anchor hanchor hS hangular
  have hm := mass_mono _ _ (tagWeight E) hsub
  have he := tag_mass (shortVertexClosure D a level (phaseDepth m) m rep E anchor)
    (pointWeight E) (spatialLabel D (2^m) anchor.2)
  exact he.symm.le.trans hm

/-- Actual queried source density on the direction-independent tagged
reference universe. Lambda, both source losses, and the original E2 weights
remain literal. The physical phase mesh is exactly the squared grain mesh. -/
theorem queried_tagged_packet_lower {n level : ℕ} {D : FiniteScaleSource n}
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
    (S : Finset Index) (directionIndex : Index → Fin n)
    (anchor : Fin n × Index) (hanchor : anchor∈E) (hS : anchor.2∈S)
    (hangular : (parentLabel D a (2^m) anchor.1).1=
      (parentLabel D a (2^m) (directionIndex (spatialLabel D (2^m) anchor.2))).1) :
    (vertexCap E (spatialLabel D (2^(phaseDepth m))) Q2:ℝ)*lambda*D.thickness^(c1+5*c2)/
        (64/((2^m:ℕ):ℝ)) ≤
      mass (packetSet D m E S directionIndex
        (assignedLabel D m directionIndex (spatialLabel D (2^m) anchor.2,anchor.2))) (tagWeight E) := by
  have hmp : m ≤ phaseDepth m := by dsimp [phaseDepth]; omega
  have hrow := queried_short_closure_lower h original horiginal ha R E hE hER F1 F2 G Q1 Q2
    hF1 hG hQ2 hQ1 hGF heta2 hdy hlambda hRich hcost1 hcost2 (phaseDepth m) m hmp hpL hm6
    HF HC HV anchor hanchor
  have htag := tagged_packet_mass_ge_closure h original horiginal ha level m hdy (hmp.trans hpL) hm6
    (NativeCoarseShadingPruning.coarse_thickness_le_one m hm6) hscale
    (representative h R a (2^(phaseDepth m))) E hE S directionIndex anchor hanchor hS hangular
  have hh := hrow.trans (show
      (mass (shortVertexClosure D a level (phaseDepth m) m (representative h R a (2^(phaseDepth m)))
        E anchor) (pointWeight E):ℝ) ≤
      mass (packetSet D m E S directionIndex
        (assignedLabel D m directionIndex (spatialLabel D (2^m) anchor.2,anchor.2))) (tagWeight E) by
    exact_mod_cast htag)
  rw [short_fine_scale_ratio m hm6] at hh
  simpa only [mul_one_div] using hh

end NativeTaggedReferenceDensity
