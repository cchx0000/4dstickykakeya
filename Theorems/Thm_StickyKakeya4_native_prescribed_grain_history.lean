import Theorems.Thm_StickyKakeya4_native_actual_grain_history

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativePrescribedGrainHistory
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeSpatialAngularGeometry
open NativeCoarseShadingUniformity NativeCoarseDirectionThinning NativeOriginalParentDensityCore
open NativeLocalPairFibers NativeSquaredGrainQueries NativeNodalReferenceLift
open NativeTaggedPacketRows NativeQueriedVertexWeights NativeTaggedReferenceDensity
open NativeJointUniformCoarseRelations NativeDirectionRankDichotomy NativeCompatibleAngularCandidates
open RichDirectionalLayers WeightedRichDirectionalLayers NativeWeightedPacketLayers NativePacketRetainedLayers
open NativeActualRichPacketLayers NativeCompatibleNodeDirections
open scoped BigOperators

open NativeActualGrainHistory NativeOriginalAngularTupleMenu

/-- The exact prescribed terminal word is retained together with the genuine
node system at the original choice. Equal words retain the same representative. -/
def IsPrescribedNodeSystem {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (stop m : ℕ)
    (E : Finset (Fin n × Index)) (P : Finset (Index × List (Fin 3 → ℤ))) (q : ℝ) (ell : ℕ)
    (point : Index → Index) (tuple : Index → Fin ell → (Fin n × Index))
    (anchor : Index → Fin ell → Fin n) : Prop :=
  IsNodeDirectionSystem D a m E (P.image Prod.fst) q ell point tuple anchor ∧
    (∀p∈P,angularTuple D a m (List.ofFn (tuple (spatialLabel D (2^m) p.1)))=projectWord stop m p.2) ∧
    ∀x y,x∈P → y∈P → projectWord stop m x.2=projectWord stop m y.2 →
      tuple (spatialLabel D (2^m) x.1)=tuple (spatialLabel D (2^m) y.1) ∧
      point (spatialLabel D (2^m) x.1)=point (spatialLabel D (2^m) y.1)

theorem prescribed_system_forget {n stop m ell : ℕ} {D : FiniteScaleSource n} {a q : ℝ}
    {E : Finset (Fin n × Index)} {P : Finset (Index × List (Fin 3 → ℤ))}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsPrescribedNodeSystem D a stop m E P q ell point tuple anchor) :
    IsNodeDirectionSystem D a m E (P.image Prod.fst) q ell point tuple anchor := H.1

theorem prescribed_system_word {n stop m ell : ℕ} {D : FiniteScaleSource n} {a q : ℝ}
    {E : Finset (Fin n × Index)} {P : Finset (Index × List (Fin 3 → ℤ))}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsPrescribedNodeSystem D a stop m E P q ell point tuple anchor) :
    ∀p∈P,angularTuple D a m (List.ofFn (tuple (spatialLabel D (2^m) p.1)))=projectWord stop m p.2 := H.2.1

/-- Preserve the word trace when selecting the directions, before the rich
history is built. The actual history and every old count consumer are unchanged. -/
theorem construct_prescribed_grain_history {n level J : ℕ} {D : FiniteScaleSource n}
    {eta eta2 a lambda c1 c2 : ℝ}
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
    (stop : ℕ) (m : Fin J → ℕ) (hms : ∀j,m j ≤ stop)
    (hm6 : ∀j,6 ≤ m j) (hpL : ∀j,phaseDepth (m j) ≤ level)
    (hscale : ∀j,D.thickness ≤ (64/((2^(m j):ℕ):ℝ))^2)
    (HF : ∀j,HasUniformFibers E Q2
      (fixedPair D a level (phaseDepth (m j)) (phaseDepth (m j))
        (representative h R a (2^(phaseDepth (m j))))))
    (HC : ∀j,HasUniformFibers E Q2
      (fixedPair D a level (phaseDepth (m j)) (m j)
        (representative h R a (2^(phaseDepth (m j))))))
    (HV : ∀j,HasUniformFibers E Q2 (fun z => spatialLabel D (2^(phaseDepth (m j))) z.2))
    (q : ℝ) (hq : 0 < q) (ell : ℕ) (hell : 0 < ell)
    (P : Finset (Index × List (Fin 3 → ℤ))) (hP : P⊆terminalFamily D a stop E q ell)
    (hPne : P.Nonempty)
    (hcompat : ∀j : Fin J,∀x y,x∈P → y∈P →
      spatialLabel D (2^(m j)) x.1=spatialLabel D (2^(m j)) y.1 →
      projectWord stop (m j) x.2=projectWord stop (m j) y.2) :
    ∃ (point : Fin J → Index → Index)
      (tuple : Fin J → Index → Fin ell → (Fin n × Index))
      (anchor : Fin J → Index → Fin ell → Fin n),
      (∀j,IsPrescribedNodeSystem D a stop (m j) E P q ell
        (point j) (tuple j) (anchor j)) ∧
      HasGrainHistory D E m ell (fun j => natStageDirectionIndex h (tuple j))
        (P.image Prod.fst) Q2 lambda c1 c2 := by
  have H (j : Fin J) := exists_node_direction_system h a stop (m j) (hms j)
    E q hq ell P hP (hcompat j)
  choose point tuple anchor hsystem using H
  have hnode (j : Fin J) := (hsystem j).1
  have hS0E : P.image Prod.fst⊆E.image Prod.snd := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
    exact ((CompatibleTupleSelection.mem_goodPairs _ _ p).mp (hP hp)).1
  refine ⟨point,tuple,anchor,hsystem,?_⟩
  apply history_of_rich_scales D E m ell (fun j => natStageDirectionIndex h (tuple j))
    (P.image Prod.fst) (hPne.image Prod.fst) Q2 lambda c1 c2
  intro j S hSS0 hSn
  have Hcurrent := node_direction_system_mono (hnode j) hSS0
  have hanchor : ∀i<ell,∀k∈S,∃v : Fin n,(v,k)∈E ∧
      (parentLabel D a (2^(m j)) v).1=
        (parentLabel D a (2^(m j))
          (natStageDirectionIndex h (tuple j) i (spatialLabel D (2^(m j)) k))).1 := by
    intro i hi k hk
    exact ⟨natStageAnchorIndex h (anchor j) i k,nat_stage_anchor_readback h Hcurrent k hk i hi⟩
  exact construct_rich_packet_layers h original horiginal ha R E hE hER F1 F2 G Q1 Q2
    hF1 hG hQ2 hQ1 hGF heta2 hdy hlambda hRich hcost1 hcost2 (m j) (hm6 j) (hpL j)
    (hscale j) (HF j) (HC j) (HV j) S (hSS0.trans hS0E) hSn ell hell
    (natStageDirectionIndex h (tuple j)) hanchor

end NativePrescribedGrainHistory
