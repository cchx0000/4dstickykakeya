import Theorems.Thm_StickyKakeya4_native_rank_four_packet_count

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeRankPacketCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeSpatialAngularGeometry NativeSquaredGrainQueries
open NativeNodalReferenceLift NativeQueriedVertexWeights NativeTaggedPacketFiberIteration
open NativeTaggedNodeVertexCount NativeCompatibleNodeDirections NativeCompatibleAngularCandidates
open NativeDirectionRankDichotomy RichDirectionalLayers WeightedRichDirectionalLayers NativeRankFourPacketCount
open scoped BigOperators

/-- Geometry and actual chain provenance convert all constructed
thresholds into a global count. This finite bridge is consumed only with
threshold bounds derived by the actual rich-layer constructor. -/
theorem stage_vertex_count {n : ℕ} {D : FiniteScaleSource n} {eta a q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m)
    (ell : ℕ) (hell : ell ≤ 4)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (S : Finset Index)
    (hS : S⊆E.image Prod.snd) (Q : ℕ)
    (HU : NativeJointUniformCoarseRelations.HasUniformFibers E Q
      (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (point : Index → Index) (tuple : Index → Fin ell → (Fin n × Index))
    (anchor : Index → Fin ell → Fin n)
    (HS : IsNodeDirectionSystem D a m E S q ell point tuple anchor) (hq : 0 < q) (hq1 : q ≤ 1)
    (k : ℕ → ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hk : ∀i<ell,L ≤ (k i:ℝ)/(vertexCap E (spatialLabel D (2^(phaseDepth m))) Q:ℝ)) :
    let U := currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ))
    let Omega := NativeTaggedPacketFiberIteration.layers D m E S U (natStageDirectionIndex h tuple) k
    ((Omega ell).image Prod.fst).card*L^ell ≤
      (vertices E (spatialLabel D (2^(phaseDepth m)))).card*((41*(256*258)/q)^4)^ell := by
  intro U Omega
  let M := vertexCap E (spatialLabel D (2^(phaseDepth m))) Q
  let nodes := (Omega ell).image Prod.fst
  let denom : ℝ := ((41*(256*258)/q)^4)^ell
  have hden : 0 < denom := by dsimp [denom]; positivity
  have hM : 0 < M := vertexCap_pos E hE _ Q HU
  have hsub : Omega ell⊆U := by
    exact NativeWeightedPacketLayers.layers_subset_start U
      (fun i => NativeTaggedPacketRows.packetSet D m E S (natStageDirectionIndex h tuple i))
      (fun i => NativeTaggedPacketRows.assignedLabel D m (natStageDirectionIndex h tuple i))
      (fun u => pointWeight E u.2) k ell
  have hprod : L^ell ≤ (∏i∈range ell,((k i ⌈/⌉ M:ℕ):ℝ)) := by
    calc
      _ = ∏_i∈range ell,L := by simp
      _ ≤ _ := prod_le_prod (fun _ _ => hL)
        (fun i hi => (hk i (mem_range.mp hi)).trans (ratio_le_ceilDiv (k i) M hM))
  have hnode : ∀node∈nodes,L^ell/denom ≤ (nodeVertices D m U node).card := by
    intro node hn
    obtain ⟨u,hu,hun⟩ := mem_image.mp hn
    have huU := hsub hu
    simp only [U,currentLift,mem_image] at huU
    obtain ⟨z,hz,hzu⟩ := huU
    have hnS : node∈NativeCompatibleNodeDirections.nodes D m S := by
      refine mem_image.mpr ⟨z,hz,?_⟩
      exact (congrArg Prod.fst hzu).trans hun
    let x := spatialLabel D (2^(phaseDepth m)) u.2
    have hx : x∈nodeVertices D m (Omega ell) node := mem_image_of_mem _ (mem_filter.mpr ⟨hu,hun⟩)
    have hxs := (HS.1 node hnS).2.2.1
    have hg := actual_chain_lower_bound h m E hE S U (natStageDirectionIndex h tuple) k Q HU
      node (point node) q hq hq1 ell hell (List.ofFn (tuple node)) hxs
      (nat_stage_index_readback h tuple node) x (by simpa only [List.length_ofFn] using hx)
    have hcount : ((∏i∈range ell,((k i ⌈/⌉ M:ℕ):ℝ))/denom) ≤ (nodeVertices D m U node).card := by
      apply le_trans (by simpa only [List.length_ofFn,Nat.cast_prod] using hg)
      exact_mod_cast card_le_card (filter_subset _ _)
    exact (div_le_div_of_nonneg_right hprod hden.le).trans hcount
  have hsum : (nodes.card:ℝ)*(L^ell/denom) ≤
      (∑node∈nodes,((nodeVertices D m U node).card:ℝ)) := by
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum hnode
  have htotal : (∑node∈nodes,((nodeVertices D m U node).card:ℝ)) ≤
      (vertices E (spatialLabel D (2^(phaseDepth m)))).card := by
    exact_mod_cast sum_current_vertices_le D m hm E S hS U (Subset.refl _) nodes
  have hh := hsum.trans htotal
  rw [←mul_div_assoc] at hh
  exact (div_le_iff₀ hden).mp hh


end NativeRankPacketCount
