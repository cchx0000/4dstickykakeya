import Theorems.Thm_StickyKakeya4_native_tagged_packet_fiber_iteration
import Theorems.Thm_StickyKakeya4_native_compatible_angular_candidates

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeTaggedNodeVertexCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection
open NativeSpatialAngularGeometry NativeSquaredGrainQueries NativeNodalReferenceLift
open NativeQueriedVertexWeights NativeTaggedPacketFiberIteration NativeCompatibleAngularCandidates
open scoped BigOperators

/-- A current tag is the exact dyadic ancestor of its raw squared-scale
vertex. The identity is read back from the original point's grid labels. -/
lemma current_tag_node {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (hm : 6 ≤ m)
    (S : Finset Index) (u : Index × Index)
    (hu : u∈currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ))) :
    u.1=spatialAncestor (phaseDepth m) m (spatialLabel D (2^(phaseDepth m)) u.2) := by
  simp only [currentLift,mem_image] at hu
  obtain ⟨k,_hk,rfl⟩ := hu
  exact (spatialAncestor_label D (show m ≤ phaseDepth m by dsimp [phaseDepth]; omega) k).symm

lemma vertex_ancestor {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (hm : 6 ≤ m)
    (S : Finset Index) (B : Finset (Index × Index))
    (hB : B⊆currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ)))
    (node x : Index) (hx : x∈nodeVertices D m B node) :
    spatialAncestor (phaseDepth m) m x=node := by
  obtain ⟨u,hu,hux⟩ := mem_image.mp hx
  obtain ⟨huB,hun⟩ := mem_filter.mp hu
  rw [←hux]
  exact (current_tag_node D m hm S u (hB huB)).symm.trans hun

/-- Distinct CURRENT nodes have disjoint vertex images. This is stronger
than the bounded duplication used for the enlarged reference labels. -/
theorem current_nodes_disjoint {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (hm : 6 ≤ m)
    (S : Finset Index) (B : Finset (Index × Index))
    (hB : B⊆currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ)))
    (node other : Index) (hne : node≠other) :
    Disjoint (nodeVertices D m B node) (nodeVertices D m B other) := by
  apply disjoint_left.mpr
  intro x hxn hxo
  exact hne ((vertex_ancestor D m hm S B hB node x hxn).symm.trans
    (vertex_ancestor D m hm S B hB other x hxo))

/-- Summing over any finite node menu pays no reference-duplication factor. -/
theorem sum_current_vertices_le {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (hm : 6 ≤ m)
    (E : Finset (Fin n × Index)) (S : Finset Index) (hS : S⊆E.image Prod.snd)
    (B : Finset (Index × Index))
    (hB : B⊆currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ))) (nodes : Finset Index) :
    (∑node∈nodes,(nodeVertices D m B node).card) ≤
      (vertices E (spatialLabel D (2^(phaseDepth m)))).card := by
  have hd : Set.PairwiseDisjoint (nodes:Set Index) (nodeVertices D m B) := by
    intro node _hn other _ho hne
    exact current_nodes_disjoint D m hm S B hB node other hne
  have hs : nodes.biUnion (nodeVertices D m B) ⊆ vertices E (spatialLabel D (2^(phaseDepth m))) := by
    intro x hx
    obtain ⟨node,_hn,hxn⟩ := mem_biUnion.mp hx
    obtain ⟨u,hu,hux⟩ := mem_image.mp hxn
    have hcur := hB (mem_filter.mp hu).1
    simp only [currentLift,mem_image] at hcur
    obtain ⟨k,hk,rfl⟩ := hcur
    exact mem_image.mpr ⟨k,hS hk,hux⟩
  calc
    _ = (nodes.biUnion (nodeVertices D m B)).card := (card_biUnion hd).symm
    _ ≤ _ := card_le_card hs

/-- Literal packet layers starting from the uniquely tagged current source
inherit the exact global raw-vertex count at every stage. -/
theorem layers_vertices_sum_le {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (hm : 6 ≤ m)
    (E : Finset (Fin n × Index)) (S : Finset Index) (hS : S⊆E.image Prod.snd)
    (dir : ℕ → Index → Fin n) (k : ℕ → ℕ) (i : ℕ) (nodes : Finset Index) :
    (∑node∈nodes,(nodeVertices D m
      (NativeTaggedPacketFiberIteration.layers D m E S
        (currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ))) dir k i) node).card) ≤
      (vertices E (spatialLabel D (2^(phaseDepth m)))).card := by
  apply sum_current_vertices_le D m hm E S hS
  exact NativeWeightedPacketLayers.layers_subset_start _
    (fun j => NativeTaggedPacketRows.packetSet D m E S (dir j))
    (fun j => NativeTaggedPacketRows.assignedLabel D m (dir j))
    (fun u => pointWeight E u.2) k i

end NativeTaggedNodeVertexCount
