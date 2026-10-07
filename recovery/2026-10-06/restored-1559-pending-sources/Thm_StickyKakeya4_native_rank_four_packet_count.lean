import Theorems.Thm_StickyKakeya4_native_tagged_node_vertex_count
import Theorems.Thm_StickyKakeya4_native_compatible_node_directions

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeRankFourPacketCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeSpatialAngularGeometry NativeSquaredGrainQueries
open NativeNodalReferenceLift NativeQueriedVertexWeights NativeTaggedPacketFiberIteration
open NativeTaggedNodeVertexCount NativeCompatibleNodeDirections NativeCompatibleAngularCandidates
open NativeDirectionRankDichotomy RichDirectionalLayers WeightedRichDirectionalLayers
open scoped BigOperators

lemma ratio_le_ceilDiv (k M : ℕ) (hM : 0 < M) :
    (k:ℝ)/(M:ℝ) ≤ (k ⌈/⌉ M:ℕ) := by
  apply (div_le_iff₀ (show (0:ℝ)<M by exact_mod_cast hM)).mpr
  have hh := (ceilDiv_le_iff_le_mul hM).mp (le_refl (k ⌈/⌉ M))
  have hh' : k ≤ (k ⌈/⌉ M)*M := by simpa only [Nat.mul_comm] using hh
  exact_mod_cast hh'

/-- The original coarse query controls the mass in each unique current tag. -/
theorem current_node_cap {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (S : Finset Index) (hS : S⊆E.image Prod.snd) (Q : ℕ)
    (HU : NativeJointUniformCoarseRelations.HasUniformFibers E Q
      (fun z => spatialLabel D (2^m) z.2)) (node : Index) :
    mass (classFiber (currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ))) Prod.fst node)
      (fun u => pointWeight E u.2) ≤ vertexCap E (spatialLabel D (2^m)) Q := by
  let B := classFiber (currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ))) Prod.fst node
  have hi : Set.InjOn Prod.snd (B:Set (Index × Index)) := by
    intro u hu v hv huv
    exact Prod.ext ((mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm) huv
  have hs : B.image Prod.snd ⊆ classFiber (E.image Prod.snd) (spatialLabel D (2^m)) node := by
    intro z hz
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hz
    obtain ⟨hu,hun⟩ := mem_filter.mp hu
    simp only [currentLift,mem_image] at hu
    obtain ⟨k,hk,rfl⟩ := hu
    exact mem_filter.mpr ⟨hS hk,hun⟩
  calc
    _ = ∑z∈B.image Prod.snd,pointWeight E z := (sum_image hi).symm
    _ ≤ mass (classFiber (E.image Prod.snd) (spatialLabel D (2^m)) node) (pointWeight E) :=
      sum_le_sum_of_subset hs
    _ ≤ _ := vertex_mass_le_cap E (spatialLabel D (2^m)) Q HU node

/-- Half the original current mass forces an actual number of occupied
coarse nodes. Only the installed original coarse raw-query uniformity is used. -/
theorem retained_node_cross {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (S : Finset Index)
    (hS : S⊆E.image Prod.snd) (Q : ℕ)
    (HU : NativeJointUniformCoarseRelations.HasUniformFibers E Q
      (fun z => spatialLabel D (2^m) z.2))
    (B : Finset (Index × Index))
    (hB : B⊆currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ)))
    (hhalf : mass S (pointWeight E) ≤ 2*mass B (fun u => pointWeight E u.2)) :
    ((mass S (pointWeight E):ℝ)/(E.card:ℝ))*(vertices E (spatialLabel D (2^m))).card ≤
      2*(Q:ℝ)^2*(B.image Prod.fst).card := by
  let M := vertexCap E (spatialLabel D (2^m)) Q
  have hmass : mass B (fun u => pointWeight E u.2) ≤ (B.image Prod.fst).card*M := by
    convert mass_le_image_card_mul _ B hB Prod.fst (fun u => pointWeight E u.2) M
      (current_node_cap D m E S hS Q HU) using 1
    congr
    exact Subsingleton.elim _ _
  have hM : M*(vertices E (spatialLabel D (2^m))).card ≤ Q^2*E.card :=
    Nat.div_mul_le_self _ _
  have hc : mass S (pointWeight E)*(vertices E (spatialLabel D (2^m))).card ≤
      2*(B.image Prod.fst).card*(Q^2*E.card) := by
    calc
      _ ≤ (2*((B.image Prod.fst).card*M))*(vertices E (spatialLabel D (2^m))).card :=
        Nat.mul_le_mul_right _ (hhalf.trans (Nat.mul_le_mul_left 2 hmass))
      _ = 2*(B.image Prod.fst).card*(M*(vertices E (spatialLabel D (2^m))).card) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hM
  have hEc : (0:ℝ)<E.card := by exact_mod_cast card_pos.mpr hE
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hEc).mpr
  have hr : (mass S (pointWeight E):ℝ)*(vertices E (spatialLabel D (2^m))).card ≤
      2*(B.image Prod.fst).card*((Q:ℝ)^2*E.card) := by exact_mod_cast hc
  nlinarith only [hr]

/-- Geometry and actual chain provenance convert the four constructed
thresholds into a global count. This finite bridge is used below only with
threshold bounds derived by the actual rich-layer constructor. -/
theorem four_stage_vertex_count {n : ℕ} {D : FiniteScaleSource n} {eta a q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (S : Finset Index)
    (hS : S⊆E.image Prod.snd) (Q : ℕ)
    (HU : NativeJointUniformCoarseRelations.HasUniformFibers E Q
      (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (point : Index → Index) (tuple : Index → Fin 4 → (Fin n × Index))
    (anchor : Index → Fin 4 → Fin n)
    (HS : IsNodeDirectionSystem D a m E S q 4 point tuple anchor) (hq : 0 < q) (hq1 : q ≤ 1)
    (k : ℕ → ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hk : ∀i<4,L ≤ (k i:ℝ)/(vertexCap E (spatialLabel D (2^(phaseDepth m))) Q:ℝ)) :
    let U := currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ))
    let Omega := NativeTaggedPacketFiberIteration.layers D m E S U (natStageDirectionIndex h tuple) k
    ((Omega 4).image Prod.fst).card*L^4 ≤
      (vertices E (spatialLabel D (2^(phaseDepth m)))).card*((41*(256*258)/q)^4)^4 := by
  intro U Omega
  let M := vertexCap E (spatialLabel D (2^(phaseDepth m))) Q
  let nodes := (Omega 4).image Prod.fst
  let denom : ℝ := ((41*(256*258)/q)^4)^4
  have hden : 0 < denom := by dsimp [denom]; positivity
  have hM : 0 < M := vertexCap_pos E hE _ Q HU
  have hsub : Omega 4⊆U := by
    exact NativeWeightedPacketLayers.layers_subset_start U
      (fun i => NativeTaggedPacketRows.packetSet D m E S (natStageDirectionIndex h tuple i))
      (fun i => NativeTaggedPacketRows.assignedLabel D m (natStageDirectionIndex h tuple i))
      (fun u => pointWeight E u.2) k 4
  have hprod : L^4 ≤ (∏i∈range 4,((k i ⌈/⌉ M:ℕ):ℝ)) := by
    calc
      _ = ∏_i∈range 4,L := by simp
      _ ≤ _ := prod_le_prod (fun _ _ => hL)
        (fun i hi => (hk i (mem_range.mp hi)).trans (ratio_le_ceilDiv (k i) M hM))
  have hnode : ∀node∈nodes,L^4/denom ≤ (nodeVertices D m U node).card := by
    intro node hn
    obtain ⟨u,hu,hun⟩ := mem_image.mp hn
    have huU := hsub hu
    simp only [U,currentLift,mem_image] at huU
    obtain ⟨z,hz,hzu⟩ := huU
    have hnS : node∈NativeCompatibleNodeDirections.nodes D m S := by
      refine mem_image.mpr ⟨z,hz,?_⟩
      exact (congrArg Prod.fst hzu).trans hun
    let x := spatialLabel D (2^(phaseDepth m)) u.2
    have hx : x∈nodeVertices D m (Omega 4) node := mem_image_of_mem _ (mem_filter.mpr ⟨hu,hun⟩)
    have hxs := (HS.1 node hnS).2.2.1
    have hg := actual_chain_lower_bound h m E hE S U (natStageDirectionIndex h tuple) k Q HU
      node (point node) q hq hq1 4 (by norm_num) (List.ofFn (tuple node)) hxs
      (nat_stage_index_readback h tuple node) x (by simpa only [List.length_ofFn] using hx)
    have hcount : ((∏i∈range 4,((k i ⌈/⌉ M:ℕ):ℝ))/denom) ≤ (nodeVertices D m U node).card := by
      apply le_trans (by simpa only [List.length_ofFn,Nat.cast_prod] using hg)
      exact_mod_cast card_le_card (filter_subset _ _)
    exact (div_le_div_of_nonneg_right hprod hden.le).trans hcount
  have hsum : (nodes.card:ℝ)*(L^4/denom) ≤
      (∑node∈nodes,((nodeVertices D m U node).card:ℝ)) := by
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum hnode
  have htotal : (∑node∈nodes,((nodeVertices D m U node).card:ℝ)) ≤
      (vertices E (spatialLabel D (2^(phaseDepth m)))).card := by
    exact_mod_cast sum_current_vertices_le D m hm E S hS U (Subset.refl _) nodes
  have hh := hsum.trans htotal
  rw [←mul_div_assoc] at hh
  exact (div_le_iff₀ hden).mp hh

end NativeRankFourPacketCount
