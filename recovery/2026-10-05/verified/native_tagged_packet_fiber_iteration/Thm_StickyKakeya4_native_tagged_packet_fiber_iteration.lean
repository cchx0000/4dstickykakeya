import Theorems.Thm_StickyKakeya4_native_tagged_packet_rows
import Theorems.Thm_StickyKakeya4_native_weighted_packet_layers
import Theorems.Thm_StickyKakeya4_native_queried_vertex_weights
import Theorems.Thm_StickyKakeya4_native_approximate_fiber_iteration
import Theorems.Thm_StickyKakeya4_native_separated_fiber_iteration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeTaggedPacketFiberIteration
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeSpatialAngularGeometry NativeDirectionRankDichotomy NativeSquaredGrainQueries
open NativeOriginalPacketReference NativeNodalReferenceLift NativeQueriedVertexWeights
open RichDirectionalLayers WeightedRichDirectionalLayers NativeApproximateFiberCount
open NativeApproximateFiberIteration BackwardFiberGrains
open scoped BigOperators

/-- Only one node's labels are projected to physical vertices. -/
def nodeVertices {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (B : Finset (Index × Index)) (node : Index) : Finset Index :=
  (B.filter (fun u => u.1=node)).image (fun u => spatialLabel D (2^(phaseDepth m)) u.2)

/-- Explicit packet restrictions with the unchanged original E2 point weights. -/
def layers {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (E : Finset (Fin n × Index))
    (S : Finset Index) (U : Finset (Index × Index))
    (dir : ℕ → Index → Fin n) (k : ℕ → ℕ) : ℕ → Finset (Index × Index) :=
  NativeWeightedPacketLayers.layers U (fun i => NativeTaggedPacketRows.packetSet D m E S (dir i))
    (fun i => NativeTaggedPacketRows.assignedLabel D m (dir i)) (fun u => pointWeight E u.2) k

/-- Installed raw-query uniformity supplies the cap on each fixed-node
reference vertex. There is no extra node-duplication factor in this cap. -/
theorem fixed_node_cap {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (S : Finset Index) (Q : ℕ)
    (HU : NativeJointUniformCoarseRelations.HasUniformFibers E Q
      (fun z => spatialLabel D (2^(phaseDepth m)) z.2)) (node b : Index) :
    mass (classFiber ((NativeTaggedPacketRows.reference D m E S).filter (fun u => u.1=node))
      (fun u => spatialLabel D (2^(phaseDepth m)) u.2) b) (fun u => pointWeight E u.2) ≤
        vertexCap E (spatialLabel D (2^(phaseDepth m))) Q := by
  have he : classFiber ((NativeTaggedPacketRows.reference D m E S).filter (fun u => u.1=node))
      (fun u => spatialLabel D (2^(phaseDepth m)) u.2) b =
      (NativeTaggedPacketRows.reference D m E S).filter
        (fun u => u.1=node ∧ spatialLabel D (2^(phaseDepth m)) u.2=b) := by
    ext u
    simp only [classFiber,mem_filter,and_assoc]
  rw [he]
  have hh := fixed_node_vertex_mass (S.image (spatialLabel D (2^m))) (64/((2^m:ℕ):ℝ))
    (E.image Prod.snd) (rawVertex D (phaseDepth m)) (pointWeight E)
    (spatialLabel D (2^(phaseDepth m))) node b
  have hb : mass ((NativeTaggedPacketRows.reference D m E S).filter
      (fun u => u.1=node ∧ spatialLabel D (2^(phaseDepth m)) u.2=b)) (fun u => pointWeight E u.2) ≤
      mass (classFiber (E.image Prod.snd) (spatialLabel D (2^(phaseDepth m))) b) (pointWeight E) := by
    dsimp only [NativeTaggedPacketRows.reference,WeightedRichDirectionalLayers.mass,classFiber]
    convert hh using 1
    all_goals congr
  exact hb.trans (vertex_mass_le_cap E (spatialLabel D (2^(phaseDepth m))) Q HU b)

theorem packet_predecessor_geometry {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (S : Finset Index) (dir : Index → Fin n)
    (a b : Index × Index)
    (hb : b∈NativeTaggedPacketRows.packetSet D m E S dir
      (NativeTaggedPacketRows.assignedLabel D m dir a)) :
    b∈NativeTaggedPacketRows.reference D m E S ∧ b.1=a.1 ∧
      Metric.infDist (rawVertex D (phaseDepth m) b.2-rawVertex D (phaseDepth m) a.2)
        (Submodule.span ℝ {slopeVector D (dir a.1)}:Set E4) ≤ 258*(64/((2^(phaseDepth m):ℕ):ℝ)) := by
  obtain ⟨hbR,hnode,hpacket⟩ := mem_filter.mp hb
  have hh := NativeScaledLinePackets.rounded_packet_geometry (slopeVector D (dir a.1))
    (64/((2^(phaseDepth m):ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) (by positivity) (by positivity)
    (rawVertex D (phaseDepth m) a.2) (rawVertex D (phaseDepth m) b.2) hpacket
  exact ⟨hbR,hnode.symm,hh.1⟩

/-- The one-step numerator is derived from the actual layer restriction.
The true packet geometry supplies its approximate line fiber. -/
theorem step_vertex_count {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (S : Finset Index)
    (U : Finset (Index × Index)) (dir : ℕ → Index → Fin n) (k : ℕ → ℕ) (Q : ℕ)
    (HU : NativeJointUniformCoarseRelations.HasUniformFibers E Q
      (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (i : ℕ) (a : Index × Index) (ha : a∈layers D m E S U dir k (i+1)) :
    k i ⌈/⌉ vertexCap E (spatialLabel D (2^(phaseDepth m))) Q ≤
      (fiber (64/((2^(phaseDepth m):ℕ):ℝ))
        (nodeVertices D m (layers D m E S U dir k i) a.1)
        (Submodule.span ℝ {slopeVector D (dir i a.1)}) (rawVertex D (phaseDepth m) a.2)
        (258*(64/((2^(phaseDepth m):ℕ):ℝ)))).card := by
  let f : Index × Index → Index := fun u => spatialLabel D (2^(phaseDepth m)) u.2
  let B := layers D m E S U dir k i ∩ NativeTaggedPacketRows.packetSet D m E S (dir i)
    (NativeTaggedPacketRows.assignedLabel D m (dir i) a)
  have hpred : k i ≤ mass B (fun u => pointWeight E u.2) := by
    have hh := NativeWeightedPacketLayers.layers_predecessors U
      (fun j => NativeTaggedPacketRows.packetSet D m E S (dir j))
      (fun j => NativeTaggedPacketRows.assignedLabel D m (dir j))
      (fun u => pointWeight E u.2) k i a ha
    dsimp only [NativeWeightedPacketLayers.packetMass] at hh
    dsimp only [B,layers]
    convert hh using 1
    congr
    exact Subsingleton.elim _ _
  have hBR : B⊆(NativeTaggedPacketRows.reference D m E S).filter (fun u => u.1=a.1) := by
    intro b hb
    have hg := packet_predecessor_geometry D m E S (dir i) a b (mem_inter.mp hb).2
    exact mem_filter.mpr ⟨hg.1,hg.2.1⟩
  have hcap : mass B (fun u => pointWeight E u.2) ≤
      (B.image f).card*vertexCap E (spatialLabel D (2^(phaseDepth m))) Q := by
    convert mass_le_image_card_mul _ B hBR f (fun u => pointWeight E u.2) _
      (fixed_node_cap D m E S Q HU a.1) using 1
    congr
    exact Subsingleton.elim _ _
  have him : B.image f ⊆ fiber (64/((2^(phaseDepth m):ℕ):ℝ))
      (nodeVertices D m (layers D m E S U dir k i) a.1)
      (Submodule.span ℝ {slopeVector D (dir i a.1)}) (rawVertex D (phaseDepth m) a.2)
      (258*(64/((2^(phaseDepth m):ℕ):ℝ))) := by
    intro b hb
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hb
    obtain ⟨hzL,hzp⟩ := mem_inter.mp hz
    have hg := packet_predecessor_geometry D m E S (dir i) a z hzp
    exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mpr ⟨hzL,hg.2.1⟩),hg.2.2⟩
  apply (ceilDiv_le_iff_le_mul (vertexCap_pos E hE (spatialLabel D (2^(phaseDepth m))) Q HU)).mpr
  have hh : k i ≤ vertexCap E (spatialLabel D (2^(phaseDepth m))) Q*(B.image f).card := by
    simpa only [Nat.mul_comm] using hpred.trans hcap
  exact hh.trans (Nat.mul_le_mul_left _ (card_le_card him))

/-- Passing to vertices retains the fixed node and the actual layer bound. -/
theorem node_vertex_predecessors {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (S : Finset Index)
    (U : Finset (Index × Index)) (dir : ℕ → Index → Fin n) (k : ℕ → ℕ) (Q : ℕ)
    (HU : NativeJointUniformCoarseRelations.HasUniformFibers E Q
      (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (i : ℕ) (node x : Index) (hx : x∈nodeVertices D m (layers D m E S U dir k (i+1)) node) :
    k i ⌈/⌉ vertexCap E (spatialLabel D (2^(phaseDepth m))) Q ≤
      (fiber (64/((2^(phaseDepth m):ℕ):ℝ))
        (nodeVertices D m (layers D m E S U dir k i) node)
        (Submodule.span ℝ {slopeVector D (dir i node)})
        (cellCenter (64/((2^(phaseDepth m):ℕ):ℝ)) x) (258*(64/((2^(phaseDepth m):ℕ):ℝ)))).card := by
  obtain ⟨a,ha,hax⟩ := mem_image.mp hx
  obtain ⟨haL,han⟩ := mem_filter.mp ha
  have hh := step_vertex_count D m E hE S U dir k Q HU i a haL
  simpa only [han,rawVertex,hax] using hh

theorem node_minimum_lower {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (S : Finset Index)
    (U : Finset (Index × Index)) (dir : ℕ → Index → Fin n) (k : ℕ → ℕ) (Q : ℕ)
    (HU : NativeJointUniformCoarseRelations.HasUniformFibers E Q
      (fun z => spatialLabel D (2^(phaseDepth m)) z.2)) (i : ℕ) (node : Index)
    (hne : (nodeVertices D m (layers D m E S U dir k (i+1)) node).Nonempty) :
    k i ⌈/⌉ vertexCap E (spatialLabel D (2^(phaseDepth m))) Q ≤
      minimumPredecessor (64/((2^(phaseDepth m):ℕ):ℝ))
        (nodeVertices D m (layers D m E S U dir k i) node)
        (nodeVertices D m (layers D m E S U dir k (i+1)) node)
        (Submodule.span ℝ {slopeVector D (dir i node)}) (258*(64/((2^(phaseDepth m):ℕ):ℝ))) := by
  simp only [minimumPredecessor,dif_pos hne]
  apply le_min'
  intro z hz
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
  exact node_vertex_predecessors D m E hE S U dir k Q HU i node x hx

lemma layers_antitone {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (S : Finset Index) (U : Finset (Index × Index))
    (dir : ℕ → Index → Fin n) (k : ℕ → ℕ) : Antitone (layers D m E S U dir k) := by
  apply antitone_nat_of_succ_le
  intro i
  exact NativeWeightedPacketLayers.layers_step_subset U
    (fun j => NativeTaggedPacketRows.packetSet D m E S (dir j))
    (fun j => NativeTaggedPacketRows.assignedLabel D m (dir j))
    (fun u => pointWeight E u.2) k i

lemma nodeVertices_mono {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    {A B : Finset (Index × Index)} (hAB : A⊆B) (node : Index) :
    nodeVertices D m A node ⊆ nodeVertices D m B node := by
  intro x hx
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
  obtain ⟨hu,hun⟩ := mem_filter.mp hu
  exact mem_image_of_mem _ (mem_filter.mpr ⟨hAB hu,hun⟩)

/-- The chosen directions are read back from one genuine incident chain.
All predecessor factors are then obtained from packet restriction, and every
stage remains in this same node. Thresholds may be zero. -/
theorem actual_chain_lower_bound {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (hNative : IsWangZakharovNativeFiniteInput D eta) (m : ℕ)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (S : Finset Index)
    (U : Finset (Index × Index)) (dir : ℕ → Index → Fin n) (k : ℕ → ℕ) (Q : ℕ)
    (HU : NativeJointUniformCoarseRelations.HasUniformFibers E Q
      (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (node oldPoint : Index) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ell : ℕ) (hell : ell ≤ 4) (xs : List (Fin n × Index))
    (hxs : xs∈chains (E.filter (fun z => z.2=oldPoint)) (fun z => slopeVector D z.1) q ell)
    (hdir : ∀i : Fin xs.length,dir i.val node=(xs.get i.rev).1)
    (x : Index) (hx : x∈nodeVertices D m (layers D m E S U dir k xs.length) node) :
    ((∏i∈range xs.length,k i ⌈/⌉ vertexCap E (spatialLabel D (2^(phaseDepth m))) Q : ℕ):ℝ)/
        ((41*(256*258)/q)^4)^xs.length ≤
      ((fiber (64/((2^(phaseDepth m):ℕ):ℝ)) (nodeVertices D m (layers D m E S U dir k 0) node)
        (spanOf (fun z : Fin n × Index => slopeVector D z.1) xs)
        (cellCenter (64/((2^(phaseDepth m):ℕ):ℝ)) x)
        (radius (258*(64/((2^(phaseDepth m):ℕ):ℝ))) xs.length)).card:ℝ) := by
  let H : ℝ := 64/((2^(phaseDepth m):ℕ):ℝ)
  let A : ℕ → Finset Index := fun i => nodeVertices D m (layers D m E S U dir k i) node
  let v := NativeSeparatedFiberIteration.reverseFamily (fun z : Fin n × Index => slopeVector D z.1) xs
  have hH : 0 < H := by dsimp [H]; positivity
  have hmin : ∀i∈range xs.length,k i ⌈/⌉ vertexCap E (spatialLabel D (2^(phaseDepth m))) Q ≤
      predecessorMinimum H A v (258*H) i := by
    intro i hi
    have hi' : i < xs.length := mem_range.mp hi
    have hs : layers D m E S U dir k xs.length ⊆ layers D m E S U dir k (i+1) :=
      layers_antitone D m E S U dir k (by omega)
    have hne : (nodeVertices D m (layers D m E S U dir k (i+1)) node).Nonempty :=
      ⟨x,nodeVertices_mono D m hs node hx⟩
    have hd : directionAt v i=slopeVector D (dir i node) := by
      calc
        _ = slopeVector D (xs.get (⟨i,hi'⟩:Fin xs.length).rev).1 := directionAt_eq v ⟨i,hi'⟩
        _ = _ := congrArg (slopeVector D) (hdir ⟨i,hi'⟩).symm
    unfold predecessorMinimum
    rw [hd]
    exact node_minimum_lower D m E hE S U dir k Q HU i node hne
  have hp : (∏i∈range xs.length,k i ⌈/⌉ vertexCap E (spatialLabel D (2^(phaseDepth m))) Q) ≤
      ∏i∈range xs.length,predecessorMinimum H A v (258*H) i := prod_le_prod' hmin
  have hg := NativeSeparatedFiberIteration.native_chain_lower_bound hNative E oldPoint q hq hq1
    ell hell xs hxs A hH (258*H) 258 (by positivity) (by norm_num) le_rfl x hx
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hp) (by positivity)).trans hg

end NativeTaggedPacketFiberIteration
