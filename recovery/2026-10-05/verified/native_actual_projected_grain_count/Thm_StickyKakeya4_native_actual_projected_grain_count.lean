import Theorems.Thm_StickyKakeya4_native_tagged_packet_fiber_iteration
import Theorems.Thm_StickyKakeya4_native_iterated_projection_grains
import Theorems.Thm_StickyKakeya4_native_tagged_node_vertex_count

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeActualProjectedGrainCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeSpatialAngularGeometry NativeDirectionRankDichotomy NativeSquaredGrainQueries
open NativeOriginalPacketReference NativeNodalReferenceLift NativeQueriedVertexWeights
open NativeJointUniformCoarseRelations NativeTaggedPacketFiberIteration
open NativeApproximateFiberCount NativeApproximateFiberIteration NativeQuantizedProjectionGrains
open NativeIteratedProjectionGrains BackwardFiberGrains
open scoped BigOperators

/-- The genuine thickened span width produced by the packet iteration. -/
def grainWidth (m ell : ℕ) : ℝ := radius (258*(64/((2^(phaseDepth m):ℕ):ℝ))) ell

lemma grainWidth_pos (m ell : ℕ) : 0 < grainWidth m ell := radius_pos (by positivity) ell

/-- Quantized projection of an ORIGINAL point's physical squared-scale vertex. -/
def projectionLabel {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (P : Submodule ℝ E4)
    (ell : ℕ) (k : Index) : Index :=
  vertexLabel (64/((2^(phaseDepth m):ℕ):ℝ)) P (grainWidth m ell)
    (spatialLabel D (2^(phaseDepth m)) k)

/-- The node is part of the grain label; planes may vary from node to node. -/
def taggedLabel {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (k : Index) : Index × Index :=
  (spatialLabel D (2^m) k,projectionLabel D m (P (spatialLabel D (2^m) k)) ell k)

def predecessorProduct {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (Q : ℕ) (k : ℕ → ℕ) (ell : ℕ) : ℕ :=
  ∏i∈range ell,k i ⌈/⌉ vertexCap E (spatialLabel D (2^(phaseDepth m))) Q

def transverseCost (q : ℝ) (ell : ℕ) : ℝ := ((41*(256*258)/q)^4)^ell

lemma transverseCost_pos {q : ℝ} (hq : 0 < q) (ell : ℕ) : 0 < transverseCost q ell := by
  unfold transverseCost
  positivity

/-- The minimum projection-fiber cardinality is bounded by the actual packet
thresholds. It is evaluated at a genuine terminal node label, rather than
supplied as a richness or capacity certificate. -/
theorem actual_projection_minimum_lower {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (S : Finset Index)
    (U : Finset (Index × Index)) (dir : ℕ → Index → Fin n) (k : ℕ → ℕ) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (node oldPoint : Index) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ell : ℕ) (hell : ell ≤ 4) (xs : List (Fin n × Index))
    (hxs : xs∈chains (E.filter (fun z => z.2=oldPoint)) (fun z => slopeVector D z.1) q ell)
    (hdir : ∀i : Fin xs.length,dir i.val node=(xs.get i.rev).1)
    (hB : ((layers D m E S U dir k xs.length).filter (fun u => u.1=node)).Nonempty) :
    (predecessorProduct D m E Q k xs.length:ℝ)/transverseCost q xs.length ≤
      (minimumFiber (nodeVertices D m (layers D m E S U dir k 0) node)
        ((layers D m E S U dir k xs.length).filter (fun u => u.1=node))
        (fun u => spatialLabel D (2^(phaseDepth m)) u.2)
        (64/((2^(phaseDepth m):ℕ):ℝ))
        (spanOf (fun z : Fin n × Index => slopeVector D z.1) xs) (grainWidth m xs.length):ℝ) := by
  obtain ⟨u,hu,hmin⟩ := minimumFiber_attained
    (nodeVertices D m (layers D m E S U dir k 0) node)
    ((layers D m E S U dir k xs.length).filter (fun u => u.1=node))
    (fun u => spatialLabel D (2^(phaseDepth m)) u.2)
    (64/((2^(phaseDepth m):ℕ):ℝ))
    (spanOf (fun z : Fin n × Index => slopeVector D z.1) xs) (grainWidth m xs.length) hB
  have huV : spatialLabel D (2^(phaseDepth m)) u.2∈
      nodeVertices D m (layers D m E S U dir k xs.length) node := mem_image_of_mem _ hu
  rw [hmin]
  exact actual_chain_lower_bound h m E hE S U dir k Q HU node oldPoint q hq hq1 ell hell xs hxs hdir
    _ huV

/-- Genuine single-node grain count from the explicit packet layers and the
original separated tuple. Neither predecessors nor grain counts are inputs. -/
theorem actual_node_grain_count {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (S : Finset Index)
    (U : Finset (Index × Index)) (dir : ℕ → Index → Fin n) (k : ℕ → ℕ) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (node oldPoint : Index) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ell : ℕ) (hell : ell ≤ 4) (xs : List (Fin n × Index))
    (hxs : xs∈chains (E.filter (fun z => z.2=oldPoint)) (fun z => slopeVector D z.1) q ell)
    (hdir : ∀i : Fin xs.length,dir i.val node=(xs.get i.rev).1) :
    (((layers D m E S U dir k xs.length).filter (fun u => u.1=node)).image
      (fun u => projectionLabel D m (spanOf (fun z : Fin n × Index => slopeVector D z.1) xs)
        xs.length u.2)).card * (predecessorProduct D m E Q k xs.length:ℝ) ≤
      625*(nodeVertices D m (layers D m E S U dir k 0) node).card*transverseCost q xs.length := by
  let B := (layers D m E S U dir k xs.length).filter (fun u => u.1=node)
  let A := nodeVertices D m (layers D m E S U dir k 0) node
  let P := spanOf (fun z : Fin n × Index => slopeVector D z.1) xs
  let loc := fun u : Index × Index => spatialLabel D (2^(phaseDepth m)) u.2
  let mesh := 64/((2^(phaseDepth m):ℕ):ℝ)
  let width := grainWidth m xs.length
  let G := (B.image (fun u => projectionLabel D m P xs.length u.2)).card
  change (G:ℝ)*(predecessorProduct D m E Q k xs.length:ℝ) ≤ 625*(A.card:ℝ)*transverseCost q xs.length
  by_cases hB : B.Nonempty
  · have hmin := actual_projection_minimum_lower h m E hE S U dir k Q HU node oldPoint q hq hq1
      ell hell xs hxs hdir hB
    have hc := grain_count_computed A B loc mesh P width (grainWidth_pos m xs.length)
    have hcross : (G:ℝ)*(predecessorProduct D m E Q k xs.length:ℝ)/transverseCost q xs.length ≤
        625*(A.card:ℝ) := by
      calc
        _ = (G:ℝ)*((predecessorProduct D m E Q k xs.length:ℝ)/transverseCost q xs.length) := by ring
        _ ≤ (G:ℝ)*(minimumFiber A B loc mesh P width:ℝ) :=
          mul_le_mul_of_nonneg_left hmin (Nat.cast_nonneg G)
        _ ≤ _ := by exact_mod_cast hc
    exact (div_le_iff₀ (transverseCost_pos hq xs.length)).mp hcross
  · have hG : G=0 := by simp only [G,not_nonempty_iff_eq_empty.mp hB,image_empty,card_empty]
    rw [hG,Nat.cast_zero,zero_mul]
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg A.card)) (transverseCost_pos hq _).le

/-- A later literal point restriction inherits this count through the history
membership statement, without preserving any pointwise predecessor density. -/
theorem restricted_node_grain_count {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (S : Finset Index)
    (U : Finset (Index × Index)) (dir : ℕ → Index → Fin n) (k : ℕ → ℕ) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (node oldPoint : Index) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ell : ℕ) (hell : ell ≤ 4) (xs : List (Fin n × Index))
    (hxs : xs∈chains (E.filter (fun z => z.2=oldPoint)) (fun z => slopeVector D z.1) q ell)
    (hdir : ∀i : Fin xs.length,dir i.val node=(xs.get i.rev).1)
    (F : Finset Index)
    (hF : ∀z∈F,(spatialLabel D (2^m) z,z)∈layers D m E S U dir k xs.length) :
    (((F.filter (fun z => spatialLabel D (2^m) z=node)).image
      (projectionLabel D m (spanOf (fun z : Fin n × Index => slopeVector D z.1) xs) xs.length)).card:ℝ)*
        predecessorProduct D m E Q k xs.length ≤
      625*(nodeVertices D m (layers D m E S U dir k 0) node).card*transverseCost q xs.length := by
  have hsub : (F.filter (fun z => spatialLabel D (2^m) z=node)).image
      (projectionLabel D m (spanOf (fun z : Fin n × Index => slopeVector D z.1) xs) xs.length) ⊆
      ((layers D m E S U dir k xs.length).filter (fun u => u.1=node)).image
        (fun u => projectionLabel D m (spanOf (fun z : Fin n × Index => slopeVector D z.1) xs)
          xs.length u.2) := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
    exact mem_image.mpr ⟨(spatialLabel D (2^m) z,z),
      mem_filter.mpr ⟨hF z (mem_filter.mp hz).1,(mem_filter.mp hz).2⟩,rfl⟩
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card hsub)
    (Nat.cast_nonneg (predecessorProduct D m E Q k xs.length))).trans
    (actual_node_grain_count h m E hE S U dir k Q HU node oldPoint q hq hq1 ell hell xs hxs hdir)

/-- Original incidence mass is converted to raw vertex cardinality only with
its actual computed multiplicity cap retained. -/
lemma cap_mul_raw_vertices_le {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (Q : ℕ) :
    vertexCap E (spatialLabel D (2^(phaseDepth m))) Q*
      (vertices E (spatialLabel D (2^(phaseDepth m)))).card ≤ Q^2*E.card :=
  Nat.div_mul_le_self _ _

/-- Every final projection class lies in a literal thickened affine fiber
of the same actual node plane, at the full iteration width. -/
theorem tagged_same_label_near {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (k l : Index)
    (he : taggedLabel D m P ell k=taggedLabel D m P ell l) :
    spatialLabel D (2^m) k=spatialLabel D (2^m) l ∧
      Metric.infDist (rawVertex D (phaseDepth m) k-rawVertex D (phaseDepth m) l)
        (P (spatialLabel D (2^m) k):Set E4) ≤ 2*grainWidth m ell := by
  have hn : spatialLabel D (2^m) k=spatialLabel D (2^m) l := congrArg Prod.fst he
  have hp := congrArg Prod.snd he
  change projectionLabel D m (P (spatialLabel D (2^m) k)) ell k=
    projectionLabel D m (P (spatialLabel D (2^m) l)) ell l at hp
  rw [←hn] at hp
  exact ⟨hn,same_label_near _ _ (grainWidth_pos m ell) _ _ hp⟩

end NativeActualProjectedGrainCount
