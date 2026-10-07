import Theorems.Thm_StickyKakeya4_native_actual_projected_grain_count
import Theorems.Thm_StickyKakeya4_native_actual_grain_history

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeHistoryGrainCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeSpatialAngularGeometry NativeDirectionRankDichotomy NativeSquaredGrainQueries
open NativeOriginalPacketReference NativeNodalReferenceLift NativeQueriedVertexWeights
open NativeJointUniformCoarseRelations NativeTaggedPacketFiberIteration NativeTaggedNodeVertexCount
open NativeActualProjectedGrainCount NativeActualGrainHistory NativeCompatibleNodeDirections
open NativeIncidentRankSelection BackwardFiberGrains RichDirectionalLayers
open scoped BigOperators

/-- Global counting retains the node in each label. It never identifies grains
from different actual node planes. -/
lemma tagged_card_le_sum {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (F : Finset Index) :
    (F.image (taggedLabel D m P ell)).card ≤
      ∑node∈F.image (spatialLabel D (2^m)),
        ((F.filter (fun k => spatialLabel D (2^m) k=node)).image
          (projectionLabel D m (P node) ell)).card := by
  let nodes := F.image (spatialLabel D (2^m))
  let V := fun node => ((F.filter (fun k => spatialLabel D (2^m) k=node)).image
    (projectionLabel D m (P node) ell)).image (fun v => (node,v))
  have hsub : F.image (taggedLabel D m P ell)⊆nodes.biUnion V := by
    intro g hg
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hg
    refine mem_biUnion.mpr ⟨spatialLabel D (2^m) k,mem_image_of_mem _ hk,?_⟩
    exact mem_image.mpr ⟨projectionLabel D m (P (spatialLabel D (2^m) k)) ell k,
      mem_image_of_mem _ (mem_filter.mpr ⟨hk,rfl⟩),rfl⟩
  exact (card_le_card hsub).trans (card_biUnion_le.trans
    (sum_le_sum (fun _ _ => card_image_le)))

/-- Exact raw vertex mass is kept in the global count. Every node uses its
already installed original tuple; there is no common-plane premise. -/
theorem actual_global_grain_count {n : ℕ} {D : FiniteScaleSource n} {eta a q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (S : Finset Index)
    (hS : S⊆E.image Prod.snd) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (hq : 0 < q) (hq1 : q ≤ 1) (ell : ℕ) (hell : ell ≤ 4)
    (point : Index → Index) (tuple : Index → Fin ell → (Fin n × Index))
    (anchor : Index → Fin ell → Fin n)
    (Hsys : IsNodeDirectionSystem D a m E S q ell point tuple anchor)
    (k : ℕ → ℕ) (F : Finset Index) (hFS : F⊆S)
    (hterminal : ∀z∈F,(spatialLabel D (2^m) z,z)∈
      layers D m E S (currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ)))
        (natStageDirectionIndex h tuple) k ell) :
    let P := fun node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple node))
    let G := (F.image (taggedLabel D m P ell)).card
    let L := predecessorProduct D m E Q k ell
    let M := vertexCap E (spatialLabel D (2^(phaseDepth m))) Q
    (G:ℝ)*L ≤ 625*(vertices E (spatialLabel D (2^(phaseDepth m)))).card*transverseCost q ell ∧
      (M:ℝ)*L*G ≤ 625*transverseCost q ell*(Q:ℝ)^2*E.card := by
  intro P G L M
  let U := currentLift S (cellCenter (mesh D)) (64/((2^m:ℕ):ℝ))
  let dir := natStageDirectionIndex h tuple
  let C := F.image (spatialLabel D (2^m))
  have hnode : ∀node∈C,
      (((F.filter (fun z => spatialLabel D (2^m) z=node)).image (projectionLabel D m (P node) ell)).card:ℝ)*L ≤
        625*(nodeVertices D m (layers D m E S U dir k 0) node).card*transverseCost q ell := by
    intro node hn
    have hnS : node∈NativeCompatibleNodeDirections.nodes D m S := image_subset_image hFS hn
    have hc := (Hsys.1 node hnS).2.2.1
    have hc' : List.ofFn (tuple node)∈chains (E.filter (fun z => z.2=point node))
        (fun z => slopeVector D z.1) q ell := hc
    have hh := restricted_node_grain_count h m E hE S U dir k Q HU node (point node) q hq hq1
      ell hell (List.ofFn (tuple node)) hc' (nat_stage_index_readback h tuple node) F (by
        simpa only [List.length_ofFn] using hterminal)
    simpa only [List.length_ofFn] using hh
  have hsum : (∑node∈C,((nodeVertices D m (layers D m E S U dir k 0) node).card:ℝ)) ≤
      (vertices E (spatialLabel D (2^(phaseDepth m)))).card := by
    exact_mod_cast layers_vertices_sum_le D m hm E S hS dir k 0 C
  have hcount : (G:ℝ)*L ≤
      625*(vertices E (spatialLabel D (2^(phaseDepth m)))).card*transverseCost q ell := by
    calc
      _ ≤ (∑node∈C,(((F.filter (fun z => spatialLabel D (2^m) z=node)).image
          (projectionLabel D m (P node) ell)).card:ℝ))*(L:ℝ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast tagged_card_le_sum D m P ell F) (Nat.cast_nonneg L)
      _ = ∑node∈C,(((F.filter (fun z => spatialLabel D (2^m) z=node)).image
          (projectionLabel D m (P node) ell)).card:ℝ)*(L:ℝ) := sum_mul _ _ _
      _ ≤ ∑node∈C,625*(nodeVertices D m (layers D m E S U dir k 0) node).card*transverseCost q ell :=
        sum_le_sum hnode
      _ = (625*transverseCost q ell)*(∑node∈C,((nodeVertices D m (layers D m E S U dir k 0) node).card:ℝ)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro node _hn
        ring
      _ ≤ (625*transverseCost q ell)*(vertices E (spatialLabel D (2^(phaseDepth m)))).card :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) (transverseCost_pos hq ell).le)
      _ = _ := by ring
  refine ⟨hcount,?_⟩
  have hcap : (M:ℝ)*(vertices E (spatialLabel D (2^(phaseDepth m)))).card ≤ (Q:ℝ)^2*E.card := by
    exact_mod_cast cap_mul_raw_vertices_le D m E Q
  calc
    _ = (M:ℝ)*((G:ℝ)*L) := by ring
    _ ≤ (M:ℝ)*(625*(vertices E (spatialLabel D (2^(phaseDepth m)))).card*transverseCost q ell) :=
      mul_le_mul_of_nonneg_left hcount (Nat.cast_nonneg M)
    _ = (625*transverseCost q ell)*((M:ℝ)*(vertices E (spatialLabel D (2^(phaseDepth m)))).card) := by ring
    _ ≤ (625*transverseCost q ell)*((Q:ℝ)^2*E.card) :=
      mul_le_mul_of_nonneg_left hcap (mul_nonneg (by norm_num) (transverseCost_pos hq ell).le)
    _ = _ := by ring

/-- The actual rich-threshold definition makes every ceiling factor positive. -/
lemma scale_predecessor_product_pos {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (S : Finset Index) (ell : ℕ)
    (dir : ℕ → Index → Fin n) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => spatialLabel D (2^(phaseDepth m)) z.2)) :
    0 < predecessorProduct D m E Q (scaleThreshold D E m S ell dir) ell := by
  apply prod_pos
  intro i _hi
  apply WeightedRichDirectionalLayers.positive_predecessor_ceiling
  · exact richThreshold_positive _ _ _ _
  · exact vertexCap_pos E hE _ Q HU

/-- Count the grains of the GENUINE history-final original point set at each
earlier scale. Original node tuples are preserved, and all growth factors
come from that scale's actual computed thresholds. -/
theorem history_grain_counts {n J : ℕ} {D : FiniteScaleSource n} {eta a q lambda c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (E : Finset (Fin n × Index)) (hE : E.Nonempty)
    (m : Fin J → ℕ) (hm : ∀j,6 ≤ m j) (ell : ℕ) (hell : ell ≤ 4)
    (S0 : Finset Index) (hS0 : S0⊆E.image Prod.snd) (Q : ℕ)
    (HU : ∀j,HasUniformFibers E Q (fun z => spatialLabel D (2^(phaseDepth (m j))) z.2))
    (hq : 0 < q) (hq1 : q ≤ 1)
    (point : Fin J → Index → Index)
    (tuple : Fin J → Index → Fin ell → (Fin n × Index))
    (anchor : Fin J → Index → Fin ell → Fin n)
    (Hsys : ∀j,IsNodeDirectionSystem D a (m j) E S0 q ell (point j) (tuple j) (anchor j))
    (Hhistory : HasGrainHistory D E m ell (fun j => natStageDirectionIndex h (tuple j))
      S0 Q lambda c1 c2) :
    let S := history D E m ell (fun j => natStageDirectionIndex h (tuple j)) S0
    let P := fun j node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple j node))
    let L := fun j => predecessorProduct D (m j) E Q
      (scaleThreshold D E (m j) (S j.val) ell (natStageDirectionIndex h (tuple j))) ell
    ∀j : Fin J,0 < L j ∧
      (vertexCap E (spatialLabel D (2^(phaseDepth (m j)))) Q:ℝ)*L j*
        ((S J).image (taggedLabel D (m j) (P j) ell)).card ≤
      625*transverseCost q ell*(Q:ℝ)^2*E.card := by
  intro S P L j
  obtain ⟨_hz,_hstep,hvalid,_hmass,_hrecord,_hlift,hfinal⟩ := Hhistory
  have hSS0 : S j.val⊆S0 := (hvalid j.val j.isLt.le).2.1
  have hFS : S J⊆S j.val := history_antitone D E m ell
    (fun j => natStageDirectionIndex h (tuple j)) S0 j.isLt.le
  have hterminal : ∀z∈S J,(spatialLabel D (2^(m j)) z,z)∈
      layers D (m j) E (S j.val)
        (currentLift (S j.val) (cellCenter (mesh D)) (64/((2^(m j):ℕ):ℝ)))
        (natStageDirectionIndex h (tuple j))
        (scaleThreshold D E (m j) (S j.val) ell (natStageDirectionIndex h (tuple j))) ell := by
    dsimp only [S,scaleLayers,scaleLift,NativeTaggedPacketFiberIteration.layers,NativeTaggedReferenceDensity.tagWeight] at hfinal ⊢
    exact hfinal j
  have hc := actual_global_grain_count h (m j) (hm j) E hE (S j.val) (hSS0.trans hS0) Q (HU j)
    hq hq1 ell hell (point j) (tuple j) (anchor j) (node_direction_system_mono (Hsys j) hSS0)
    (scaleThreshold D E (m j) (S j.val) ell (natStageDirectionIndex h (tuple j))) (S J) hFS hterminal
  exact ⟨scale_predecessor_product_pos D (m j) E hE (S j.val) ell _ Q (HU j),hc.2⟩

end NativeHistoryGrainCount
