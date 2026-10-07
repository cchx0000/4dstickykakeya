import Theorems.Thm_StickyKakeya4_native_parent_height_spatial_cells
import Theorems.Thm_StickyKakeya4_native_weighted_height_node_selection
import Theorems.Thm_StickyKakeya4_native_parent_grain_incidence_cleanup

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeParentHeightAlignment
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeSpatialAngularGeometry
open NativeParentHeightSpatialCells NativeCompatibleAngularCandidates
open NativeWeightedHeightNodeSelection NativeParentGrainIncidenceCleanup
open RichDirectionalLayers
open scoped BigOperators

/-- The spatial node is the raw label of the original microcell center. -/
def fineNode {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (z : Fin n × Index) : Index :=
  spatialLabel D (2^m) z.2

/-- Each node retains its original incidence count as its weight. -/
def nodeWeight {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (u : Index) : ℕ :=
  (E.filter (fun z => fineNode D m z=u)).card

def nodeCut {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (B : Finset Index) : Finset (Fin n × Index) :=
  cutByNodes E (fineNode D m) B

@[simp] lemma mem_nodeCut {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (B : Finset Index) (z : Fin n × Index) :
    z∈nodeCut D m E B ↔ z∈E ∧ fineNode D m z∈B := by
  simp only [nodeCut,mem_cutByNodes]

lemma nodeWeight_total {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) :
    (∑u∈E.image (fineNode D m),nodeWeight D m E u)=E.card :=
  (card_eq_sum_card_image (fineNode D m) E).symm

lemma nodeCut_card {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (B : Finset Index) :
    (nodeCut D m E B).card=∑u∈B,nodeWeight D m E u :=
  (sum_card_fiberwise_eq_card_filter E B (fineNode D m)).symm

lemma nodeCut_subset {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (B : Finset Index) : nodeCut D m E B⊆E :=
  filter_subset _ _

/-- Restricting whole fine nodes preserves all original incidences in a surviving node. -/
lemma nodeCut_saturated {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (B : Finset Index) (x y : Fin n × Index)
    (hx : x∈nodeCut D m E B) (hy : y∈E) (he : fineNode D m y=fineNode D m x) :
    y∈nodeCut D m E B := by
  apply (mem_nodeCut D m E B y).mpr
  exact ⟨hy,by simpa only [he] using ((mem_nodeCut D m E B x).mp hx).2⟩

/-- The actual geometric bound supplies the finite weighted selector. The
number of menu entries is fixed independently of the source; only their depths
are installed after the stopping depth is known. -/
theorem exists_height_aligned_nodes {n J : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m : ℕ) (depth : Fin J → ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hm : m ≤ level) (hdepth : ∀j,depth j ≤ m)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (hEn : E.Nonempty)
    (p : Parent) (hparent : ∀z∈E,parentLabel D a (2^m) z.1=p) :
    ∃B⊆E.image (fineNode D m), B.Nonempty ∧
      (nodeCut D m E B).Nonempty ∧ E.card ≤ 343^J*(nodeCut D m E B).card ∧
      ∀j u v,u∈B→v∈B→
        spatialAncestor m (depth j) u (3:Fin 4)=spatialAncestor m (depth j) v (3:Fin 4)→
        spatialAncestor m (depth j) u=spatialAncestor m (depth j) v := by
  have hcap : ∀j t,(((E.image (fineNode D m)).filter
      (fun u => spatialAncestor m (depth j) u (3:Fin 4)=t)).image
      (spatialAncestor m (depth j))).card ≤ 343 := by
    intro j t
    exact ancestor_height_spatial_count h original horiginal ha level m (depth j)
      hdy hm (hdepth j) E hE p hparent t
  have hpos : 0<∑u∈E.image (fineNode D m),nodeWeight D m E u := by
    rw [nodeWeight_total]
    exact card_pos.mpr hEn
  obtain ⟨B,hBN,hBn,hweight,halign⟩ := weighted_height_node_selection_nonempty
    (nodeWeight D m E) (E.image (fineNode D m))
    (fun j => spatialAncestor m (depth j))
    (fun j u => spatialAncestor m (depth j) u (3:Fin 4)) 343 hcap hpos
  have hcount : E.card ≤ 343^J*(nodeCut D m E B).card := by
    rw [nodeCut_card]
    simpa only [nodeWeight_total] using hweight
  have hcutn : (nodeCut D m E B).Nonempty := by
    apply card_pos.mp
    have hEc := card_pos.mpr hEn
    by_contra hh
    have hz : (nodeCut D m E B).card=0 := by omega
    rw [hz,mul_zero] at hcount
    omega
  exact ⟨B,hBN,hBn,hcutn,hcount,halign⟩

/-- The selected raw coarse node is a function of the raw coarse height. -/
def heightNode (B : Finset Index) (m depth : ℕ) (t : ℤ) : Index :=
  if H : ∃u∈B,spatialAncestor m depth u (3:Fin 4)=t then
    spatialAncestor m depth H.choose else 0

lemma heightNode_readback (B : Finset Index) (m depth : ℕ)
    (Halign : ∀u v,u∈B→v∈B→
      spatialAncestor m depth u (3:Fin 4)=spatialAncestor m depth v (3:Fin 4)→
      spatialAncestor m depth u=spatialAncestor m depth v)
    (u : Index) (hu : u∈B) :
    heightNode B m depth (spatialAncestor m depth u (3:Fin 4))=spatialAncestor m depth u := by
  have hex : ∃v∈B,spatialAncestor m depth v (3:Fin 4)=spatialAncestor m depth u (3:Fin 4) :=
    ⟨u,hu,rfl⟩
  rw [heightNode,dif_pos hex]
  exact Halign hex.choose u hex.choose_spec.1 hu hex.choose_spec.2

lemma heightNode_occupied (B : Finset Index) (m depth : ℕ) (t : ℤ)
    (ht : ∃u∈B,spatialAncestor m depth u (3:Fin 4)=t) :
    heightNode B m depth t∈B.image (spatialAncestor m depth) ∧
      heightNode B m depth t (3:Fin 4)=t := by
  rw [heightNode,dif_pos ht]
  exact ⟨mem_image_of_mem _ ht.choose_spec.1,ht.choose_spec.2⟩

lemma spatialAncestor_self (m : ℕ) (u : Index) : spatialAncestor m m u=u := by
  ext j
  simp only [spatialAncestor,Nat.sub_self,pow_zero,Nat.cast_one,Int.ediv_one]

/-- Include the fine depth itself in the menu to obtain a plane indexed by
fine height. Coarser entries alone do not give this conclusion. -/
lemma fine_heightNode_readback (B : Finset Index) (m : ℕ)
    (Halign : ∀u v,u∈B→v∈B→
      spatialAncestor m m u (3:Fin 4)=spatialAncestor m m v (3:Fin 4)→
      spatialAncestor m m u=spatialAncestor m m v)
    (u : Index) (hu : u∈B) : heightNode B m m (u (3:Fin 4))=u := by
  simpa only [spatialAncestor_self] using heightNode_readback B m m Halign u hu

lemma cut_heightNode_readback {n : ℕ} (D : FiniteScaleSource n) (m depth : ℕ)
    (hd : depth ≤ m) (E : Finset (Fin n × Index)) (B : Finset Index)
    (Halign : ∀u v,u∈B→v∈B→
      spatialAncestor m depth u (3:Fin 4)=spatialAncestor m depth v (3:Fin 4)→
      spatialAncestor m depth u=spatialAncestor m depth v)
    (z : Fin n × Index) (hz : z∈nodeCut D m E B) :
    heightNode B m depth (spatialLabel D (2^depth) z.2 (3:Fin 4))=
      spatialLabel D (2^depth) z.2 := by
  have hh := heightNode_readback B m depth Halign (fineNode D m z)
    ((mem_nodeCut D m E B z).mp hz).2
  simpa only [fineNode,spatialAncestor_label D hd z.2] using hh

lemma height_plane_readback {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (B : Finset Index) (P : Index → Submodule ℝ E4)
    (Halign : ∀u v,u∈B→v∈B→
      spatialAncestor m m u (3:Fin 4)=spatialAncestor m m v (3:Fin 4)→
      spatialAncestor m m u=spatialAncestor m m v)
    (z : Fin n × Index) (hz : z∈nodeCut D m E B) :
    P (heightNode B m m (spatialLabel D (2^m) z.2 (3:Fin 4)))=
      P (spatialLabel D (2^m) z.2) := by
  rw [cut_heightNode_readback D m m le_rfl E B Halign z hz]

/-- The actual mixed label contains the fine node, so every surviving mixed
fiber is the unchanged original fiber. -/
theorem nodeCut_mixed_fiber_eq {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (E : Finset (Fin n × Index)) (B : Finset Index)
    (c : Parent × (Index × Index))
    (hc : c∈(nodeCut D m E B).image (mixedLabel D a m P ell)) :
    mixedFiber D a m P ell (nodeCut D m E B) c=mixedFiber D a m P ell E c := by
  have hh := surviving_grain_label_fiber_eq E (mixedLabel D a m P ell) (fineNode D m) B
    (fun x y _hx _hy he => congrArg (fun c : Parent × (Index × Index) => c.2.1) he) hc
  dsimp only [mixedFiber,RichDirectionalLayers.classFiber,nodeCut]
  convert hh using 1
  all_goals congr

theorem nodeCut_mixed_vertices_eq {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ)
    (P : Index → Submodule ℝ E4) (ell : ℕ) (E : Finset (Fin n × Index)) (B : Finset Index)
    (c : Parent × (Index × Index))
    (hc : c∈(nodeCut D m E B).image (mixedLabel D a m P ell)) :
    mixedVertices D a m f P ell (nodeCut D m E B) c=mixedVertices D a m f P ell E c := by
  unfold mixedVertices
  rw [nodeCut_mixed_fiber_eq D a m P ell E B c hc]

end NativeParentHeightAlignment
