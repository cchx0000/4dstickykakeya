import Theorems.Thm_StickyKakeya4_native_actual_horizontal_grain_slice
import Theorems.Thm_StickyKakeya4_native_height_slope_coordinates
import Theorems.Thm_StickyKakeya4_native_height_residue_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000
noncomputable section
namespace NativeActualParentHeightChart
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeSpatialAngularGeometry
open NativeCompatibleNodeDirections NativeCompatibleAngularCandidates NativeDirectionRankDichotomy
open NativeHorizontalGrainSlice NativeActualHorizontalGrainSlice NativeParentHeightAlignment
open NativeParentGrainIncidenceCleanup NativeHeightSlopeCoordinates NativeHorizontalGraphCoordinates
open NativeProjectorCellChart
open scoped BigOperators Matrix.Norms.Elementwise

lemma nodeCut_image {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (B : Finset Index) (hB : B⊆E.image (fineNode D m)) :
    (nodeCut D m E B).image (fineNode D m)=B := by
  ext u
  simp only [mem_image,mem_nodeCut]
  constructor
  · rintro ⟨z,⟨_hz,hzu⟩,rfl⟩
    exact hzu
  · intro hu
    obtain ⟨z,hz,rfl⟩ := mem_image.mp (hB hu)
    exact ⟨z,⟨hz,hu⟩,rfl⟩

lemma nodeCut_nested {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (E : Finset (Fin n × Index)) (A B : Finset Index) (hBA : B⊆A) :
    nodeCut D m (nodeCut D m E A) B=nodeCut D m E B := by
  ext z
  simp only [mem_nodeCut]
  constructor
  · exact fun hz => ⟨hz.1.1,hz.2⟩
  · exact fun hz => ⟨⟨hz.1,hBA hz.2⟩,hz.2⟩

/-- Compose actual height alignment, one fixed graph chart, and mod-three
boundary protection. All selections cut whole original nodes, so the final
mixed fibers and raw vertex sets remain literal original fibers. -/
theorem select_actual_parent_height_chart {n J ell : ℕ} {D : FiniteScaleSource n}
    {eta a q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m : ℕ) (depth : Fin J → ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hm : m ≤ level) (hdepth : ∀j,depth j ≤ m) (hcontains : ∃j,depth j=m)
    (E2 E : Finset (Fin n × Index)) (S0 : Finset Index)
    (point : Index → Index) (tuple : Index → Fin ell → (Fin n × Index))
    (anchor : Index → Fin ell → Fin n)
    (Hsys : IsNodeDirectionSystem D a m E2 S0 q ell point tuple anchor)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hq : 0 < q)
    (hE : E⊆incidences original) (hEn : E.Nonempty) (hpoints : ∀z∈E,z.2∈S0)
    (p : Parent) (hparent : ∀z∈E,parentLabel D a (2^m) z.1=p) :
    let plane := fun u => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple u))
    let horizontal := fun u => sliceSpace (plane u)
    ∃A⊆E.image (fineNode D m),∃u0∈A,∃hP : horizontal u0≤heightKernel,
      ∃hd : Module.finrank ℝ (horizontal u0)=ell-1,
      ∃f : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ,
      ∃B⊆A,B.Nonempty ∧ (nodeCut D m E B).Nonempty ∧
        E.card ≤ (343^J*chartCount*3^J)*(nodeCut D m E B).card ∧
        (∀j u v,u∈A → v∈A →
          spatialAncestor m (depth j) u (3:Fin 4)=spatialAncestor m (depth j) v (3:Fin 4) →
          spatialAncestor m (depth j) u=spatialAncestor m (depth j) v) ∧
        (∀j u v,u∈B → v∈B → |u (3:Fin 4)-v (3:Fin 4)| < ((2^(m-depth j):ℕ):ℤ) →
          spatialAncestor m (depth j) u (3:Fin 4)=spatialAncestor m (depth j) v (3:Fin 4)) ∧
        (∀t,t∉A.image (fun u => u (3:Fin 4)) → f t=0) ∧ (∀t,‖f t‖ ≤ (1/4:ℝ)) ∧
        (∀u∈A,cell (horizontal u0)=cell (horizontal u)) ∧
        (∀u∈A,f (u (3:Fin 4))=nodeSlope (horizontal u0) hP ell hell hell4 hd
          (horizontal u) (show horizontal u≤heightKernel from inf_le_right)) ∧
        (∀u∈A,∀v : E4,v∈horizontal u ↔ ∃x : EuclideanSpace ℝ (Fin (ell-1)),
          ((domainBasis (horizontal u0) ell hd).repr.symm x:horizontal u0)+
            (((normalBasis (horizontal u0) hP ell hell hell4 hd).repr.symm
              (matrixVector (f (u (3:Fin 4))) x):normalSpace (horizontal u0)):E4)=v) ∧
        (∀u∈A,∀v∈A,∀epsilon : ℝ,0 ≤ epsilon →
          (∀x∈horizontal u,Metric.infDist x (horizontal v:Set E4) ≤ epsilon*‖x‖) →
          ‖f (u (3:Fin 4))-f (v (3:Fin 4))‖ ≤ 6*epsilon) ∧
        ∀c∈(nodeCut D m E B).image (mixedLabel D a m plane ell),
          mixedFiber D a m plane ell (nodeCut D m E B) c=mixedFiber D a m plane ell E c ∧
          ∀b,mixedVertices D a m b plane ell (nodeCut D m E B) c=mixedVertices D a m b plane ell E c := by
  intro plane horizontal
  obtain ⟨C,hCE,hCn,_hCcut,hCmass,hCalign⟩ := exists_height_aligned_nodes h original horiginal ha
    level m depth hdy hm hdepth E hE hEn p hparent
  have hRank : ∀u∈C,Module.finrank ℝ (horizontal u)=ell-1 := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := mem_image.mp (hCE hu)
    have hnode : fineNode D m z∈nodes D m S0 := mem_image_of_mem _ (hpoints z hz)
    exact (node_graph_direction Hsys hell hq _ hnode).1
  have hHorizontal : ∀u∈C,horizontal u≤heightKernel := fun _ _ => inf_le_right
  have hFineAlign : ∀u v,u∈C → v∈C → u (3:Fin 4)=v (3:Fin 4) → u=v := by
    obtain ⟨j,hj⟩ := hcontains
    intro u v hu hv he
    simpa only [hj,spatialAncestor_self] using hCalign j u v hu hv (by simpa only [hj,spatialAncestor_self] using he)
  obtain ⟨u0,hu0,A,hAC,hP,hd,f,hA,huA,hAmass,hzero,hnorm,hread,hgraph,hvariation⟩ :=
    exists_height_slope_chart C hCn (nodeWeight D m E) m ell hell hell4 horizontal hRank hHorizontal hFineAlign
  have hAE : A⊆E.image (fineNode D m) := hAC.trans hCE
  have hAcutn : (nodeCut D m E A).Nonempty := by
    have hh : ((nodeCut D m E A).image (fineNode D m)).Nonempty := by
      rw [nodeCut_image D m E A hAE]
      exact ⟨u0,huA⟩
    exact hh.of_image
  have hAmass' : (nodeCut D m E C).card ≤ chartCount*(nodeCut D m E A).card := by
    simpa only [SelfUniform.mass,←nodeCut_card D m E C,←nodeCut_card D m E A] using hAmass
  obtain ⟨B,hBAimage,hBn,hBcutn,hBmass,hresidue⟩ := NativeHeightResidueSelection.exists_residue_separated_node_cut
    D m depth (nodeCut D m E A) hAcutn
  have hBA : B⊆A := by simpa only [nodeCut_image D m E A hAE] using hBAimage
  rw [nodeCut_nested D m E A B hBA] at hBcutn hBmass
  have htotal : E.card ≤ (343^J*chartCount*3^J)*(nodeCut D m E B).card := by
    calc
      _ ≤ 343^J*(nodeCut D m E C).card := hCmass
      _ ≤ 343^J*(chartCount*(nodeCut D m E A).card) := Nat.mul_le_mul_left _ hAmass'
      _ ≤ 343^J*(chartCount*(3^J*(nodeCut D m E B).card)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hBmass)
      _ = _ := by ring
  refine ⟨A,hAE,u0,huA,hP,hd,f,B,hBA,hBn,hBcutn,htotal,?_,hresidue,hzero,hnorm,?_,hread,hgraph,hvariation,?_⟩
  · exact fun j u v hu hv => hCalign j u v (hAC hu) (hAC hv)
  · intro u hu
    rw [hA] at hu
    exact (mem_filter.mp hu).2.symm
  · intro c hc
    exact ⟨nodeCut_mixed_fiber_eq D a m plane ell E B c hc,
      fun b => nodeCut_mixed_vertices_eq D a m b plane ell E B c hc⟩

end NativeActualParentHeightChart
