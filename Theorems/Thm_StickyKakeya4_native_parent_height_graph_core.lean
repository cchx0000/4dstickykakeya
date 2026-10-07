import Theorems.Thm_StickyKakeya4_native_actual_parent_height_chart
import Theorems.Thm_StickyKakeya4_native_actual_height_metric_variation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeParentHeightGraphCore
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeSpatialAngularGeometry
open NativeCompatibleNodeDirections NativeCompatibleAngularCandidates NativeDirectionRankDichotomy
open NativeHorizontalGrainSlice NativeActualHorizontalGrainSlice NativeParentHeightAlignment
open NativeParentGrainIncidenceCleanup NativeHeightSlopeCoordinates NativeHorizontalGraphCoordinates
open NativeProjectorCellChart NativeActualParentHeightChart NativeHeightMetricMenu NativeMiddleGrainParentBudget
open NativeActualHeightSlopeVariation NativeCoarseHeightSlopeVariation NativeOriginalAngularTupleMenu
open scoped BigOperators Matrix.Norms.Elementwise

def selectionCost (K : ℕ) : ℕ := 343^(K+1)*chartCount*3^(K+1)

/-- Instantiate the three actual whole-node selections on the SAME cleaned
parent H. The first half of the even grain menu supplies all interpolation
scales. The returned matrix function and reference plane are unchanged by
the last residue cut, and every surviving original grain remains intact. -/
theorem construct_parent_height_graph_core {n ell : ℕ} {D : FiniteScaleSource n}
    {eta a q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m stop K : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hm : m ≤ level) (hs : 6 ≤ stop) (hK : 0 < K) (hf : m=middleDepth stop)
    (E2 H : Finset (Fin n × Index)) (P : Finset (Index × List (Fin 3 → ℤ)))
    (hP : P⊆terminalFamily D a stop E2 q ell)
    (point : Index → Index) (tuple : Index → Fin ell → (Fin n × Index))
    (anchor : Index → Fin ell → Fin n)
    (Hsys : IsNodeDirectionSystem D a m E2 (P.image Prod.fst) q ell point tuple anchor)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hq : 0 < q)
    (Hword : ∀p∈P,angularTuple D a m (List.ofFn (tuple (spatialLabel D (2^m) p.1)))=
      projectWord stop m p.2)
    (HC : ∀j p t,p∈P→t∈P→
      spatialLabel D (2^(halfDepth K stop j)) p.1=spatialLabel D (2^(halfDepth K stop j)) t.1→
      projectWord stop (halfDepth K stop j) p.2=projectWord stop (halfDepth K stop j) t.2)
    (hH : H⊆incidences original) (hHn : H.Nonempty) (hpoints : ∀z∈H,z.2∈P.image Prod.fst)
    (p : Parent) (hparent : ∀z∈H,parentLabel D a (2^m) z.1=p) :
    let plane := fun u => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple u))
    let horizontal := fun u => sliceSpace (plane u)
    let L := metricConstant ((stop-6)/(2*K)+1) (NativeSeparatedSpanControl.coefficientCost 2 q ell)
    ∃A⊆H.image (fineNode D m),∃u0∈A,∃hP0 : horizontal u0≤heightKernel,
      ∃hd : Module.finrank ℝ (horizontal u0)=ell-1,
      ∃f : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ,
      ∃B⊆A,B.Nonempty ∧ ∃S : Finset (Fin n × Index),
        S=nodeCut D m H B ∧ S⊆H ∧ S.Nonempty ∧ S.image (fineNode D m)=B ∧
        H.card ≤ selectionCost K*S.card ∧
        (∀z∈S,parentLabel D a (2^m) z.1=p) ∧
        (∀j u v,u∈A→v∈A→
          spatialAncestor m (halfDepth K stop j) u (3:Fin 4)=spatialAncestor m (halfDepth K stop j) v (3:Fin 4)→
          spatialAncestor m (halfDepth K stop j) u=spatialAncestor m (halfDepth K stop j) v) ∧
        (∀j u v,u∈B→v∈B→|u (3:Fin 4)-v (3:Fin 4)| < ((2^(m-halfDepth K stop j):ℕ):ℤ)→
          spatialAncestor m (halfDepth K stop j) u (3:Fin 4)=spatialAncestor m (halfDepth K stop j) v (3:Fin 4)) ∧
        (∀t,t∉A.image (fun u => u (3:Fin 4))→f t=0) ∧ (∀t,‖f t‖ ≤ (1/4:ℝ)) ∧
        (∀u∈A,cell (horizontal u0)=cell (horizontal u)) ∧
        (∀u∈A,f (u (3:Fin 4))=nodeSlope (horizontal u0) hP0 ell hell hell4 hd
          (horizontal u) (show horizontal u≤heightKernel from inf_le_right)) ∧
        (∀u∈A,∀v : E4,v∈horizontal u ↔ ∃x : EuclideanSpace ℝ (Fin (ell-1)),
          ((domainBasis (horizontal u0) ell hd).repr.symm x:horizontal u0)+
            (((normalBasis (horizontal u0) hP0 ell hell hell4 hd).repr.symm
              (matrixVector (f (u (3:Fin 4))) x):normalSpace (horizontal u0)):E4)=v) ∧
        (∀u∈B,∀v∈B,
          (‖f (u (3:Fin 4))-f (v (3:Fin 4))‖ ≤ L*
            |rawHeightCoordinate m (u (3:Fin 4))-rawHeightCoordinate m (v (3:Fin 4))|) ∧
          ∀shift : ℝ,‖f (u (3:Fin 4))-f (v (3:Fin 4))‖ ≤ (512*L)*
            |chartHeightCoordinate m shift (u (3:Fin 4))-chartHeightCoordinate m shift (v (3:Fin 4))|) ∧
        ∀c∈S.image (mixedLabel D a m plane ell),
          mixedFiber D a m plane ell S c=mixedFiber D a m plane ell H c ∧
          ∀b,mixedVertices D a m b plane ell S c=mixedVertices D a m b plane ell H c := by
  intro plane horizontal L
  have hfs : m ≤ stop := by rw [hf]; exact (middle_depth_bounds stop hs).2.1
  have hdepth : ∀j,halfDepth K stop j ≤ m := by
    intro j
    rw [hf]
    exact halfDepth_le_middle K stop hK hs j
  have hlast : halfDepth K stop (Fin.last K)=m := (halfDepth_last K stop hK hs).trans hf.symm
  obtain ⟨A,hAH,u0,huA,hP0,hd,f,B,hBA,hBn,hSn,hmass,hAlign,hClose,hzero,hnorm,hcell,hread,hgraph,_hconditional,hfiber⟩ :=
    select_actual_parent_height_chart h original horiginal ha level m (halfDepth K stop) hdy hm hdepth
      ⟨Fin.last K,hlast⟩ E2 H (P.image Prod.fst) point tuple anchor Hsys hell hell4 hq hH hHn hpoints p hparent
  let S := nodeCut D m H B
  have hSH : S⊆H := nodeCut_subset D m H B
  have hBE : B⊆H.image (fineNode D m) := hBA.trans hAH
  have hANodes : A⊆nodes D m (P.image Prod.fst) := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := mem_image.mp (hAH hu)
    exact mem_image_of_mem _ (hpoints z hz)
  have hmetric : ∀u∈B,∀v∈B,
      ‖f (u (3:Fin 4))-f (v (3:Fin 4))‖ ≤ L*
        |rawHeightCoordinate m (u (3:Fin 4))-rawHeightCoordinate m (v (3:Fin 4))| := by
    intro u hu v hv
    apply metric_from_menu f (u (3:Fin 4)) (v (3:Fin 4)) m K ((stop-6)/(2*K)+1) hK
      (halfDepth K stop) (halfDepth_zero K stop hs) hlast hdepth (halfDepth_mono K stop)
      (halfDepth_gap K stop hK hs) (NativeSeparatedSpanControl.coefficientCost 2 q ell)
      (NativeSeparatedSpanControl.coefficientCost_nonneg (by norm_num) hq ell) (hnorm _) (hnorm _)
    intro j hj
    have hclose : |u (3:Fin 4)-v (3:Fin 4)| < ((2^(m-halfDepth K stop j):ℕ):ℤ) := by
      have hh : ((u (3:Fin 4)-v (3:Fin 4)).natAbs:ℤ)<((2^(m-halfDepth K stop j):ℕ):ℤ) := by exact_mod_cast hj
      simpa only [Int.natCast_natAbs] using hh
    have hheight := hClose j u v hu hv hclose
    have hancestor := hAlign j u v (hBA hu) (hBA hv) hheight
    have hword := same_ancestor_installed_word D a stop m (halfDepth K stop j) hfs (hdepth j)
      E2 q P hP tuple Hword (HC j) u v (hANodes (hBA hu)) (hANodes (hBA hv)) hancestor
    rw [hread u (hBA hu),hread v (hBA hv)]
    exact matching_node_matrix_variation h hq hell hell4 Hsys (horizontal u0) hP0 hd
      (halfDepth K stop j) u v (hANodes (hBA hu)) (hANodes (hBA hv))
      (hcell u (hBA hu)) (hcell v (hBA hv)) hword
  refine ⟨A,hAH,u0,huA,hP0,hd,f,B,hBA,hBn,S,rfl,hSH,hSn,nodeCut_image D m H B hBE,
    hmass,?_,hAlign,hClose,hzero,hnorm,hcell,hread,hgraph,?_,hfiber⟩
  · exact fun z hz => hparent z (hSH hz)
  · intro u hu v hv
    refine ⟨hmetric u hu v hv,?_⟩
    intro shift
    exact metric_from_menu_chart f (u (3:Fin 4)) (v (3:Fin 4)) m ((stop-6)/(2*K)+1)
      (NativeSeparatedSpanControl.coefficientCost 2 q ell) shift (hmetric u hu v hv)

end NativeParentHeightGraphCore
