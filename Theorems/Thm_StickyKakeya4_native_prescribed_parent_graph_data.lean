import Theorems.Thm_StickyKakeya4_native_complete_parent_profiles
import Theorems.Thm_StickyKakeya4_native_parent_height_graph_core
import Theorems.Thm_StickyKakeya4_native_height_metric_power

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativePrescribedParentGraphData
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeSpatialAngularGeometry
open NativeCompatibleNodeDirections NativeCompatibleAngularCandidates NativeDirectionRankDichotomy
open NativeHorizontalGrainSlice NativeParentHeightAlignment NativeParentGrainIncidenceCleanup
open NativeHeightSlopeCoordinates NativeHorizontalGraphCoordinates NativeProjectorCellChart
open NativeHeightMetricMenu NativeMiddleGrainParentBudget NativeParentHeightGraphCore
open NativeActualGrainHistory NativeQueriedVertexWeights NativeOriginalPacketReference
open NativeActualProjectedGrainCount NativeCombinedParentProfiles NativeCompleteParentProfiles
open NativeActivePhasePopulation NativePhaseHeightPopulation NativeFixedCompactKakeyaExponent
open RichDirectionalLayers WeightedRichDirectionalLayers NativeSourceParentGrainCleanup
open NativeOriginalCellChartGeometry NativeOriginalAngularTupleMenu
open NativeSquaredGrainQueries NativeFullCoarseShadow NativeMiddleWindowBalance NativeAllTwoScaleConfiguration
open scoped BigOperators Matrix.Norms.Elementwise

/-- The actual graph core data, with the raw-height matrix key retained explicitly. -/
def HasParentHeightCore {n ell : ℕ} (D : FiniteScaleSource n) (a q : ℝ)
    (m stop K : ℕ) (H : Finset (Fin n × Index))
    (tuple : Index → Fin ell → (Fin n × Index)) (p : Parent)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) : Prop :=
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
          ∀b,mixedVertices D a m b plane ell S c=mixedVertices D a m b plane ell H c

def HasCurveParentProfiles {n K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 E2 : Finset (Fin n × Index)) (a : ℝ) (level m : ℕ)
    (plane : Index → Submodule ℝ E4) (points : Finset Index) (q : ℝ) (ell Q2 F1 G Lgrain : ℕ)
    (lambda zeta tau seed c2 : ℝ) (depths : Fin K → ℕ)
    (stop Khalf : ℕ) (tuple : Index → Fin ell → (Fin n × Index)) (r epsilon : ℝ) : Prop :=
  let W := mass points (pointWeight E2)
  let theta := lambda*(W:ℝ)/(2*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ))
  let mu := theta*D.thickness^eta
  let retain := mu/rowConstant
  0 < theta ∧ 0 < mu ∧ 0 < retain ∧
    ∃H⊆cutEdges E2 points,H.Nonempty ∧ W ≤ 2*H.card ∧
      ∃p∈R.image (parentLabel D a (2^m)),(parentEdges D a (2^m) H p).Nonempty ∧
        mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤ D.thickness*(parentEdges D a (2^m) H p).card ∧
        (∀I⊆retained original R,retain*(parentEdges D a (2^m) I p).card ≤ (parentEdges D a (2^m) H p).card) ∧
        (∀x∈parentEdges D a (2^m) H p,
          lambda*D.thickness^(2*eta+3*zeta+7*tau)*(W:ℝ)*Lgrain <
            parentGrainConstant*transverseCost q ell*(Q2:ℝ)^2*(F1:ℝ)*G*E2.card*
              (mixedVertices D a m (phaseDepth m) plane ell (parentEdges D a (2^m) H p)
                (mixedLabel D a m plane ell x)).card) ∧
        (∀u,HasParentProfiles h R E1 E2 a level m (depths u) p retain lambda tau seed c2) ∧
        (∀u,
          let relative := (64/((2^(depths u):ℕ):ℝ))/(64/((2^m:ℕ):ℝ))
          let M := (NativeFiniteKakeyaCounts.multiplicity
            (fullSource h R a level (depths u) (parentEdges D a (2^m) H p))).toReal
          retain*D.thickness^(tau+seed/8+10*min (boundaryWindow tau) ((tau/16)/1000))*relative^(-extremalExponent) ≤ M ∧
            M ≤ D.thickness^(-(3*tau))*relative^(-extremalExponent)) ∧
        mu ≤ (43904*(64/((2^m:ℕ):ℝ)))*(heightLabels D a (64/((2^m:ℕ):ℝ)) (parentEdges D a (2^m) E2 p)).card ∧
        (64/((2^m:ℕ):ℝ))*(heightLabels D a (64/((2^m:ℕ):ℝ)) (parentEdges D a (2^m) E2 p)).card ≤ 10 ∧
        (∀f : ℕ,m ≤ f → f ≤ level →
          (mu*D.thickness^(2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3 ≤
            rowConstant*(activePhases D a f (parentEdges D a (2^m) E2 p)).card ∧
          ((activePhases D a f (parentEdges D a (2^m) E2 p)).card:ℝ) ≤
            D.thickness^(-2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3) ∧
          mu*D.thickness^(2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3 ≤
            (43904*(64/((2^m:ℕ):ℝ)))*
              (phaseHeightLabels D a (64/((2^m:ℕ):ℝ)) f (parentEdges D a (2^m) E2 p)).card) ∧
        plane=(fun u => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple u))) ∧
        512*metricConstant ((stop-6)/(2*Khalf)+1) (NativeSeparatedSpanControl.coefficientCost 2 q ell) ≤ r^(-2*epsilon) ∧
        ∃hell : 1 ≤ ell,∃hell4 : ell ≤ 4,
          HasParentHeightCore D a q m stop Khalf (parentEdges D a (2^m) H p) tuple p hell hell4


/-- Apply the actual whole-node graph constructor to the ALREADY chosen
parent. Hword is the retained trace of the original direction choice. -/
theorem attach_prescribed_parent_graph {n ell Kmenu : ℕ} {D : FiniteScaleSource n} {eta a q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E1 E2 : Finset (Fin n × Index)) (h2R : E2⊆retained original R)
    (level m stop Khalf : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hm : m ≤ level) (hs : 6 ≤ stop) (hHalf : 0 < Khalf) (hmid : m=middleDepth stop)
    (P : Finset (Index × List (Fin 3 → ℤ))) (hP : P⊆terminalFamily D a stop E2 q ell)
    (point : Index → Index) (tuple : Index → Fin ell → (Fin n × Index))
    (anchor : Index → Fin ell → Fin n)
    (Hsys : IsNodeDirectionSystem D a m E2 (P.image Prod.fst) q ell point tuple anchor)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hq : 0 < q)
    (Hword : ∀p∈P,angularTuple D a m (List.ofFn (tuple (spatialLabel D (2^m) p.1)))=
      projectWord stop m p.2)
    (HC : ∀j : Fin (Khalf+1),∀x y,x∈P → y∈P →
      spatialLabel D (2^(halfDepth Khalf stop j)) x.1=spatialLabel D (2^(halfDepth Khalf stop j)) y.1 →
      projectWord stop (halfDepth Khalf stop j) x.2=projectWord stop (halfDepth Khalf stop j) y.2)
    (points : Finset Index) (hpoints : points⊆P.image Prod.fst)
    (Q2 F1 G Lgrain : ℕ) (lambda zeta tau seed c2 r epsilon : ℝ) (depths : Fin Kmenu → ℕ)
    (hmetric : 512*metricConstant ((stop-6)/(2*Khalf)+1)
      (NativeSeparatedSpanControl.coefficientCost 2 q ell) ≤ r^(-2*epsilon))
    (H : HasCompleteParentProfiles h original R E1 E2 a level m
      (fun u => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple u)))
      points q ell Q2 F1 G Lgrain lambda zeta tau seed c2 depths) :
    HasCurveParentProfiles h original R E1 E2 a level m
      (fun u => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple u)))
      points q ell Q2 F1 G Lgrain lambda zeta tau seed c2 depths stop Khalf tuple r epsilon := by
  obtain ⟨ht,hmu,hretain,E,hEK,hEn,hhalf,p,hp,hEpn,hpop,href,hgrain,hprofiles,hcleaned,
    hheightL,hheightU,hdescendant⟩ := H
  have hEE2 : E⊆E2 := hEK.trans (cutEdges_subset E2 points)
  have hEp : parentEdges D a (2^m) E p⊆incidences original :=
    (filter_subset _ _).trans (hEE2.trans (h2R.trans (filter_subset _ _)))
  have hpointEp : ∀z∈parentEdges D a (2^m) E p,z.2∈P.image Prod.fst := by
    intro z hz
    exact hpoints (mem_filter.mp (hEK (mem_filter.mp hz).1)).2
  have hparent : ∀z∈parentEdges D a (2^m) E p,parentLabel D a (2^m) z.1=p :=
    fun z hz => (mem_filter.mp hz).2
  refine ⟨ht,hmu,hretain,E,hEK,hEn,hhalf,p,hp,hEpn,hpop,href,hgrain,hprofiles,hcleaned,
    hheightL,hheightU,hdescendant,rfl,hmetric,hell,hell4,?_⟩
  exact construct_parent_height_graph_core h original horiginal ha level m stop Khalf hdy hm hs hHalf hmid
    E2 (parentEdges D a (2^m) E p) P hP point tuple anchor Hsys hell hell4 hq Hword HC
    hEp hEpn hpointEp p hparent

/-- Forget only the additional graph data; all stored source/parent witnesses
and their reference profiles remain the very same objects. -/
theorem curve_parent_profiles_forget {n K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {original : Fin n → Finset Index}
    {R : Finset (Fin n)} {E1 E2 : Finset (Fin n × Index)} {a : ℝ} {level m : ℕ}
    {plane : Index → Submodule ℝ E4} {points : Finset Index} {q : ℝ} {ell Q2 F1 G Lgrain : ℕ}
    {lambda zeta tau seed c2 : ℝ} {depths : Fin K → ℕ}
    {stop Khalf : ℕ} {tuple : Index → Fin ell → (Fin n × Index)} {r epsilon : ℝ}
    (H : HasCurveParentProfiles h original R E1 E2 a level m plane points q ell Q2 F1 G Lgrain
      lambda zeta tau seed c2 depths stop Khalf tuple r epsilon) :
    HasCompleteParentProfiles h original R E1 E2 a level m plane points q ell Q2 F1 G Lgrain
      lambda zeta tau seed c2 depths := by
  obtain ⟨ht,hmu,hretain,E,hEK,hEn,hhalf,p,hp,hEpn,hpop,href,hgrain,hprofiles,hcleaned,
    hheightL,hheightU,hdescendant,_hplane,_hmetric,_hgraph⟩ := H
  exact ⟨ht,hmu,hretain,E,hEK,hEn,hhalf,p,hp,hEpn,hpop,href,hgrain,hprofiles,hcleaned,
    hheightL,hheightU,hdescendant⟩

end NativePrescribedParentGraphData
