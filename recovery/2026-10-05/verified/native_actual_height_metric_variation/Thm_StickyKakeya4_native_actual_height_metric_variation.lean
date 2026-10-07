import Theorems.Thm_StickyKakeya4_native_height_metric_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeActualHeightMetricVariation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeSpatialAngularGeometry
open NativeDirectionRankDichotomy NativeOriginalAngularTupleMenu NativeCompatibleAngularCandidates
open NativeCompatibleNodeDirections NativeActualHeightSlopeVariation NativeCoarseHeightSlopeVariation
open NativeHorizontalGrainSlice NativeSeparatedSpanControl NativeProjectorCellChart
open NativeHorizontalGraphCoordinates NativeHeightSlopeCoordinates NativeHeightResidueSelection
open NativeHeightMetricMenu NativeMiddleGrainParentBudget
open scoped BigOperators Matrix.Norms.Elementwise

/-- Metric variation from the literal retained node system, original tuple
compatibility, installed height alignment and actual modulo-three selection.
Close selected heights are proved to share the needed ancestor. -/
theorem actual_metric_variation {n ell fine J : ℕ} {D : FiniteScaleSource n} {eta a q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hell : 0 < ell) (hell4 : ell  ≤  4)
    (stop : ℕ) (hfs : fine  ≤  stop) (hJ : 0 < J)
    (depth : Fin (J+1) → ℕ) (hzero : depth 0=6) (hlast : depth (Fin.last J)=fine)
    (hdepth : ∀j,depth j ≤ fine) (hmono : Monotone depth)
    (G : ℕ) (hgap : ∀i : Fin J,depth i.succ-depth i.castSucc ≤ G)
    (E : Finset (Fin n × Index)) (P : Finset (Index × List (Fin 3 → ℤ)))
    (hP : P⊆terminalFamily D a stop E q ell)
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a fine E (P.image Prod.fst) q ell point tuple anchor)
    (Hword : ∀p∈P,angularTuple D a fine (List.ofFn (tuple (spatialLabel D (2^fine) p.1)))=
      projectWord stop fine p.2)
    (HC : ∀j p t,p∈P→t∈P→spatialLabel D (2^(depth j)) p.1=spatialLabel D (2^(depth j)) t.1→
      projectWord stop (depth j) p.2=projectWord stop (depth j) t.2)
    (B : Finset Index) (hB : B⊆nodes D fine (P.image Prod.fst))
    (Hfine : ∀u v,u∈B→v∈B→u (3:Fin 4)=v (3:Fin 4)→u=v)
    (Hcoarse : ∀j u v,u∈B→v∈B→spatialAncestor fine (depth j) u (3:Fin 4)=spatialAncestor fine (depth j) v (3:Fin 4)→
      spatialAncestor fine (depth j) u=spatialAncestor fine (depth j) v)
    (Hresidue : ∀j u v,u∈B→v∈B→spatialAncestor fine (depth j) u (3:Fin 4)%3=
      spatialAncestor fine (depth j) v (3:Fin 4)%3)
    (P0 : Submodule ℝ E4) (hP0 : P0 ≤ heightKernel) (hd0 : Module.finrank ℝ P0=ell-1)
    (u v : Index) (hu : u∈B) (hv : v∈B)
    (hcellu : cell P0=cell (horizontalPlane D tuple u)) (hcellv : cell P0=cell (horizontalPlane D tuple v)) :
    let plane := horizontalPlane D tuple
    let hplane : ∀u∈B,plane u ≤ heightKernel := fun u _ => horizontalPlane_le D tuple u
    let F := heightSlope B fine P0 hP0 ell hell hell4 hd0 plane hplane
    ‖F (u (3:Fin 4))-F (v (3:Fin 4))‖  ≤  metricConstant G (coefficientCost 2 q ell)*
      |rawHeightCoordinate fine (u (3:Fin 4))-rawHeightCoordinate fine (v (3:Fin 4))| := by
  intro plane hplane F
  apply metric_from_menu F (u (3:Fin 4)) (v (3:Fin 4)) fine J G hJ depth hzero hlast hdepth hmono hgap
    (coefficientCost 2 q ell) (coefficientCost_nonneg (by norm_num) hq ell)
    (heightSlope_norm B fine P0 hP0 ell hell hell4 hd0 plane hplane _)
    (heightSlope_norm B fine P0 hP0 ell hell hell4 hd0 plane hplane _)
  intro j hj
  have hclose : |u (3:Fin 4)-v (3:Fin 4)| < ((2^(fine-depth j):ℕ):ℤ) := by
    have hh : ((u (3:Fin 4)-v (3:Fin 4)).natAbs:ℤ)<((2^(fine-depth j):ℕ):ℤ) := by exact_mod_cast hj
    simpa only [Int.natCast_natAbs] using hh
  have hheight := selected_close_heights_same_ancestor (Hresidue j u v hu hv) hclose
  exact same_coarse_height_slope_variation h hq hell hell4 stop (depth j) hfs (hdepth j)
    E P hP H Hword (HC j) B hB Hfine (Hcoarse j) P0 hP0 hd0 u v hu hv hcellu hcellv hheight

/-- The actual even grain schedule supplies every menu bound. The factorG
is computed from stop and the grain count fixed before tau. Both raw-grid
and normalized translated-time distances are returned with their exact512 conversion. -/
theorem actual_half_metric_variation {n ell fine K : ℕ} {D : FiniteScaleSource n} {eta a q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hell : 0 < ell) (hell4 : ell  ≤  4)
    (stop : ℕ) (hs : 6  ≤  stop) (hK : 0 < K) (hf : fine=middleDepth stop)
    (E : Finset (Fin n × Index)) (P : Finset (Index × List (Fin 3 → ℤ)))
    (hP : P⊆terminalFamily D a stop E q ell)
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a fine E (P.image Prod.fst) q ell point tuple anchor)
    (Hword : ∀p∈P,angularTuple D a fine (List.ofFn (tuple (spatialLabel D (2^fine) p.1)))=
      projectWord stop fine p.2)
    (HC : ∀j p t,p∈P→t∈P→spatialLabel D (2^(halfDepth K stop j)) p.1=spatialLabel D (2^(halfDepth K stop j)) t.1→
      projectWord stop (halfDepth K stop j) p.2=projectWord stop (halfDepth K stop j) t.2)
    (B : Finset Index) (hB : B⊆nodes D fine (P.image Prod.fst))
    (Hfine : ∀u v,u∈B→v∈B→u (3:Fin 4)=v (3:Fin 4)→u=v)
    (Hcoarse : ∀j u v,u∈B→v∈B→spatialAncestor fine (halfDepth K stop j) u (3:Fin 4)=spatialAncestor fine (halfDepth K stop j) v (3:Fin 4)→
      spatialAncestor fine (halfDepth K stop j) u=spatialAncestor fine (halfDepth K stop j) v)
    (Hresidue : ∀j u v,u∈B→v∈B→spatialAncestor fine (halfDepth K stop j) u (3:Fin 4)%3=
      spatialAncestor fine (halfDepth K stop j) v (3:Fin 4)%3)
    (P0 : Submodule ℝ E4) (hP0 : P0 ≤ heightKernel) (hd0 : Module.finrank ℝ P0=ell-1)
    (u v : Index) (hu : u∈B) (hv : v∈B)
    (hcellu : cell P0=cell (horizontalPlane D tuple u)) (hcellv : cell P0=cell (horizontalPlane D tuple v)) :
    let plane := horizontalPlane D tuple
    let hplane : ∀u∈B,plane u ≤ heightKernel := fun u _ => horizontalPlane_le D tuple u
    let F := heightSlope B fine P0 hP0 ell hell hell4 hd0 plane hplane
    let L := metricConstant ((stop-6)/(2*K)+1) (coefficientCost 2 q ell)
    (‖F (u (3:Fin 4))-F (v (3:Fin 4))‖  ≤  L*
      |rawHeightCoordinate fine (u (3:Fin 4))-rawHeightCoordinate fine (v (3:Fin 4))|) ∧
    ∀shift : ℝ,‖F (u (3:Fin 4))-F (v (3:Fin 4))‖  ≤  (512*L)*
      |chartHeightCoordinate fine shift (u (3:Fin 4))-chartHeightCoordinate fine shift (v (3:Fin 4))| := by
  intro plane hplane F L
  have hfs : fine ≤ stop := by rw [hf]; exact (middle_depth_bounds stop hs).2.1
  have hlast : halfDepth K stop (Fin.last K)=fine := (halfDepth_last K stop hK hs).trans hf.symm
  have hdepth : ∀j,halfDepth K stop j ≤ fine := by intro j; rw [hf]; exact halfDepth_le_middle K stop hK hs j
  have hraw := actual_metric_variation h hq hell hell4 stop hfs hK (halfDepth K stop)
    (halfDepth_zero K stop hs) hlast hdepth (halfDepth_mono K stop) ((stop-6)/(2*K)+1)
    (halfDepth_gap K stop hK hs) E P hP H Hword HC B hB Hfine Hcoarse Hresidue P0 hP0 hd0
    u v hu hv hcellu hcellv
  refine ⟨hraw,?_⟩
  intro shift
  exact metric_from_menu_chart F (u (3:Fin 4)) (v (3:Fin 4)) fine ((stop-6)/(2*K)+1)
    (coefficientCost 2 q ell) shift hraw

end NativeActualHeightMetricVariation
