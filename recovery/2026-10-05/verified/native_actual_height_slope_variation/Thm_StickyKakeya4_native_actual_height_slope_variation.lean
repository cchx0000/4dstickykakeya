import Theorems.Thm_StickyKakeya4_native_height_slope_coordinates
import Theorems.Thm_StickyKakeya4_native_compatible_plane_variation
import Theorems.Thm_StickyKakeya4_native_actual_horizontal_grain_slice

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeActualHeightSlopeVariation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeSpatialAngularGeometry
open NativeDirectionRankDichotomy NativeIncidentRankSelection NativeOriginalAngularTupleMenu
open NativeCompatibleNodeDirections NativeCompatiblePlaneVariation NativeActualHorizontalGrainSlice
open NativeHorizontalGrainSlice NativeSeparatedSpanControl NativeProjectorCellChart
open NativeHorizontalGraphCoordinates NativeHeightSlopeCoordinates
open scoped BigOperators Matrix.Norms.Elementwise

def horizontalPlane {n ell : ℕ} (D : FiniteScaleSource n)
    (tuple : Index → Fin ell → (Fin n × Index)) (u : Index) : Submodule ℝ E4 :=
  sliceSpace (spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple u)))

lemma horizontalPlane_le {n ell : ℕ} (D : FiniteScaleSource n)
    (tuple : Index → Fin ell → (Fin n × Index)) (u : Index) : horizontalPlane D tuple u≤heightKernel := inf_le_right

/-- The actual matching original words give horizontal plane variation.
The full separated-chain coefficient cost is preserved. -/
theorem matching_node_horizontal_gap {n ell f : ℕ} {D : FiniteScaleSource n} {eta a q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hell : 0 < ell)
    {E : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a f E S q ell point tuple anchor)
    (m : ℕ) (u v : Index) (hu : u∈nodes D f S) (hv : v∈nodes D f S)
    (hword : angularTuple D a m (List.ofFn (tuple u))=angularTuple D a m (List.ofFn (tuple v))) :
    ∀w∈horizontalPlane D tuple v,
      Metric.infDist w (horizontalPlane D tuple u:Set E4) ≤
        (12/((2^m:ℕ):ℝ))*coefficientCost 2 q ell*‖w‖ := by
  intro w hw
  have hspan := matching_word_span_variation h a m (List.ofFn (tuple u)) (List.ofFn (tuple v))
    hword (pointSet E (point v)) q hq ell (H.1 v hv).2.2.1 w hw.1
  obtain ⟨_hd,d,hdP,hdheight,hdnorm⟩ := node_graph_direction H hell hq u hu
  have hslice := near_horizontal_slice _ hdP hdheight hdnorm hspan
  have hwheight : w (3:Fin 4)=0 := hw.2
  have hremove : removeHeight d w=w := by simp only [removeHeight,hwheight,zero_smul,sub_zero]
  rw [hremove] at hslice
  exact hslice.trans_eq (by ring)

/-- Matrix variation is read directly from the original chains and their
matching angular words, not from an assumed plane-gap certificate. -/
theorem matching_node_matrix_variation {n ell f : ℕ} {D : FiniteScaleSource n} {eta a q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hell : 0 < ell) (hell4 : ell ≤ 4)
    {E : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a f E S q ell point tuple anchor)
    (P0 : Submodule ℝ E4) (hP0 : P0≤heightKernel) (hd0 : Module.finrank ℝ P0=ell-1)
    (m : ℕ) (u v : Index) (hu : u∈nodes D f S) (hv : v∈nodes D f S)
    (hcellu : cell P0=cell (horizontalPlane D tuple u)) (hcellv : cell P0=cell (horizontalPlane D tuple v))
    (hword : angularTuple D a m (List.ofFn (tuple u))=angularTuple D a m (List.ofFn (tuple v))) :
    ‖nodeSlope P0 hP0 ell hell hell4 hd0 (horizontalPlane D tuple u) (horizontalPlane_le D tuple u)-
      nodeSlope P0 hP0 ell hell hell4 hd0 (horizontalPlane D tuple v) (horizontalPlane_le D tuple v)‖ ≤
        (72/((2^m:ℕ):ℝ))*coefficientCost 2 q ell := by
  have hdu := (node_graph_direction H hell hq u hu).1
  have hdv := (node_graph_direction H hell hq v hv).1
  have hgap := matching_node_horizontal_gap h hq hell H m v u hv hu hword.symm
  have hC := coefficientCost_nonneg (by norm_num : (0:ℝ)≤2) hq ell
  have hm := nodeSlope_variation P0 hP0 ell hell hell4 hd0 (horizontalPlane D tuple u)
    (horizontalPlane D tuple v) (horizontalPlane_le D tuple u) (horizontalPlane_le D tuple v)
    (hd0.trans hdu.symm) hcellu (hd0.trans hdv.symm) hcellv
    ((12/((2^m:ℕ):ℝ))*coefficientCost 2 q ell) (by positivity) hgap
  exact hm.trans_eq (by ring)

/-- The genuine function of raw height inherits the original q-dependent
variation at every installed common angular scale. -/
theorem matching_height_slope_variation {n ell f : ℕ} {D : FiniteScaleSource n} {eta a q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hell : 0 < ell) (hell4 : ell ≤ 4)
    {E : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a f E S q ell point tuple anchor)
    (B : Finset Index) (hB : B⊆nodes D f S)
    (Halign : ∀u v,u∈B→v∈B→u (3:Fin 4)=v (3:Fin 4)→u=v)
    (P0 : Submodule ℝ E4) (hP0 : P0≤heightKernel) (hd0 : Module.finrank ℝ P0=ell-1)
    (m : ℕ) (u v : Index) (hu : u∈B) (hv : v∈B)
    (hcellu : cell P0=cell (horizontalPlane D tuple u)) (hcellv : cell P0=cell (horizontalPlane D tuple v))
    (hword : angularTuple D a m (List.ofFn (tuple u))=angularTuple D a m (List.ofFn (tuple v))) :
    let plane := horizontalPlane D tuple
    let hplane : ∀u∈B,plane u≤heightKernel := fun u _ => horizontalPlane_le D tuple u
    let F := heightSlope B f P0 hP0 ell hell hell4 hd0 plane hplane
    ‖F (u (3:Fin 4))-F (v (3:Fin 4))‖ ≤ (72/((2^m:ℕ):ℝ))*coefficientCost 2 q ell := by
  intro plane hplane F
  dsimp only [F]
  rw [heightSlope_readback B f Halign P0 hP0 ell hell hell4 hd0 plane hplane u hu (hplane u hu),
    heightSlope_readback B f Halign P0 hP0 ell hell hell4 hd0 plane hplane v hv (hplane v hv)]
  exact matching_node_matrix_variation h hq hell hell4 H P0 hP0 hd0 m u v
    (hB hu) (hB hv) hcellu hcellv hword

end NativeActualHeightSlopeVariation
