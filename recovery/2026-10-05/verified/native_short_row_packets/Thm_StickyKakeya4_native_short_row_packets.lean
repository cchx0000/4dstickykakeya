import Theorems.Thm_StickyKakeya4_native_same_fine_parent_packet
import Theorems.Thm_StickyKakeya4_native_coarse_shading_uniformity
import Theorems.Thm_StickyKakeya4_native_spatial_angular_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeShortRowPackets
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeOriginalParentPhysicalData
open NativeOriginalPaddedCells NativeCoarseShadingCapacity NativeCoarseDyadicShading
open NativeCoarseShadingUniformity NativeSpatialAngularGeometry NativeDirectionRankDichotomy

/-- The literal retained old incidences in the anchor's occupied short shadow
cell and fine phase-parent. The representative is the same in both query maps. -/
def shortEdges {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level p m : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (anchor : Fin n × Index) :
    Finset (Fin n × Index) :=
  E.filter (fun z => fixedPair D a level p m rep z=fixedPair D a level p m rep anchor)

/-- The literal original microcell union of the retained short-row edges. -/
def shortCells {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level p m : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (anchor : Fin n × Index) :
    Finset Index := (shortEdges D a level p m rep E anchor).image Prod.snd

/-- Actual spatial vertices have width 64/2^p in ORIGINAL coordinates.
No original-cell ancestor is identified with a projected shadow cell. -/
def shortVertices {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level p m : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (anchor : Fin n × Index) :
    Finset Index :=
  (shortEdges D a level p m rep E anchor).image (fun z => spatialLabel D (2^p) z.2)

/-- Full ORIGINAL point fibers in the occupied physical vertices. This set
may contain other old tubes; the whole-cube packet theorem controls them. -/
def shortVertexClosure {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level p m : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (anchor : Fin n × Index) :
    Finset Index :=
  (E.image Prod.snd).filter (fun k => spatialLabel D (2^p) k∈shortVertices D a level p m rep E anchor)

lemma shortVertices_eq_cells_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (level p m : ℕ) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (anchor : Fin n × Index) :
    shortVertices D a level p m rep E anchor=
      (shortCells D a level p m rep E anchor).image (spatialLabel D (2^p)) := by
  simp only [shortVertices,shortCells,image_image,Function.comp_def]

/-- Exact readback: the fine projected image of this actual edge union is
the existing short-row child set used by the density theorem. -/
theorem projected_image_eq_rowChildren {n : ℕ} {D : FiniteScaleSource n} (a : ℝ)
    (level p m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmp : m ≤ p) (hpL : p ≤ level)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (anchor : Fin n × Index) :
    (shortEdges D a level p m rep E anchor).image
      (fun z => (fixedPair D a level p p rep z).2)=
      rowChildren D a level p m rep E (parentLabel D a (2^p) anchor.1)
        (fixedPair D a level p m rep anchor).2 := by
  ext r
  constructor
  · intro hr
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hr
    obtain ⟨hz,he⟩ := mem_filter.mp hz
    have hpz := congrArg Prod.fst he
    refine mem_filter.mpr ⟨?_,?_⟩
    · apply (mem_rowCells D a level p p rep E _ _).mpr
      exact mem_image.mpr ⟨z,hz,Prod.ext hpz rfl⟩
    · have hh := congrArg Prod.snd (fixedPair_ancestor a level p m hdy hmp hpL rep z)
      exact hh.trans (congrArg Prod.snd he)
  · intro hr
    obtain ⟨hr,hancestor⟩ := mem_filter.mp hr
    obtain ⟨z,hz,hzr⟩ := mem_image.mp ((mem_rowCells D a level p p rep E _ _).mp hr)
    have hpz := congrArg Prod.fst hzr
    refine mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,?_⟩,congrArg Prod.snd hzr⟩
    apply Prod.ext
    · exact hpz
    · have hh := congrArg Prod.snd (fixedPair_ancestor a level p m hdy hmp hpL rep z)
      exact hh.symm.trans ((congrArg (cellAncestor p m) (congrArg Prod.snd hzr)).trans hancestor)

/-- A common projected short cell has original height diameter 256 times
the physical scale 64/2^m. This is the exact chart contraction factor. -/
theorem projected_short_height {n : ℕ} {D : FiniteScaleSource n} (a : ℝ)
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmL : m ≤ level)
    (i j : Fin n) (k l : Index)
    (he : projectedLabel D a (block level m) i k=projectedLabel D a (block level m) j l) :
    |cellCenter (mesh D) k (3:Fin 4)-cellCenter (mesh D) l (3:Fin 4)| ≤
      256*(64/((2^m:ℕ):ℝ)) := by
  have hw : 0 < (block level m:ℝ)*D.thickness/128 := by
    rw [block_mesh hdy hmL]
    positivity
  have hh := same_cell_coordinate_close hw (frontPoint D a (0,0) i k)
    (frontPoint D a (0,0) j l) he (3:Fin 4)
  have heq : frontPoint D a (0,0) i k (3:Fin 4)-frontPoint D a (0,0) j l (3:Fin 4)=
      (cellCenter (mesh D) k (3:Fin 4)-cellCenter (mesh D) l (3:Fin 4))/512 := by
    rw [frontPoint_height,frontPoint_height,←sub_div,oldTime_sub]
    ring
  rw [heq,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512),block_mesh hdy hmL] at hh
  have hh' := (div_le_iff₀ (by norm_num : (0:ℝ)<512)).mp hh
  calc
    _ ≤ (32/((2^m:ℕ):ℝ))*512 := hh'
    _ = _ := by ring

/-- Membership in the literal union supplies the original retained edge,
its fine-parent equality, and its actual original height window. -/
theorem short_member_readback {n : ℕ} {D : FiniteScaleSource n} (a : ℝ)
    (level p m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmL : m ≤ level)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (anchor z : Fin n × Index)
    (hz : z∈shortEdges D a level p m rep E anchor) :
    z∈E ∧ parentLabel D a (2^p) z.1=parentLabel D a (2^p) anchor.1 ∧
      |cellCenter (mesh D) z.2 (3:Fin 4)-cellCenter (mesh D) anchor.2 (3:Fin 4)| ≤
        256*(64/((2^m:ℕ):ℝ)) := by
  obtain ⟨hz,he⟩ := mem_filter.mp hz
  exact ⟨hz,congrArg Prod.fst he,
    projected_short_height a level m hdy hmL _ _ _ _ (congrArg Prod.snd he)⟩

/-- The genuine original cell of every member of the short-row union lies
in the squared-scale packet of the matching original angular witness. -/
theorem short_member_packet {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level p m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmL : m ≤ level)
    (hscale : D.thickness ≤ (64/((2^m:ℕ):ℝ))^2)
    (hparentScale : 1/((2^p:ℕ):ℝ) ≤ (64/((2^m:ℕ):ℝ))^2)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (anchor : Fin n × Index) (hanchor : anchor∈E) (j : Fin n)
    (hangular : (parentLabel D a (2^m) anchor.1).1=(parentLabel D a (2^m) j).1)
    (z : Fin n × Index) (hz : z∈shortEdges D a level p m rep E anchor) :
    Metric.infDist (cellCenter (mesh D) z.2-cellCenter (mesh D) anchor.2)
      (Submodule.span ℝ {slopeVector D j}:Set E4) ≤ 48*(64/((2^m:ℕ):ℝ))^2 := by
  obtain ⟨hzE,hparent,hheight⟩ := short_member_readback a level p m hdy hmL rep E anchor z hz
  let x := cellCenter (mesh D) anchor.2
  let y := cellCenter (mesh D) z.2
  let c := y (3:Fin 4)-x (3:Fin 4)
  let Delta := 64/((2^m:ℕ):ℝ)
  have hx := original_cell_in_tube h original horiginal (hE hanchor)
  have hy := original_cell_in_tube h original horiginal (hE hzE)
  have hm : 2*mesh D=D.thickness := by unfold mesh; ring
  rw [hm] at hx hy
  have he := NativeSameFineParentPacket.same_parent_displacement_error h ha (2^p)
    (by positivity) anchor.1 z.1 hparent hx hy
  have hd : ‖slopeVector D anchor.1-slopeVector D j‖ ≤ 2/((2^m:ℕ):ℝ) := by
    simpa only [dist_eq_norm] using NativeAngularPacketReadback.same_angular_slopeVector_dist
      D a (2^m) (by positivity) anchor.1 j hangular
  have hc : ‖c • (slopeVector D anchor.1-slopeVector D j)‖ ≤
      (256*Delta)*(2/((2^m:ℕ):ℝ)) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hheight hd (norm_nonneg _) (by dsimp [Delta]; positivity)
  have hv : slopeVector D j∈(Submodule.span ℝ {slopeVector D j}:Set E4) :=
    Submodule.subset_span (by simp)
  apply (Metric.infDist_le_dist_of_mem ((Submodule.span ℝ {slopeVector D j}).smul_mem c hv)).trans
  rw [dist_eq_norm]
  have hid : (y-x)-c • slopeVector D j =
      ((y-x)-c • slopeVector D anchor.1)+c • (slopeVector D anchor.1-slopeVector D j) := by
    rw [smul_sub]
    abel
  change ‖(y-x)-c • slopeVector D j‖ ≤ 48*Delta^2
  rw [hid]
  calc
    _ ≤ ‖(y-x)-c • slopeVector D anchor.1‖+
        ‖c • (slopeVector D anchor.1-slopeVector D j)‖ := norm_add_le _ _
    _ ≤ (24*D.thickness+16/((2^p:ℕ):ℝ))+(256*Delta)*(2/((2^m:ℕ):ℝ)) := add_le_add he hc
    _ ≤ 48*Delta^2 := by
      have hp : 16/((2^p:ℕ):ℝ) ≤ 16*Delta^2 := by
        simpa only [mul_one_div] using
          mul_le_mul_of_nonneg_left hparentScale (by norm_num : (0:ℝ)≤16)
      have heq : (256*Delta)*(2/((2^m:ℕ):ℝ))=8*Delta^2 := by dsimp [Delta]; ring
      rw [heq]
      change D.thickness ≤ Delta^2 at hscale
      nlinarith only [hscale,hp]

/-- A physical vertex retains an actual old incidence from the short row.
The index is the physical spatial label, rather than a shadow-cell ancestor. -/
theorem short_vertex_witness {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (level p m : ℕ) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (anchor : Fin n × Index) (v : Index) (hv : v∈shortVertices D a level p m rep E anchor) :
    ∃z∈E, z∈shortEdges D a level p m rep E anchor ∧ spatialLabel D (2^p) z.2=v := by
  obtain ⟨z,hz,hzv⟩ := mem_image.mp hv
  exact ⟨z,(mem_filter.mp hz).1,hz,hzv⟩

/-- Every point of every occupied physical vertex cube is in the packet.
Cube diameter contributes 2*Delta²; the anchor remains its literal old cell. -/
theorem short_vertex_cube_packet {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level p m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmL : m ≤ level)
    (hscale : D.thickness ≤ (64/((2^m:ℕ):ℝ))^2)
    (hparentScale : 1/((2^p:ℕ):ℝ) ≤ (64/((2^m:ℕ):ℝ))^2)
    (hvertexScale : 64/((2^p:ℕ):ℝ) ≤ (64/((2^m:ℕ):ℝ))^2)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (anchor : Fin n × Index) (hanchor : anchor∈E) (j : Fin n)
    (hangular : (parentLabel D a (2^m) anchor.1).1=(parentLabel D a (2^m) j).1)
    (v : Index) (hv : v∈shortVertices D a level p m rep E anchor)
    {y : E4} (hy : y∈wzDyadicCell (64/((2^p:ℕ):ℝ)) v) :
    Metric.infDist (y-cellCenter (mesh D) anchor.2)
      (Submodule.span ℝ {slopeVector D j}:Set E4) ≤ 50*(64/((2^m:ℕ):ℝ))^2 := by
  obtain ⟨z,_hzE,hz,hzv⟩ := short_vertex_witness D a level p m rep E anchor v hv
  have hpacket := short_member_packet h original horiginal ha level p m hdy hmL
    hscale hparentScale rep E hE anchor hanchor j hangular z hz
  have hzc : cellCenter (mesh D) z.2∈wzDyadicCell (64/((2^p:ℕ):ℝ)) v := by
    rw [←hzv]
    exact mem_wzDyadicCell_index (by positivity) _
  have hdist : dist y (cellCenter (mesh D) z.2) ≤ 2*(64/((2^p:ℕ):ℝ)) :=
    (wzDyadicCell_subset_ball_of_mem (by positivity) v hzc hy).le
  have htri := Metric.infDist_le_infDist_add_dist
    (x := y-cellCenter (mesh D) anchor.2)
    (y := cellCenter (mesh D) z.2-cellCenter (mesh D) anchor.2)
    (s := (Submodule.span ℝ {slopeVector D j}:Set E4))
  rw [dist_sub_right] at htri
  linarith

/-- The packet can be anchored at the center of the actual spatial vertex.
The original anchor edge and incidence are kept; its rounding costs 2*Delta². -/
theorem short_vertex_rounded_packet {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level p m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmL : m ≤ level)
    (hscale : D.thickness ≤ (64/((2^m:ℕ):ℝ))^2)
    (hparentScale : 1/((2^p:ℕ):ℝ) ≤ (64/((2^m:ℕ):ℝ))^2)
    (hvertexScale : 64/((2^p:ℕ):ℝ) ≤ (64/((2^m:ℕ):ℝ))^2)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (anchor : Fin n × Index) (hanchor : anchor∈E) (j : Fin n)
    (hangular : (parentLabel D a (2^m) anchor.1).1=(parentLabel D a (2^m) j).1)
    (v : Index) (hv : v∈shortVertices D a level p m rep E anchor)
    {y : E4} (hy : y∈wzDyadicCell (64/((2^p:ℕ):ℝ)) v) :
    Metric.infDist (y-cellCenter (64/((2^p:ℕ):ℝ)) (spatialLabel D (2^p) anchor.2))
      (Submodule.span ℝ {slopeVector D j}:Set E4) ≤ 52*(64/((2^m:ℕ):ℝ))^2 := by
  have hpacket := short_vertex_cube_packet h original horiginal ha level p m hdy hmL
    hscale hparentScale hvertexScale rep E hE anchor hanchor j hangular v hv hy
  have hOld : cellCenter (mesh D) anchor.2∈wzDyadicCell (64/((2^p:ℕ):ℝ))
      (spatialLabel D (2^p) anchor.2) := mem_wzDyadicCell_index (by positivity) _
  have hRounded := cellCenter_mem (show 0 < 64/((2^p:ℕ):ℝ) by positivity)
    (spatialLabel D (2^p) anchor.2)
  have hd : dist (cellCenter (64/((2^p:ℕ):ℝ)) (spatialLabel D (2^p) anchor.2))
      (cellCenter (mesh D) anchor.2) ≤ 2*(64/((2^p:ℕ):ℝ)) :=
    (wzDyadicCell_subset_ball_of_mem (by positivity) _ hOld hRounded).le
  have htri := Metric.infDist_le_infDist_add_dist
    (x := y-cellCenter (64/((2^p:ℕ):ℝ)) (spatialLabel D (2^p) anchor.2))
    (y := y-cellCenter (mesh D) anchor.2)
    (s := (Submodule.span ℝ {slopeVector D j}:Set E4))
  rw [dist_sub_left] at htri
  linarith

/-- The full physical vertex cubes also retain the actual short height window
after BOTH predecessor and anchor rounding. No old witness is replaced. -/
theorem short_vertex_rounded_height {n : ℕ} {D : FiniteScaleSource n} (a : ℝ)
    (level p m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmL : m ≤ level)
    (hlarge : 64/((2^m:ℕ):ℝ) ≤ 1)
    (hvertexScale : 64/((2^p:ℕ):ℝ) ≤ (64/((2^m:ℕ):ℝ))^2)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (anchor : Fin n × Index)
    (v : Index) (hv : v∈shortVertices D a level p m rep E anchor)
    {y : E4} (hy : y∈wzDyadicCell (64/((2^p:ℕ):ℝ)) v) :
    |y (3:Fin 4)-cellCenter (64/((2^p:ℕ):ℝ)) (spatialLabel D (2^p) anchor.2) (3:Fin 4)| ≤
      512*(64/((2^m:ℕ):ℝ)) := by
  obtain ⟨z,_hzE,hz,hzv⟩ := short_vertex_witness D a level p m rep E anchor v hv
  have hheight := (short_member_readback a level p m hdy hmL rep E anchor z hz).2.2
  let rho := 64/((2^p:ℕ):ℝ)
  let Delta := 64/((2^m:ℕ):ℝ)
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hD : 0 ≤ Delta := by dsimp [Delta]; positivity
  have hzc : cellCenter (mesh D) z.2∈wzDyadicCell rho v := by
    rw [←hzv]
    exact mem_wzDyadicCell_index hrho _
  have hdistY : dist y (cellCenter (mesh D) z.2) ≤ 2*rho :=
    (wzDyadicCell_subset_ball_of_mem hrho v hzc hy).le
  have hcoordY : |y (3:Fin 4)-cellCenter (mesh D) z.2 (3:Fin 4)| ≤ 2*rho := by
    simpa only [Real.dist_eq] using
      (PiLp.dist_apply_le y (cellCenter (mesh D) z.2) (3:Fin 4)).trans hdistY
  have hOld : cellCenter (mesh D) anchor.2∈wzDyadicCell rho (spatialLabel D (2^p) anchor.2) :=
    mem_wzDyadicCell_index hrho _
  have hRounded := cellCenter_mem hrho (spatialLabel D (2^p) anchor.2)
  have hdistA : dist (cellCenter (mesh D) anchor.2)
      (cellCenter rho (spatialLabel D (2^p) anchor.2)) ≤ 2*rho :=
    (wzDyadicCell_subset_ball_of_mem hrho _ hRounded hOld).le
  have hcoordA : |cellCenter (mesh D) anchor.2 (3:Fin 4)-
      cellCenter rho (spatialLabel D (2^p) anchor.2) (3:Fin 4)| ≤ 2*rho := by
    simpa only [Real.dist_eq] using
      (PiLp.dist_apply_le (cellCenter (mesh D) anchor.2)
        (cellCenter rho (spatialLabel D (2^p) anchor.2)) (3:Fin 4)).trans hdistA
  have hsq : Delta^2 ≤ Delta := by
    nlinarith only [mul_nonneg hD (sub_nonneg.mpr hlarge)]
  calc
    _ ≤ |y (3:Fin 4)-cellCenter (mesh D) z.2 (3:Fin 4)|+
        |cellCenter (mesh D) z.2 (3:Fin 4)-
          cellCenter rho (spatialLabel D (2^p) anchor.2) (3:Fin 4)| := abs_sub_le _ _ _
    _ ≤ 2*rho+(|cellCenter (mesh D) z.2 (3:Fin 4)-cellCenter (mesh D) anchor.2 (3:Fin 4)|+
        |cellCenter (mesh D) anchor.2 (3:Fin 4)-
          cellCenter rho (spatialLabel D (2^p) anchor.2) (3:Fin 4)|) :=
      add_le_add hcoordY (abs_sub_le _ _ _)
    _ ≤ 2*rho+(256*Delta+2*rho) := add_le_add le_rfl (add_le_add hheight hcoordA)
    _ ≤ _ := by change rho ≤ Delta^2 at hvertexScale; change _ ≤ 512*Delta; linarith

/-- Saturating the occupied spatial vertices by all ORIGINAL E-point fibers
preserves the packet, even for old cells on other fine phase-parents. -/
theorem short_vertex_closure_packet {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level p m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmL : m ≤ level)
    (hscale : D.thickness ≤ (64/((2^m:ℕ):ℝ))^2)
    (hparentScale : 1/((2^p:ℕ):ℝ) ≤ (64/((2^m:ℕ):ℝ))^2)
    (hvertexScale : 64/((2^p:ℕ):ℝ) ≤ (64/((2^m:ℕ):ℝ))^2)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (anchor : Fin n × Index) (hanchor : anchor∈E) (j : Fin n)
    (hangular : (parentLabel D a (2^m) anchor.1).1=(parentLabel D a (2^m) j).1)
    (k : Index) (hk : k∈shortVertexClosure D a level p m rep E anchor) :
    k∈E.image Prod.snd ∧
      Metric.infDist (cellCenter (mesh D) k-
        cellCenter (64/((2^p:ℕ):ℝ)) (spatialLabel D (2^p) anchor.2))
        (Submodule.span ℝ {slopeVector D j}:Set E4) ≤ 52*(64/((2^m:ℕ):ℝ))^2 := by
  obtain ⟨hk,hv⟩ := mem_filter.mp hk
  refine ⟨hk,?_⟩
  exact short_vertex_rounded_packet h original horiginal ha level p m hdy hmL hscale
    hparentScale hvertexScale rep E hE anchor hanchor j hangular (spatialLabel D (2^p) k) hv
    (mem_wzDyadicCell_index (by positivity) _)

end NativeShortRowPackets
