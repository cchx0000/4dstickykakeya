import Theorems.Thm_StickyKakeya4_native_grain_height_projection_direct

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeGrainHeightProjectionSource
open Classical Finset StickyKakeya4 NativeGrainHeightProjectionTransport NativeGrainHeightProjectionDirect
open NativeGrainQuotientGeometry NativeGrainQuotientBins NativeGrainQuotientFibers
open NativeHorizontalGrainSlice NativeProjectorCellChart NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCommonCubicalMesh NativeSquaredGrainQueries
open NativeParentGrainIncidenceCleanup NativeCompatibleAngularCandidates NativeSpatialAngularGeometry
open RichDirectionalLayers NativeDirectionRankDichotomy NativeCompatibleNodeDirections
open NativeActualProjectedGrainCount NativeActualHorizontalGrainSlice

/-- The original node tuple plane, unchanged by the quotient construction. -/
def nodePlane {n ell : ℕ} (D : FiniteScaleSource n)
    (tuple : Index → Fin ell → (Fin n × Index)) (node : Index) : Submodule ℝ E4 :=
  spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple node))

/-- Absolute direction-to-plane error from the original preserved node theorem. -/
def sourceError (m ell : ℕ) (q : ℝ) : ℝ :=
  (1+16*(4/q)^ell)*(64/((2^m:ℕ):ℝ))

/-- Exact whole-grain quotient diameter, including its raw time range. -/
def sourceDiameter (m ell : ℕ) (q : ℝ) : ℝ :=
  (15/4:ℝ)*(((2^m:ℕ):ℝ)/512)*
    (2*grainWidth m ell+(64/((2^m:ℕ):ℝ))*sourceError m ell q)+
      (5/2:ℝ)*(64/((2^m:ℕ):ℝ))/512

lemma sourceError_pos (m ell : ℕ) {q : ℝ} (hq : 0 < q) : 0 < sourceError m ell q := by
  unfold sourceError
  positivity

lemma sourceDiameter_pos (m ell : ℕ) {q : ℝ} (hq : 0 < q) : 0 < sourceDiameter m ell q := by
  have hg := grainWidth_pos m ell
  have he := sourceError_pos m ell hq
  unfold sourceDiameter
  positivity

/-- Whole-grain spread from an actual retained parent incidence. Every
quotient coordinate is evaluated at the unchanged raw physical point. -/
theorem source_mixed_spread {n ell m : ℕ} {D : FiniteScaleSource n} {eta a q r : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hq1 : q ≤ 1) (hr : 0 < r)
    (hm : m ≤ phaseDepth m) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    {E0 : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E0 S q ell point tuple anchor)
    (A : Index → Submodule ℝ E4) (hA : ∀k∈S,Module.finrank ℝ (A k)=ell)
    (hnear : ∀z∈E0,Metric.infDist (slopeVector D z.1) (A z.2:Set E4) ≤ r)
    (hrD : r ≤ 64/((2^m:ℕ):ℝ))
    (E : Finset (Fin n × Index)) (hEE0 : E⊆E0) (c : Parent × (Index × Index))
    (z : Fin n × Index) (hz : z∈mixedFiber D a m (nodePlane D tuple) ell E c) (hzS : z.2∈S)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=ell-1)
    (hc : cell P=cell (sliceSpace (nodePlane D tuple c.2.1)))
    (k l : Index)
    (hk : k∈mixedVertices D a m (phaseDepth m) (nodePlane D tuple) ell E c)
    (hl : l∈mixedVertices D a m (phaseDepth m) (nodePlane D tuple) ell E c) :
    ‖rawCoordinates D a m ell c.1 P (sliceSpace (nodePlane D tuple c.2.1)) hP hell hell4 hd k-
      rawCoordinates D a m ell c.1 P (sliceSpace (nodePlane D tuple c.2.1)) hP hell hell4 hd l‖ ≤
        sourceDiameter m ell q := by
  have hzc := hz
  simp only [mixedFiber,classFiber,mem_filter] at hzc
  have hparent : parentLabel D a (2^m) z.1=c.1 := congrArg Prod.fst hzc.2
  have hnode : spatialLabel D (2^m) z.2=c.2.1 := congrArg (fun c : Parent × (Index × Index) => c.2.1) hzc.2
  have hn : c.2.1∈nodes D m S := by rw [←hnode]; exact mem_image_of_mem _ hzS
  obtain ⟨hQ,u,huQ,hu,hun⟩ := node_graph_direction H hell hq c.2.1 hn
  have hwnear := NativePreservedNodePlanes.incident_near_grain_plane h hq hq1 hr H A hA hnear hrD
    z.2 hzS z.1 (hEE0 hzc.1)
  rw [hnode] at hwnear
  have htime := ancestor_height_gap m (phaseDepth m) hm k l
    ((mixed_vertex_ancestor D a m ell hm _ E c k hk).trans (mixed_vertex_ancestor D a m ell hm _ E c l hl).symm)
  exact unchanged_quotient_difference D a (2^m) c.1 P (nodePlane D tuple c.2.1) hP ell hell hell4 hd
    (hd.trans hQ.symm) hc u (slopeVector D z.1) _ _ huQ hu hun (slopeVector_last D z.1)
    (retained_direction_norm D a (2^m) c.1 z.1 hparent)
    (sourceError m ell q) (2*grainWidth m ell) (64/((2^m:ℕ):ℝ))
    (sourceError_pos m ell hq).le hwnear (mixed_vertices_near D a m ell _ E c k l hk hl) htime

/-- Computed occupied quotient bins of ALL original raw grain vertices.
There is no exact-height restriction and no projected surrogate point. -/
theorem source_occupied_quotient_card {n ell m : ℕ} {D : FiniteScaleSource n} {eta a q r : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hq1 : q ≤ 1) (hr : 0 < r)
    (hm : m ≤ phaseDepth m) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    {E0 : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E0 S q ell point tuple anchor)
    (A : Index → Submodule ℝ E4) (hA : ∀k∈S,Module.finrank ℝ (A k)=ell)
    (hnear : ∀z∈E0,Metric.infDist (slopeVector D z.1) (A z.2:Set E4) ≤ r)
    (hrD : r ≤ 64/((2^m:ℕ):ℝ))
    (E : Finset (Fin n × Index)) (hEE0 : E⊆E0) (c : Parent × (Index × Index))
    (z : Fin n × Index) (hz : z∈mixedFiber D a m (nodePlane D tuple) ell E c) (hzS : z.2∈S)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=ell-1)
    (hc : cell P=cell (sliceSpace (nodePlane D tuple c.2.1))) (mu : ℝ) (hmu : 0 < mu) :
    let f := rawCoordinates D a m ell c.1 P (sliceSpace (nodePlane D tuple c.2.1)) hP hell hell4 hd
    (((mixedVertices D a m (phaseDepth m) (nodePlane D tuple) ell E c).image
      (fun k => label mu (f k))).card:ℝ) ≤ (2*sourceDiameter m ell q/mu+2)^(4-ell) := by
  intro f
  let k := spatialLabel D (2^(phaseDepth m)) z.2
  have hk : k∈mixedVertices D a m (phaseDepth m) (nodePlane D tuple) ell E c := mem_image_of_mem _ hz
  exact occupied_card _ f hmu (sourceDiameter_pos m ell hq).le (f k)
    (fun l hl => source_mixed_spread h hq hq1 hr hm hell hell4 H A hA hnear hrD E hEE0 c z hz hzS
      P hP hd hc l k hl hk)

/-- Simplification at the genuine squared grain: the entire height drift
costs a polynomial in the already present separation q. -/
lemma sourceDiameter_le (m ell : ℕ) (hm : 6 ≤ m) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    sourceDiameter m ell q ≤ 250*(64/((2^m:ℕ):ℝ))*(4/q)^ell := by
  let D : ℝ := 64/((2^m:ℕ):ℝ)
  let A : ℝ := (4/q)^ell
  have hD : 0 < D := by dsimp [D]; positivity
  have hp : (4:ℝ)^ell ≤ A := by
    apply pow_le_pow_left₀ (by norm_num)
    exact (le_div_iff₀ hq).mpr (by nlinarith)
  have hA : 1 ≤ A := one_le_pow₀ (by apply (le_div_iff₀ hq).mpr; linarith)
  have hs := squared_scale_identity m hm
  have hN : (((2^m:ℕ):ℝ))≠0 := by positivity
  have he : sourceDiameter m ell q=
      D*((15/32:ℝ)*(516*(4:ℝ)^ell+1+16*A)+5/1024) := by
    unfold sourceDiameter sourceError grainWidth NativeApproximateFiberIteration.radius
    rw [hs]
    dsimp [D,A]
    field_simp
    ring
  rw [he]
  have hc : (15/32:ℝ)*(516*(4:ℝ)^ell+1+16*A)+5/1024 ≤ 250*A := by linarith only [hp,hA]
  simpa only [D,A,mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_left hc hD.le

/-- Exact terminal mesh after the physical map, including its fixed factor64. -/
lemma phase_working_mesh (m : ℕ) (hm : 6 ≤ m) :
    physicalMesh m (phaseDepth m)/8=(64/((2^m:ℕ):ℝ))/64 := by
  unfold physicalMesh
  rw [squared_scale_identity m hm]
  have hN : (((2^m:ℕ):ℝ))≠0 := by positivity
  field_simp
  ring

/-- The q-dependent occupied-bin cost at the actual terminal working mesh. -/
lemma source_quotient_cost (m ell : ℕ) (hm : 6 ≤ m) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    (2*sourceDiameter m ell q/(physicalMesh m (phaseDepth m)/8)+2)^(4-ell) ≤
      (32002*(4/q)^ell)^(4-ell) := by
  rw [phase_working_mesh m hm]
  apply pow_le_pow_left₀ (by have hp := sourceDiameter_pos m ell hq; positivity)
  have hb := sourceDiameter_le m ell hm hq hq1
  have hA : (1:ℝ) ≤ (4/q)^ell := one_le_pow₀ (by apply (le_div_iff₀ hq).mpr; linarith)
  have hdiv : 2*sourceDiameter m ell q/((64/((2^m:ℕ):ℝ))/64) ≤ 32000*(4/q)^ell := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(64/((2^m:ℕ):ℝ))/64)).mpr
    nlinarith only [hb]
  linarith only [hdiv,hA]

end NativeGrainHeightProjectionSource
