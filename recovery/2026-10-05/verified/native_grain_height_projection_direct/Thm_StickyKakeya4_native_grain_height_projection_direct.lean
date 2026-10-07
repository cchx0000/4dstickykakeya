import Theorems.Thm_StickyKakeya4_native_grain_height_projection_transport

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeGrainHeightProjectionDirect
open Classical Finset StickyKakeya4 NativeGrainHeightProjectionTransport
open NativeGrainQuotientGeometry NativeGrainQuotientBins NativeGrainQuotientFibers
open NativeHorizontalGrainSlice NativeHorizontalGraphCoordinates NativeProjectorCellChart
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeCommonCubicalMesh
open NativeSquaredGrainQueries NativeParentGrainIncidenceCleanup NativeCompatibleAngularCandidates
open NativeSpatialAngularGeometry RichDirectionalLayers NativeDirectionRankDichotomy

/-- Norm control for the fixed horizontal quotient on arbitrary vectors,
including vectors with a nonzero height component. -/
lemma coordinates_norm (P Q : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (x : E4) :
    ‖coordinates P Q hP ell hell hell4 hd x‖ ≤ (5/4:ℝ)*‖x‖ := by
  change ‖(normalBasis P hP ell hell hell4 hd).repr
    ((normalSpace P).orthogonalProjectionOnto (NativeGrainQuotientGeometry.residual P Q x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact ((normalSpace P).norm_orthogonalProjectionOnto_apply_le _).trans (residual_norm P Q x)

lemma infDist_sub_smul_le (Q : Submodule ℝ E4) (z w : E4) (t : ℝ) :
    Metric.infDist (z-t • w) (Q:Set E4) ≤
      Metric.infDist z (Q:Set E4)+|t| * Metric.infDist w (Q:Set E4) := by
  rw [←NativeEqualRankPlaneTransfer.projection_residual_eq_infDist,
    ←NativeEqualRankPlaneTransfer.projection_residual_eq_infDist Q z,
    ←NativeEqualRankPlaneTransfer.projection_residual_eq_infDist Q w]
  have he : (z-t • w)-Q.starProjection (z-t • w)=
      (z-Q.starProjection z)-t • (w-Q.starProjection w) := by
    rw [map_sub,map_smul,smul_sub]
    abel
  rw [he]
  simpa only [norm_smul,Real.norm_eq_abs] using
    norm_sub_le (z-Q.starProjection z) (t • (w-Q.starProjection w))

/-- An algebraic decomposition of unchanged physical point differences.
The retained parent direction removes time before horizontal scaling. -/
lemma physical_difference_decomposition {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (w x y : E4) (hw : w (3:Fin 4)=1) :
    NativeLocalParentPhysicalMap.physicalMap D a N p x-
      NativeLocalParentPhysicalMap.physicalMap D a N p y=
      ((N:ℝ)/512) • removeHeight w (x-y)+
        ((x (3:Fin 4)-y (3:Fin 4))/512) • parentDirection N p w := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [NativeLocalParentPhysicalMap.physicalMap,NativeLocalParentPhysicalMap.baseMap,
      NativeContractedUnitParent.contractPoint,removeHeight,parentDirection,
      ActualSlopeSource.heightPoint_last,PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,hw]
    simp only [show (Fin.last 3:Fin 4)=3 by rfl,hw]
    ring
  · simp only [NativeLocalParentPhysicalMap.physicalMap,NativeLocalParentPhysicalMap.baseMap,
      NativeContractedUnitParent.contractPoint,removeHeight,parentDirection,
      ActualSlopeSource.heightPoint_castSucc,PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,hw]
    ring

/-- Whole-height quotient spread for UNCHANGED points. The global in-plane
direction is used only before rescaling; the retained parent direction is
used only for its true normalized bound and its absolute near-plane error. -/
theorem unchanged_quotient_difference {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (P Q : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (hPQ : Module.finrank ℝ P=Module.finrank ℝ (sliceSpace Q)) (hc : cell P=cell (sliceSpace Q))
    (u w x y : E4) (huQ : u∈Q) (hu : u (3:Fin 4)=1) (hun : ‖u‖ ≤ 2)
    (hw : w (3:Fin 4)=1) (hwn : ‖parentDirection N p w‖ ≤ 2)
    (e H T : ℝ) (_he : 0 ≤ e) (hnearw : Metric.infDist w (Q:Set E4) ≤ e)
    (hnear : Metric.infDist (x-y) (Q:Set E4) ≤ H) (htime : |x (3:Fin 4)-y (3:Fin 4)| ≤ T) :
    ‖coordinates P (sliceSpace Q) hP ell hell hell4 hd
      (NativeLocalParentPhysicalMap.physicalMap D a N p x)-
      coordinates P (sliceSpace Q) hP ell hell hell4 hd
      (NativeLocalParentPhysicalMap.physicalMap D a N p y)‖ ≤
      (15/4:ℝ)*((N:ℝ)/512)*(H+T*e)+(5/2:ℝ)*T/512 := by
  let z := removeHeight w (x-y)
  let C := coordinates P (sliceSpace Q) hP ell hell hell4 hd
  have hzH : z∈heightKernel := removeHeight_mem_heightKernel hw _
  have hzt : z (3:Fin 4)=0 := hzH
  have hznear : Metric.infDist z (Q:Set E4) ≤ H+T*e := by
    have hh := infDist_sub_smul_le Q (x-y) w (x (3:Fin 4)-y (3:Fin 4))
    have he0 := Metric.infDist_nonneg (x:=w) (s:=(Q:Set E4))
    have ht0 : 0 ≤ T := (abs_nonneg _).trans htime
    have hm := mul_le_mul htime hnearw he0 ht0
    exact hh.trans (add_le_add hnear hm)
  have hhorizontal := near_horizontal_slice Q huQ hu hun hznear
  have hr : removeHeight u z=z := by simp only [removeHeight,hzt,zero_smul,sub_zero]
  rw [hr] at hhorizontal
  have hCz : ‖C z‖ ≤ (15/4:ℝ)*(H+T*e) := by
    have hh := coordinates_norm_le_infDist P (sliceSpace Q) hP ell hell hell4 hd hPQ hc z
    dsimp only [C]
    linarith only [hh,hhorizontal]
  have hCw : ‖C (parentDirection N p w)‖ ≤ (5/2:ℝ) := by
    have hh := coordinates_norm P (sliceSpace Q) hP ell hell hell4 hd (parentDirection N p w)
    dsimp only [C]
    linarith only [hh,hwn]
  rw [←map_sub,physical_difference_decomposition D a N p w x y hw,map_add,map_smul,map_smul]
  change ‖((N:ℝ)/512) • C z+((x (3:Fin 4)-y (3:Fin 4))/512) • C (parentDirection N p w)‖ ≤ _
  have hn1 : ‖((N:ℝ)/512) • C z‖ ≤ ((N:ℝ)/512)*((15/4:ℝ)*(H+T*e)) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ) ≤ N/512)]
    exact mul_le_mul_of_nonneg_left hCz (by positivity)
  have hn2 : ‖((x (3:Fin 4)-y (3:Fin 4))/512) • C (parentDirection N p w)‖ ≤ (5/2:ℝ)*T/512 := by
    rw [norm_smul,Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    have hh := mul_le_mul htime hCw (norm_nonneg _) ((abs_nonneg _).trans htime)
    nlinarith only [hh]
  have hh := norm_add_le (((N:ℝ)/512) • C z)
    (((x (3:Fin 4)-y (3:Fin 4))/512) • C (parentDirection N p w))
  nlinarith only [hh,hn1,hn2]

lemma raw_mesh_times_ancestor (m f : ℕ) (hmf : m ≤ f) :
    (64/((2^f:ℕ):ℝ))*((2^(f-m):ℕ):ℝ)=64/((2^m:ℕ):ℝ) := by
  have hp : (2:ℕ)^(f-m)*2^m=2^f := by rw [←pow_add,Nat.sub_add_cancel hmf]
  have hpR : (((2^(f-m):ℕ):ℝ))*((2^m:ℕ):ℝ)=((2^f:ℕ):ℝ) := by exact_mod_cast hp
  have hm : (((2^m:ℕ):ℝ))≠0 := by positivity
  have hf : (((2^f:ℕ):ℝ))≠0 := by positivity
  field_simp
  nlinarith only [hpR]

/-- Literal phase centers in the same raw m-node have height diameter Delta.
This is proved by integer ancestry, including all raw heights. -/
theorem ancestor_height_gap (m f : ℕ) (hmf : m ≤ f) (k l : Index)
    (hancestor : spatialAncestor f m k=spatialAncestor f m l) :
    |cellCenter (64/((2^f:ℕ):ℝ)) k (3:Fin 4)-
      cellCenter (64/((2^f:ℕ):ℝ)) l (3:Fin 4)| ≤ 64/((2^m:ℕ):ℝ) := by
  let N : ℕ := 2^(f-m)
  let u : ℤ := l (3:Fin 4)/(N:ℤ)
  have hN : (0:ℤ)<N := by dsimp [N]; positivity
  have hk : k (3:Fin 4)/(N:ℤ)=u := congrFun hancestor (3:Fin 4)
  have hl : l (3:Fin 4)/(N:ℤ)=u := rfl
  obtain ⟨hkl,hku⟩ := (Int.ediv_eq_iff_of_pos hN).mp hk
  obtain ⟨hll,hlu⟩ := (Int.ediv_eq_iff_of_pos hN).mp hl
  have hgap : -(N:ℤ) ≤ k (3:Fin 4)-l (3:Fin 4) ∧ k (3:Fin 4)-l (3:Fin 4) ≤ N := by omega
  have hgapR : |(k (3:Fin 4):ℝ)-(l (3:Fin 4):ℝ)| ≤ N := by
    apply abs_le.mpr
    exact_mod_cast hgap
  have he : cellCenter (64/((2^f:ℕ):ℝ)) k (3:Fin 4)-
      cellCenter (64/((2^f:ℕ):ℝ)) l (3:Fin 4)=
      (64/((2^f:ℕ):ℝ))*((k (3:Fin 4):ℝ)-(l (3:Fin 4):ℝ)) := by dsimp [cellCenter]; ring
  rw [he,abs_mul,abs_of_pos (by positivity : (0:ℝ)<64/((2^f:ℕ):ℝ))]
  exact (mul_le_mul_of_nonneg_left hgapR (by positivity)).trans_eq (raw_mesh_times_ancestor m f hmf)

lemma mixed_vertex_ancestor {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4)
    (E : Finset (Fin n × Index)) (c : Parent × (Index × Index)) (k : Index)
    (hk : k∈mixedVertices D a m (phaseDepth m) plane ell E c) :
    spatialAncestor (phaseDepth m) m k=c.2.1 := by
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
  simp only [mixedFiber,classFiber,mem_filter] at hz
  rw [spatialAncestor_label D hm]
  exact congrArg (fun c : Parent × (Index × Index) => c.2.1) hz.2

end NativeGrainHeightProjectionDirect
