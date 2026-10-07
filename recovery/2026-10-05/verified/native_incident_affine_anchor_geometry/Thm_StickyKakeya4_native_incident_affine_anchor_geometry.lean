import Theorems.Thm_StickyKakeya4_native_grain_quotient_injection
import Theorems.Thm_StickyKakeya4_native_height_slope_coordinates

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeIncidentAffineAnchorGeometry
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeSpatialAngularGeometry
open NativeOriginalParentSelection NativeLocalParentGeometry NativeParentHorizontalReadback
open NativeHorizontalGrainSlice NativeHorizontalGraphCoordinates NativeHeightSlopeCoordinates
open NativeGrainQuotientGeometry NativeGrainQuotientInjection NativeSelectedHorizontalGraphChart
open NativeProjectorCellChart NativeDirectionRankDichotomy
open scoped BigOperators Matrix.Norms.Elementwise

/-- Actual normalized parent slope, embedded horizontally; there is no1/512
factor because spatial and time contractions cancel in slope coordinates. -/
def localHorizontalSlope {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (p : Parent) (i : Fin n) : E4 :=
  ActualSlopeSource.heightPoint (localSlope D N p i) 0

lemma localHorizontalSlope_sub {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (p : Parent) (i j : Fin n) :
    localHorizontalSlope D N p i-localHorizontalSlope D N p j=(N:ℝ) • (slopeVector D i-slopeVector D j) := by
  rw [←local_slope_difference D N p i j]
  ext k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp only [localHorizontalSlope,PiLp.sub_apply,ActualSlopeSource.heightPoint_last,sub_zero]
  · simp only [localHorizontalSlope,PiLp.sub_apply,ActualSlopeSource.heightPoint_castSucc]

lemma localHorizontalSlope_mem_heightKernel {n : ℕ} (D : FiniteScaleSource n) (N : ℕ)
    (p : Parent) (i : Fin n) : localHorizontalSlope D N p i∈heightKernel := by
  change ActualSlopeSource.heightPoint (localSlope D N p i) 0 (3:Fin 4)=0
  exact ActualSlopeSource.heightPoint_last _ _

lemma localHorizontalSlope_norm {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p) : ‖localHorizontalSlope D N p i‖ ≤ 2 := by
  have hsq : ‖localHorizontalSlope D N p i‖^2 ≤ 3 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_castSucc]
    simp only [localHorizontalSlope,ActualSlopeSource.heightPoint_castSucc,ActualSlopeSource.heightPoint_last,
      Fin.sum_univ_three,zero_pow (by decide : 2≠0),add_zero]
    have h0 := (sq_le_one_iff_abs_le_one (localSlope D N p i (0:Fin 3))).mpr (localSlope_bound D a N p i hp 0)
    have h1 := (sq_le_one_iff_abs_le_one (localSlope D N p i (1:Fin 3))).mpr (localSlope_bound D a N p i hp 1)
    have h2 := (sq_le_one_iff_abs_le_one (localSlope D N p i (2:Fin 3))).mpr (localSlope_bound D a N p i hp 2)
    linarith only [h0,h1,h2]
  nlinarith only [hsq,norm_nonneg (localHorizontalSlope D N p i)]

/-- The fixed orthonormal normal coordinate map, independent of the node plane. -/
def normalCoordinates (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) :
    E4 →ₗ[ℝ] EuclideanSpace ℝ (Fin (4-ell)) :=
  (normalBasis P hP ell hell hell4 hd).repr.toLinearMap.comp (normalSpace P).orthogonalProjectionOnto.toLinearMap

/-- The literal normal-minus-matrix-times-tangent expression is the verified
linear graph quotient in the same fixed coordinate bases. -/
lemma coordinates_normal_sub_matrix (P Q : Submodule ℝ E4) (hP : P≤heightKernel) (hQ : Q≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (x : E4) :
    normalCoordinates P hP ell hell hell4 hd x-
      matrixVector (nodeSlope P hP ell hell hell4 hd Q hQ) (tangentCoordinates P ell hd x)=
        coordinates P Q hP ell hell hell4 hd x := by
  let G := totalGraph P Q
  let hG : ∀p,(G p:E4)∈heightKernel := totalGraph_horizontal P Q hP hQ
  have hproj (p : P) : (normalSpace P).orthogonalProjectionOnto (G p:E4)=horizontalGraph P G hG p := by
    change (normalSpace P).orthogonalProjectionOnto ((horizontalGraph P G hG p:normalSpace P):E4)=_
    exact (normalSpace P).orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [nodeSlope_action]
  change (normalBasis P hP ell hell hell4 hd).repr ((normalSpace P).orthogonalProjectionOnto x)-
    (normalBasis P hP ell hell hell4 hd).repr
      (horizontalGraph P G hG ((domainBasis P ell hd).repr.symm
        ((domainBasis P ell hd).repr (P.orthogonalProjectionOnto x))))=
    (normalBasis P hP ell hell hell4 hd).repr ((normalSpace P).orthogonalProjectionOnto (residual P Q x))
  rw [LinearIsometryEquiv.symm_apply_apply,residual_apply,map_sub,
    Submodule.orthogonalProjectionOnto_starProjection_of_le (show normalSpace P≤Pᗮ from inf_le_left),hproj,map_sub]

lemma coordinates_norm_le (P Q : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (x : E4) :
    ‖coordinates P Q hP ell hell hell4 hd x‖ ≤ (5/4:ℝ)*‖x‖ := by
  change ‖(normalBasis P hP ell hell hell4 hd).repr
    ((normalSpace P).orthogonalProjectionOnto (residual P Q x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact ((normalSpace P).norm_orthogonalProjectionOnto_apply_le _).trans (residual_norm P Q x)

/-- Pick from the CURRENT retained point fiber. The default is used only
at unoccupied points and cannot affect any retained incidence. -/
def anchorTube {n : ℕ} (H : Finset (Fin n × Index)) (fallback : Fin n) (k : Index) : Fin n :=
  if hk : k∈H.image Prod.snd then ((mem_image.mp hk).choose).1 else fallback

lemma anchorTube_mem {n : ℕ} (H : Finset (Fin n × Index)) (fallback : Fin n)
    (k : Index) (hk : k∈H.image Prod.snd) : (anchorTube H fallback k,k)∈H := by
  rw [anchorTube,dif_pos hk]
  obtain ⟨hz,hzk⟩ := (mem_image.mp hk).choose_spec
  have heq : ((mem_image.mp hk).choose.1,k)=(mem_image.mp hk).choose := Prod.ext rfl hzk.symm
  exact (congrArg (fun z : Fin n × Index => z∈H) heq).mpr hz

/-- Finite local affine anchors are constructed from actual retained tubes.
The only error input is a direction-difference estimate; the source-facing
companion derives that estimate from the actual small-loss hierarchy. -/
theorem exists_incident_affine_anchors {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (parent : Parent)
    (H : Finset (Fin n × Index)) (fallback : Fin n)
    (hparent : ∀z∈H,parentLabel D a (2^m) z.1=parent)
    (P0 : Submodule ℝ E4) (hP0 : P0≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P0=ell-1)
    (Q : Index → Submodule ℝ E4)
    (hQ : ∀k∈H.image Prod.snd,Q k≤heightKernel)
    (hDim : ∀k∈H.image Prod.snd,Module.finrank ℝ P0=Module.finrank ℝ (Q k))
    (hCell : ∀k∈H.image Prod.snd,cell P0=cell (Q k))
    (f : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (hread : ∀k (hk : k∈H.image Prod.snd),f (spatialLabel D (2^m) k (3:Fin 4))=
      nodeSlope P0 hP0 ell hell hell4 hd (Q k) (hQ k hk))
    (error : ℝ)
    (herror : ∀k∈H.image Prod.snd,∀i j : Fin n,(i,k)∈H→(j,k)∈H→
      Metric.infDist (localHorizontalSlope D (2^m) parent i-localHorizontalSlope D (2^m) parent j)
        (Q k:Set E4) ≤ error) :
    ∃j : Index → Fin n,∃xi : Index → EuclideanSpace ℝ (Fin (4-ell)),
      ∀k∈H.image Prod.snd,(j k,k)∈H ∧
        xi k=normalCoordinates P0 hP0 ell hell hell4 hd (localHorizontalSlope D (2^m) parent (j k))-
          matrixVector (f (spatialLabel D (2^m) k (3:Fin 4)))
            (tangentCoordinates P0 ell hd (localHorizontalSlope D (2^m) parent (j k))) ∧
        ‖xi k‖ ≤ (5/2:ℝ) ∧
        ∀i : Fin n,(i,k)∈H→
          ‖normalCoordinates P0 hP0 ell hell hell4 hd (localHorizontalSlope D (2^m) parent i)-xi k-
            matrixVector (f (spatialLabel D (2^m) k (3:Fin 4)))
              (tangentCoordinates P0 ell hd (localHorizontalSlope D (2^m) parent i))‖ ≤ (5/4:ℝ)*error := by
  let j := anchorTube H fallback
  let xi := fun k => coordinates P0 (Q k) hP0 ell hell hell4 hd (localHorizontalSlope D (2^m) parent (j k))
  refine ⟨j,xi,?_⟩
  intro k hk
  have hj : (j k,k)∈H := anchorTube_mem H fallback k hk
  have hquot (i : Fin n) : normalCoordinates P0 hP0 ell hell hell4 hd (localHorizontalSlope D (2^m) parent i)-
      matrixVector (f (spatialLabel D (2^m) k (3:Fin 4)))
        (tangentCoordinates P0 ell hd (localHorizontalSlope D (2^m) parent i))=
      coordinates P0 (Q k) hP0 ell hell hell4 hd (localHorizontalSlope D (2^m) parent i) := by
    rw [hread k hk]
    exact coordinates_normal_sub_matrix P0 (Q k) hP0 (hQ k hk) ell hell hell4 hd _
  refine ⟨hj,(hquot (j k)).symm,?_,?_⟩
  · have hnorm := coordinates_norm_le P0 (Q k) hP0 ell hell hell4 hd (localHorizontalSlope D (2^m) parent (j k))
    have hlocal := localHorizontalSlope_norm D a (2^m) parent (j k) (hparent (j k,k) hj)
    dsimp only [xi]
    linarith only [hnorm,hlocal]
  · intro i hi
    have heq : normalCoordinates P0 hP0 ell hell hell4 hd (localHorizontalSlope D (2^m) parent i)-xi k-
        matrixVector (f (spatialLabel D (2^m) k (3:Fin 4)))
          (tangentCoordinates P0 ell hd (localHorizontalSlope D (2^m) parent i))=
        coordinates P0 (Q k) hP0 ell hell hell4 hd
          (localHorizontalSlope D (2^m) parent i-localHorizontalSlope D (2^m) parent (j k)) := by
      rw [map_sub,←hquot i]
      change _=(_-_)-xi k
      abel
    rw [heq]
    exact (coordinates_norm_le_infDist P0 (Q k) hP0 ell hell hell4 hd (hDim k hk) (hCell k hk) _).trans
      (mul_le_mul_of_nonneg_left (herror k hk i (j k) hi hj) (by norm_num))

end NativeIncidentAffineAnchorGeometry
