import Theorems.Thm_StickyKakeya4_native_grain_quotient_fibers
import Theorems.Thm_StickyKakeya4_native_coarse_original_heights

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeGrainQuotientInjection
open Classical Finset StickyKakeya4 NativeGrainQuotientGeometry NativeGrainQuotientBins
open NativeGrainQuotientFibers NativeHorizontalGrainSlice NativeHorizontalGraphCoordinates
open NativeSelectedHorizontalGraphChart NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeSquaredGrainQueries NativeParentGrainIncidenceCleanup
open scoped BigOperators

/-- Actual tangent coordinates in the fixed orthonormal reference plane. -/
def tangentCoordinates (P : Submodule ℝ E4) (ell : ℕ) (hd : Module.finrank ℝ P=ell-1) :
    E4 →ₗ[ℝ] EuclideanSpace ℝ (Fin (ell-1)) :=
  (domainBasis P ell hd).repr.toLinearMap.comp P.orthogonalProjectionOnto.toLinearMap

lemma tangentCoordinates_norm (P : Submodule ℝ E4) (ell : ℕ)
    (hd : Module.finrank ℝ P=ell-1) (x : E4) :
    ‖tangentCoordinates P ell hd x‖=‖P.starProjection x‖ := by
  change ‖(domainBasis P ell hd).repr (P.orthogonalProjectionOnto x)‖=_
  rw [LinearIsometryEquiv.norm_map]
  rfl

lemma residual_mem_normalSpace (P Q : Submodule ℝ E4)
    (hP : P≤heightKernel) (hQ : Q≤heightKernel) {x : E4} (hx : x∈heightKernel) :
    residual P Q x∈normalSpace P := by
  rw [residual_apply]
  refine ⟨Pᗮ.sub_mem (Pᗮ.starProjection_apply_mem x) (totalGraph P Q (P.orthogonalProjectionOnto x)).property,?_⟩
  apply heightKernel.sub_mem _ (totalGraph_horizontal P Q hP hQ _)
  rw [Submodule.starProjection_orthogonal_val]
  exact heightKernel.sub_mem hx (hP (P.starProjection_apply_mem x))

lemma coordinates_norm_eq_residual (P Q : Submodule ℝ E4)
    (hP : P≤heightKernel) (hQ : Q≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) {x : E4} (hx : x∈heightKernel) :
    ‖coordinates P Q hP ell hell hell4 hd x‖=‖residual P Q x‖ := by
  change ‖(normalBasis P hP ell hell hell4 hd).repr
    ((normalSpace P).orthogonalProjectionOnto (residual P Q x))‖=_
  rw [LinearIsometryEquiv.norm_map]
  exact (normalSpace P).norm_orthogonalProjectionOnto_apply (residual_mem_normalSpace P Q hP hQ hx)

/-- The full horizontal point is quantitatively determined by its two
actual coordinates. This applies to thick points without snapping. -/
theorem norm_le_coordinates (P Q : Submodule ℝ E4)
    (hP : P≤heightKernel) (hQ : Q≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) {x : E4} (hx : x∈heightKernel) :
    ‖x‖ ≤ (5/4:ℝ)*‖tangentCoordinates P ell hd x‖+
      ‖coordinates P Q hP ell hell hell4 hd x‖ := by
  rw [tangentCoordinates_norm,coordinates_norm_eq_residual P Q hP hQ ell hell hell4 hd hx]
  have he : x=P.starProjection x+
      (totalGraph P Q (P.orthogonalProjectionOnto x):E4)+residual P Q x := by
    rw [residual_apply,Submodule.starProjection_orthogonal_val]
    abel
  have hg := totalGraph_norm P Q (P.orthogonalProjectionOnto x)
  change ‖(totalGraph P Q (P.orthogonalProjectionOnto x):E4)‖ ≤ (1/4:ℝ)*‖P.starProjection x‖ at hg
  calc
    _ = ‖P.starProjection x+(totalGraph P Q (P.orthogonalProjectionOnto x):E4)+residual P Q x‖ := by rw [←he]
    _ ≤ ‖P.starProjection x‖+‖(totalGraph P Q (P.orthogonalProjectionOnto x):E4)‖+‖residual P Q x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by linarith only [hg]

lemma same_label_coordinate_bound {d : ℕ} {mu : ℝ} (hmu : 0 < mu)
    (x y : EuclideanSpace ℝ (Fin d)) (hlabel : label mu x=label mu y) (j : Fin d) :
    |x j-y j| ≤ mu := by
  have he := congrFun hlabel j
  change ⌊x j/mu⌋=⌊y j/mu⌋ at he
  have hxl := Int.floor_le (x j/mu)
  have hxu := Int.lt_floor_add_one (x j/mu)
  have hyl := Int.floor_le (y j/mu)
  have hyu := Int.lt_floor_add_one (y j/mu)
  rw [he] at hxl hxu
  have hh : |x j/mu-y j/mu| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  rw [←sub_div,abs_div,abs_of_pos hmu] at hh
  simpa only [one_mul] using (div_le_iff₀ hmu).mp hh

lemma same_label_norm_bound {d : ℕ} {mu : ℝ} (hmu : 0 < mu)
    (x y : EuclideanSpace ℝ (Fin d)) (hlabel : label mu x=label mu y) :
    ‖x-y‖ ≤ (d:ℝ)*mu := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have he : ∑j : Fin d,(x-y) j • b j=x-y := b.sum_repr (x-y)
  calc
    _ = ‖∑j : Fin d,(x-y) j • b j‖ := by rw [he]
    _ ≤ ∑j : Fin d,‖(x-y) j • b j‖ := norm_sum_le _ _
    _ ≤ ∑_j : Fin d,mu := by
      apply sum_le_sum
      intro j _hj
      rw [norm_smul,b.orthonormal.norm_eq_one,mul_one]
      simpa only [PiLp.sub_apply,Real.norm_eq_abs] using same_label_coordinate_bound hmu x y hlabel j
    _ = _ := by simp

/-- Same terminal bins in both actual coordinates force horizontal physical
points to be within four terminal mesh lengths. -/
theorem same_coordinate_bins_norm {mu : ℝ} (hmu : 0 < mu)
    (P Q : Submodule ℝ E4) (hP : P≤heightKernel) (hQ : Q≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (x y : E4) (hxy : x-y∈heightKernel)
    (hX : label mu (tangentCoordinates P ell hd x)=label mu (tangentCoordinates P ell hd y))
    (hY : label mu (coordinates P Q hP ell hell hell4 hd x)=label mu (coordinates P Q hP ell hell hell4 hd y)) :
    ‖x-y‖ ≤ 4*mu := by
  have hx := same_label_norm_bound hmu _ _ hX
  have hy := same_label_norm_bound hmu _ _ hY
  rw [←map_sub] at hx hy
  have hn := norm_le_coordinates P Q hP hQ ell hell hell4 hd hxy
  have he : ((ell-1:ℕ):ℝ)+((4-ell:ℕ):ℝ)=3 := by exact_mod_cast (show ell-1+(4-ell)=3 by omega)
  have hk : ((ell-1:ℕ):ℝ) ≤ 3 := by exact_mod_cast (show ell-1 ≤ 3 by omega)
  have hm := mul_le_mul_of_nonneg_right hk hmu.le
  have hes := congrArg (fun t : ℝ => t*mu) he
  rw [add_mul] at hes
  nlinarith only [hx,hy,hn,hes,hm,hmu]

/-- Actual raw vertices have the original physical lattice separation after
applying the genuine parent map on an exact-height slice. -/
theorem physical_vertex_separated {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m f : ℕ) (parent : Parent) (k l : Index)
    (ht : k (3:Fin 4)=l (3:Fin 4)) (hne : k≠l) :
    physicalMesh m f ≤ ‖NativeLocalParentPhysicalMap.physicalMap D a (2^m) parent
      (cellCenter (64/((2^f:ℕ):ℝ)) k)-
      NativeLocalParentPhysicalMap.physicalMap D a (2^m) parent
      (cellCenter (64/((2^f:ℕ):ℝ)) l)‖ := by
  have hheight : cellCenter (64/((2^f:ℕ):ℝ)) k (3:Fin 4)=
      cellCenter (64/((2^f:ℕ):ℝ)) l (3:Fin 4) := by simp only [cellCenter,ht]
  rw [NativeParentHorizontalReadback.physical_map_horizontal_difference D a (2^m) parent _ _ hheight,
    norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : (0:ℝ)<((2^m:ℕ):ℝ)/512)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  obtain ⟨j,hj⟩ : ∃j,k j≠l j := by contrapose! hne; exact funext hne
  have hg := NativeCoarseOriginalHeights.integer_center_gap
    (by positivity : (0:ℝ)<64/((2^f:ℕ):ℝ)) (k j) (l j) hj
  exact hg.trans (by simpa only [cellCenter,PiLp.sub_apply,Real.norm_eq_abs] using
    PiLp.norm_apply_le (cellCenter (64/((2^f:ℕ):ℝ)) k-cellCenter (64/((2^f:ℕ):ℝ)) l) j)

/-- Physical horizontal membership for exact raw heights. -/
lemma physical_difference_horizontal {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m f : ℕ) (parent : Parent) (k l : Index) (ht : k (3:Fin 4)=l (3:Fin 4)) :
    NativeLocalParentPhysicalMap.physicalMap D a (2^m) parent
      (cellCenter (64/((2^f:ℕ):ℝ)) k)-
      NativeLocalParentPhysicalMap.physicalMap D a (2^m) parent
      (cellCenter (64/((2^f:ℕ):ℝ)) l)∈heightKernel := by
  have hheight : cellCenter (64/((2^f:ℕ):ℝ)) k (3:Fin 4)=
      cellCenter (64/((2^f:ℕ):ℝ)) l (3:Fin 4) := by simp only [cellCenter,ht]
  rw [NativeParentHorizontalReadback.physical_map_horizontal_difference D a (2^m) parent _ _ hheight]
  apply heightKernel.smul_mem
  change cellCenter (64/((2^f:ℕ):ℝ)) k (3:Fin 4)-cellCenter (64/((2^f:ℕ):ℝ)) l (3:Fin 4)=0
  exact sub_eq_zero.mpr hheight

end NativeGrainQuotientInjection
