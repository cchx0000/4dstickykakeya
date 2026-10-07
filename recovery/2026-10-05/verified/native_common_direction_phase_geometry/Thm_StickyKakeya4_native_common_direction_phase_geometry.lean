import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_angular_cap
import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeCommonDirectionPhaseGeometry
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeLocalParentGeometry NativeLocalParentCells
open NativeRelativeParentLabels NativeNormalizedCellRelativeMenu NativeCubicalIncidenceCounts
open NativeOriginalParentPhysicalData NativeLocalCellCoherence NativeReferenceXYGridMaps
open NativeReferenceXYGridAngularCap NativeIncidentAffineAnchorGeometry

lemma physical_cell_gap {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N M : ℕ)
    (hM : 0 < M) (p : Parent) (k l : Index)
    (he : physicalCell D a N M p k=physicalCell D a N M p l) (v : Fin 4) :
    |physicalPoint D a N p k v-physicalPoint D a N p l v| ≤ 64/(M:ℝ) :=
  same_floor_abs (by positivity) (congrFun he v)

lemma physical_height_bound {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (p : Parent) (i : Fin n) (k : Index) (hk : k∈original i) :
    |physicalPoint D a N p k (3:Fin 4)| ≤ 1 := by
  have ht := (original_cell_bounds h original horiginal a ha ((mem_incidences original i k).mpr hk)).1
  change |NativeOriginalPaddedCells.oldTime D a k| ≤ 1 at ht
  change |NativeLocalParentPhysicalMap.physicalMap D a N p (cellCenter (mesh D) k) (3:Fin 4)| ≤ 1
  rw [physicalCell_height,abs_div,abs_of_pos (by norm_num : (0:ℝ)<128)]
  linarith

/-- The original tube's genuine front point at the same original cell
height satisfies this exact affine equation in the parent chart. -/
lemma front_equation {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (i : Fin n) (k : Index) (v : Fin 3) :
    frontPoint D a N p i k v.castSucc=
      intercept (NativeLocalParentGeometry.line D a N p i) v+
        physicalPoint D a N p k (3:Fin 4)*localSlope D N p i v := by
  rw [actual_local_intercept]
  change _ = _+NativeLocalParentPhysicalMap.physicalMap D a N p (cellCenter (mesh D) k) (3:Fin 4)*_
  rw [physicalCell_height]
  simp only [frontPoint,NativeContractedUnitParent.contractPoint,ActualSlopeSource.heightPoint_castSucc,
    PiLp.smul_apply,PiLp.add_apply,smul_eq_mul]
  ring

/-- The old incidence error is paid at the preserved physical rho scale,
using only the actual original shading and its source mesh. -/
theorem source_front_error {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N M : ℕ) (hM : 0 < M) (hscale : (N:ℝ)*D.thickness*(M:ℝ) ≤ 64)
    (p : Parent) (i : Fin n) (k : Index) (hk : k∈original i) (v : Fin 4) :
    |frontPoint D a N p i k v-physicalPoint D a N p k v| ≤ 64/(M:ℝ) := by
  have hh := frontPoint_near_physicalCell h original horiginal ha N p i k hk v
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hs : (N:ℝ)*D.thickness ≤ 64/(M:ℝ) := (le_div_iff₀ hMr).mpr hscale
  have hr : (0:ℝ)<64/(M:ℝ) := by positivity
  change |frontPoint D a N p i k v-physicalPoint D a N p k v| ≤ _ at hh
  nlinarith only [hh,hs,hr]

lemma scalar_intercept_spread {rho sigma bi bj ti tj wi wj xi xj fi fj : ℝ}
    (hrs : rho ≤ sigma) (hfi : fi=bi+ti*wi) (hfj : fj=bj+tj*wj)
    (hi : |fi-xi| ≤ rho) (hj : |fj-xj| ≤ rho) (hx : |xi-xj| ≤ rho)
    (ht : |ti-tj| ≤ rho) (hti : |ti| ≤ 1) (hwj : |wj| ≤ 1) (hw : |wi-wj| ≤ sigma) :
    |bi-bj| ≤ 5*sigma := by
  have hprod1 : |ti*(wi-wj)| ≤ sigma := by
    rw [abs_mul]
    exact (mul_le_mul hti hw (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hprod2 : |(ti-tj)*wj| ≤ rho := by
    rw [abs_mul]
    exact (mul_le_mul ht hwj (abs_nonneg _) ((abs_nonneg _).trans ht)).trans_eq (mul_one _)
  have hp : |ti*wi-tj*wj| ≤ sigma+rho := by
    rw [show ti*wi-tj*wj=ti*(wi-wj)+(ti-tj)*wj by ring]
    exact (abs_add_le _ _).trans (add_le_add hprod1 hprod2)
  have hf : |fi-fj| ≤ 3*rho := by
    have hh1 := abs_sub_le fi xi xj
    have hh2 := abs_sub_le fi xj fj
    rw [abs_sub_comm xj fj] at hh2
    linarith
  have he : bi-bj=(fi-fj)-(ti*wi-tj*wj) := by rw [hfi,hfj]; ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith only [hf,hp,hrs])

/-- Actual incidences in one physical rho cube and one standard sigma
slope cube have physical graph intercept spread at most5sigma. -/
theorem physical_intercept_spread {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N M : ℕ) (hM : 0 < M) (hscale : (N:ℝ)*D.thickness*(M:ℝ) ≤ 64)
    (sigma : ℝ) (hsigma : 0 < sigma) (hrs : 64/(M:ℝ) ≤ sigma)
    (p : Parent) (i j : Fin n) (k l : Index) (hk : k∈original i) (hl : l∈original j)
    (hj : parentLabel D a N j=p)
    (hcell : physicalCell D a N M p k=physicalCell D a N M p l)
    (hangle : localAngle D N p sigma i=localAngle D N p sigma j) (v : Fin 3) :
    |intercept (NativeLocalParentGeometry.line D a N p i) v-
      intercept (NativeLocalParentGeometry.line D a N p j) v| ≤ 5*sigma := by
  have hslope : |localSlope D N p i v-localSlope D N p j v| ≤ sigma := by
    apply same_floor_abs hsigma
    simpa only [localAngle,angle,localHorizontalSlope,ActualSlopeSource.heightPoint_castSucc] using congrFun hangle v
  exact scalar_intercept_spread hrs (front_equation D a N p i k v) (front_equation D a N p j l v)
    (source_front_error h original horiginal ha N M hM hscale p i k hk v.castSucc)
    (source_front_error h original horiginal ha N M hM hscale p j l hl v.castSucc)
    (physical_cell_gap D a N M hM p k l hcell v.castSucc)
    (physical_cell_gap D a N M hM p k l hcell 3)
    (physical_height_bound h original horiginal ha N p i k hk)
    (localSlope_bound D a N p j hj v) hslope

/-- Exact128 factor between the physical local intercept and the ORIGINAL
fine-parent intercept parameter. No contraction is dropped. -/
lemma original_intercept_difference {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N R : ℕ) (p : Parent) (i j : Fin n) (v : Fin 3) :
    (((N*R:ℕ):ℝ)*shiftedIntercept (D.line i) (mesh D) (shift D a) v-
      ((N*R:ℕ):ℝ)*shiftedIntercept (D.line j) (mesh D) (shift D a) v)=
      (128*(R:ℝ))*(intercept (NativeLocalParentGeometry.line D a N p i) v-
        intercept (NativeLocalParentGeometry.line D a N p j) v) := by
  rw [actual_local_intercept,actual_local_intercept]
  simp only [localIntercept]
  push_cast
  ring

end NativeCommonDirectionPhaseGeometry
