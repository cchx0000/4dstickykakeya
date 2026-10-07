import Theorems.Thm_StickyKakeya4_native_local_parent_physical_map
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
Independent reconstruction from the public canonical physical map.

The affine determinant is computed for the actual common map of the original
`N`-parent. No volume certificate is added to the source assumptions.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section

namespace NativeLocalParentVolume
open Classical MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeUnitParentNormalization NativeContractedUnitParent
open NativeLocalParentPhysicalMap
open scoped Matrix ENNReal

private def parentSlope (p : Parent) : Fin 4 → ℝ :=
  Fin.lastCases 0 (fun j => (p.1 j : ℝ))

private def spatialScale (N : ℕ) (i : Fin 4) : ℝ :=
  if i = 3 then 1 else N

/-- The derivative of the actual contracted, anisotropic parent map. -/
def matrix (N : ℕ) (p : Parent) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (if i = j then spatialScale N i / 512 else 0) -
    parentSlope p i * (if j = 3 then 1 / 512 else 0)

def rawLinear (N : ℕ) (p : Parent) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
  Matrix.toLin' (matrix N p)

def linearPart (N : ℕ) (p : Parent) : E4 →ₗ[ℝ] E4 :=
  let e := WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)
  e.symm.toLinearMap.comp ((rawLinear N p).comp e.toLinearMap)

lemma matrix_det (N : ℕ) (p : Parent) :
    (matrix N p).det = (N : ℝ)^3 / 512^4 := by
  have ht : (matrix N p).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    have hne : i ≠ j := ne_of_gt hij
    have hj : j ≠ (3 : Fin 4) := by omega
    simp only [matrix, if_neg hne, if_neg hj, mul_zero, sub_zero]
  have hd (i : Fin 4) : matrix N p i i = spatialScale N i / 512 := by
    by_cases hi : i = (3 : Fin 4)
    · subst i
      simp only [matrix, ite_true, parentSlope,
        show (3 : Fin 4) = Fin.last 3 by rfl, Fin.lastCases_last, zero_mul, sub_zero]
    · simp only [matrix, ite_true, if_neg hi, mul_zero, sub_zero]
  rw [Matrix.det_of_isUpperTriangular ht]
  simp_rw [hd]
  rw [Fin.prod_univ_four]
  simp only [spatialScale, if_neg (show (0 : Fin 4) ≠ 3 by decide),
    if_neg (show (1 : Fin 4) ≠ 3 by decide),
    if_neg (show (2 : Fin 4) ≠ 3 by decide), ite_true]
  ring

lemma linearPart_det (N : ℕ) (p : Parent) :
    LinearMap.det (linearPart N p) = (N : ℝ)^3 / 512^4 := by
  have he : LinearMap.det (linearPart N p) = LinearMap.det (rawLinear N p) := by
    simpa only [linearPart, LinearEquiv.symm_symm] using
      LinearMap.det_conj (rawLinear N p) (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm
  rw [he, rawLinear, LinearMap.det_toLin', matrix_det]

lemma linearPart_det_ne_zero (N : ℕ) (hN : 0 < N) (p : Parent) :
    LinearMap.det (linearPart N p) ≠ 0 := by
  rw [linearPart_det]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

lemma rawLinear_apply (N : ℕ) (p : Parent) (x : Fin 4 → ℝ) (i : Fin 4) :
    rawLinear N p x i =
      (spatialScale N i * x i - parentSlope p i * x 3) / 512 := by
  simp only [rawLinear, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, matrix,
    sub_mul, Finset.sum_sub_distrib]
  simp only [mul_assoc, ← Finset.mul_sum, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma linearPart_apply (N : ℕ) (p : Parent) (x : E4) (i : Fin 4) :
    linearPart N p x i =
      (spatialScale N i * x i - parentSlope p i * x 3) / 512 :=
  rawLinear_apply N p (WithLp.ofLp x) i

/-- This is an identity for the canonical map, including its actual translation. -/
lemma physicalMap_eq_linear_add {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (p : Parent) (x : E4) :
    NativeLocalParentPhysicalMap.physicalMap D a N p x =
      linearPart N p x + NativeLocalParentPhysicalMap.physicalMap D a N p 0 := by
  ext j
  rw [PiLp.add_apply, linearPart_apply]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [NativeLocalParentPhysicalMap.physicalMap, contractPoint,
      PiLp.smul_apply, smul_eq_mul, baseMap, ActualSlopeSource.heightPoint_last,
      parentSlope, Fin.lastCases_last, spatialScale,
      if_pos (show (Fin.last 3 : Fin 4) = 3 by rfl), PiLp.zero_apply]
    simp only [show (Fin.last 3 : Fin 4) = 3 by rfl]
    ring
  · have hj : j.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last j
    simp only [NativeLocalParentPhysicalMap.physicalMap, contractPoint,
      PiLp.smul_apply, smul_eq_mul, baseMap, ActualSlopeSource.heightPoint_castSucc,
      parentSlope, Fin.lastCases_castSucc, spatialScale, if_neg hj, PiLp.zero_apply]
    ring

lemma continuous_physicalMap {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (p : Parent) :
    Continuous (NativeLocalParentPhysicalMap.physicalMap D a N p) := by
  have he : NativeLocalParentPhysicalMap.physicalMap D a N p =
      (fun x => linearPart N p x + NativeLocalParentPhysicalMap.physicalMap D a N p 0) :=
    funext (physicalMap_eq_linear_add D a N p)
  rw [he]
  exact (linearPart N p).continuous_of_finiteDimensional.add continuous_const

/-- Positive spatial scaling makes the canonical physical map a homeomorphism. -/
def homeomorph {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (p : Parent) : E4 ≃ₜ E4 :=
  ((linearPart N p).equivOfDetNeZero (linearPart_det_ne_zero N hN p)).toContinuousLinearEquiv.toHomeomorph.trans
    (Homeomorph.addRight (NativeLocalParentPhysicalMap.physicalMap D a N p 0))

lemma homeomorph_apply {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (p : Parent) (x : E4) :
    homeomorph D a N hN p x = NativeLocalParentPhysicalMap.physicalMap D a N p x := by
  change linearPart N p x + NativeLocalParentPhysicalMap.physicalMap D a N p 0 = _
  exact (physicalMap_eq_linear_add D a N p x).symm

lemma measurableSet_image {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (p : Parent)
    {A : Set E4} (hA : MeasurableSet A) :
    MeasurableSet (NativeLocalParentPhysicalMap.physicalMap D a N p '' A) := by
  have he : (homeomorph D a N hN p : E4 → E4) =
      NativeLocalParentPhysicalMap.physicalMap D a N p :=
    funext (homeomorph_apply D a N hN p)
  rw [← he]
  exact (homeomorph D a N hN p).toMeasurableEquiv.measurableSet_image.mpr hA

lemma measurableSet_preimage {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (p : Parent) {A : Set E4} (hA : MeasurableSet A) :
    MeasurableSet (NativeLocalParentPhysicalMap.physicalMap D a N p ⁻¹' A) :=
  hA.preimage (continuous_physicalMap D a N p).measurable

/-- Exact four-dimensional volume scaling for every set under the actual map. -/
theorem volume_image {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (p : Parent) (A : Set E4) :
    volume (NativeLocalParentPhysicalMap.physicalMap D a N p '' A) =
      ENNReal.ofReal ((N : ℝ)^3 / 512^4) * volume A := by
  have he : NativeLocalParentPhysicalMap.physicalMap D a N p '' A =
      (fun x : E4 => x + NativeLocalParentPhysicalMap.physicalMap D a N p 0) ''
        (linearPart N p '' A) := by
    rw [Set.image_image]
    congr 1
    funext x
    exact physicalMap_eq_linear_add D a N p x
  rw [he]
  have ht (S : Set E4) :
      volume ((fun x : E4 => x + NativeLocalParentPhysicalMap.physicalMap D a N p 0) '' S) =
        volume S := by
    have hset :
        (fun x : E4 => x + NativeLocalParentPhysicalMap.physicalMap D a N p 0) '' S =
        (fun x : E4 => x + (-NativeLocalParentPhysicalMap.physicalMap D a N p 0)) ⁻¹' S := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa only [add_neg_cancel_right] using hy
      · intro hx
        exact ⟨x + -NativeLocalParentPhysicalMap.physicalMap D a N p 0, hx, by simp⟩
    rw [hset, measure_preimage_add_right]
  rw [ht, Measure.addHaar_image_linearMap, linearPart_det,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)^3 / 512^4)]

/-- Exact inverse-volume cost; only positivity of the actual parent scale is needed. -/
theorem volume_preimage {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (p : Parent) (A : Set E4) :
    volume (NativeLocalParentPhysicalMap.physicalMap D a N p ⁻¹' A) =
      ENNReal.ofReal (512^4 / (N : ℝ)^3) * volume A := by
  have he : NativeLocalParentPhysicalMap.physicalMap D a N p ⁻¹' A =
      linearPart N p ⁻¹'
        ((fun x : E4 => x + NativeLocalParentPhysicalMap.physicalMap D a N p 0) ⁻¹' A) := by
    ext x
    simp only [Set.mem_preimage]
    rw [physicalMap_eq_linear_add]
  rw [he, Measure.addHaar_preimage_linearMap volume (linearPart_det_ne_zero N hN p),
    measure_preimage_add_right, linearPart_det, inv_div,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 512^4 / (N : ℝ)^3)]

lemma convex_preimage {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (p : Parent) {A : Set E4} (hA : Convex ℝ A) :
    Convex ℝ (NativeLocalParentPhysicalMap.physicalMap D a N p ⁻¹' A) := by
  intro x hx y hy u v hu hv huv
  have hm : NativeLocalParentPhysicalMap.physicalMap D a N p (u • x + v • y) =
      u • NativeLocalParentPhysicalMap.physicalMap D a N p x +
        v • NativeLocalParentPhysicalMap.physicalMap D a N p y := by
    rw [physicalMap_eq_linear_add D a N p (u • x + v • y),
      physicalMap_eq_linear_add D a N p x, physicalMap_eq_linear_add D a N p y]
    simp only [map_add, map_smul]
    calc
      _ = u • linearPart N p x + v • linearPart N p y +
          (u + v) • NativeLocalParentPhysicalMap.physicalMap D a N p 0 := by
        rw [huv, one_smul]
      _ = _ := by module
  change NativeLocalParentPhysicalMap.physicalMap D a N p (u • x + v • y) ∈ A
  rw [hm]
  exact hA hx hy hu hv huv

end NativeLocalParentVolume
