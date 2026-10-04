import Theorems.Thm_StickyKakeya4_native_unit_parent_normalization
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeUnitParentVolume
open Classical MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeUnitParentNormalization
open scoped Matrix ENNReal

private def parentSlope (p : Parent) : Fin 4 → ℝ := Fin.lastCases 0 (fun j => (p.1 j:ℝ))
def matrix (p : Parent) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (if i=j then 1/16 else 0)-parentSlope p i*(if j=3 then 1/16 else 0)
def rawLinear (p : Parent) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) := Matrix.toLin' (matrix p)
def linearPart (p : Parent) : E4 →ₗ[ℝ] E4 :=
  let e := WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)
  e.symm.toLinearMap.comp ((rawLinear p).comp e.toLinearMap)

lemma matrix_det (p : Parent) : (matrix p).det = 1/65536 := by
  have ht : (matrix p).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    have hne : i≠j := ne_of_gt hij
    have hj : j≠(3:Fin 4) := by omega
    simp only [matrix,if_neg hne,if_neg hj,mul_zero,sub_zero]
  have hd (i : Fin 4) : matrix p i i=1/16 := by
    by_cases hi : i=(3:Fin 4)
    · subst i
      simp only [matrix,ite_true,parentSlope,show (3:Fin 4)=Fin.last 3 by rfl,Fin.lastCases_last,zero_mul,sub_zero]
    · simp only [matrix,ite_true,if_neg hi,mul_zero,sub_zero]
  rw [Matrix.det_of_isUpperTriangular ht]
  simp_rw [hd]
  norm_num

lemma linearPart_det (p : Parent) : LinearMap.det (linearPart p) = 1/65536 := by
  have he : LinearMap.det (linearPart p)=LinearMap.det (rawLinear p) := by
    simpa only [linearPart,LinearEquiv.symm_symm] using
      LinearMap.det_conj (rawLinear p) (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm
  rw [he,rawLinear,LinearMap.det_toLin',matrix_det]

lemma rawLinear_apply (p : Parent) (x : Fin 4 → ℝ) (i : Fin 4) :
    rawLinear p x i=(x i-parentSlope p i*x 3)/16 := by
  simp only [rawLinear,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,matrix,sub_mul,Finset.sum_sub_distrib]
  simp only [mul_assoc,←Finset.mul_sum,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

lemma linearPart_apply (p : Parent) (x : E4) (i : Fin 4) :
    linearPart p x i=(x i-parentSlope p i*x 3)/16 := rawLinear_apply p (WithLp.ofLp x) i

lemma pointMap_eq_linear_add (s : ℝ) (p : Parent) (x : E4) :
    pointMap s p x=linearPart p x+pointMap s p 0 := by
  ext j
  rw [PiLp.add_apply,linearPart_apply]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [pointMap,ActualSlopeSource.heightPoint_last,parentSlope,Fin.lastCases_last]
    change (x (3:Fin 4)-s)/16=(x (3:Fin 4)-0*x 3)/16+(0-s)/16
    ring
  · simp only [pointMap,ActualSlopeSource.heightPoint_castSucc,parentSlope,Fin.lastCases_castSucc,PiLp.zero_apply]
    ring

lemma continuous_pointMap (s : ℝ) (p : Parent) : Continuous (pointMap s p) := by
  have he : pointMap s p=(fun x=>linearPart p x+pointMap s p 0) := funext (pointMap_eq_linear_add s p)
  rw [he]
  exact (linearPart p).continuous_of_finiteDimensional.add continuous_const

lemma continuous_pointInv (s : ℝ) (p : Parent) : Continuous (pointInv s p) := by
  unfold pointInv ActualSlopeSource.heightPoint
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [Fin.lastCases_last]
    fun_prop
  · simp only [Fin.lastCases_castSucc]
    fun_prop

/-- The actual original-coordinate normalization is a homeomorphism. -/
def homeomorph (s : ℝ) (p : Parent) : E4 ≃ₜ E4 where
  toFun := pointMap s p
  invFun := pointInv s p
  left_inv := pointInv_pointMap s p
  right_inv := pointMap_pointInv s p
  continuous_toFun := continuous_pointMap s p
  continuous_invFun := continuous_pointInv s p

lemma measurableSet_image (s : ℝ) (p : Parent) {A : Set E4} (hA : MeasurableSet A) :
    MeasurableSet (pointMap s p '' A) := (homeomorph s p).toMeasurableEquiv.measurableSet_image.mpr hA

/-- Exact volume of every actual affine image, including arbitrary original shadings. -/
theorem volume_image (s : ℝ) (p : Parent) (A : Set E4) :
    volume (pointMap s p '' A) = ENNReal.ofReal (1/65536) * volume A := by
  have he : pointMap s p '' A =
      (fun x : E4 => x + pointMap s p 0) '' (linearPart p '' A) := by
    rw [Set.image_image]
    congr 1
    funext x
    exact pointMap_eq_linear_add s p x
  rw [he]
  have ht (S : Set E4) : volume ((fun x : E4 => x+pointMap s p 0) '' S)=volume S := by
    have hset : (fun x : E4 => x+pointMap s p 0) '' S =
        (fun x : E4 => x+(-pointMap s p 0)) ⁻¹' S := by
      ext x
      simp only [Set.mem_image,Set.mem_preimage]
      constructor
      · rintro ⟨y,hy,rfl⟩
        simpa only [add_neg_cancel_right] using hy
      · intro hx
        exact ⟨x+-pointMap s p 0,hx,by simp⟩
    rw [hset,measure_preimage_add_right]
  rw [ht,Measure.addHaar_image_linearMap,linearPart_det]
  norm_num

/-- The inverse-volume cost in CW is the fixed determinant reciprocal. -/
theorem volume_preimage (s : ℝ) (p : Parent) (A : Set E4) :
    volume (pointMap s p ⁻¹' A) = 65536 * volume A := by
  have h := volume_image s p (pointMap s p ⁻¹' A)
  have hsurj : Function.Surjective (pointMap s p) := (homeomorph s p).surjective
  rw [Set.image_preimage_eq _ hsurj] at h
  have he : (ENNReal.ofReal (1/65536):ℝ≥0∞) = (65536:ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num only [ENNReal.ofReal_one,ENNReal.ofReal_ofNat,one_div]
  rw [he] at h
  rw [h]
  rw [←mul_assoc,ENNReal.mul_inv_cancel (by norm_num) (by norm_num),one_mul]

lemma convex_preimage (s : ℝ) (p : Parent) {A : Set E4} (hA : Convex ℝ A) :
    Convex ℝ (pointMap s p ⁻¹' A) := by
  intro x hx y hy u v hu hv huv
  have hm : pointMap s p (u • x + v • y)=u • pointMap s p x+v • pointMap s p y := by
    rw [pointMap_eq_linear_add s p (u • x+v • y),pointMap_eq_linear_add s p x,
      pointMap_eq_linear_add s p y]
    simp only [map_add,map_smul]
    calc
      _ = u • linearPart p x+v • linearPart p y+(u+v) • pointMap s p 0 := by rw [huv,one_smul]
      _ = _ := by module
  change pointMap s p (u • x+v • y) ∈ A
  rw [hm]
  exact hA hx hy hu hv huv
end NativeUnitParentVolume
