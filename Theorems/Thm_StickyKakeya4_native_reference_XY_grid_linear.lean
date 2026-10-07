import Theorems.Thm_StickyKakeya4_native_translated_grain_height_chart
import Theorems.Thm_StickyKakeya4_native_translated_grain_height_fibers

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeReferenceXYGridLinear
open Classical Finset StickyKakeya4 NativeHorizontalGrainSlice NativeHorizontalGraphCoordinates
open NativeGrainQuotientInjection NativeHeightSlopeCoordinates
open scoped BigOperators Matrix.Norms.Elementwise

/-- One bounded height field, fixed before any later core; zero off the
originally used translated heights, including on unused reference points. -/
def totalField {ell : ℕ} (used : Finset ℤ)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (t : ℤ) :
    Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ := if t∈used then F t else 0

lemma totalField_on {ell : ℕ} (used : Finset ℤ)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (t : ℤ) (ht : t∈used) :
    totalField used F t=F t := by simp only [totalField,if_pos ht]

lemma totalField_off {ell : ℕ} (used : Finset ℤ)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (t : ℤ) (ht : t∉used) :
    totalField used F t=0 := by simp only [totalField,if_neg ht]

lemma totalField_norm {ell : ℕ} (used : Finset ℤ)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (hF : ∀t∈used,‖F t‖ ≤ (1/4:ℝ)) (t : ℤ) : ‖totalField used F t‖ ≤ (1/4:ℝ) := by
  unfold totalField
  split_ifs with ht
  · exact hF t ht
  · norm_num

lemma euclidean_norm_le_sum {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ≤ ∑j : Fin d,|x j| := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have he : ∑j : Fin d,x j • b j=x := b.sum_repr x
  calc
    _ = ‖∑j : Fin d,x j • b j‖ := by rw [he]
    _ ≤ ∑j : Fin d,‖x j • b j‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul,Real.norm_eq_abs,b.orthonormal.norm_eq_one,mul_one]

/-- Elementwise matrix norm is converted to a true Euclidean action bound.
The rank restriction gives (ell-1)(4-ell)≤4; no operator-norm identification. -/
theorem matrix_action_norm (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (x : EuclideanSpace ℝ (Fin (ell-1))) : ‖M.toEuclideanLin x‖ ≤ ‖x‖ := by
  have hent (i : Fin (4-ell)) (j : Fin (ell-1)) : |M i j| ≤ (1/4:ℝ) := by
    simpa only [Real.norm_eq_abs] using (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1/4)).mp hM i j
  have hout (i : Fin (4-ell)) : |M.toEuclideanLin x i| ≤ ((ell-1:ℕ):ℝ)*(1/4:ℝ)*‖x‖ := by
    change |∑j : Fin (ell-1),M i j*x j| ≤ _
    calc
      _ ≤ ∑j : Fin (ell-1),|M i j*x j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑_j : Fin (ell-1),(1/4:ℝ)*‖x‖ := by
        apply sum_le_sum
        intro j _hj
        rw [abs_mul]
        exact mul_le_mul (hent i j) (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j)
          (abs_nonneg _) (by norm_num)
      _ = _ := by simp; ring
  have hab : (((ell-1:ℕ):ℝ))*((4-ell:ℕ):ℝ) ≤ 4 := by
    exact_mod_cast (show (ell-1)*(4-ell) ≤ 4 by interval_cases ell <;> norm_num)
  have hh := mul_le_mul_of_nonneg_right hab (norm_nonneg x)
  calc
    _ ≤ ∑i : Fin (4-ell),|M.toEuclideanLin x i| := euclidean_norm_le_sum _
    _ ≤ ∑_i : Fin (4-ell),((ell-1:ℕ):ℝ)*(1/4:ℝ)*‖x‖ := sum_le_sum (fun i _ => hout i)
    _ ≤ _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; nlinarith only [hh]

/-- The fixed orthonormal horizontal normal coordinates. -/
def normalCoordinates (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) :
    E4 →ₗ[ℝ] EuclideanSpace ℝ (Fin (4-ell)) :=
  (normalBasis P hP ell hell hell4 hd).repr.toLinearMap.comp (normalSpace P).orthogonalProjectionOnto.toLinearMap

lemma normalCoordinates_norm (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (x : E4) :
    ‖normalCoordinates P hP ell hell hell4 hd x‖=‖(normalSpace P).starProjection x‖ := by
  change ‖(normalBasis P hP ell hell hell4 hd).repr ((normalSpace P).orthogonalProjectionOnto x)‖=_
  rw [LinearIsometryEquiv.norm_map]
  rfl

lemma tangent_norm_le (P : Submodule ℝ E4) (ell : ℕ) (hd : Module.finrank ℝ P=ell-1) (x : E4) :
    ‖tangentCoordinates P ell hd x‖ ≤ ‖x‖ := by
  rw [tangentCoordinates_norm]
  exact P.norm_starProjection_apply_le x

lemma normal_norm_le (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (x : E4) :
    ‖normalCoordinates P hP ell hell hell4 hd x‖ ≤ ‖x‖ := by
  rw [normalCoordinates_norm]
  exact (normalSpace P).norm_starProjection_apply_le x

/-- Actual triangular quotient map for one fixed matrix at a reference height. -/
def quotientMap (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) : E4 →ₗ[ℝ] EuclideanSpace ℝ (Fin (4-ell)) :=
  normalCoordinates P hP ell hell hell4 hd-M.toEuclideanLin.comp (tangentCoordinates P ell hd)

lemma quotient_norm_le (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ)) (x : E4) :
    ‖quotientMap P hP ell hell hell4 hd M x‖ ≤ 2*‖x‖ := by
  have ht := tangent_norm_le P ell hd x
  have hn := normal_norm_le P hP ell hell hell4 hd x
  have hm := matrix_action_norm ell hell hell4 M hM (tangentCoordinates P ell hd x)
  have hh := norm_sub_le (normalCoordinates P hP ell hell hell4 hd x) (M.toEuclideanLin (tangentCoordinates P ell hd x))
  change ‖normalCoordinates P hP ell hell hell4 hd x-M.toEuclideanLin (tangentCoordinates P ell hd x)‖ ≤ _
  linarith

lemma normalProjection_horizontal (P : Submodule ℝ E4) (hP : P≤heightKernel)
    {x : E4} (hx : x∈heightKernel) : (normalSpace P).starProjection x=Pᗮ.starProjection x := by
  have hm : Pᗮ.starProjection x∈normalSpace P := by
    refine ⟨Pᗮ.starProjection_apply_mem x,?_⟩
    rw [Submodule.starProjection_orthogonal_val]
    exact heightKernel.sub_mem hx (hP (P.starProjection_apply_mem x))
  have hh := Submodule.orthogonalProjectionOnto_starProjection_of_le
    (show normalSpace P≤Pᗮ from inf_le_left) x
  have hcoe := congrArg (fun y : normalSpace P => (y:E4)) hh
  change (normalSpace P).starProjection (Pᗮ.starProjection x)=(normalSpace P).starProjection x at hcoe
  rw [(normalSpace P).starProjection_eq_self_iff.mpr hm] at hcoe
  exact hcoe.symm

lemma horizontal_inverse (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    {x : E4} (hx : x∈heightKernel) :
    ‖x‖ ≤ 2*‖tangentCoordinates P ell hd x‖+‖quotientMap P hP ell hell hell4 hd M x‖ := by
  have hdec : x=P.starProjection x+(normalSpace P).starProjection x := by
    rw [normalProjection_horizontal P hP hx,Submodule.starProjection_orthogonal_val]
    abel
  have hn : ‖x‖ ≤ ‖tangentCoordinates P ell hd x‖+‖normalCoordinates P hP ell hell hell4 hd x‖ := by
    rw [tangentCoordinates_norm,normalCoordinates_norm]
    simpa only [←hdec] using norm_add_le (P.starProjection x) ((normalSpace P).starProjection x)
  have hm := matrix_action_norm ell hell hell4 M hM (tangentCoordinates P ell hd x)
  have he : normalCoordinates P hP ell hell hell4 hd x=
      quotientMap P hP ell hell hell4 hd M x+M.toEuclideanLin (tangentCoordinates P ell hd x) := by
    change normalCoordinates P hP ell hell hell4 hd x=
      (normalCoordinates P hP ell hell hell4 hd x-M.toEuclideanLin (tangentCoordinates P ell hd x))+
        M.toEuclideanLin (tangentCoordinates P ell hd x)
    abel
  have hb := norm_add_le (quotientMap P hP ell hell hell4 hd M x) (M.toEuclideanLin (tangentCoordinates P ell hd x))
  rw [←he] at hb
  linarith

def vertical : E4 := EuclideanSpace.single (3:Fin 4) (1:ℝ)

lemma vertical_last : vertical (3:Fin 4)=1 := by simp [vertical]

lemma vertical_norm : ‖vertical‖=1 := by simp [vertical]

lemma vertical_orthogonal (P : Submodule ℝ E4) (hP : P≤heightKernel) : vertical∈Pᗮ := by
  apply (P.mem_orthogonal _).mpr
  intro u hu
  have hh : u (3:Fin 4)=0 := hP hu
  simp only [vertical,EuclideanSpace.inner_single_right,hh,map_zero,mul_zero]

lemma coordinates_remove_vertical (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (x : E4) :
    tangentCoordinates P ell hd (removeHeight vertical x)=tangentCoordinates P ell hd x ∧
      normalCoordinates P hP ell hell hell4 hd (removeHeight vertical x)=normalCoordinates P hP ell hell hell4 hd x := by
  have hp := P.orthogonalProjectionOnto_apply_of_mem_orthogonal (vertical_orthogonal P hP)
  have hn := (normalSpace P).orthogonalProjectionOnto_apply_of_mem_orthogonal
    (vertical_orthogonal (normalSpace P) inf_le_right)
  constructor
  · simp only [tangentCoordinates,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,removeHeight,map_sub,map_smul,hp,
      map_zero,smul_zero,sub_zero]
  · simp only [normalCoordinates,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,removeHeight,map_sub,map_smul,hn,
      map_zero,smul_zero,sub_zero]

/-- Full metric inverse with the actual vertical difference displayed. -/
theorem inverse_norm (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ)) (x : E4) :
    ‖x‖ ≤ 2*‖tangentCoordinates P ell hd x‖+‖quotientMap P hP ell hell hell4 hd M x‖+|x (3:Fin 4)| := by
  have hh := horizontal_inverse P hP ell hell hell4 hd M hM (removeHeight_mem_heightKernel vertical_last x)
  obtain ⟨ht,hn⟩ := coordinates_remove_vertical P hP ell hell hell4 hd x
  have hq : quotientMap P hP ell hell hell4 hd M (removeHeight vertical x)=quotientMap P hP ell hell hell4 hd M x := by
    change normalCoordinates P hP ell hell hell4 hd (removeHeight vertical x)-
      M.toEuclideanLin (tangentCoordinates P ell hd (removeHeight vertical x))=_
    rw [hn,ht]
    rfl
  rw [ht,hq] at hh
  have hnorm : ‖x‖ ≤ ‖removeHeight vertical x‖+|x (3:Fin 4)| := by
    have he : removeHeight vertical x+x (3:Fin 4) • vertical=x := by dsimp [removeHeight]; abel
    have hn := norm_add_le (removeHeight vertical x) (x (3:Fin 4) • vertical)
    rw [he,norm_smul,vertical_norm,mul_one,Real.norm_eq_abs] at hn
    exact hn
  linarith

end NativeReferenceXYGridLinear
