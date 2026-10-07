import Theorems.Thm_StickyKakeya4_native_grain_height_projection_transport
import Theorems.Thm_StickyKakeya4_native_incident_affine_anchor_geometry
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_linear

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeSlabParentNormalization
open Classical StickyKakeya4 NativeOriginalParentSelection NativeOriginalCellChartGeometry
open NativeHorizontalGrainSlice NativeDirectionRankDichotomy NativeLocalParentGeometry
open NativeGrainHeightProjectionTransport NativeIncidentAffineAnchorGeometry
open NativeReferenceXYGridLinear NativeGrainQuotientInjection

/-- Inverse of the actual parent direction shear, with no physical1/512
contraction: graph slopes use the same spatial/time contraction ratio. -/
def unparentDirection (N : ℕ) (p : Parent) (v : E4) : E4 :=
  ActualSlopeSource.heightPoint
    (WithLp.toLp 2 (fun j : Fin 3 => (v j.castSucc+(p.1 j:ℝ)*v (3:Fin 4))/(N:ℝ)))
    (v (3:Fin 4))

lemma unparentDirection_last (N : ℕ) (p : Parent) (v : E4) :
    unparentDirection N p v (3:Fin 4)=v (3:Fin 4) := rfl

lemma unparent_parent (N : ℕ) (hN : 0 < N) (p : Parent) (v : E4) :
    unparentDirection N p (parentDirection N p v)=v := by
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rfl
  · rw [unparentDirection,ActualSlopeSource.heightPoint_castSucc,parentDirection_last]
    simp only [parentDirection,ActualSlopeSource.heightPoint_castSucc]
    field_simp
    ring

lemma parent_unparent (N : ℕ) (hN : 0 < N) (p : Parent) (v : E4) :
    parentDirection N p (unparentDirection N p v)=v := by
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rfl
  · rw [parentDirection,ActualSlopeSource.heightPoint_castSucc,unparentDirection_last]
    simp only [unparentDirection,ActualSlopeSource.heightPoint_castSucc]
    field_simp
    ring

/-- The parent normalization is an actual linear equivalence on E4. -/
def parentEquiv (N : ℕ) (hN : 0 < N) (p : Parent) : E4 ≃ₗ[ℝ] E4 where
  toFun := parentDirection N p
  invFun := unparentDirection N p
  left_inv := unparent_parent N hN p
  right_inv := parent_unparent N hN p
  map_add' x y := by
    ext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rfl
    · simp only [parentDirection,ActualSlopeSource.heightPoint_castSucc,PiLp.add_apply]
      ring
  map_smul' r x := by
    ext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rfl
    · simp only [parentDirection,ActualSlopeSource.heightPoint_castSucc,PiLp.smul_apply,smul_eq_mul,RingHom.id_apply]
      ring

lemma parentEquiv_apply (N : ℕ) (hN : 0 < N) (p : Parent) (v : E4) :
    parentEquiv N hN p v=parentDirection N p v := rfl

lemma parentEquiv_symm_apply (N : ℕ) (hN : 0 < N) (p : Parent) (v : E4) :
    (parentEquiv N hN p).symm v=unparentDirection N p v := rfl

/-- Equal heights cancel the shear exactly, leaving precisely1/N. -/
lemma unparentDirection_sub (N : ℕ) (p : Parent) (v w : E4)
    (hvw : v (3:Fin 4)=w (3:Fin 4)) :
    unparentDirection N p v-unparentDirection N p w=(1/(N:ℝ)) • (v-w) := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · change v (3:Fin 4)-w (3:Fin 4)=(1/(N:ℝ))*(v (3:Fin 4)-w (3:Fin 4))
    rw [hvw,sub_self,mul_zero]
  · simp only [unparentDirection,ActualSlopeSource.heightPoint_castSucc,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    rw [hvw]
    ring

lemma unparent_distance (N : ℕ) (p : Parent) (v w : E4)
    (hvw : v (3:Fin 4)=w (3:Fin 4)) :
    dist (unparentDirection N p v) (unparentDirection N p w)=dist v w/(N:ℝ) := by
  rw [dist_eq_norm,unparentDirection_sub N p v w hvw,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ)≤1/(N:ℝ)),dist_eq_norm]
  ring

lemma parentDirection_lift {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (p : Parent) (i : Fin n) :
    parentDirection N p (slopeVector D i)=localHorizontalSlope D N p i+vertical := by
  rw [parentDirection_slopeVector]
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · change northSlopeLift (localSlope D N p i) (Fin.last 3)=
      ActualSlopeSource.heightPoint (localSlope D N p i) 0 (Fin.last 3)+vertical (Fin.last 3)
    rw [northSlopeLift_last,ActualSlopeSource.heightPoint_last,show vertical (Fin.last 3)=1 from vertical_last]
    norm_num
  · have hj : j.castSucc≠(3:Fin 4) := ne_of_lt (Fin.castSucc_lt_last j)
    have hv : vertical j.castSucc=0 := by simp [vertical,hj]
    simp only [PiLp.add_apply,northSlopeLift_castSucc,localHorizontalSlope,ActualSlopeSource.heightPoint_castSucc,hv,add_zero]

/-- Read the source's actual horizontal slope coordinates from its genuine
height-one normalized direction; no projected direction replaces the tube. -/
lemma parent_coordinates {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (p : Parent) (i : Fin n)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) :
    tangentCoordinates P ell hd (parentDirection N p (slopeVector D i))=
      tangentCoordinates P ell hd (localHorizontalSlope D N p i) ∧
    quotientMap P hP ell hell hell4 hd M (parentDirection N p (slopeVector D i))=
      quotientMap P hP ell hell hell4 hd M (localHorizontalSlope D N p i) := by
  have hrem : removeHeight vertical (parentDirection N p (slopeVector D i))=localHorizontalSlope D N p i := by
    unfold removeHeight
    rw [parentDirection_last,slopeVector_last,one_smul,parentDirection_lift]
    abel
  obtain ⟨ht,hn⟩ := coordinates_remove_vertical P hP ell hell hell4 hd (parentDirection N p (slopeVector D i))
  rw [hrem] at ht hn
  refine ⟨ht.symm,?_⟩
  simp only [quotientMap,LinearMap.sub_apply,LinearMap.comp_apply]
  rw [←ht,←hn]

end NativeSlabParentNormalization
