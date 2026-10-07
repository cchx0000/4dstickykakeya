import Theorems.Thm_StickyKakeya4_native_grain_quotient_source
import Theorems.Thm_StickyKakeya4_native_graph_direction_in_plane

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeGrainHeightProjectionTransport
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeOriginalCellChartGeometry
open NativeHorizontalGrainSlice NativeDirectionRankDichotomy NativeLocalParentGeometry

/-- Linear direction induced by the actual parent's shear, before its1/512
physical contraction. This applies to arbitrary vectors, including height1. -/
def parentDirection (N : ℕ) (p : Parent) (v : E4) : E4 :=
  ActualSlopeSource.heightPoint
    (WithLp.toLp 2 (fun j : Fin 3 => (N:ℝ)*v j.castSucc-(p.1 j:ℝ)*v (3:Fin 4)))
    (v (3:Fin 4))

lemma parentDirection_last (N : ℕ) (p : Parent) (v : E4) :
    parentDirection N p v (3:Fin 4)=v (3:Fin 4) := rfl

/-- Equal-height direction differences cancel the parent shear exactly. -/
lemma parentDirection_sub (N : ℕ) (p : Parent) (v w : E4)
    (hvw : v (3:Fin 4)=w (3:Fin 4)) :
    parentDirection N p v-parentDirection N p w=(N:ℝ) • (v-w) := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · change v (3:Fin 4)-w (3:Fin 4)=(N:ℝ)*(v (3:Fin 4)-w (3:Fin 4))
    rw [hvw,sub_self,mul_zero]
  · simp only [parentDirection,ActualSlopeSource.heightPoint_castSucc,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    rw [hvw]
    ring

lemma parentDirection_slopeVector {n : ℕ} (D : FiniteScaleSource n) (N : ℕ)
    (p : Parent) (i : Fin n) :
    parentDirection N p (slopeVector D i)=northSlopeLift (localSlope D N p i) := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · change slopeVector D i (3:Fin 4)=1
    exact slopeVector_last D i
  · simp only [parentDirection,ActualSlopeSource.heightPoint_castSucc,northSlopeLift_castSucc]
    rw [slopeVector_last,mul_one]
    simp only [slopeVector,ActualSlopeSource.heightPoint_castSucc,localSlope]

lemma retained_direction_norm {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (i : Fin n) (hi : parentLabel D a N i=p) :
    ‖parentDirection N p (slopeVector D i)‖ ≤ 2 := by
  rw [parentDirection_slopeVector]
  exact NativeGraphMarkedLine.lift_norm_le_two _ (localSlope_bound D a N p i hi)

/-- Construct a graph direction in the old plane from an ACTUAL incidence
in the retained parent. Its normalized error retains the full N factor. -/
theorem exists_parent_controlled_direction {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (N : ℕ) (p : Parent)
    (i : Fin n) (hi : parentLabel D a N i=p) (Q : Submodule ℝ E4) (e : ℝ)
    (he : e ≤ 1/2) (hnear : Metric.infDist (slopeVector D i) (Q:Set E4) ≤ e) :
    ∃v∈Q,v (3:Fin 4)=1 ∧ dist v (slopeVector D i) ≤ 5*e ∧
      ‖v‖ ≤ 2+5*e ∧ ‖parentDirection N p v‖ ≤ 2+5*(N:ℝ)*e := by
  obtain ⟨v,hvQ,hv,hclose,hvn⟩ := NativeGraphDirectionInPlane.exists_near_graph_direction
    Q (slopeVector D i) e (slopeVector_last D i) (NativeRankOneSlopeCap.slopeVector_norm_le_two h i) he hnear
  have hd : dist (parentDirection N p v) (parentDirection N p (slopeVector D i)) ≤ 5*(N:ℝ)*e := by
    rw [dist_eq_norm,parentDirection_sub N p v (slopeVector D i) (hv.trans (slopeVector_last D i).symm),
      norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ) ≤ N)]
    have hh := mul_le_mul_of_nonneg_left hclose (by positivity : (0:ℝ) ≤ N)
    simpa only [dist_eq_norm,mul_left_comm,mul_assoc] using hh
  have hb := retained_direction_norm D a N p i hi
  have ht : ‖parentDirection N p v‖ ≤
      dist (parentDirection N p v) (parentDirection N p (slopeVector D i))+
        ‖parentDirection N p (slopeVector D i)‖ := by
    simpa only [dist_eq_norm,sub_add_cancel] using
      norm_add_le (parentDirection N p v-parentDirection N p (slopeVector D i))
        (parentDirection N p (slopeVector D i))
  exact ⟨v,hvQ,hv,hclose,hvn,by linarith⟩

/-- Move a raw point along one genuine graph direction to a common height. -/
def projectToHeight (v : E4) (s : ℝ) (x : E4) : E4 := x+(s-x (3:Fin 4)) • v

lemma projectToHeight_last {v : E4} (hv : v (3:Fin 4)=1) (s : ℝ) (x : E4) :
    projectToHeight v s x (3:Fin 4)=s := by simp [projectToHeight,hv]

lemma projectToHeight_sub (v : E4) (s : ℝ) (x y : E4) :
    projectToHeight v s x-projectToHeight v s y=removeHeight v (x-y) := by
  simp only [projectToHeight,removeHeight,PiLp.sub_apply]
  rw [sub_smul,sub_smul,sub_smul]
  abel

/-- Exact affine readback: the physical location changes by the displayed
vector. No original point is asserted to equal its height projection. -/
theorem physical_projectToHeight {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (v x : E4) (s : ℝ) :
    NativeLocalParentPhysicalMap.physicalMap D a N p (projectToHeight v s x)-
      NativeLocalParentPhysicalMap.physicalMap D a N p x=
        ((s-x (3:Fin 4))/512) • parentDirection N p v := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [NativeLocalParentPhysicalMap.physicalMap,NativeLocalParentPhysicalMap.baseMap,
      NativeContractedUnitParent.contractPoint,projectToHeight,parentDirection,
      ActualSlopeSource.heightPoint_last,PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul]
    ring
  · simp only [NativeLocalParentPhysicalMap.physicalMap,NativeLocalParentPhysicalMap.baseMap,
      NativeContractedUnitParent.contractPoint,projectToHeight,parentDirection,
      ActualSlopeSource.heightPoint_castSucc,PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul]
    ring

/-- The precise displacement bound keeps the raw time width and the parent
normalized direction norm as separate factors. -/
theorem physical_projection_displacement {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (v x : E4) (s T B : ℝ)
    (htime : |s-x (3:Fin 4)| ≤ T) (hv : ‖parentDirection N p v‖ ≤ B) :
    dist (NativeLocalParentPhysicalMap.physicalMap D a N p (projectToHeight v s x))
      (NativeLocalParentPhysicalMap.physicalMap D a N p x) ≤ T*B/512 := by
  rw [dist_eq_norm,physical_projectToHeight,norm_smul,Real.norm_eq_abs,
    abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
  have hh := mul_le_mul htime hv (norm_nonneg _) ((abs_nonneg _).trans htime)
  nlinarith only [hh]

lemma removeHeight_norm_general (v x : E4) :
    ‖removeHeight v x‖ ≤ (1+‖v‖)*‖x‖ := by
  have hc := PiLp.norm_apply_le x (3:Fin 4)
  have hh := mul_le_mul_of_nonneg_right hc (norm_nonneg v)
  calc
    _ ≤ ‖x‖+‖x (3:Fin 4) • v‖ := norm_sub_le _ _
    _ = ‖x‖+‖x (3:Fin 4)‖*‖v‖ := by rw [norm_smul]
    _ ≤ _ := by nlinarith only [hh]

/-- Projecting along a direction of the grain plane makes the ENTIRE grain
horizontal, with error controlled by its original thickness. -/
theorem projected_grain_near (Q : Submodule ℝ E4) {v : E4}
    (hvQ : v∈Q) (hv : v (3:Fin 4)=1) (s : ℝ) (x y : E4) :
    Metric.infDist (projectToHeight v s x-projectToHeight v s y) (sliceSpace Q:Set E4) ≤
      (1+‖v‖)*Metric.infDist (x-y) (Q:Set E4) := by
  let z := Q.starProjection (x-y)
  have hz : z∈Q := Q.starProjection_apply_mem _
  have hmem := removeHeight_mem_slice Q hvQ hv hz
  rw [projectToHeight_sub]
  calc
    _ ≤ dist (removeHeight v (x-y)) (removeHeight v z) := Metric.infDist_le_dist_of_mem hmem
    _ = ‖removeHeight v ((x-y)-z)‖ := by simp only [dist_eq_norm,removeHeight_sub]
    _ ≤ (1+‖v‖)*‖(x-y)-z‖ := removeHeight_norm_general _ _
    _ = _ := by rw [NativeEqualRankPlaneTransfer.projection_residual_eq_infDist]

end NativeGrainHeightProjectionTransport
