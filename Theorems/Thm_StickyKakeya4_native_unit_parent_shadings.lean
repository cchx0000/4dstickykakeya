import Theorems.Thm_StickyKakeya4_native_unit_parent_volume
import Theorems.Thm_StickyKakeya4_native_original_pruned_mass
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeUnitParentShadings
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeUnitParentNormalization NativeUnitParentVolume NativeOriginalPrunedMass
open scoped ENNReal BigOperators

/-- The transformed shading is the actual affine image of the original shading. -/
def shading {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (p : Parent) (i : Fin n) : Set E4 :=
  pointMap ((shift D a:ℝ)*mesh D) p '' D.shading i

lemma shading_measurable {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (p : Parent) (i : Fin n) :
    MeasurableSet (shading D a p i) := measurableSet_image _ _ (h.1.2.2.2.2.2.2.1 i)

lemma shading_subset_tube {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (p : Parent) (i : Fin n) (hp : parentLabel D a 1 i=p) :
    shading D a p i ⊆ markedUnitTube (newLine (D.line i) (mesh D) (shift D a) p) (D.thickness/2) :=
  (Set.image_mono (h.1.2.2.2.2.2.2.2.2.1 i)).trans (original_tube_maps_into_padded_tube h ha p i hp)

/-- Exact summed density mass on the same retained original labels. -/
theorem shading_sum_volume {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (p : Parent) :
    (∑i∈R,volume (shading D a p i))=ENNReal.ofReal (1/65536)*shadingMass D R := by
  simp only [shading,volume_image,shadingMass,mul_sum]

/-- The actual shaded union has the same exact affine volume scaling. -/
theorem shading_union_volume {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (p : Parent) :
    volume (⋃i∈R,shading D a p i)=
      ENNReal.ofReal (1/65536)*volume (⋃i∈R,D.shading i) := by
  have he : (⋃i∈R,shading D a p i)=pointMap ((shift D a:ℝ)*mesh D) p '' (⋃i∈R,D.shading i) := by
    simp only [shading,Set.image_iUnion]
  rw [he,volume_image]

/-- CW for the actual padded tubes follows from original CW and the fixed
Jacobian. The original-to-retained count is kept visible as the original n. -/
theorem original_CW_to_padded {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (p : Parent) (hp : ∀i∈R,parentLabel D a 1 i=p)
    (U : Set E4) (hU : Convex ℝ U) :
    ((R.filter (fun i=>markedUnitTube (newLine (D.line i) (mesh D) (shift D a) p)
        (D.thickness/2) ⊆ U)).card:ℝ≥0∞) ≤ 
      65536*(ENNReal.ofReal D.thickness).rpow (-eta)*volume U*n := by
  let F := pointMap ((shift D a:ℝ)*mesh D) p
  have hcount : (R.filter (fun i=>markedUnitTube (newLine (D.line i) (mesh D) (shift D a) p)
      (D.thickness/2) ⊆ U)).card ≤ wzContainedTubeCount D (F ⁻¹' U) := by
    apply card_le_card
    intro i hi
    obtain ⟨hiR,hiU⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    intro x hx
    exact hiU (original_tube_maps_into_padded_tube h ha p i (hp i hiR) (Set.mem_image_of_mem F hx))
  have hcw := h.1.2.2.2.2.2.2.2.2.2.2.2.1 (F ⁻¹' U) (convex_preimage _ _ hU)
  have hv : volume (F ⁻¹' U)=65536*volume U := volume_preimage _ _ _
  rw [hv] at hcw
  exact (show _ ≤ (wzContainedTubeCount D (F ⁻¹' U):ℝ≥0∞) by exact_mod_cast hcount).trans
    (hcw.trans_eq (by ring))

/-- Unit-length padding has a fixed actual tube-volume cost, derived from the
original and padded geometric tube estimates. -/
theorem padded_tube_volume_le_original {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hsmall : D.thickness ≤ 1/8)
    (p : Parent) (i : Fin n) (hp : parentLabel D a 1 i=p) :
    volume (markedUnitTube (newLine (D.line i) (mesh D) (shift D a) p) (D.thickness/2)) ≤ 
      256*volume (markedUnitTube (D.line i) D.thickness) := by
  have hu := volume_markedUnitTube_upper_bound (padded_line_common_slab D a p i hp).1
    (half_pos h.1.2.1) (by linarith [h.1.2.2.1] : D.thickness/2 ≤ 1)
  have hl := volume_markedUnitTube_lower_bound (h.1.2.2.2.2.1 i) h.1.2.1 hsmall
  have hmesh : ENNReal.ofReal (D.thickness/2) ≤ ENNReal.ofReal D.thickness :=
    ENNReal.ofReal_le_ofReal (by linarith [h.1.2.1])
  calc
    _ ≤ 32*(ENNReal.ofReal D.thickness)^3*ENNReal.ofReal (Real.pi^2/2) :=
      hu.trans (mul_le_mul' (mul_le_mul' le_rfl (pow_le_pow_left' hmesh 3)) le_rfl)
    _ = 256*(ENNReal.ofReal (1/8:ℝ)*(ENNReal.ofReal D.thickness)^3*
        ENNReal.ofReal (Real.pi^2/2)) := by
      have hc : ENNReal.ofReal (1/8:ℝ)*(256:ℝ≥0∞)=32 := by
        rw [←ENNReal.ofReal_ofNat,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/8)]
        norm_num
      calc
        _ = (ENNReal.ofReal (1/8:ℝ)*256)*((ENNReal.ofReal D.thickness)^3*ENNReal.ofReal (Real.pi^2/2)) := by rw [hc]; ring
        _ = _ := by ring
    _ ≤ _ := mul_le_mul' le_rfl hl
end NativeUnitParentShadings
