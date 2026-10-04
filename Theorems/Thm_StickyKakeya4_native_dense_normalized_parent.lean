import Theorems.Thm_StickyKakeya4_native_unit_parent_shadings
import Theorems.Thm_StickyKakeya4_native_dense_retained_unit_parent
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeDenseNormalizedParent
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeOriginalPrunedMass
open NativeUnitParentNormalization NativeUnitParentShadings NativeDenseRetainedUnitParent
open scoped BigOperators

def realNormalizedShadingMass {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (p : Parent) : ℝ := ∑i∈R,(volume (shading D a p i)).toReal
def realPaddedTubeMass {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (p : Parent) : ℝ := ∑i∈R,
      (volume (markedUnitTube (newLine (D.line i) (mesh D) (shift D a) p) (D.thickness/2))).toReal

lemma realNormalizedShadingMass_eq {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (p : Parent) : realNormalizedShadingMass D R a p=realShadingMass D R/65536 := by
  simp only [realNormalizedShadingMass,shading,NativeUnitParentVolume.volume_image,ENNReal.toReal_mul]
  norm_num
  simp only [realShadingMass,div_eq_mul_inv,one_mul,mul_comm]
  rw [Finset.mul_sum]

lemma realPaddedTubeMass_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hsmall : D.thickness ≤ 1/8)
    (R : Finset (Fin n)) (p : Parent) (hp : ∀i∈R,parentLabel D a 1 i=p) :
    realPaddedTubeMass D R a p ≤ 256*realTubeMass D R := by
  unfold realPaddedTubeMass realTubeMass
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have ht : 256*volume (markedUnitTube (D.line i) D.thickness) ≠ ⊤ := by
    apply ENNReal.mul_ne_top (by norm_num)
    exact ne_top_of_le_ne_top (by finiteness) (tube_volume_upper h i)
  have hh := ENNReal.toReal_mono ht (padded_tube_volume_le_original h hsmall p i (hp i hi))
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat] using hh

/-- A dense unit parent is selected from the SAME retained original R. The
normalized density is bounded below by an explicit fixed fraction of R's
actual original shading/tube-volume ratio. No density certificate is added. -/
theorem exists_dense_normalized_parent {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (hR : R.Nonempty) (hshade : 0 < shadingMass D R) (hsmall : D.thickness ≤ 1/8) :
    ∃ p∈R.image (parentLabel D a 1), (parentSubset D R a p).Nonempty ∧
      0 < realShadingMass D (parentSubset D R a p) ∧
      realShadingMass D R ≤ 2*((R.image (parentLabel D a 1)).card:ℝ)*
        realShadingMass D (parentSubset D R a p) ∧
      (realShadingMass D R/realTubeMass D R)/33554432 *
          realPaddedTubeMass D (parentSubset D R a p) a p ≤ 
        realNormalizedShadingMass D (parentSubset D R a p) a p := by
  obtain ⟨p,hp,hQ,hpos,hret,hden⟩ := exists_dense_retained_volume_parent h R a hR hshade hsmall
  have hT := realTubeMass_pos h R hR hsmall
  let lam := realShadingMass D R/realTubeMass D R
  have hlam : 0 ≤ lam := div_nonneg (sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)) hT.le
  have hdens : lam*realTubeMass D (parentSubset D R a p) ≤ 
      2*realShadingMass D (parentSubset D R a p) :=
    retained_parent_density h R a hR hsmall p (by dsimp [lam]; rw [div_mul_cancel₀ _ hT.ne']) hden
  have hnew := realPaddedTubeMass_le h hsmall (parentSubset D R a p) p
    (fun i hi=>(mem_filter.mp hi).2)
  refine ⟨p,hp,hQ,hpos,hret,?_⟩
  rw [realNormalizedShadingMass_eq]
  change lam/33554432*realPaddedTubeMass D (parentSubset D R a p) a p ≤ _
  calc
    _ ≤ lam/33554432*(256*realTubeMass D (parentSubset D R a p)) :=
      mul_le_mul_of_nonneg_left hnew (by positivity)
    _ = (lam*realTubeMass D (parentSubset D R a p))/131072 := by ring
    _ ≤ (2*realShadingMass D (parentSubset D R a p))/131072 :=
      div_le_div_of_nonneg_right hdens (by norm_num)
    _ = _ := by ring
end NativeDenseNormalizedParent
