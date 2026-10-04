import Theorems.Thm_StickyKakeya4_native_compact_ancestor_budget
import Theorems.Thm_StickyKakeya4_native_finite_kakeya_counts
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeOriginalPrunedMass
open Classical Finset MeasureTheory StickyKakeya4
open scoped ENNReal BigOperators

def shadingMass {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) : ℝ≥0∞ :=
  ∑i∈R,volume (D.shading i)
def tubeMass {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) : ℝ≥0∞ :=
  ∑i∈R,volume (markedUnitTube (D.line i) D.thickness)
def volumeConstant : ℝ := 32*(Real.pi^2/2)
lemma volumeConstant_pos : 0<volumeConstant := by dsimp [volumeConstant]; positivity

lemma tube_volume_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (i : Fin n) :
    volume (markedUnitTube (D.line i) D.thickness)≤
      ENNReal.ofReal volumeConstant*(ENNReal.ofReal D.thickness)^3 := by
  have hh := volume_markedUnitTube_upper_bound (h.1.2.2.2.2.1 i) h.1.2.1 h.1.2.2.1
  calc
    _ ≤ 32*(ENNReal.ofReal D.thickness)^3*ENNReal.ofReal (Real.pi^2/2) := hh
    _ = _ := by
      rw [volumeConstant,ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤32),ENNReal.ofReal_ofNat]
      ring


lemma shadingMass_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) :
    shadingMass D R≤R.card*(ENNReal.ofReal volumeConstant*(ENNReal.ofReal D.thickness)^3) := by
  calc
    _ ≤ ∑_i∈R,ENNReal.ofReal volumeConstant*(ENNReal.ofReal D.thickness)^3 := by
      apply sum_le_sum
      intro i _hi
      exact (measure_mono (h.1.2.2.2.2.2.2.2.2.1 i)).trans (tube_volume_upper h i)
    _ = _ := by simp
lemma shadingMass_ne_top {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) :
    shadingMass D R≠⊤ := ne_top_of_le_ne_top (by finiteness) (shadingMass_upper h R)
lemma shadingMass_partition {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) :
    shadingMass D R+shadingMass D (univ\R)=wzTotalShadingVolume D := by
  simpa only [shadingMass,wzTotalShadingVolume,add_comm] using
    sum_sdiff (show R⊆univ from subset_univ R) (f:=fun i=>volume (D.shading i))
lemma tubeMass_le_total {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) :
    tubeMass D R≤wzTotalTubeVolume D := sum_le_sum_of_subset (subset_univ R)

/-- Small actual removed shading mass preserves half of original shading
mass and half of the original native density on the unchanged retained tubes. -/
theorem retained_shading_density {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (hsmall : 2*shadingMass D (univ\R)≤
      (ENNReal.ofReal D.thickness).rpow eta*wzTotalTubeVolume D) :
    wzTotalShadingVolume D≤2*shadingMass D R ∧
      (ENNReal.ofReal D.thickness).rpow eta*tubeMass D R≤2*shadingMass D R := by
  have hden := h.1.2.2.2.2.2.2.2.2.2.2.2.2
  have hpart := shadingMass_partition D R
  have hlost : shadingMass D (univ\R)≤ shadingMass D R := by
    apply (ENNReal.add_le_add_iff_right (shadingMass_ne_top h (univ\R))).mp
    calc
      _ = 2*shadingMass D (univ\R) := by rw [two_mul]
      _ ≤ _ := hsmall.trans hden
      _ = _ := hpart.symm
  have hret : wzTotalShadingVolume D≤2*shadingMass D R := by
    rw [←hpart,two_mul]
    exact add_le_add le_rfl hlost
  exact ⟨hret,(mul_le_mul' le_rfl (tubeMass_le_total D R)).trans (hden.trans hret)⟩

/-- CW inheritance for the actual retained original tube labels has exactly
the original-to-retained tube-count ratio; half retention costs only two. -/
theorem retained_convexWolff {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (hret : n≤2*R.card)
    (U : Set E4) (hU : Convex ℝ U) :
    ((R.filter (fun i=>markedUnitTube (D.line i) D.thickness⊆U)).card:ℝ≥0∞)≤
      2*(ENNReal.ofReal D.thickness).rpow (-eta)*volume U*R.card := by
  have hc : (R.filter (fun i=>markedUnitTube (D.line i) D.thickness⊆U)).card≤
      wzContainedTubeCount D U := card_le_card (filter_subset_filter _ (subset_univ R))
  calc
    _ ≤ (wzContainedTubeCount D U:ℝ≥0∞) := by exact_mod_cast hc
    _ ≤ (ENNReal.ofReal D.thickness).rpow (-eta)*volume U*n := h.1.2.2.2.2.2.2.2.2.2.2.2.1 U hU
    _ ≤ (ENNReal.ofReal D.thickness).rpow (-eta)*volume U*(2*R.card) :=
      mul_le_mul' le_rfl (by exact_mod_cast hret)
    _ = _ := by ring

end NativeOriginalPrunedMass
