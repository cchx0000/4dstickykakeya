import Theorems.Thm_StickyKakeya4_native_original_parent_density_core
import Theorems.Thm_StickyKakeya4_native_same_source_balance_absorption
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section

namespace NativeReferenceCoreGlobalNear
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeIncidenceMultiplicityTower
open NativeSameSourceMultiplicityBalance NativeSameSourceBalanceAbsorption

/-- The actual returned source cost pays the complete original-incidence
retention factor. Thus a native near bound survives on the literal reference
core with only the stated cost exponent, without assuming a near bound for E. -/
theorem core_global_near {n : ℕ} {D : FiniteScaleSource n} {eta a zeta kappa theta b : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (heta : 0 ≤ eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (d g L : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) (scales : Fin g → ℕ)
    (hcore : IsCore D original R a eta zeta d g L Rel scales E)
    (hcost : (125 * 175616 * 16384 : ℝ) * (factor d g L : ℝ) *
      (coreRadix original R L : ℝ) ^ (2 : ℕ) * D.thickness ^ (-eta) ≤ D.thickness ^ (-b))
    (hnear : D.thickness ^ (-kappa + theta) ≤
      (NativeFiniteKakeyaCounts.multiplicity D).toReal) :
    D.thickness ^ (-kappa + theta + b) ≤ multiplicity E := by
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hE : E ⊆ incidences original := hcore.1.trans (filter_subset _ _)
  have hfactor : 0 < factor d g L := by
    have hret := hcore.2.2.1
    have hIpos := card_pos.mpr (hcore.2.1.mono hE)
    by_contra hnot
    have hz : factor d g L = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz, zero_mul] at hret
    omega
  have hQ4 : (4 : ℝ) ≤ (coreRadix original R L : ℝ) := by
    exact_mod_cast NativeSourceSizeBounds.radix_four_le (retained original R).card L
  have hQ1 : (1 : ℝ) ≤ (coreRadix original R L : ℝ) := by linarith
  have hQsq : (1 : ℝ) ≤ (coreRadix original R L : ℝ) ^ (2 : ℕ) := by
    simpa only [one_mul, pow_two] using mul_le_mul hQ1 hQ1 (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : (0 : ℝ) ≤ (coreRadix original R L : ℝ))
  have hp : 1 ≤ D.thickness ^ (-eta) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (neg_nonpos.mpr heta)
  have hcoefficient : 1 ≤ (125 * 175616 * 16384 : ℝ) *
      (coreRadix original R L : ℝ) ^ (2 : ℕ) * D.thickness ^ (-eta) := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) hQsq) hp
  have hfactorCost : (factor d g L : ℝ) ≤ D.thickness ^ (-b) := by
    calc
      _ = (factor d g L : ℝ) * 1 := (mul_one _).symm
      _ ≤ (factor d g L : ℝ) * ((125 * 175616 * 16384 : ℝ) *
          (coreRadix original R L : ℝ) ^ (2 : ℕ) * D.thickness ^ (-eta)) :=
        mul_le_mul_of_nonneg_left hcoefficient (Nat.cast_nonneg _)
      _ = (125 * 175616 * 16384 : ℝ) * (factor d g L : ℝ) *
          (coreRadix original R L : ℝ) ^ (2 : ℕ) * D.thickness ^ (-eta) := by ring
      _ ≤ _ := hcost
  have hselected := selected_source_near h original horiginal E hE (factor d g L) hfactor
    hcore.2.2.1 hnear
  have habsorbed := absorb_balance_cost (power := -kappa + theta) (loss := b) (X := 1)
    hd (NativeSameSourceMultiplicityBalance.multiplicity_nonneg E)
    (by simpa only [mul_one] using hselected) hfactorCost
  simpa only [mul_one] using habsorbed

end NativeReferenceCoreGlobalNear
