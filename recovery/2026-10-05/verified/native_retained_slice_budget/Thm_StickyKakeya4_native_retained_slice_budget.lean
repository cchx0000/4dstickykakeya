import Theorems.Thm_StickyKakeya4_native_retained_slice_core
import Theorems.Thm_StickyKakeya4_native_second_refinement_cost
import Theorems.Thm_StickyKakeya4_native_two_stage_transversality_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeRetainedSliceBudget
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeRetainedSliceCore NativeOriginalParentDensityCore NativeSecondRefinementCost NativeOriginalParentSelection

/-- The third refinement's retention cost and FOUR radix powers are paid
before the source and before the actual cleaned subset are known. -/
theorem exists_retained_slice_budget (cost : ℝ) (hcost : 0 < cost) (d K : ℕ) :
    ∃L : ℕ,0 < L ∧ ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
        IsWangZakharovNativeFiniteInput D eta → D.thickness ≤ delta0 →
        0 ≤ eta → eta ≤ cost/8 →
        ∀original : Fin n → Finset Index,
          (∀i,D.shading i=wzCellShading (mesh D) original i) →
          ∀H : Finset (Fin n × Index),H⊆incidences original → H.Nonempty →
            (refinementCost d K L:ℝ)*(NativeSourceSizeBounds.radix H.card L:ℝ)^4 ≤
              D.thickness^(-cost) := by
  obtain ⟨L,hL,delta0,hd0,hd01,hbudget⟩ := exists_second_refinement_cost
    (cost/2) (half_pos hcost) (d+(1+K)) 0
  refine ⟨L,hL,delta0,hd0,hd01,?_⟩
  intro n D eta h hsmall heta hetaSmall original horiginal H hH hHn
  let Q := NativeSourceSizeBounds.radix H.card L
  let C : ℝ := refinementCost d K L
  have hraw := hbudget n D eta h hsmall (by linarith only [hetaSmall]) original horiginal H hH hHn
  have hCF : C ≤ (factor (d+(1+K)) 0 L:ℝ) := by
    dsimp only [C,refinementCost]
    exact_mod_cast retained_cost_le_factor (d+(1+K)) 0 L (by omega)
  have hCQ : C*(Q:ℝ)^2 ≤ D.thickness^(-(cost/2)) :=
    NativeTwoStageTransversalityBudget.retention_radix_le_of_transfer_cost
      h.1.2.1 (hsmall.trans hd01) heta (factor (d+(1+K)) 0 L) Q C hCF hraw
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (refinementCost_pos d K L).ne'
  have hCC : C ≤ C^2 := by nlinarith only [hC1]
  change C*(Q:ℝ)^4 ≤ D.thickness^(-cost)
  calc
    _ ≤ C^2*(Q:ℝ)^4 := mul_le_mul_of_nonneg_right hCC (pow_nonneg (Nat.cast_nonneg _) _)
    _ = (C*(Q:ℝ)^2)^2 := by ring
    _ ≤ (D.thickness^(-(cost/2)))^2 := pow_le_pow_left₀ (by positivity) hCQ 2
    _ = _ := by
      rw [pow_two,←Real.rpow_add h.1.2.1]
      congr 1
      ring

end NativeRetainedSliceBudget
