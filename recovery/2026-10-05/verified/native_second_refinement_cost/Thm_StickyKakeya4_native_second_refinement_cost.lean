import Theorems.Thm_StickyKakeya4_native_local_transfer_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section
namespace NativeSecondRefinementCost
open StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeLocalPairUniformCore NativeOriginalParentDensityCore NativeLocalTransferBudget

lemma retained_cost_le_factor (d g L : ℕ) (hdg : 0 < d+g) :
    retentionCost d g L ≤ factor d g L := by
  have hb : 4*(d+g) ≤ 4*((d+g)+g) := by omega
  have he : (d+g)*L ≤ ((d+g)+g)*L := Nat.mul_le_mul_right L (by omega)
  have hp1 := Nat.pow_le_pow_left hb ((d+g)*L)
  have hp2 := Nat.pow_le_pow_right (show 0 < 4*((d+g)+g) by omega) he
  simp only [factor,retentionCost]
  exact (Nat.mul_le_mul_left 2 (hp1.trans hp2)).trans (by omega)

/-- Choose the second uniformization depth and source cutoff before the
native source and before ANY actual rank-selected incidence subset. Its
cost uses the unchanged original source geometry; no bound on the chosen
subset's size or radix is supplied. -/
theorem exists_second_refinement_cost (cost : ℝ) (hcost : 0 < cost) (d g : ℕ) :
    ∃ L : ℕ, 0 < L ∧ ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
        IsWangZakharovNativeFiniteInput D eta → D.thickness ≤ delta0 →
        eta ≤ cost/4 → ∀ original : Fin n → Finset Index,
        (∀i,D.shading i=wzCellShading (mesh D) original i) →
        ∀ A : Finset (Fin n × Index), A ⊆ NativeCubicalIncidenceCounts.incidences original →
          A.Nonempty →
          (125*175616*16384:ℝ)*(factor d g L:ℝ)*
            (NativeSourceSizeBounds.radix A.card L:ℝ)^2*D.thickness^(-eta) ≤
              D.thickness^(-cost) := by
  obtain ⟨L,hbig⟩ := exists_nat_gt (max (1:ℝ) (32/cost))
  have hLreal : (0:ℝ) < L := lt_trans (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) hbig
  have hL : 0 < L := by exact_mod_cast hLreal
  have hlarge : 32/cost < (L:ℝ) := (le_max_right _ _).trans_lt hbig
  have hmul : 32 < (L:ℝ)*cost := (div_lt_iff₀ hcost).mp hlarge
  have hsmall : 8/(L:ℝ) ≤ cost/4 := by
    apply (div_le_iff₀ hLreal).mpr
    nlinarith
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_parent_transfer_cutoff cost hcost d g L hL
    (cost/4) (by linarith)
  exact ⟨L,hL,delta0,hd0,hd01,hcut⟩

end NativeSecondRefinementCost
