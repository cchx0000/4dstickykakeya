import Theorems.Thm_StickyKakeya4_native_local_admission_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeLocalTransferBudget
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentSelection

/-- The fixed local multiplicity transfer cost includes the actual finite-menu
retention factor and the source-derived incidence constant. -/
def transferCoefficient (d g L : ℕ) : ℝ :=
  (125 * 175616 * 16384 : ℝ) *
    (NativeOriginalParentDensityCore.factor d g L : ℝ) *
      16 * NativeLocalAdmissionBudget.incidenceConstant^(2 / (L : ℝ))

lemma transferCoefficient_nonneg (d g L : ℕ) : 0 ≤ transferCoefficient d g L := by
  have hC := NativeLocalAdmissionBudget.incidenceConstant_pos
  dsimp [transferCoefficient]
  positivity

/-- Choose the cutoff before the original native source and retained relation.
The actual radix is paid using original source geometry, with no cardinal or
subpower bound assumed for the retained relation. -/
theorem exists_parent_transfer_cutoff (theta : ℝ) (htheta : 0 < theta)
    (d g L : ℕ) (hL : 0 < L) (eta0 : ℝ)
    (hgap : eta0 + 8 / (L : ℝ) ≤ theta / 2) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
        IsWangZakharovNativeFiniteInput D eta → D.thickness ≤ delta0 → eta ≤ eta0 →
        ∀ original : Fin n → Finset Index,
          (∀ i, D.shading i = wzCellShading (mesh D) original i) →
          ∀ A : Finset (Fin n × Index), A ⊆ incidences original → A.Nonempty →
            (125 * 175616 * 16384 : ℝ) *
              (NativeOriginalParentDensityCore.factor d g L : ℝ) *
                (NativeSourceSizeBounds.radix A.card L : ℝ)^2 * D.thickness^(-eta) ≤
                  D.thickness^(-theta) := by
  obtain ⟨delta0, hd0, hd01, habsorb⟩ :=
    exists_positive_rpow_absorption_threshold (gap := theta / 2)
      (coefficient := transferCoefficient d g L) (pointConstant := 1)
      (by positivity) (transferCoefficient_nonneg d g L) (by norm_num)
  refine ⟨delta0, hd0, hd01, ?_⟩
  intro n D eta h hsmall heta original horiginal A hA hAne
  have hd := h.1.2.1
  have hd1 : D.thickness ≤ 1 := hsmall.trans hd01
  have hC := NativeLocalAdmissionBudget.incidenceConstant_pos
  have hQ := NativeLocalAdmissionBudget.retained_radix_sq_upper
    h original horiginal A hA hAne L hL
  have hpaid := NativeLocalAdmissionBudget.pay_power hd hd1
    (habsorb D.thickness hd hsmall)
    (show -theta + theta / 2 ≤ -8 / (L : ℝ) + -eta by rw [neg_div]; linarith)
  calc
    _ ≤ (125 * 175616 * 16384 : ℝ) *
        (NativeOriginalParentDensityCore.factor d g L : ℝ) *
        (16 * NativeLocalAdmissionBudget.incidenceConstant^(2 / (L : ℝ)) *
          D.thickness^(-8 / (L : ℝ))) * D.thickness^(-eta) := by gcongr
    _ = transferCoefficient d g L * D.thickness^(-8 / (L : ℝ) + -eta) := by
      dsimp [transferCoefficient]
      rw [Real.rpow_add hd]
      ring
    _ ≤ _ := hpaid

end NativeLocalTransferBudget
