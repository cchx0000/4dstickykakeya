import Theorems.Thm_StickyKakeya4_native_quarter_scale_parameters
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
noncomputable section
namespace NativeOriginalCutoffSelection
open NativeQuarterScaleParameters
/-- The analytic cutoff is fixed first. A positive original-delta cutoff
 then places every actual spatial mesh with the proved envelope below it. -/
theorem exists_native_mesh_cutoff {a : ℝ} (ha : 0 < a) (n0 : ℕ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ ∀ delta t : ℝ,
      0 < delta → delta ≤ delta0 → t ≤ delta^a → t ≤ ((2:ℝ)^n0)⁻¹ := by
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_small_power_cutoff ha
    (by positivity : (0:ℝ)<((2:ℝ)^n0)⁻¹)
  exact ⟨delta0,hd0,hd01,fun delta t hd hsmall ht => ht.trans (hcut delta hd hsmall)⟩
/-- Original Phi packing is usable uniformly in its exponent once the
 original AD loss and the scheduled angular-mesh loss are both charged. -/
theorem quarter_angular_packing_budget {delta angularK angularMesh eta g : ℝ}
    (hd : 0 < delta) (_hK : 0 ≤ angularK) (hq : 0 ≤ angularMesh)
    (hKcap : angularK ≤ delta^(-eta))
    (hqcap : angularMesh ≤ delta^((1/4:ℝ)-g))
    (hsmall : delta^((1/4:ℝ)-g-eta) ≤ (1/8:ℝ)) : angularK*angularMesh ≤ (1/8:ℝ) := by
  calc
    _ ≤ delta^(-eta)*delta^((1/4:ℝ)-g) :=
      mul_le_mul hKcap hqcap hq (Real.rpow_pos_of_pos hd _).le
    _ = delta^((1/4:ℝ)-g-eta) := by rw [← Real.rpow_add hd]; congr 1; ring
    _ ≤ _ := hsmall
/-- One small original-delta cutoff supplies BOTH the analytic large-n
 cutoff and the original angular packing condition, with all scheduled
 mesh and original AD losses displayed in the exponent gaps. -/
theorem exists_quarter_mesh_and_packing_cutoff {a g eta : ℝ}
    (ha : 0 < a) (hgap : g+eta < (1/4:ℝ)) (n0 : ℕ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ ∀ delta t angularK angularMesh : ℝ,
      0 < delta → delta ≤ delta0 → t ≤ delta^a → 0 ≤ angularK → 0 ≤ angularMesh →
      angularK ≤ delta^(-eta) → angularMesh ≤ delta^((1/4:ℝ)-g) →
      t ≤ ((2:ℝ)^n0)⁻¹ ∧ angularK*angularMesh ≤ (1/8:ℝ) := by
  obtain ⟨d1,hd1,hd11,hcut1⟩ := exists_native_mesh_cutoff ha n0
  obtain ⟨d2,hd2,_hd21,hcut2⟩ := exists_small_power_cutoff
    (show 0 < (1/4:ℝ)-g-eta by linarith) (by norm_num : (0:ℝ)<1/8)
  refine ⟨min d1 d2,lt_min hd1 hd2,(min_le_left _ _).trans hd11,?_⟩
  intro delta t K q hd hd0 ht hK hq hKcap hqcap
  exact ⟨hcut1 delta t hd (hd0.trans (min_le_left _ _)) ht,
    quarter_angular_packing_budget hd hK hq hKcap hqcap
      (hcut2 delta hd (hd0.trans (min_le_right _ _)))⟩
end NativeOriginalCutoffSelection
