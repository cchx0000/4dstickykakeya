import Theorems.Thm_StickyKakeya4_native_dyadic_mesh_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeQuarterBalancedMesh
open NativeQuarterScaleParameters NativeDyadicMeshSelection
/-- A common spatial normalization and the actual nearby dyadic rounding
 leave the balanced ABC mesh between fixed original-delta powers. -/
theorem balanced_quarter_mesh_bounds {delta S0 g rho : ℝ}
    (hd : 0 < delta) (hS : 1 ≤ S0) (hScap : S0 ≤ delta^(-g))
    (hhalf : (quarterScale delta/S0)/2 ≤ rho) (hr : rho ≤ quarterScale delta/S0)
    (hsmall : delta^((1/4:ℝ)-g) ≤ (1/16:ℝ)) :
    delta^(1/2:ℝ) ≤ rho/8 ∧ rho/8 ≤ quarterScale delta := by
  have hS0 : 0 < S0 := lt_of_lt_of_le (by norm_num) hS
  have hq : 0 < quarterScale delta := Real.rpow_pos_of_pos hd _
  have hpower : delta^((1/4:ℝ)+g) ≤ quarterScale delta/S0 := by
    calc
      _ = quarterScale delta/delta^(-g) := by
        unfold quarterScale
        rw [← Real.rpow_sub hd]
        congr 1
        ring
      _ ≤ _ := div_le_div_of_nonneg_left hq.le hS0 hScap
  have hsplit : delta^(1/2:ℝ)=delta^((1/4:ℝ)-g)*delta^((1/4:ℝ)+g) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hlow := mul_le_mul_of_nonneg_right hsmall (Real.rpow_pos_of_pos hd ((1/4:ℝ)+g)).le
  rw [← hsplit] at hlow
  have htupper : quarterScale delta/S0 ≤ quarterScale delta :=
    (div_le_iff₀ hS0).mpr (by nlinarith only [hS,hq])
  constructor
  · linarith only [hlow,hpower,hhalf]
  · linarith only [hr,htupper,hq]
/-- The analytic integer cutoff is fixed before the original scale and
 common spatial normalization. The actual balanced mesh is exactly dyadic. -/
theorem exists_balanced_quarter_dyadic {delta S0 g : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hS : 1 ≤ S0) (hScap : S0 ≤ delta^(-g))
    (hsmall : delta^((1/4:ℝ)-g) ≤ (1/16:ℝ)) (n0 : ℕ)
    (hcutoff : quarterScale delta ≤ ((2:ℝ)^n0)⁻¹) :
    ∃ n : ℕ, ∃ rho : ℝ, n0 ≤ n ∧ 0 < rho ∧ rho/8=((2:ℝ)^n)⁻¹ ∧
      (quarterScale delta/S0)/2 ≤ rho ∧ rho < quarterScale delta/S0 ∧
      delta^(1/2:ℝ) ≤ rho/8 ∧ rho/8 ≤ quarterScale delta := by
  have hS0 : 0 < S0 := lt_of_lt_of_le (by norm_num) hS
  have hq : 0 < quarterScale delta := Real.rpow_pos_of_pos hd _
  have hq1 : quarterScale delta ≤ 1 := by
    exact Real.rpow_le_one hd.le hd1 (by norm_num)
  have htupper : quarterScale delta/S0 ≤ quarterScale delta :=
    (div_le_iff₀ hS0).mpr (by nlinarith only [hS,hq])
  obtain ⟨n,rho,hn,hr,heq,hlo,hhi⟩ := exists_balanced_nearby_dyadic_mesh
    (div_pos hq hS0) (htupper.trans hq1) n0 (htupper.trans hcutoff)
  exact ⟨n,rho,hn,hr,heq,hlo,hhi,balanced_quarter_mesh_bounds hd hS hScap hlo hhi.le hsmall⟩
/-- At this actual mesh, the projected Euclidean strip width admits the
 fixed native exponent 32s, including its explicit factor-eight loss. -/
theorem native_strip_width {delta mu s : ℝ} (hd : 0 < delta) (hmu : 0 ≤ mu)
    (hmesh : mu ≤ quarterScale delta) (hs : 0 ≤ s)
    (hsmall : delta^(4*s) ≤ (1/8:ℝ)) : mu^(32*s) ≤ delta^(4*s)/8 := by
  have hh := Real.rpow_le_rpow hmu hmesh (show 0 ≤ 32*s by positivity)
  have hid : (quarterScale delta)^(32*s)=delta^(8*s) := by
    unfold quarterScale
    rw [← Real.rpow_mul hd.le]
    congr 1
    ring
  rw [hid] at hh
  have hsplit : delta^(8*s)=delta^(4*s)*delta^(4*s) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hc := mul_le_mul_of_nonneg_right hsmall (Real.rpow_pos_of_pos hd (4*s)).le
  rw [← hsplit] at hc
  exact hh.trans (by linarith only [hc])
/-- After charging the original graph projection loss, the surviving
 original line fraction has a fixed native exponent u/4. -/
theorem native_line_fraction {delta mu u fraction : ℝ} (hd : 0 < delta)
    (hmesh : delta^(1/2:ℝ) ≤ mu) (hu : 0 ≤ u) (hfrac : fraction ≤ delta^(u/8)) :
    fraction ≤ mu^(u/4) := by
  have hh := Real.rpow_le_rpow (Real.rpow_pos_of_pos hd (1/2:ℝ)).le hmesh
    (show 0 ≤ u/4 by positivity)
  have hid : (delta^(1/2:ℝ))^(u/4)=delta^(u/8) := by
    rw [← Real.rpow_mul hd.le]
    congr 1
    ring
  rw [hid] at hh
  exact hfrac.trans hh
/-- The actual mesh converts every original power loss by the fixed factor
 four, including density lower bounds and upper Frostman/cover constants. -/
theorem native_power_loss {delta mu a : ℝ} (hd : 0 < delta) (hmu : 0 < mu)
    (hmesh : mu ≤ quarterScale delta) (ha : 0 ≤ a) :
    mu^(4*a) ≤ delta^a ∧ delta^(-a) ≤ mu^(-4*a) := by
  have hh := Real.rpow_le_rpow hmu.le hmesh (show 0 ≤ 4*a by positivity)
  have hid : (quarterScale delta)^(4*a)=delta^a := by
    unfold quarterScale
    rw [← Real.rpow_mul hd.le]
    congr 1
    ring
  rw [hid] at hh
  refine ⟨hh,?_⟩
  have hinv := (inv_le_inv₀ (Real.rpow_pos_of_pos hd a) (Real.rpow_pos_of_pos hmu (4*a))).mpr hh
  simpa only [Real.rpow_neg hd.le,Real.rpow_neg hmu.le,neg_mul] using hinv
/-- The proved original coarse-height mass is transported through the
 SAME common spatial normalization and the actual dyadic mesh choice.
 The original finite carrier is unchanged throughout this transport. -/
theorem original_B_mass_at_balanced_projection {X : Type*} (B : Finset X)
    {delta S0 rho lambda : ℝ} (hS : 0 < S0)
    (hhalf : (quarterScale delta/S0)/2 ≤ rho)
    (hOriginalMass : lambda ≤ quarterScale delta*(B.card:ℝ)) :
    lambda/(2*S0) ≤ rho*(B.card:ℝ) := by
  have hm : lambda/S0 ≤ (quarterScale delta/S0)*(B.card:ℝ) := by
    calc
      _ ≤ (quarterScale delta*(B.card:ℝ))/S0 := div_le_div_of_nonneg_right hOriginalMass hS.le
      _ = _ := by ring
  have hh := original_mass_at_nearby_mesh hhalf (Nat.cast_nonneg B.card) hm
  simpa only [div_div,mul_comm S0 2] using hh
end NativeQuarterBalancedMesh
