import Theorems.Thm_StickyKakeya4_native_original_pruned_mass
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativePruningMassBudget
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalPrunedMass NativeFiniteKakeyaCounts
open scoped ENNReal BigOperators

lemma deleted_card_le {n : ℕ} (R : Finset (Fin n)) {loss : ℝ}
    (hret : (n:ℝ)≤R.card+loss) : ((univ\R).card:ℝ)≤loss := by
  have hh : (univ\R).card+R.card=n := by
    simpa only [card_univ,Fintype.card_fin] using card_sdiff_add_card_eq_card (subset_univ R)
  have hhR : ((univ\R).card:ℝ)+R.card=n := by exact_mod_cast hh
  linarith

lemma source_tube_density_lower {n : ℕ} {D : FiniteScaleSource n} {eta beta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (htube : ∀ i,(ENNReal.ofReal D.thickness).rpow (3+beta)≤
      volume (markedUnitTube (D.line i) D.thickness)) :
    (ENNReal.ofReal D.thickness).rpow (2*eta+beta)≤
      (ENNReal.ofReal D.thickness).rpow eta*wzTotalTubeVolume D := by
  have hd := h.1.2.1
  let e := ENNReal.ofReal D.thickness
  have he0 : e≠0 := by dsimp [e]; positivity
  have heT : e≠⊤ := ENNReal.ofReal_ne_top
  calc
    _ = e.rpow eta*(e.rpow (eta-3)*e.rpow (3+beta)) := by
      simp only [ENNReal.rpow_eq_pow]
      rw [←ENNReal.rpow_add _ _ he0 heT,←ENNReal.rpow_add _ _ he0 heT]
      congr 1
      ring
    _ ≤ e.rpow eta*((n:ℝ≥0∞)*e.rpow (3+beta)) :=
      mul_le_mul' le_rfl (mul_le_mul' (carrier_count_lower h) le_rfl)
    _ ≤ _ := mul_le_mul' le_rfl (total_tube_lower htube)

/-- The actual finite deletion loss, multiplied by the true unit-tube upper
volume, controls removed original shading. The numerical inequality is later
provided by the fixed compact-source dyadic cutoff. -/
theorem removed_mass_small {n : ℕ} {D : FiniteScaleSource n} {eta beta loss : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (hret : (n:ℝ)≤R.card+loss)
    (hbudget : 2*loss*volumeConstant*D.thickness^3≤D.thickness^(2*eta+beta))
    (htube : ∀ i,(ENNReal.ofReal D.thickness).rpow (3+beta)≤
      volume (markedUnitTube (D.line i) D.thickness)) :
    2*shadingMass D (univ\R)≤(ENNReal.ofReal D.thickness).rpow eta*wzTotalTubeVolume D := by
  have hlost := deleted_card_le R hret
  have hloss : 0≤loss := (Nat.cast_nonneg _).trans hlost
  have hd := h.1.2.1
  have hv := volumeConstant_pos
  have hnum := ENNReal.ofReal_le_ofReal hbudget
  have hnum' : 2*ENNReal.ofReal loss*ENNReal.ofReal volumeConstant*(ENNReal.ofReal D.thickness)^3≤
      (ENNReal.ofReal D.thickness).rpow (2*eta+beta) := by
    rw [ENNReal.ofReal_mul (show 0≤2*loss*volumeConstant by positivity),
      ENNReal.ofReal_mul (show 0≤2*loss by positivity),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_pow hd.le] at hnum
    simpa only [ENNReal.rpow_eq_pow,ENNReal.ofReal_ofNat,ENNReal.ofReal_rpow_of_pos hd] using hnum

  calc
    _ ≤ 2*((univ\R).card*(ENNReal.ofReal volumeConstant*(ENNReal.ofReal D.thickness)^3)) :=
      mul_le_mul' le_rfl (shadingMass_upper h (univ\R))
    _ ≤ 2*(ENNReal.ofReal loss*(ENNReal.ofReal volumeConstant*(ENNReal.ofReal D.thickness)^3)) := by
      apply mul_le_mul' le_rfl
      apply mul_le_mul' _ le_rfl
      exact_mod_cast ENNReal.ofReal_le_ofReal hlost
    _ = 2*ENNReal.ofReal loss*ENNReal.ofReal volumeConstant*(ENNReal.ofReal D.thickness)^3 := by ring
    _ ≤ _ := hnum'.trans (source_tube_density_lower h htube)

/-- The original radius-one AD lower count converts a proved numerical loss
budget into true half-retention of original tube labels. -/
lemma half_card_of_loss_budget {n : ℕ} {D : FiniteScaleSource n} {eta loss : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (hret : (n:ℝ)≤R.card+loss) (hbudget : 2*loss≤D.thickness^(eta-3)) :
    n≤2*R.card := by
  have hh := ENNReal.toReal_mono (by finiteness) (carrier_count_lower h)
  simp only [ENNReal.rpow_eq_pow,←ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal h.1.2.1.le,ENNReal.toReal_natCast] at hh
  have hr : (n:ℝ)≤2*R.card := by linarith
  exact_mod_cast hr

end NativePruningMassBudget
