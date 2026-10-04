import Theorems.Thm_StickyKakeya4_native_dyadic_mesh_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeScheduledScaleSelection
/-- A literal nonnegative-index member of the original scale schedule. -/
def scheduledScale (delta eta : ℝ) (n : ℕ) : ℝ := delta^(eta*(n:ℝ))
lemma scheduledScale_eq_pow {delta eta : ℝ} (hd : 0 ≤ delta) (n : ℕ) :
    scheduledScale delta eta n=(delta^eta)^n := Real.rpow_mul_natCast hd eta n
lemma scheduledScale_integer (delta eta : ℝ) (n : ℕ) :
    ∃ k : ℤ, scheduledScale delta eta n=delta^(eta*(k:ℝ)) := by
  exact ⟨(n:ℤ),by simp only [scheduledScale,Int.cast_natCast]⟩
/-- Choose an actual scheduled scale above an arbitrary target. The scale
 stays in the original admissible interval and the overshoot is charged. -/
theorem exists_scheduled_scale_above {delta eta r : ℝ}
    (hd : 0 < delta) (hd1 : delta < 1) (heta : 0 < eta)
    (hdr : delta ≤ r) (hr1 : r ≤ 1) :
    ∃ n : ℕ, delta ≤ scheduledScale delta eta n ∧
      scheduledScale delta eta n ≤ 1 ∧ r ≤ scheduledScale delta eta n ∧
      scheduledScale delta eta n ≤ delta^(-eta)*r := by
  have hq : 0 < delta^eta := Real.rpow_pos_of_pos hd eta
  obtain ⟨n,hnext,hprev⟩ := exists_nat_pow_near_of_lt_one (hd.trans_le hdr) hr1 hq
    (Real.rpow_lt_one hd.le hd1 heta)
  have hupper : (delta^eta)^n ≤ delta^(-eta)*r := by
    rw [Real.rpow_neg hd.le]
    have hs : (delta^eta)^n ≤ r/(delta^eta) := (le_div_iff₀ hq).mpr (by
      simpa only [pow_succ] using hnext.le)
    simpa only [div_eq_mul_inv,mul_comm] using hs
  refine ⟨n,?_,?_,?_,?_⟩
  · simpa only [scheduledScale_eq_pow hd.le] using hdr.trans hprev
  · exact Real.rpow_le_one hd.le hd1.le (mul_nonneg heta.le (Nat.cast_nonneg n))
  · simpa only [scheduledScale_eq_pow hd.le] using hprev
  · simpa only [scheduledScale_eq_pow hd.le] using hupper
/-- Field laws are accepted only at literal scheduled scales in [delta,1].
 They are not extended to an arbitrary target-scale floor cell. -/
def ScheduledLaw (delta eta : ℝ) (law : ℝ → Prop) : Prop :=
  ∀ k : ℤ, delta ≤ delta^(eta*(k:ℝ)) → delta^(eta*(k:ℝ)) ≤ 1 → law (delta^(eta*(k:ℝ)))
theorem scheduled_law_at_selected {delta eta : ℝ} {law : ℝ → Prop}
    (hsource : ScheduledLaw delta eta law) (n : ℕ)
    (hlo : delta ≤ scheduledScale delta eta n) (hhi : scheduledScale delta eta n ≤ 1) :
    law (scheduledScale delta eta n) := by
  obtain ⟨k,hk⟩ := scheduledScale_integer delta eta n
  rw [hk] at hlo hhi ⊢
  exact hsource k hlo hhi
/-- Select once and instantiate both the slope and xi source laws at the
 identical original scheduled scale. -/
theorem exists_scheduled_scale_with_laws {delta eta r : ℝ} {slopeLaw xiLaw : ℝ → Prop}
    (hd : 0 < delta) (hd1 : delta < 1) (heta : 0 < eta)
    (hdr : delta ≤ r) (hr1 : r ≤ 1)
    (hf : ScheduledLaw delta eta slopeLaw) (hxi : ScheduledLaw delta eta xiLaw) :
    ∃ n : ℕ, delta ≤ scheduledScale delta eta n ∧ scheduledScale delta eta n ≤ 1 ∧
      r ≤ scheduledScale delta eta n ∧ scheduledScale delta eta n ≤ delta^(-eta)*r ∧
      slopeLaw (scheduledScale delta eta n) ∧ xiLaw (scheduledScale delta eta n) := by
  obtain ⟨n,hnlo,hnhi,hr,hover⟩ := exists_scheduled_scale_above hd hd1 heta hdr hr1
  exact ⟨n,hnlo,hnhi,hr,hover,scheduled_law_at_selected hf n hnlo hnhi,
    scheduled_law_at_selected hxi n hnlo hnhi⟩
end NativeScheduledScaleSelection
