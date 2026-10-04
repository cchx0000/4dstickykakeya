import Theorems.Thm_StickyKakeya4_native_a2_critical_tube_family
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace OriginalCriticalCapParameterTransfer
open Classical OriginalPairStripGeometry OriginalUnitLineParameters OriginalClippedUnitTube
open OriginalArbitraryStripCapCharge OriginalCriticalWidthBound NativeOriginalCriticalQueryRange

/-- A selected actual tube belongs to its own critical strip. Thus the
proved critical cap forces a genuine lower population of the same family. -/
theorem original_critical_cap_population
    (S : Finset Pair) (rho delta chi : ℝ) (hrho : 0<rho) (hd : 0<delta)
    (hS : S.Nonempty) (hdistinct : ∀ z∈S, z.1≠z.2)
    (hcap : ∀ (nx ny c : ℝ) (A : Set Point), nx^2+ny^2=1 →
      (∀ p∈A, |nx*p.1+ny*p.2-c|≤criticalWidth rho S) →
      ((containedInSet S (3*rho) A).card : ℝ)≤delta^chi*S.card) :
    1≤delta^chi*(S.card : ℝ) ∧ delta^(-chi)≤(S.card : ℝ) := by
  obtain ⟨z,hz⟩ := hS
  have hwidth := original_critical_width_ge_base rho S hrho ⟨z,hz⟩
  have hzcap : z∈containedInSet S (3*rho) (clippedTube z (3*rho)) :=
    Finset.mem_filter.mpr ⟨hz,Set.Subset.rfl⟩
  have hone : (1:ℝ)≤(containedInSet S (3*rho) (clippedTube z (3*rho))).card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨z,hzcap⟩
  have hh := hcap (unitX z) (unitY z) (unitOffset z/2) (clippedTube z (3*rho))
    (original_unit_normal_square z (hdistinct z hz)) (fun _ hp => hp.1.trans hwidth)
  have hmass : 1≤delta^chi*(S.card : ℝ) := hone.trans hh
  refine ⟨hmass,?_⟩
  rw [Real.rpow_neg hd.le,← one_div]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hd chi)).mpr
  nlinarith only [hmass]

/-- The actual original-mesh cap transfers to the actual coarse tube
scale for every target exponent at most chi. -/
theorem original_critical_cap_coarse_exponent
    (S : Finset Pair) (rho delta chi u : ℝ) (hd : 0<delta) (hd1 : delta≤1)
    (hmesh : delta≤rho) (hu : 0≤u) (huchi : u≤chi)
    (hcap : ∀ (nx ny c : ℝ) (A : Set Point), nx^2+ny^2=1 →
      (∀ p∈A, |nx*p.1+ny*p.2-c|≤criticalWidth rho S) →
      ((containedInSet S (3*rho) A).card : ℝ)≤delta^chi*S.card) :
    ∀ (nx ny c : ℝ) (A : Set Point), nx^2+ny^2=1 →
      (∀ p∈A, |nx*p.1+ny*p.2-c|≤criticalWidth rho S) →
      ((containedInSet S (3*rho) A).card : ℝ)≤(3*rho)^u*S.card := by
  have hpow1 : delta^chi≤delta^u := Real.rpow_le_rpow_of_exponent_ge hd hd1 huchi
  have hpow2 : delta^u≤(3*rho)^u := Real.rpow_le_rpow hd.le
    (by linarith only [hd,hmesh]) hu
  intro nx ny c A hunit hA
  exact (hcap nx ny c A hunit hA).trans
    (mul_le_mul_of_nonneg_right (hpow1.trans hpow2) (Nat.cast_nonneg S.card))

end OriginalCriticalCapParameterTransfer
