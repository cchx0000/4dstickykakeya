import Theorems.Thm_StickyKakeya4_native_planar_lemma53
import Theorems.Thm_StickyKakeya4_native_scalar_cover_ad
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace NativePlanarCoverLemma53
open NativePlanarLemma53 NativeScalarCoverAD NativePaperAlignmentScales
open NativeDyadicTubeStopping FiniteVoronoiRealADCoarsening
noncomputable section

lemma relative_dyadic_mesh {delta rho tau : ℝ} (hdelta : 0 < delta) (hrt : rho ≤ tau)
    {ir it : ℕ} (hr : rho = scale delta ir) (ht : tau = scale delta it) :
    rho / tau = 1 / (2 : ℝ) ^ (it - ir) := by
  have hij : ir ≤ it := (scale_le_iff hdelta ir it).mp (by rwa [← hr, ← ht])
  rw [hr, ht, one_div, ← inv_div, scale_ratio hdelta hij]

/-- Occupied-cell AD on the same scalar fibers and quotient. Half the desired
exponent absorbs the exact C squared conversion with no fixed-factor loss. -/
theorem native_quarter_square_cover_lemma53 {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ eta0 chi : ℝ, 0 < eta0 ∧ 0 < chi ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 → ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ (A : Finset Plane) (delta t : ℝ),
          A.Nonempty → 0 < delta → delta ≤ delta0 → 0 ≤ t → t ≤ 2 →
          (∀ p ∈ A, ∀ i : Fin 2, |p i| ≤ 1 / 4) → ADBounds A delta (delta ^ (-eta)) t →
          ∃ rho tau s : ℝ, ∃ j : Fin 2, ∃ A' : Finset Plane,
            A' ⊆ A ∧ A'.Nonempty ∧ delta ≤ rho ∧ rho < tau ∧ tau ≤ 1 ∧
            0 ≤ s ∧ s ≤ min t 1 ∧
            (∃ ir it : ℕ, rho = scale delta ir ∧ tau = scale delta it) ∧
            (∃ n : ℕ, rho / tau = 1 / (2 : ℝ) ^ n) ∧
            delta ^ (-chi) ≤ tau / rho ∧
            (rho / tau) ^ zeta * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
            delta ^ zeta * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
            ∀ a ∈ A', NearlyCoverAligned
              ((localBall A' a tau).image (normalization j a tau))
              (rho / tau) t s ((rho / tau) ^ (-zeta)) := by
  obtain ⟨eta0, chi, heta0, hchi, hmain⟩ := native_quarter_square_lemma53
    (show 0 < zeta / 2 by positivity)
  refine ⟨eta0, chi, heta0, hchi, ?_⟩
  intro eta heta hetasmall
  obtain ⟨delta0, hdelta0, hwork⟩ := hmain eta heta hetasmall
  refine ⟨delta0, hdelta0, ?_⟩
  intro A delta t hne hdelta hdeltasmall ht ht2 hbox hAD
  obtain ⟨rho, tau, s, j, A', hsub, hne', hdr, hrt, htau, hs, hst,
    ⟨ir, it, hr, hτ⟩, hgap, hret, _hdret, hnear⟩ := hwork A delta t hne hdelta hdeltasmall ht ht2 hbox hAD
  have hrho : 0 < rho := hdelta.trans_le hdr
  have htaup : 0 < tau := hrho.trans hrt
  have he : 0 < rho / tau := div_pos hrho htaup
  have heone : rho / tau ≤ 1 := (div_le_one htaup).mpr hrt.le
  have hde : delta ≤ rho / tau := (le_div_iff₀ htaup).mpr
    ((mul_le_of_le_one_right hdelta.le htau).trans hdr)
  have hpow : (rho / tau) ^ zeta ≤ (rho / tau) ^ (zeta / 2) :=
    Real.rpow_le_rpow_of_exponent_ge he heone (by linarith)
  have hret' := (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg A.card)).trans hret
  refine ⟨rho, tau, s, j, A', hsub, hne', hdr, hrt, htau, hs, hst,
    ⟨ir, it, hr, hτ⟩, ⟨it - ir, relative_dyadic_mesh hdelta hrt.le hr hτ⟩,
    hgap, hret', retained_delta_power hdelta.le hde hzeta.le (Nat.cast_nonneg _) hret', ?_⟩
  intro a ha
  have hC : 1 ≤ (rho / tau) ^ (-(zeta / 2)) := by
    rw [Real.rpow_neg_eq_inv_rpow]
    exact Real.one_le_rpow ((one_le_inv₀ he).mpr heone) (by positivity)
  have hh := nearly_literal_to_cover (hnear a ha) heone hC
  have hsq : ((rho / tau) ^ (-(zeta / 2))) ^ 2 = (rho / tau) ^ (-zeta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul he.le]
    congr 1
    push_cast
    ring
  rwa [hsq] at hh
end
end NativePlanarCoverLemma53
