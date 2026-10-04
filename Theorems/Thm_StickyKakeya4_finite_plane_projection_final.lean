import Theorems.Thm_StickyKakeya4_finite_plane_projection_separated

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Finset
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

/-- Final native projection theorem from original spatial premises: one actual
surjective linear map, original retained labels, separated actual images,
all-radius/all-center Frostman caps, and original B anti-line concentration. -/
theorem exists_common_separated_original_subsets {X Y : Type*}
    (P : Finset X) (p : X → Point3) (B : Finset Y) (b : Y → Point3)
    (n J : ℕ) {rho KP KB r0 w0 w kappa epsilon theta : ℝ}
    (hP : P.Nonempty) (hBnon : B.Nonempty) (hmesh : mesh n ≤ rho)
    (hKP : 0 < KP) (hKB : 0 < KB) (hr0 : 0 < r0) (hw0 : 0 < w0)
    (hw : 0 ≤ w) (hepsilon : 0 ≤ epsilon) (htheta : 0 ≤ theta)
    (hscalar : 3 * (kappa + epsilon + 128 * w / (r0 * w0) + 2 * mesh n) ≤ theta ^ 3)
    (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (htopP : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (htopB : ∀ i ∈ B, ∀ k ∈ B, dist3 (b i) (b k) ≤ 2)
    (hKTP : ∀ i ∈ P, ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ KP * R / rho)
    (hKTB : ∀ i ∈ B, ∀ R : ℝ, rho ≤ R →
      ((B.filter (fun k => dist3 (b i) (b k) ≤ R)).card : ℝ) ≤ KB * R / rho)
    (hB : ∀ i ∈ B, |(b i).1| ≤ 1 ∧ |(b i).2.1| ≤ 1 ∧ |(b i).2.2| ≤ 1)
    (hclose : ∀ i ∈ B,
      ((B.filter (fun j => dist3 (b i) (b j) ≤ r0)).card : ℝ) ≤ kappa * B.card)
    (hline : ∀ i ∈ B, ∀ j ∈ B, r0 < dist3 (b i) (b j) →
      ((originalCrossTube B b i j w0).card : ℝ) ≤ epsilon * B.card) :
    ∃ uv ∈ parameters n, ∃ S : Finset X, ∃ T : Finset Y,
      S ⊆ P ∧ T ⊆ B ∧
      (P.card : ℝ) / (18 * allscaleLoss J rho KP) ≤ S.card ∧
      (B.card : ℝ) / (18 * allscaleLoss J rho KB) ≤ T.card ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j →
        2 * rho < ‖projectionLinear uv (p i) - projectionLinear uv (p j)‖) ∧
      (∀ i ∈ T, ∀ j ∈ T, i ≠ j →
        2 * rho < ‖projectionLinear uv (b i) - projectionLinear uv (b j)‖) ∧
      (∀ c : ℝ × ℝ, ∀ R : ℝ, rho ≤ R →
        ((S.filter (fun i => ‖projectionLinear uv (p i) - c‖ ≤ R)).card : ℝ) ≤ 50 * allscaleLoss J rho KP * R / rho) ∧
      (∀ c : ℝ × ℝ, ∀ R : ℝ, rho ≤ R →
        ((T.filter (fun i => ‖projectionLinear uv (b i) - c‖ ≤ R)).card : ℝ) ≤ 50 * allscaleLoss J rho KB * R / rho) ∧
      ∀ a d c : ℝ, max |a| |d| = 1 →
        ((projectedLineStrip T b uv a d c w).card : ℝ) ≤
          (18 * allscaleLoss J rho KB * theta) * T.card := by
  have hrho := (mesh_pos n).trans_le hmesh
  have hDP := allscaleLoss_pos J rho hKP
  have hDB := allscaleLoss_pos J rho hKB
  obtain ⟨uv, huv, S, T, hSP, hTB, hSsize, hTsize, hSinj, hTinj, hSball, hTball, hTline⟩ :=
    exists_common_allscale_original_subsets P p B b n J hP hBnon hmesh hKP hKB
      hr0 hw0 hw hepsilon htheta hscalar hJ htopP htopB hKTP hKTB hB hclose hline
  obtain ⟨U, hUS, hScard, hUsep⟩ := exists_separated_projection_subset S p uv hrho hSinj
  obtain ⟨V, hVT, hTcard, hVsep⟩ := exists_separated_projection_subset T b uv hrho hTinj
  have hSreal : (S.card : ℝ) ≤ 9 * U.card := by exact_mod_cast hScard
  have hTreal : (T.card : ℝ) ≤ 9 * V.card := by exact_mod_cast hTcard
  have hUsize : (P.card : ℝ) / (18 * allscaleLoss J rho KP) ≤ U.card := by
    have hh := (div_le_iff₀ (show 0 < 2 * allscaleLoss J rho KP by positivity)).mp hSsize
    apply (div_le_iff₀ (show 0 < 18 * allscaleLoss J rho KP by positivity)).2
    nlinarith
  have hVsize : (B.card : ℝ) / (18 * allscaleLoss J rho KB) ≤ V.card := by
    have hh := (div_le_iff₀ (show 0 < 2 * allscaleLoss J rho KB by positivity)).mp hTsize
    apply (div_le_iff₀ (show 0 < 18 * allscaleLoss J rho KB by positivity)).2
    nlinarith
  refine ⟨uv, huv, U, V, hUS.trans hSP, hVT.trans hTB, hUsize, hVsize, hUsep, hVsep, ?_, ?_, ?_⟩
  · intro c R hR
    rw [← projectedBall_eq_native_ball]
    exact (Nat.cast_le.mpr (Finset.card_le_card (projectedBall_mono S U p uv c R hUS))).trans
      (hSball c R hR)
  · intro c R hR
    rw [← projectedBall_eq_native_ball]
    exact (Nat.cast_le.mpr (Finset.card_le_card (projectedBall_mono T V b uv c R hVT))).trans
      (hTball c R hR)
  · intro a d c hnormal
    have htheta' : 0 ≤ 2 * allscaleLoss J rho KB * theta := by positivity
    have hh := line_fraction_to_original_subset T V b uv hVT htheta' hTreal (hTline a d c hnormal)
    convert hh using 1
    ring

/-- Generic relative Frostman conversion keeps both losses explicit: C is the
proved absolute ball cap, L is the proved original-label retention loss. -/
lemma relative_native_ball_bound {X : Type*} (P Q : Finset X) (p : X → Point3)
    (uv c : ℝ × ℝ) {rho R C L eta : ℝ}
    (hrho : 0 < rho) (heta : 0 < eta) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hdensity : eta ≤ rho * P.card) (hret : (P.card : ℝ) ≤ L * Q.card)
    (hball : ((Q.filter (fun i => ‖projectionLinear uv (p i) - c‖ ≤ R)).card : ℝ) ≤ C * R / rho) :
    ((Q.filter (fun i => ‖projectionLinear uv (p i) - c‖ ≤ R)).card : ℝ) ≤
      (C * L / eta) * R * Q.card := by
  have hmass : eta ≤ rho * (L * Q.card) :=
    hdensity.trans (mul_le_mul_of_nonneg_left hret hrho.le)
  have hcompare : C * R / rho ≤ (C * L / eta) * R * Q.card := by
    apply (div_le_iff₀ hrho).2
    have hh := mul_le_mul_of_nonneg_left hmass (show 0 ≤ C * R by positivity)
    have hdiv := div_le_div_of_nonneg_right hh heta.le
    have hcancel : C * R * eta / eta = C * R := by field_simp
    rw [hcancel] at hdiv
    convert hdiv using 1
    ring
  exact hball.trans hcompare

end FinitePlaneProjectionGrid
