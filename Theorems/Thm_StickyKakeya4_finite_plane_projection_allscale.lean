import Theorems.Thm_StickyKakeya4_finite_plane_projection_frostman_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Finset
open scoped BigOperators
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

/-- Explicit logarithmic multiscale loss, derived from the original KT1 constant. -/
def allscaleLoss (J : ℕ) (rho K : ℝ) : ℝ :=
  1542 * K * (dyadicScales J rho).card

lemma allscaleLoss_pos (J : ℕ) (rho : ℝ) {K : ℝ} (hK : 0 < K) :
    0 < allscaleLoss J rho K := by
  have hcard : 0 < ((dyadicScales J rho).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨rho, base_mem_dyadicScales J rho⟩
  unfold allscaleLoss
  positivity

lemma allscaleLoss_ge (J : ℕ) (rho : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    K ≤ allscaleLoss J rho K := by
  have hcard : (1 : ℝ) ≤ (dyadicScales J rho).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨rho, base_mem_dyadicScales J rho⟩
  unfold allscaleLoss
  nlinarith

/-- Large radii use the original spatial cap directly, so no upper radius
restriction is imposed on the final Frostman conclusion. -/
lemma projectedBall_wide_bound {X : Type*} (P Q : Finset X) (p : X → Point3)
    (uv c : ℝ × ℝ) {rho K D R : ℝ} (hP : P.Nonempty) (hQP : Q ⊆ P)
    (hrho : 0 < rho) (hK : 0 ≤ K) (hKD : K ≤ D) (hR : rho ≤ R) (hwide : 2 ≤ R)
    (htop : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (hKT : ∀ i ∈ P, ∀ r : ℝ, rho ≤ r →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ r)).card : ℝ) ≤ K * r / rho) :
    ((projectedBall Q p uv c R).card : ℝ) ≤ 50 * D * R / rho := by
  obtain ⟨i, hi⟩ := hP
  have he : P.filter (fun k => dist3 (p i) (p k) ≤ R) = P :=
    Finset.filter_eq_self.mpr (fun k hk => (htop i hi k hk).trans hwide)
  have hpop := hKT i hi R hR
  rw [he] at hpop
  have hsub : projectedBall Q p uv c R ⊆ P := (Finset.filter_subset _ _).trans hQP
  have hDR : K * R ≤ (50 * D) * R :=
    mul_le_mul_of_nonneg_right (by linarith) (hrho.le.trans hR)
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (hpop.trans (div_le_div_of_nonneg_right hDR hrho.le))

/-- A common parameter has bounded multiscale energies for both original
families and a bounded number of projected small triangles for the second. -/
theorem exists_common_scale_energies {X Y : Type*} (P : Finset X) (p : X → Point3)
    (B : Finset Y) (b : Y → Point3) (n J : ℕ) {rho KP KB r A : ℝ}
    (hP : P.Nonempty) (hB : B.Nonempty) (hmesh : mesh n ≤ rho)
    (hKP : 0 < KP) (hKB : 0 < KB) (hr : 0 ≤ r) (hA : 0 < A)
    (hJ : 2 ≤ 2 ^ (J + 1) * rho)
    (htopP : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (htopB : ∀ i ∈ B, ∀ k ∈ B, dist3 (b i) (b k) ≤ 2)
    (hKTP : ∀ i ∈ P, ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ KP * R / rho)
    (hKTB : ∀ i ∈ B, ∀ R : ℝ, rho ≤ R →
      ((B.filter (fun k => dist3 (b i) (b k) ≤ R)).card : ℝ) ≤ KB * R / rho) :
    ∃ uv ∈ parameters n,
      scaleEnergy P p (dyadicScales J rho) uv rho ≤ allscaleLoss J rho KP / 2 * P.card ∧
      scaleEnergy B b (dyadicScales J rho) uv rho ≤ allscaleLoss J rho KB / 2 * B.card ∧
      ((smallProjectedTriples B b uv r).card : ℝ) ≤
        3 * (((degenerateTriples B b A).card : ℝ) +
          (8 * r / A + 2 * mesh n) * (B.card : ℝ) ^ 3) := by
  let scales := dyadicScales J rho
  let F := 257 * KP * scales.card * (P.card : ℝ)
  let G := 257 * KB * scales.card * (B.card : ℝ)
  let H := ((degenerateTriples B b A).card : ℝ) +
    (8 * r / A + 2 * mesh n) * (B.card : ℝ) ^ 3
  have hNp : 0 < (P.card : ℝ) := by exact_mod_cast hP.card_pos
  have hNb : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hm := mesh_pos n
  have hrho := hm.trans_le hmesh
  have hscales : ∀ s ∈ scales, rho ≤ s := fun s hs => dyadicScales_ge_base J hrho.le hs
  have hscales0 : ∀ s ∈ scales, 0 ≤ s := fun s hs => hrho.le.trans (hscales s hs)
  have hcard : 0 < (scales.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨rho, base_mem_dyadicScales J rho⟩
  have hF : 0 < F := by dsimp [F]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨uv, huv, hEP, hEB, htri⟩ := exists_three_averages (parameters n)
    (fun uv => scaleEnergy P p scales uv rho)
    (fun uv => scaleEnergy B b scales uv rho)
    (fun uv => ((smallProjectedTriples B b uv r).card : ℝ)) (parameters_nonempty n) hF hG hH
    (fun uv _ => scaleEnergy_nonneg P p scales uv hrho.le hscales0)
    (fun uv _ => scaleEnergy_nonneg B b scales uv hrho.le hscales0)
    (fun _ _ => Nat.cast_nonneg _)
    (scaleEnergy_budget P p scales n J hmesh hKP.le hscales hJ htopP hKTP)
    (scaleEnergy_budget B b scales n J hmesh hKB.le hscales hJ htopB hKTB)
    (original_triangle_projection_budget B b n hr hA)
  refine ⟨uv, huv, ?_, ?_, htri⟩
  · dsimp [F] at hEP
    dsimp [allscaleLoss]
    nlinarith
  · dsimp [G] at hEB
    dsimp [allscaleLoss]
    nlinarith

/-- Genuine common spatial projection: retained ORIGINAL labels have injective
base cells, quantitative relative retention, projected KT1 at EVERY radius above rho
and every center, and B's line exclusion from ORIGINAL spatial caps. -/
theorem exists_common_allscale_original_subsets {X Y : Type*}
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
      (P.card : ℝ) / (2 * allscaleLoss J rho KP) ≤ S.card ∧
      (B.card : ℝ) / (2 * allscaleLoss J rho KB) ≤ T.card ∧
      Set.InjOn (fun i => projectedCell uv rho (p i)) (↑S) ∧
      Set.InjOn (fun i => projectedCell uv rho (b i)) (↑T) ∧
      (∀ c : ℝ × ℝ, ∀ R : ℝ, rho ≤ R →
        ((projectedBall S p uv c R).card : ℝ) ≤ 50 * allscaleLoss J rho KP * R / rho) ∧
      (∀ c : ℝ × ℝ, ∀ R : ℝ, rho ≤ R →
        ((projectedBall T b uv c R).card : ℝ) ≤ 50 * allscaleLoss J rho KB * R / rho) ∧
      ∀ a d c : ℝ, max |a| |d| = 1 →
        ((projectedLineStrip T b uv a d c w).card : ℝ) ≤
          (2 * allscaleLoss J rho KB * theta) * T.card := by
  have hrho := (mesh_pos n).trans_le hmesh
  have hDP := allscaleLoss_pos J rho hKP
  have hDB := allscaleLoss_pos J rho hKB
  have hscales : ∀ s ∈ dyadicScales J rho, 0 < s :=
    fun s hs => hrho.trans_le (dyadicScales_ge_base J hrho.le hs)
  obtain ⟨uv, huv, hEP, hEB, htri⟩ := exists_common_scale_energies P p B b n J
    hP hBnon hmesh hKP hKB (by positivity : 0 ≤ 16 * w) (mul_pos hr0 hw0)
    hJ htopP htopB hKTP hKTB
  have hretP := retainedScales_half P p (dyadicScales J rho) uv hrho hDP hscales hEP
  have hretB := retainedScales_half B b (dyadicScales J rho) uv hrho hDB hscales hEB
  obtain ⟨S, hSret, hSsize, hSinj⟩ := retainedScales_representatives P p (dyadicScales J rho) uv
    hrho hDP (base_mem_dyadicScales J rho) hretP
  obtain ⟨T, hTret, hTsize, hTinj⟩ := retainedScales_representatives B b (dyadicScales J rho) uv
    hrho hDB (base_mem_dyadicScales J rho) hretB
  have hSP := hSret.trans (retainedScales_subset P p _ uv rho _)
  have hTB := hTret.trans (retainedScales_subset B b _ uv rho _)
  refine ⟨uv, huv, S, T, hSP, hTB, hSsize, hTsize, hSinj, hTinj, ?_, ?_, ?_⟩
  · intro c R hR
    by_cases hRtop : R ≤ 2
    · exact retainedScales_allscale_ball_bound P S p J uv c hrho hDP.le hR hRtop hJ hSret
    · exact projectedBall_wide_bound P S p uv c hP hSP hrho hKP.le
        (allscaleLoss_ge J rho hKP.le) hR (le_of_not_ge hRtop) htopP hKTP
  · intro c R hR
    by_cases hRtop : R ≤ 2
    · exact retainedScales_allscale_ball_bound B T b J uv c hrho hDB.le hR hRtop hJ hTret
    · exact projectedBall_wide_bound B T b uv c hBnon hTB hrho hKB.le
        (allscaleLoss_ge J rho hKB.le) hR (le_of_not_ge hRtop) htopB hKTB
  · intro a d c hnormal
    have hdeg := original_degenerate_triple_count B b hw0.le hepsilon hclose hline
    have hcube := projected_line_strip_cube B b (c := c) huv hw hnormal hB
    have hsmall : ((projectedLineStrip B b uv a d c w).card : ℝ) ^ 3 ≤
        (3 * (kappa + epsilon + 128 * w / (r0 * w0) + 2 * mesh n)) * (B.card : ℝ) ^ 3 := by
      calc
        _ ≤ 3 * (((degenerateTriples B b (r0 * w0)).card : ℝ) +
            (8 * (16 * w) / (r0 * w0) + 2 * mesh n) * (B.card : ℝ) ^ 3) := hcube.trans htri
        _ ≤ 3 * ((kappa + epsilon) * (B.card : ℝ) ^ 3 +
            (8 * (16 * w) / (r0 * w0) + 2 * mesh n) * (B.card : ℝ) ^ 3) := by linarith
        _ = _ := by ring
    have hfrac := line_strip_fraction_of_cube B b uv a d c w theta _ htheta hscalar hsmall
    have hmass : (B.card : ℝ) ≤ (2 * allscaleLoss J rho KB) * T.card := by
      have hh := (div_le_iff₀ (show 0 < 2 * allscaleLoss J rho KB by positivity)).mp hTsize
      nlinarith
    have hsubfrac := line_fraction_to_original_subset B T b uv hTB htheta hmass hfrac
    convert hsubfrac using 1
    ring

/-- A lower ORIGINAL population converts the absolute projected KT1 count to a
relative Frostman count. This uses the proved representative retention loss. -/
lemma relative_ball_bound_of_original_density {X : Type*}
    (P S : Finset X) (p : X → Point3) (uv c : ℝ × ℝ) {rho D R eta : ℝ}
    (hrho : 0 < rho) (hD : 0 ≤ D) (hR : 0 ≤ R) (heta : 0 < eta)
    (hdensity : eta ≤ rho * P.card)
    (hretention : (P.card : ℝ) ≤ 2 * D * S.card)
    (hball : ((projectedBall S p uv c R).card : ℝ) ≤ 50 * D * R / rho) :
    ((projectedBall S p uv c R).card : ℝ) ≤
      (100 * D ^ 2 / eta) * R * S.card := by
  have hmass : eta ≤ rho * (2 * D * S.card) :=
    hdensity.trans (mul_le_mul_of_nonneg_left hretention hrho.le)
  have hcompare : 50 * D * R / rho ≤ (100 * D ^ 2 / eta) * R * S.card := by
    apply (div_le_iff₀ hrho).2
    have hh := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 50 * D * R by positivity)
    have hdiv := div_le_div_of_nonneg_right hh heta.le
    have hcancel : 50 * D * R * eta / eta = 50 * D * R := by field_simp
    rw [hcancel] at hdiv
    convert hdiv using 1
    ring
  exact hball.trans hcompare

end FinitePlaneProjectionGrid
