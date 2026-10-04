import Theorems.Thm_StickyKakeya4_native_ambient_ad_geometry
import Theorems.Thm_StickyKakeya4_actual_scalar_ad_profiles

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace FullNormalizedAmbientAD

open NativeDyadicTubeStopping ShearedGridADReference SmallFiberAlignment FractionalFiberAlignment
open NativeFractionalReferenceComposition NativeAmbientADGeometry ActualScalarADProfiles
open DyadicAlignmentParameters DyadicADInterpolation RealScalarADInterpolation

noncomputable section
attribute [local instance] Classical.propDecidable

lemma realInterpolationLoss_ge_one (M H : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ realInterpolationLoss M H t := by
  have htwo : 1 ≤ (2 : ℝ) ^ t := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2) ht
  have hgap : 1 ≤ scalePower t (gap M H) := by
    unfold scalePower
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)
      (mul_nonneg ht (Nat.cast_nonneg (gap M H)))
  exact one_le_mul_of_one_le_of_one_le htwo hgap

lemma raw_ball_le_actual (P : Finset Vertex) (p : Vertex) (μ angle L : ℝ) (c : Plane)
    (hμ : 0 < μ) (hL : 0 < L) (hangle : |angle| ≤ 1) {R : ℝ} (hR : 0 ≤ R) :
    ballCount (P.image rawPoint) (rawPoint p) R ≤
      ballCount (P.image (actualPoint μ angle L c)) (actualPoint μ angle L c p) (4 * (μ / L) * R) := by
  classical
  unfold ballCount
  rw [Finset.filter_image, Finset.filter_image,
    Finset.card_image_of_injective _ rawPoint_injective,
    Finset.card_image_of_injective _ (actualPoint_injective μ angle L c hμ hL)]
  exact_mod_cast Finset.card_le_card (show P.filter (fun k => dist (rawPoint k) (rawPoint p) ≤ R) ⊆
    P.filter (fun k => dist (actualPoint μ angle L c k) (actualPoint μ angle L c p) ≤ 4 * (μ / L) * R) from by
      intro k hk
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1,
        raw_close_imp_actual_close μ angle L c hμ hL hangle hR (Finset.mem_filter.mp hk).2⟩)

lemma actual_ball_le_raw (P : Finset Vertex) (p : Vertex) (μ angle L : ℝ) (c : Plane)
    (hμ : 0 < μ) (hL : 0 < L) (hangle : |angle| ≤ 1) {r : ℝ} (hr : 0 ≤ r) :
    ballCount (P.image (actualPoint μ angle L c)) (actualPoint μ angle L c p) r ≤
      ballCount (P.image rawPoint) (rawPoint p) ((2 * L / μ) * r) := by
  classical
  unfold ballCount
  rw [Finset.filter_image, Finset.filter_image,
    Finset.card_image_of_injective _ (actualPoint_injective μ angle L c hμ hL),
    Finset.card_image_of_injective _ rawPoint_injective]
  exact_mod_cast Finset.card_le_card (show P.filter
    (fun k => dist (actualPoint μ angle L c k) (actualPoint μ angle L c p) ≤ r) ⊆
    P.filter (fun k => dist (rawPoint k) (rawPoint p) ≤ (2 * L / μ) * r) from by
      intro k hk
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1,
        actual_close_imp_raw_close μ angle L c hμ hL hangle hr (Finset.mem_filter.mp hk).2⟩)

theorem raw_real_ball_bounds (P : Finset Vertex) (M H Q J : ℕ) (hH : 0 < H)
    (t s dens Bad Bcolumn Btube : ℝ) (ht : 0 ≤ t) (hdens : 0 ≤ dens) (hBad : 0 ≤ Bad)
    (hC : 0 < comparisonCost (H + 1) J Q * Bad)
    (hcounts : RefinedCounts P (workingRadii M H) (2 ^ M) Q J t s dens Bad Bcolumn Btube)
    {p : Vertex} (hp : p ∈ P) {r : ℝ} (hrlo : 1 ≤ r) (hrhi : r ≤ (2 : ℝ) ^ M) :
    (dens / (comparisonCost (H + 1) J Q * Bad)) * r ^ t ≤
        realInterpolationLoss M H t * ballCount (P.image rawPoint) (rawPoint p) r ∧
      ballCount (P.image rawPoint) (rawPoint p) r ≤
        realInterpolationLoss M H t * (9 * Bad) * r ^ t := by
  have hw : ∀ j ≤ H,
      (dens / (comparisonCost (H + 1) J Q * Bad)) * ((2 : ℝ) ^ level M H j) ^ t ≤
        ballCount (P.image rawPoint) (rawPoint p) (scale 1 (level M H j)) ∧
      ballCount (P.image rawPoint) (rawPoint p) (scale 1 (level M H j)) ≤
        (9 * Bad) * ((2 : ℝ) ^ level M H j) ^ t := by
    intro j hj
    let jj : Fin (H + 1) := ⟨j, by omega⟩
    have h := (hcounts p hp).2 jj
    have he : scale 1 (level M H j) = (workingRadii M H jj : ℝ) := by
      simp only [scale, workingRadii, jj, one_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [he, rawPoint_ball_card P p]
    constructor
    · rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hC).mpr
      simpa only [workingRadii, jj, Nat.cast_pow, Nat.cast_ofNat, mul_comm] using h.1
    · simpa only [workingRadii, jj, Nat.cast_pow, Nat.cast_ofNat] using h.2.1
  have hh := real_ball_interpolation _ _ M H hH (by norm_num : (0 : ℝ) < 1) ht
    (div_nonneg hdens hC.le) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hBad) hw hrlo
    (by simpa only [scale, one_mul] using hrhi)
  simpa only [div_one, realInterpolationLoss] using hh

/-- Genuine Euclidean t-AD estimates on the normalized vertex image at every
output radius. The original source's global vertex bound handles large radii;
there is no AD claim for collapsed original delta-point populations. -/
theorem ambient_normalized_AD (P : Finset Vertex) (M H Q J : ℕ) (hH : 0 < H)
    (t s dens Bad Bcolumn Btube μ angle L : ℝ) (c : Plane)
    (hμ : 0 < μ) (hL : 0 < L) (hangle : |angle| ≤ 1)
    (ht : 0 ≤ t) (hdens : 0 ≤ dens) (hBad : 0 ≤ Bad)
    (hC : 0 < comparisonCost (H + 1) J Q * Bad)
    (hcounts : RefinedCounts P (workingRadii M H) (2 ^ M) Q J t s dens Bad Bcolumn Btube)
    (hglobal : (P.card : ℝ) ≤ Bad * ((2 : ℝ) ^ M) ^ t)
    (hscale : (μ / L) * (2 : ℝ) ^ M = 1 / 64)
    {p : Vertex} (hp : p ∈ P) {r : ℝ} (hrlo : 64 * (μ / L) ≤ r) (hrhi : r ≤ 1) :
    (dens / (comparisonCost (H + 1) J Q * Bad)) * (r / (64 * (μ / L))) ^ t ≤
        realInterpolationLoss M H t *
          ballCount (P.image (actualPoint μ angle L c)) (actualPoint μ angle L c p) r ∧
      ballCount (P.image (actualPoint μ angle L c)) (actualPoint μ angle L c p) r ≤
        realInterpolationLoss M H t * (9 * Bad) * (128 : ℝ) ^ t * (r / (64 * (μ / L))) ^ t := by
  let lam := μ / L
  have hlam : 0 < lam := div_pos hμ hL
  have hr : 0 < r := (mul_pos (by norm_num : (0 : ℝ) < 64) hlam).trans_le hrlo
  have hN : 1 ≤ (2 : ℝ) ^ M := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hJ := realInterpolationLoss_ge_one M H ht
  have hJ0 : 0 ≤ realInterpolationLoss M H t := zero_le_one.trans hJ
  have hA : 0 ≤ dens / (comparisonCost (H + 1) J Q * Bad) := div_nonneg hdens hC.le
  have hD : 0 ≤ r / (64 * lam) := by positivity
  have hDtop : r / (64 * lam) ≤ (2 : ℝ) ^ M := by
    apply (div_le_iff₀ (by positivity : 0 < 64 * lam)).mpr
    change lam * (2 : ℝ) ^ M = 1 / 64 at hscale
    nlinarith only [hscale, hrhi]
  constructor
  · let u := r / (4 * lam)
    have hu : 1 ≤ u := by
      apply (le_div_iff₀ (by positivity : 0 < 4 * lam)).mpr
      change 64 * lam ≤ r at hrlo
      nlinarith only [hrlo, hlam]
    have hDu : r / (64 * lam) ≤ u := by
      apply div_le_div_of_nonneg_left hr.le (by positivity : 0 < 4 * lam)
      nlinarith only [hlam]
    have hpow := Real.rpow_le_rpow hD hDu ht
    by_cases huN : u ≤ (2 : ℝ) ^ M
    · have hh := (raw_real_ball_bounds P M H Q J hH t s dens Bad Bcolumn Btube ht hdens hBad hC hcounts hp hu huN).1
      have hball := raw_ball_le_actual P p μ angle L c hμ hL hangle (show 0 ≤ u by linarith only [hu])
      have he : 4 * (μ / L) * u = r := by dsimp only [u, lam]; field_simp
      rw [he] at hball
      exact (mul_le_mul_of_nonneg_left hpow hA).trans
        (hh.trans (mul_le_mul_of_nonneg_left hball hJ0))
    · have hh := (raw_real_ball_bounds P M H Q J hH t s dens Bad Bcolumn Btube ht hdens hBad hC hcounts hp hN le_rfl).1
      have hball := raw_ball_le_actual P p μ angle L c hμ hL hangle
        (show 0 ≤ (2 : ℝ) ^ M by positivity)
      have hrange : 4 * (μ / L) * (2 : ℝ) ^ M ≤ r := by
        have hn := le_of_not_ge huN
        have hc := (le_div_iff₀ (by positivity : 0 < 4 * lam)).mp hn
        simpa only [mul_comm, lam] using hc
      have hball' := hball.trans (ballCount_mono _ _ hrange)
      exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hD hDtop ht) hA).trans
        (hh.trans (mul_le_mul_of_nonneg_left hball' hJ0))
  · let v := 2 * r / lam
    have hv : 1 ≤ v := by
      apply (le_div_iff₀ hlam).mpr
      change 64 * lam ≤ r at hrlo
      nlinarith only [hrlo, hlam]
    have hid : v = 128 * (r / (64 * lam)) := by dsimp only [v]; ring
    have hpow : v ^ t = (128 : ℝ) ^ t * (r / (64 * lam)) ^ t := by
      rw [hid, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 128) hD]
    by_cases hvN : v ≤ (2 : ℝ) ^ M
    · have hball := actual_ball_le_raw P p μ angle L c hμ hL hangle hr.le
      have he : (2 * L / μ) * r = v := by dsimp only [v, lam]; field_simp
      rw [he] at hball
      have hh := (raw_real_ball_bounds P M H Q J hH t s dens Bad Bcolumn Btube ht hdens hBad hC hcounts hp hv hvN).2
      rw [hpow] at hh
      simpa only [mul_assoc] using hball.trans hh
    · have hcard : ballCount (P.image (actualPoint μ angle L c)) (actualPoint μ angle L c p) r ≤ (P.card : ℝ) := by
        unfold ballCount
        rw [Finset.filter_image, Finset.card_image_of_injective _ (actualPoint_injective μ angle L c hμ hL)]
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      have hpowN := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ) ^ M) (le_of_not_ge hvN) ht
      have hbound := hcard.trans (hglobal.trans (mul_le_mul_of_nonneg_left hpowN hBad))
      rw [hpow] at hbound
      have hcoef : Bad ≤ realInterpolationLoss M H t * (9 * Bad) := by
        have hh := mul_le_mul_of_nonneg_right hJ hBad
        nlinarith only [hh, hBad]
      have hpownonneg : 0 ≤ (128 : ℝ) ^ t * (r / (64 * lam)) ^ t := by positivity
      have hh := hbound.trans (mul_le_mul_of_nonneg_right hcoef hpownonneg)
      simpa only [mul_assoc] using hh

end
end FullNormalizedAmbientAD
