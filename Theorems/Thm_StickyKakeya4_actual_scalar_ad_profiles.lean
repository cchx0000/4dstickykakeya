import Theorems.Thm_StickyKakeya4_literal_affine_fiber_coordinates
import Theorems.Thm_StickyKakeya4_real_scalar_ad_interpolation

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace ActualScalarADProfiles

open NativeDyadicTubeStopping ShearedGridADReference SmallFiberAlignment FractionalFiberAlignment
open NativeFractionalReferenceComposition LiteralAffineFiberCoordinates
open DyadicAlignmentParameters DyadicADInterpolation RealScalarADInterpolation

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual longitudinal integer labels of one parent have span at most
N=b/μ. This concerns vertex labels and makes no source injectivity claim. -/
theorem parent_time_labels_close (Ω : Finset Plane) {μ angle x₀ b : ℝ} {N : ℕ}
    (hμ : 0 < μ) (hNscale : μ * (N : ℝ) = b)
    (hparent : ∀ p ∈ Ω, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b) :
    ∀ k ∈ Ω.image (vertex μ angle), ∀ l ∈ Ω.image (vertex μ angle), |k.1 - l.1| ≤ (N : ℤ) := by
  intro k hk l hl
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hl
  have hupper : p 0 / μ ≤ q 0 / μ + (N : ℝ) := by
    apply (div_le_iff₀ hμ).mpr
    have he : (q 0 / μ + (N : ℝ)) * μ = q 0 + b := by rw [add_mul, div_mul_cancel₀ _ hμ.ne', mul_comm, hNscale]
    rw [he]
    linarith only [(hparent p hp).2, (hparent q hq).1]
  have hlower : q 0 / μ ≤ p 0 / μ + (N : ℝ) := by
    apply (div_le_iff₀ hμ).mpr
    have he : (p 0 / μ + (N : ℝ)) * μ = p 0 + b := by rw [add_mul, div_mul_cancel₀ _ hμ.ne', mul_comm, hNscale]
    rw [he]
    linarith only [(hparent q hq).2, (hparent p hp).1]
  have hu := Int.floor_mono hupper
  have hl := Int.floor_mono hlower
  rw [Int.floor_add_natCast] at hu hl
  change |⌊p 0 / μ⌋ - ⌊q 0 / μ⌋| ≤ (N : ℤ)
  exact abs_le.mpr ⟨by omega, by omega⟩

lemma fiberBall_top_eq (P : Finset Vertex) (N : ℕ)
    (hspan : ∀ k ∈ P, ∀ l ∈ P, |k.1 - l.1| ≤ (N : ℤ)) {p : Vertex} (hp : p ∈ P) :
    fiberBall P N p = fiber P p.2 := by
  ext k
  simp only [fiberBall, fiber, Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hspan k h.1 p hp⟩⟩


def workingRadii (M H : ℕ) (j : Fin (H + 1)) : ℕ := 2 ^ level M H j

def realInterpolationLoss (M H : ℕ) (s : ℝ) : ℝ := (2 : ℝ) ^ s * scalePower s (gap M H)

def fullInterpolationLoss (M H : ℕ) (s : ℝ) : ℝ := max (realInterpolationLoss M H s) ((64 : ℝ) ^ s)

lemma fiber_ballCount_eq (P : Finset Vertex) (μ L : ℝ) (c : Plane)
    (hμ : 0 < μ) (hL : 0 < L) (p : Vertex) (R : ℕ) :
    ballCount (fiberCoordinates P μ L c p.2) (timeCoord μ (c 0) L p.1) ((μ / L) * (R : ℝ)) =
      ((fiberBall P R p).card : ℝ) := by
  refine Eq.trans ?_ (congrArg (fun n : ℕ => (n : ℝ)) (fiberCoordinates_ball_card P μ L c hμ hL p R))
  unfold ballCount
  apply congrArg (fun F : Finset ℝ => (F.card : ℝ))
  ext x
  simp only [Finset.mem_filter]

lemma quotient_ballCount_eq (P : Finset Vertex) (μ angle L : ℝ) (c : Plane)
    (hμ : 0 < μ) (hL : 0 < L) (y : Normal 1) (R : ℕ) :
    ballCount (quotientCoordinates P μ angle L c) (normalCoord μ angle L c y) ((μ / L) * (R : ℝ)) =
      ((normalBall P R y).card : ℝ) := by
  refine Eq.trans ?_ (congrArg (fun n : ℕ => (n : ℝ)) (quotientCoordinates_ball_card P μ angle L c hμ hL y R))
  unfold ballCount
  apply congrArg (fun F : Finset ℝ => (F.card : ℝ))
  ext x
  simp only [Finset.mem_filter]

/-- Real normalized radii up to one, including the range above 1/64. The
global upper count is an actual cardinality bound; it does not identify the
radius-1/64 ball with the entire set. -/
theorem normalized_full_ball_interpolation {X : Type*} [PseudoMetricSpace X]
    (S : Finset X) (x : X) (M H : ℕ) (hH : 0 < H)
    {μ s A B G r : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hworking : ∀ j ≤ H,
      A * ((2 : ℝ) ^ level M H j) ^ s ≤ ballCount S x (scale μ (level M H j)) ∧
        ballCount S x (scale μ (level M H j)) ≤ B * ((2 : ℝ) ^ level M H j) ^ s)
    (hglobal : (S.card : ℝ) ≤ G * ((2 : ℝ) ^ M) ^ s)
    (hscale : μ * (2 : ℝ) ^ M = 1 / 64) (hlo : μ ≤ r) (hhi : r ≤ 1) :
    A * (r / μ) ^ s ≤ fullInterpolationLoss M H s * ballCount S x r ∧
      ballCount S x r ≤ fullInterpolationLoss M H s * max B G * (r / μ) ^ s := by
  have hC64 : (64 : ℝ) ^ s ≤ fullInterpolationLoss M H s := le_max_right _ _
  have hCJ : realInterpolationLoss M H s ≤ fullInterpolationLoss M H s := le_max_left _ _
  have h64 : 1 ≤ (64 : ℝ) ^ s := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 64) hs
  have hC : 1 ≤ fullInterpolationLoss M H s := h64.trans hC64
  have hC0 : 0 ≤ fullInterpolationLoss M H s := zero_le_one.trans hC
  have hpow : 0 ≤ (r / μ) ^ s := Real.rpow_nonneg (div_nonneg (hμ.le.trans hlo) hμ.le) _
  have hcount := ballCount_nonneg S x r
  by_cases hr : r ≤ scale μ M
  · have hh := real_ball_interpolation S x M H hH hμ hs hA hB hworking hlo hr
    refine ⟨hh.1.trans (mul_le_mul_of_nonneg_right hCJ hcount), ?_⟩
    calc
      _ ≤ realInterpolationLoss M H s * B * (r / μ) ^ s := hh.2
      _ ≤ fullInterpolationLoss M H s * B * (r / μ) ^ s :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCJ hB) hpow
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left B G) hC0) hpow
  · have htop : A * ((2 : ℝ) ^ M) ^ s ≤ ballCount S x (μ * (2 : ℝ) ^ M) := by
      simpa only [level_endpoint M H hH, scale] using (hworking H le_rfl).1
    have hrlo : μ * (2 : ℝ) ^ M ≤ r := le_of_not_ge hr
    have hrhi : r ≤ 64 * (μ * (2 : ℝ) ^ M) := by rw [hscale]; norm_num; exact hhi
    have hh := top_scale_extension S x hμ (by positivity : 0 < (2 : ℝ) ^ M) hs hA hG
      (by norm_num : (0 : ℝ) ≤ 64) htop hglobal hrlo hrhi
    refine ⟨hh.1.trans (mul_le_mul_of_nonneg_right hC64 hcount), ?_⟩
    calc
      _ ≤ G * (r / μ) ^ s := hh.2
      _ ≤ max B G * (r / μ) ^ s := mul_le_mul_of_nonneg_right (le_max_right B G) hpow
      _ ≤ fullInterpolationLoss M H s * (max B G * (r / μ) ^ s) :=
        le_mul_of_one_le_left (mul_nonneg (hG.trans (le_max_right B G)) hpow) hC
      _ = _ := by ring

theorem fiber_real_ball_bounds (P : Finset Vertex) (M H Q J : ℕ) (hH : 0 < H)
    (t s dens Bad Bcolumn Btube μ L : ℝ) (c : Plane) (hμ : 0 < μ) (hL : 0 < L)
    (hs : 0 ≤ s) (hdens : 0 ≤ dens) (hBtube : 0 ≤ Btube)
    (hC : 0 < comparisonCost (H + 1) J Q * Bcolumn * Btube)
    (hcounts : RefinedCounts P (workingRadii M H) (2 ^ M) Q J t s dens Bad Bcolumn Btube)
    {p : Vertex} (hp : p ∈ P) {r : ℝ} (hrlo : μ / L ≤ r) (hrhi : r ≤ (μ / L) * (2 : ℝ) ^ M) :
    (dens / (comparisonCost (H + 1) J Q * Bcolumn * Btube)) * (r / (μ / L)) ^ s ≤
        realInterpolationLoss M H s * ballCount (fiberCoordinates P μ L c p.2) (timeCoord μ (c 0) L p.1) r ∧
      ballCount (fiberCoordinates P μ L c p.2) (timeCoord μ (c 0) L p.1) r ≤
        realInterpolationLoss M H s * Btube * (r / (μ / L)) ^ s := by
  have hw : ∀ j ≤ H,
      (dens / (comparisonCost (H + 1) J Q * Bcolumn * Btube)) * ((2 : ℝ) ^ level M H j) ^ s ≤
        ballCount (fiberCoordinates P μ L c p.2) (timeCoord μ (c 0) L p.1) (scale (μ / L) (level M H j)) ∧
      ballCount (fiberCoordinates P μ L c p.2) (timeCoord μ (c 0) L p.1) (scale (μ / L) (level M H j)) ≤
        Btube * ((2 : ℝ) ^ level M H j) ^ s := by
    intro j hj
    let jj : Fin (H + 1) := ⟨j, by omega⟩
    have h := (hcounts p hp).2 jj
    have hradius : scale (μ / L) (level M H j) = (μ / L) * (workingRadii M H jj : ℝ) := by
      simp only [scale, workingRadii, jj, Nat.cast_pow, Nat.cast_ofNat]
    have hlo : dens * ((2 : ℝ) ^ level M H j) ^ s ≤
        (comparisonCost (H + 1) J Q * Bcolumn * Btube) *
          ballCount (fiberCoordinates P μ L c p.2) (timeCoord μ (c 0) L p.1) (scale (μ / L) (level M H j)) := by
      rw [hradius, fiber_ballCount_eq P μ L c hμ hL p]
      simpa only [workingRadii, jj, Nat.cast_pow, Nat.cast_ofNat] using h.2.2.1
    have hup : ballCount (fiberCoordinates P μ L c p.2) (timeCoord μ (c 0) L p.1) (scale (μ / L) (level M H j)) ≤
        Btube * ((2 : ℝ) ^ level M H j) ^ s := by
      rw [hradius, fiber_ballCount_eq P μ L c hμ hL p]
      simpa only [workingRadii, jj, Nat.cast_pow, Nat.cast_ofNat] using h.2.2.2.1
    refine ⟨?_, hup⟩
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hC).mpr
    simpa only [mul_comm] using hlo
  exact real_ball_interpolation _ _ M H hH (div_pos hμ hL) hs (div_nonneg hdens hC.le) hBtube hw hrlo hrhi

theorem quotient_real_ball_bounds (P : Finset Vertex) (M H Q J : ℕ) (hH : 0 < H)
    (t s dens Bad Bcolumn Btube μ angle L : ℝ) (c : Plane) (hμ : 0 < μ) (hL : 0 < L)
    (hst : s ≤ t) (hdens : 0 < dens)
    (hClow : 0 < comparisonCost (H + 1) J Q * Bad * Btube)
    (hCup : 0 ≤ comparisonCost (H + 1) J Q * Bcolumn * Bad * Btube)
    (hcounts : RefinedCounts P (workingRadii M H) (2 ^ M) Q J t s dens Bad Bcolumn Btube)
    {p : Vertex} (hp : p ∈ P) {r : ℝ} (hrlo : μ / L ≤ r) (hrhi : r ≤ (μ / L) * (2 : ℝ) ^ M) :
    (dens / (comparisonCost (H + 1) J Q * Bad * Btube)) * (r / (μ / L)) ^ (t - s) ≤
        realInterpolationLoss M H (t - s) *
          ballCount (quotientCoordinates P μ angle L c) (normalCoord μ angle L c p.2) r ∧
      ballCount (quotientCoordinates P μ angle L c) (normalCoord μ angle L c p.2) r ≤
        realInterpolationLoss M H (t - s) *
          ((comparisonCost (H + 1) J Q * Bcolumn * Bad * Btube) / dens) * (r / (μ / L)) ^ (t - s) := by
  have hw : ∀ j ≤ H,
      (dens / (comparisonCost (H + 1) J Q * Bad * Btube)) * ((2 : ℝ) ^ level M H j) ^ (t - s) ≤
        ballCount (quotientCoordinates P μ angle L c) (normalCoord μ angle L c p.2) (scale (μ / L) (level M H j)) ∧
      ballCount (quotientCoordinates P μ angle L c) (normalCoord μ angle L c p.2) (scale (μ / L) (level M H j)) ≤
        ((comparisonCost (H + 1) J Q * Bcolumn * Bad * Btube) / dens) * ((2 : ℝ) ^ level M H j) ^ (t - s) := by
    intro j hj
    let jj : Fin (H + 1) := ⟨j, by omega⟩
    have h := (hcounts p hp).2 jj
    have hradius : scale (μ / L) (level M H j) = (μ / L) * (workingRadii M H jj : ℝ) := by
      simp only [scale, workingRadii, jj, Nat.cast_pow, Nat.cast_ofNat]
    have hlo : dens * ((2 : ℝ) ^ level M H j) ^ (t - s) ≤
        (comparisonCost (H + 1) J Q * Bad * Btube) *
          ballCount (quotientCoordinates P μ angle L c) (normalCoord μ angle L c p.2) (scale (μ / L) (level M H j)) := by
      rw [hradius, quotient_ballCount_eq P μ angle L c hμ hL p.2]
      simpa only [workingRadii, jj, Nat.cast_pow, Nat.cast_ofNat] using h.2.2.2.2.1
    have hup : dens * ballCount (quotientCoordinates P μ angle L c) (normalCoord μ angle L c p.2)
        (scale (μ / L) (level M H j)) ≤
        comparisonCost (H + 1) J Q * Bcolumn * Bad * Btube * ((2 : ℝ) ^ level M H j) ^ (t - s) := by
      rw [hradius, quotient_ballCount_eq P μ angle L c hμ hL p.2]
      simpa only [workingRadii, jj, Nat.cast_pow, Nat.cast_ofNat] using h.2.2.2.2.2
    constructor
    · rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hClow).mpr
      simpa only [mul_comm] using hlo
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hdens).mpr
      simpa only [mul_comm] using hup
  exact real_ball_interpolation _ _ M H hH (div_pos hμ hL) (sub_nonneg.mpr hst)
    (div_nonneg hdens.le hClow.le) (div_nonneg hCup hdens.le) hw hrlo hrhi

end
end ActualScalarADProfiles
