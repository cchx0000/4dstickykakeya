import Theorems.Thm_StickyKakeya4_euclidean_alignment_patches
import Theorems.Thm_StickyKakeya4_finite_voronoi_real_ad_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeLiteralEuclideanAD
open Classical Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening

/-- This is the literal coordinate map, with no translation or regridding. -/
lemma toLp_injective (d : ℕ) :
    Function.Injective (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) :=
  WithLp.toLp_injective 2

lemma sup_dist_le_toLp {d : ℕ} (x y : Fin d → ℝ) :
    dist x y ≤ dist (WithLp.toLp 2 x) (WithLp.toLp 2 y) :=
  EuclideanAlignmentPatches.sup_dist_le x y

/-- Dimension-only comparison, also valid for the empty coordinate type. -/
lemma toLp_dist_le {d : ℕ} (x y : Fin d → ℝ) :
    dist (WithLp.toLp 2 x) (WithLp.toLp 2 y) ≤ max 1 (d : ℝ) * dist x y := by
  have hcoord (j : Fin d) : |x j - y j| ≤ dist x y := by
    simpa only [Real.dist_eq] using dist_le_pi_dist x y j
  exact (EuclideanAlignmentPatches.euclidean_dist_le_card_mul x y (dist x y)
    dist_nonneg hcoord).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 (d : ℝ)) dist_nonneg)

/-- Sup-metric AD transfers to the literal Euclidean image at the same
base mesh. Below the reduced query radius, the actual center supplies the
lower bound. No global count or AD conclusion for the image is assumed. -/
theorem ADBounds_toLp {d : ℕ} (A : Finset (Fin d → ℝ))
    {mu K s : ℝ} (hmu : 0 < mu) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hAD : ADBounds A mu K s) :
    ADBounds (A.image (WithLp.toLp 2)) mu ((max 1 (d : ℝ)) ^ s * K) s := by
  let L : ℝ := max 1 (d : ℝ)
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hLp : 0 < L ^ s := Real.rpow_pos_of_pos hL s
  have hLp1 : 1 ≤ L ^ s := by
    have hh := Real.rpow_le_rpow_of_exponent_le hL1 hs
    simpa only [Real.rpow_zero] using hh
  have hKle : K ≤ L ^ s * K := le_mul_of_one_le_left hK0.le hLp1
  intro z hz r hmur hr1
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hz
  have hr : 0 < r := hmu.trans_le hmur
  let B := A.filter (fun x => dist (WithLp.toLp 2 x) (WithLp.toLp 2 c) ≤ r)
  have hball : carrierBall (A.image (WithLp.toLp 2)) (WithLp.toLp 2 c) r =
      B.image (WithLp.toLp 2) := by
    ext y
    simp only [B, mem_carrierBall, mem_image, mem_filter]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hdist⟩
      exact ⟨x, ⟨hx, hdist⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hdist⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hdist⟩
  rw [hball, card_image_of_injective B (toLp_injective d)]
  change (r / mu) ^ s / (L ^ s * K) ≤ (B.card : ℝ) ∧
    (B.card : ℝ) ≤ (L ^ s * K) * (r / mu) ^ s
  constructor
  · by_cases hquery : mu ≤ r / L
    · have hsub : carrierBall A c (r / L) ⊆ B := by
        intro x hx
        obtain ⟨hxA, hdist⟩ := (mem_carrierBall A x c (r / L)).mp hx
        apply mem_filter.mpr
        refine ⟨hxA, ?_⟩
        calc
          dist (WithLp.toLp 2 x) (WithLp.toLp 2 c) ≤ L * dist x c := toLp_dist_le x c
          _ ≤ L * (r / L) := mul_le_mul_of_nonneg_left hdist hL.le
          _ = r := mul_div_cancel₀ r hL.ne'
      have hquery1 : r / L ≤ 1 := (div_le_self hr.le hL1).trans hr1
      have hlo := (hAD c hc (r / L) hquery hquery1).1
      have hratio : r / mu = L * ((r / L) / mu) := by field_simp
      have hpow : (r / mu) ^ s = L ^ s * ((r / L) / mu) ^ s := by
        rw [hratio, Real.mul_rpow hL.le (by positivity : 0 ≤ (r / L) / mu)]
      have heq : (r / mu) ^ s / (L ^ s * K) = ((r / L) / mu) ^ s / K := by
        rw [hpow]
        exact mul_div_mul_left _ _ hLp.ne'
      rw [heq]
      exact hlo.trans (by exact_mod_cast card_le_card hsub)
    · have hsmall : r < mu * L := (div_lt_iff₀ hL).mp (lt_of_not_ge hquery)
      have hratio : r / mu ≤ L := (div_le_iff₀ hmu).mpr (by linarith only [hsmall])
      have hpow := Real.rpow_le_rpow (div_nonneg hr.le hmu.le) hratio hs
      have hone : (r / mu) ^ s / (L ^ s * K) ≤ 1 :=
        (div_le_one (mul_pos hLp hK0)).mpr
          (hpow.trans (le_mul_of_one_le_right hLp.le hK))
      have hself : c ∈ B := mem_filter.mpr ⟨hc, by simp only [dist_self]; exact hr.le⟩
      have hcard : 1 ≤ B.card := Nat.succ_le_iff.mpr (card_pos.mpr ⟨c, hself⟩)
      exact hone.trans (by exact_mod_cast hcard)
  · have hsub : B ⊆ carrierBall A c r := by
      intro x hx
      obtain ⟨hxA, hdist⟩ := mem_filter.mp hx
      exact (mem_carrierBall A x c r).mpr ⟨hxA, (sup_dist_le_toLp x c).trans hdist⟩
    calc
      (B.card : ℝ) ≤ (carrierBall A c r).card := by exact_mod_cast card_le_card hsub
      _ ≤ K * (r / mu) ^ s := (hAD c hc r hmur hr1).2
      _ ≤ (L ^ s * K) * (r / mu) ^ s :=
        mul_le_mul_of_nonneg_right hKle (Real.rpow_nonneg (div_nonneg hr.le hmu.le) s)

/-- One-dimensional coordinate presentation has exactly the same AD
constant and base mesh. -/
theorem one_dimensional_AD (A : Finset (Fin 1 → ℝ))
    {mu K s : ℝ} (hmu : 0 < mu) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hAD : ADBounds A mu K s) :
    ADBounds (A.image (WithLp.toLp 2)) mu K s := by
  simpa only [Nat.cast_one, max_self, Real.one_rpow, one_mul] using ADBounds_toLp A hmu hK hs hAD

/-- The literal planar type used by LiteralAligned.ambient requires only
the displayed factor 2^s; its original labels and base mesh are unchanged. -/
theorem planar_AD (A : Finset (Fin 2 → ℝ))
    {mu K s : ℝ} (hmu : 0 < mu) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hAD : ADBounds A mu K s) :
    ADBounds (A.image EuclideanAlignmentPatches.euclidean) mu ((2 : ℝ) ^ s * K) s := by
  have hh := ADBounds_toLp A hmu hK hs hAD
  norm_num only [Nat.cast_ofNat, max_eq_right (by norm_num : (1 : ℝ) ≤ 2)] at hh
  exact hh

end NativeLiteralEuclideanAD
