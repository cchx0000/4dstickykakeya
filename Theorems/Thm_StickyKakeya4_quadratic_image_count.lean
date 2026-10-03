import Theorems.Thm_StickyKakeya4_noisy_affine_image_count

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
set_option Elab.async false

namespace QuadraticImageCount

open NoisyAffineImageCount
open scoped BigOperators

def time (δ x₀ : ℝ) (n : ℤ) : ℝ := x₀ + δ * (n : ℝ)

lemma time_gap (δ x₀ : ℝ) (hδ : 0 ≤ δ) (n m : ℤ) :
    |time δ x₀ n - time δ x₀ m| = δ * |(n : ℝ) - (m : ℝ)| := by
  rw [show time δ x₀ n - time δ x₀ m = δ * ((n : ℝ) - (m : ℝ)) by
    dsimp [time]; ring, abs_mul, abs_of_nonneg hδ]

/-- Count actual grid indices in a short neighborhood, using their extreme
indices. The source set need not fill any interval. -/
theorem near_vertex_card (J : Finset ℤ) (δ x₀ z r : ℝ)
    (hδ : 0 < δ) (hr : 0 ≤ r)
    (hnear : ∀ n ∈ J, |time δ x₀ n - z| ≤ r) :
    δ * (J.card : ℝ) ≤ 2 * r + δ := by
  apply integer_card_bound J δ (2 * r) hδ.le (by positivity)
  intro n hn m hm
  rw [← time_gap δ x₀ hδ.le n m]
  have heq : time δ x₀ n - time δ x₀ m =
      (time δ x₀ n - z) - (time δ x₀ m - z) := by ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith [hnear n hn, hnear m hm])

/-- After discarding a near-vertex set of at most half the actual indices,
one of the two actual sides retains at least a quarter of all indices. -/
theorem select_side (J : Finset ℤ) (t : ℤ → ℝ) (z r : ℝ)
    (hnear : 2 * (J.filter (fun n => |t n - z| < r)).card ≤ J.card) :
    ∃ S ⊆ J, J.card ≤ 4 * S.card ∧
      ((∀ n ∈ S, r ≤ t n - z) ∨ (∀ n ∈ S, t n - z ≤ -r)) := by
  classical
  let N := J.filter (fun n => |t n - z| < r)
  let P := J.filter (fun n => r ≤ t n - z)
  let L := J.filter (fun n => t n - z ≤ -r)
  have hcover : J ⊆ N ∪ (P ∪ L) := by
    intro n hn
    by_cases hp : r ≤ t n - z
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn, hp⟩))
    · by_cases hl : t n - z ≤ -r
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn, hl⟩))
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn, abs_lt.mpr ⟨by linarith, by linarith⟩⟩)
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hPL := Finset.card_union_le P L
  change 2 * N.card ≤ J.card at hnear
  by_cases hbig : L.card ≤ P.card
  · refine ⟨P, Finset.filter_subset _ _, by omega, Or.inl ?_⟩
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  · refine ⟨L, Finset.filter_subset _ _, by omega, Or.inr ?_⟩
    intro n hn
    exact (Finset.mem_filter.mp hn).2

/-- The density and M>=4 construct the required one-sided set at distance
lambda*rho/8 from the vertex. No side or slope certificate is an input. -/
theorem select_dense_side (J : Finset ℤ) (δ ρ lam x₀ z : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hlam : 0 < lam)
    (hfour : 4 ≤ J.card) (hdensity : lam * ρ / δ ≤ (J.card : ℝ)) :
    ∃ S ⊆ J, S.Nonempty ∧ J.card ≤ 4 * S.card ∧
      ((∀ n ∈ S, lam * ρ / 8 ≤ time δ x₀ n - z) ∨
        (∀ n ∈ S, time δ x₀ n - z ≤ -(lam * ρ / 8))) := by
  classical
  let N := J.filter (fun n => |time δ x₀ n - z| < lam * ρ / 8)
  have hcap : δ * (N.card : ℝ) ≤ 2 * (lam * ρ / 8) + δ := by
    apply near_vertex_card N δ x₀ z (lam * ρ / 8) hδ (by positivity)
    intro n hn
    exact (Finset.mem_filter.mp hn).2.le
  have hden := (div_le_iff₀ hδ).mp hdensity
  have hfourR : (4 : ℝ) ≤ J.card := by exact_mod_cast hfour
  have hnearR : (2 : ℝ) * N.card ≤ J.card := by nlinarith
  have hnear : 2 * N.card ≤ J.card := by exact_mod_cast hnearR
  obtain ⟨S, hSJ, hretain, hside⟩ := select_side J (time δ x₀) z (lam * ρ / 8) hnear
  have hpos : 0 < S.card := by omega
  exact ⟨S, hSJ, Finset.card_pos.mp hpos, hretain, hside⟩

/-- Exact square factorization supplies expansion on either side of the vertex. -/
lemma square_difference_lower (r u v : ℝ) (hr : 0 ≤ r)
    (hside : (r ≤ u ∧ r ≤ v) ∨ (u ≤ -r ∧ v ≤ -r)) :
    2 * r * |u - v| ≤ |u ^ 2 - v ^ 2| := by
  have hsum : 2 * r ≤ |u + v| := by
    rcases hside with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rw [abs_of_nonneg (by linarith : 0 ≤ u + v)]
      linarith
    · rw [abs_of_nonpos (by linarith : u + v ≤ 0)]
      linarith
  rw [show u ^ 2 - v ^ 2 = (u - v) * (u + v) by ring, abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsum (abs_nonneg (u - v))

/-- Same actual output cells and bounded noise give a quadratic-value gap cap. -/
lemma noisy_square_gap (Δ E b q u v y w : ℝ) (hΔ : 0 < Δ)
    (hy : |y - q - b * u ^ 2| ≤ E * Δ)
    (hw : |w - q - b * v ^ 2| ≤ E * Δ)
    (hcell : ⌊y / Δ⌋ = ⌊w / Δ⌋) :
    |b| * |u ^ 2 - v ^ 2| ≤ (1 + 2 * E) * Δ := by
  have hc := (same_floor_difference hΔ hcell).le
  let ey := y - q - b * u ^ 2
  let ew := w - q - b * v ^ 2
  have heq : b * (u ^ 2 - v ^ 2) = (y - w) - (ey - ew) := by
    dsimp [ey, ew]
    ring
  have ht : |b * (u ^ 2 - v ^ 2)| ≤ |y - w| + |ey| + |ew| := by
    rw [heq]
    exact (abs_sub _ _).trans (by linarith [abs_sub ey ew])
  rw [abs_mul] at ht
  dsimp [ey, ew] at ht
  linarith

/-- The scalar grid-gap estimate is derived from actual one-sided positions,
actual square differences and actual noisy floor-cell witnesses. -/
theorem quadratic_pair_gap (δ Δ E b q x₀ z r : ℝ) (n m : ℤ) (y w : ℝ)
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hr : 0 ≤ r)
    (hside : (r ≤ time δ x₀ n - z ∧ r ≤ time δ x₀ m - z) ∨
      (time δ x₀ n - z ≤ -r ∧ time δ x₀ m - z ≤ -r))
    (hy : |y - q - b * (time δ x₀ n - z) ^ 2| ≤ E * Δ)
    (hw : |w - q - b * (time δ x₀ m - z) ^ 2| ≤ E * Δ)
    (hcell : ⌊y / Δ⌋ = ⌊w / Δ⌋) :
    (2 * r * |b| * δ) * |(n : ℝ) - (m : ℝ)| ≤ (1 + 2 * E) * Δ := by
  have hl := square_difference_lower r (time δ x₀ n - z) (time δ x₀ m - z) hr hside
  have hl' := mul_le_mul_of_nonneg_left hl (abs_nonneg b)
  have hgap := noisy_square_gap Δ E b q (time δ x₀ n - z) (time δ x₀ m - z) y w hΔ hy hw hcell
  have heq : (time δ x₀ n - z) - (time δ x₀ m - z) = time δ x₀ n - time δ x₀ m := by ring
  rw [heq, time_gap δ x₀ hδ.le n m] at hl'
  calc
    _ = |b| * (2 * r * (δ * |(n : ℝ) - (m : ℝ)|)) := by ring
    _ ≤ |b| * |(time δ x₀ n - z) ^ 2 - (time δ x₀ m - z) ^ 2| := hl'
    _ ≤ _ := hgap

/-- Each actual noisy output cell has the proved sharp integer endpoint cap. -/
theorem quadratic_fiber_bound (S : Finset ℤ) (y : ℤ → ℝ)
    (δ Δ E b q x₀ z r : ℝ) (hδ : 0 < δ) (hΔ : 0 < Δ) (hE : 0 ≤ E) (hr : 0 ≤ r)
    (hside : (∀ n ∈ S, r ≤ time δ x₀ n - z) ∨ (∀ n ∈ S, time δ x₀ n - z ≤ -r))
    (herror : ∀ n ∈ S, |y n - q - b * (time δ x₀ n - z) ^ 2| ≤ E * Δ)
    (c : ℤ) :
    (2 * r * |b| * δ) * ((S.filter (fun n => ⌊y n / Δ⌋ = c)).card : ℝ) ≤
      (1 + 2 * E) * Δ + 2 * r * |b| * δ := by
  apply integer_card_bound _ (2 * r * |b| * δ) ((1 + 2 * E) * Δ) (by positivity) (by positivity)
  intro n hn m hm
  obtain ⟨hnS, hnc⟩ := Finset.mem_filter.mp hn
  obtain ⟨hmS, hmc⟩ := Finset.mem_filter.mp hm
  apply quadratic_pair_gap δ Δ E b q x₀ z r n m (y n) (y m) hδ hΔ hr
    ?_ (herror n hnS) (herror m hmS) (hnc.trans hmc.symm)
  rcases hside with h | h
  · exact Or.inl ⟨h n hnS, h m hmS⟩
  · exact Or.inr ⟨h n hnS, h m hmS⟩

/-- Sum the constructed caps over the ACTUAL image, with all repeated image
values and all noise collisions counted from their original time indices. -/
theorem quadratic_image_count (S : Finset ℤ) (y : ℤ → ℝ)
    (δ Δ E b q x₀ z r : ℝ) (hδ : 0 < δ) (hΔ : 0 < Δ) (hE : 0 ≤ E) (hr : 0 ≤ r)
    (hside : (∀ n ∈ S, r ≤ time δ x₀ n - z) ∨ (∀ n ∈ S, time δ x₀ n - z ≤ -r))
    (herror : ∀ n ∈ S, |y n - q - b * (time δ x₀ n - z) ^ 2| ≤ E * Δ) :
    (2 * r * |b| * δ) * (S.card : ℝ) ≤
      ((1 + 2 * E) * Δ + 2 * r * |b| * δ) *
        ((S.image (fun n => ⌊y n / Δ⌋)).card : ℝ) := by
  classical
  have hsum : (S.card : ℝ) =
      ∑ c ∈ S.image (fun n => ⌊y n / Δ⌋), ((S.filter (fun n => ⌊y n / Δ⌋ = c)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (fun n => ⌊y n / Δ⌋) S
  calc
    _ = ∑ c ∈ S.image (fun n => ⌊y n / Δ⌋),
        (2 * r * |b| * δ) * ((S.filter (fun n => ⌊y n / Δ⌋ = c)).card : ℝ) := by
      rw [hsum, Finset.mul_sum]
    _ ≤ ∑ _c ∈ S.image (fun n => ⌊y n / Δ⌋), ((1 + 2 * E) * Δ + 2 * r * |b| * δ) :=
      Finset.sum_le_sum (fun c _ => quadratic_fiber_bound S y δ Δ E b q x₀ z r hδ hΔ hE hr hside herror c)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring


set_option maxHeartbeats 200000

/-- The customary divided fiber cap, with its genuine positive denominator. -/
theorem quadratic_fiber_card_bound (S : Finset ℤ) (y : ℤ → ℝ)
    (δ Δ E b q x₀ z r : ℝ) (hδ : 0 < δ) (hΔ : 0 < Δ) (hE : 0 ≤ E)
    (hr : 0 < r) (hb : b ≠ 0)
    (hside : (∀ n ∈ S, r ≤ time δ x₀ n - z) ∨ (∀ n ∈ S, time δ x₀ n - z ≤ -r))
    (herror : ∀ n ∈ S, |y n - q - b * (time δ x₀ n - z) ^ 2| ≤ E * Δ)
    (c : ℤ) :
    ((S.filter (fun n => ⌊y n / Δ⌋ = c)).card : ℝ) ≤
      1 + (1 + 2 * E) * Δ / (2 * r * |b| * δ) := by
  have hcap := quadratic_fiber_bound S y δ Δ E b q x₀ z r hδ hΔ hE hr.le hside herror c
  have hpos : 0 < 2 * r * |b| * δ := by
    have habs := abs_pos.mpr hb
    positivity
  calc
    _ ≤ ((1 + 2 * E) * Δ + 2 * r * |b| * δ) / (2 * r * |b| * δ) :=
      (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hcap)
    _ = _ := by rw [add_div, div_self hpos.ne']; ring


/-- Construct the dense side AND derive its actual quadratic image lower bound.
The coefficient keeps lambda explicit, so no hidden lambda<=1 assumption is
needed. Neither a filled time interval nor an image-count certificate enters. -/
theorem exists_dense_quadratic_image (J : Finset ℤ) (y : ℤ → ℝ)
    (δ ρ lam Δ E b q x₀ z : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hlam : 0 < lam) (hΔ : 0 < Δ) (hE : 0 ≤ E)
    (hfour : 4 ≤ J.card) (hdensity : lam * ρ / δ ≤ (J.card : ℝ))
    (hmesh : ρ * |b| * δ ≤ Δ)
    (herror : ∀ n ∈ J, |y n - q - b * (time δ x₀ n - z) ^ 2| ≤ E * Δ) :
    ∃ S ⊆ J, S.Nonempty ∧ J.card ≤ 4 * S.card ∧
      ((∀ n ∈ S, lam * ρ / 8 ≤ time δ x₀ n - z) ∨
        (∀ n ∈ S, time δ x₀ n - z ≤ -(lam * ρ / 8))) ∧
      lam ^ 2 * ρ ^ 2 * |b| ≤ (16 + 32 * E + 4 * lam) * Δ *
        ((S.image (fun n => ⌊y n / Δ⌋)).card : ℝ) := by
  obtain ⟨S, hSJ, hSne, hret, hside⟩ := select_dense_side J δ ρ lam x₀ z hδ hρ hlam hfour hdensity
  have hcount := quadratic_image_count S y δ Δ E b q x₀ z (lam * ρ / 8)
    hδ hΔ hE (by positivity) hside (fun n hn => herror n (hSJ hn))
  have hden := (div_le_iff₀ hδ).mp hdensity
  have hretR : (J.card : ℝ) ≤ 4 * (S.card : ℝ) := by exact_mod_cast hret
  have hdenS : lam * ρ ≤ 4 * δ * (S.card : ℝ) := by
    calc
      lam * ρ ≤ (J.card : ℝ) * δ := hden
      _ ≤ (4 * (S.card : ℝ)) * δ := mul_le_mul_of_nonneg_right hretR hδ.le
      _ = _ := by ring
  have hmult := mul_le_mul_of_nonneg_left hdenS
    (show 0 ≤ lam * ρ * |b| by positivity)
  have hstart : lam ^ 2 * ρ ^ 2 * |b| ≤
      16 * ((2 * (lam * ρ / 8) * |b| * δ) * (S.card : ℝ)) := by
    calc
      _ = (lam * ρ * |b|) * (lam * ρ) := by ring
      _ ≤ (lam * ρ * |b|) * (4 * δ * (S.card : ℝ)) := hmult
      _ = _ := by ring
  have hmesh' := mul_le_mul_of_nonneg_left hmesh (show 0 ≤ lam / 4 by positivity)
  have hcoef : (1 + 2 * E) * Δ + 2 * (lam * ρ / 8) * |b| * δ ≤
      (1 + 2 * E + lam / 4) * Δ := by
    calc
      _ = (1 + 2 * E) * Δ + (lam / 4) * (ρ * |b| * δ) := by ring
      _ ≤ (1 + 2 * E) * Δ + (lam / 4) * Δ := add_le_add le_rfl hmesh'
      _ = _ := by ring
  have hC : 0 ≤ ((S.image (fun n => ⌊y n / Δ⌋)).card : ℝ) := Nat.cast_nonneg _
  refine ⟨S, hSJ, hSne, hret, hside, ?_⟩
  calc
    _ ≤ 16 * ((2 * (lam * ρ / 8) * |b| * δ) * (S.card : ℝ)) := hstart
    _ ≤ 16 * (((1 + 2 * E) * Δ + 2 * (lam * ρ / 8) * |b| * δ) *
        ((S.image (fun n => ⌊y n / Δ⌋)).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hcount (by norm_num)
    _ ≤ 16 * (((1 + 2 * E + lam / 4) * Δ) *
        ((S.image (fun n => ⌊y n / Δ⌋)).card : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef hC) (by norm_num)
    _ = _ := by ring


/-- The lower count also holds for the full actual witness image. -/
theorem dense_quadratic_image_count (J : Finset ℤ) (y : ℤ → ℝ)
    (δ ρ lam Δ E b q x₀ z : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hlam : 0 < lam) (hΔ : 0 < Δ) (hE : 0 ≤ E)
    (hfour : 4 ≤ J.card) (hdensity : lam * ρ / δ ≤ (J.card : ℝ))
    (hmesh : ρ * |b| * δ ≤ Δ)
    (herror : ∀ n ∈ J, |y n - q - b * (time δ x₀ n - z) ^ 2| ≤ E * Δ) :
    lam ^ 2 * ρ ^ 2 * |b| ≤ (16 + 32 * E + 4 * lam) * Δ *
      ((J.image (fun n => ⌊y n / Δ⌋)).card : ℝ) := by
  obtain ⟨S, hSJ, _, _, _, hcount⟩ :=
    exists_dense_quadratic_image J y δ ρ lam Δ E b q x₀ z hδ hρ hlam hΔ hE hfour hdensity hmesh herror
  have hc : ((S.image (fun n => ⌊y n / Δ⌋)).card : ℝ) ≤
      ((J.image (fun n => ⌊y n / Δ⌋)).card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hSJ))
  exact hcount.trans (mul_le_mul_of_nonneg_left hc (by positivity))


/-- With lambda a density fraction, the explicit source estimate is
lambda^2*rho^2*|b| <= 32*(1+E)*Delta times the actual occupied-cell count. -/
theorem unit_density_quadratic_image_count (J : Finset ℤ) (y : ℤ → ℝ)
    (δ ρ lam Δ E b q x₀ z : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hlam : 0 < lam) (hlamone : lam ≤ 1)
    (hΔ : 0 < Δ) (hE : 0 ≤ E)
    (hfour : 4 ≤ J.card) (hdensity : lam * ρ / δ ≤ (J.card : ℝ))
    (hmesh : ρ * |b| * δ ≤ Δ)
    (herror : ∀ n ∈ J, |y n - q - b * (time δ x₀ n - z) ^ 2| ≤ E * Δ) :
    lam ^ 2 * ρ ^ 2 * |b| ≤ 32 * (1 + E) * Δ *
      ((J.image (fun n => ⌊y n / Δ⌋)).card : ℝ) := by
  have h := dense_quadratic_image_count J y δ ρ lam Δ E b q x₀ z
    hδ hρ hlam hΔ hE hfour hdensity hmesh herror
  have hc : 16 + 32 * E + 4 * lam ≤ 32 * (1 + E) := by linarith only [hlamone]
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hΔ.le) (Nat.cast_nonneg _))


/-- A real interval containing at least four actual mesh points controls the
density parameter. The bound is derived from integer spacing, not postulated. -/
theorem interval_density_le (J : Finset ℤ) (δ ρ lam x₀ lo : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hfour : 4 ≤ J.card)
    (hdensity : lam * ρ / δ ≤ (J.card : ℝ))
    (hinterval : ∀ n ∈ J, lo ≤ time δ x₀ n ∧ time δ x₀ n ≤ lo + ρ) :
    lam ≤ 4 / 3 := by
  have hcap : δ * (J.card : ℝ) ≤ ρ + δ := by
    have h := near_vertex_card J δ x₀ (lo + ρ / 2) (ρ / 2) hδ (by positivity) (by
      intro n hn
      obtain ⟨hl, hu⟩ := hinterval n hn
      exact abs_le.mpr ⟨by linarith only [hl], by linarith only [hu]⟩)
    linarith only [h]
  have hden := (div_le_iff₀ hδ).mp hdensity
  have hfourR : (4 : ℝ) ≤ J.card := by exact_mod_cast hfour
  have hfourδ := mul_le_mul_of_nonneg_left hfourR hδ.le
  have hmul : lam * ρ ≤ (4 / 3 : ℝ) * ρ := by linarith only [hcap, hden, hfourδ]
  exact (mul_le_mul_iff_left₀ hρ).mp hmul

/-- The source-interval version of the quadratic image lower bound. All side
selection and density bounds are derived from the actual original time set;
no separate upper bound on lambda or KT upper bound is assumed. -/
theorem interval_quadratic_image_count (J : Finset ℤ) (y : ℤ → ℝ)
    (δ ρ lam Δ E b q x₀ z lo : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hlam : 0 < lam) (hΔ : 0 < Δ) (hE : 0 ≤ E)
    (hfour : 4 ≤ J.card) (hdensity : lam * ρ / δ ≤ (J.card : ℝ))
    (hinterval : ∀ n ∈ J, lo ≤ time δ x₀ n ∧ time δ x₀ n ≤ lo + ρ)
    (hmesh : ρ * |b| * δ ≤ Δ)
    (herror : ∀ n ∈ J, |y n - q - b * (time δ x₀ n - z) ^ 2| ≤ E * Δ) :
    lam ^ 2 * ρ ^ 2 * |b| ≤ 32 * (1 + E) * Δ *
      ((J.image (fun n => ⌊y n / Δ⌋)).card : ℝ) := by
  have hlamBound := interval_density_le J δ ρ lam x₀ lo hδ hρ hfour hdensity hinterval
  have h := dense_quadratic_image_count J y δ ρ lam Δ E b q x₀ z
    hδ hρ hlam hΔ hE hfour hdensity hmesh herror
  have hc : 16 + 32 * E + 4 * lam ≤ 32 * (1 + E) := by linarith only [hlamBound]
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hΔ.le) (Nat.cast_nonneg _))


end QuadraticImageCount
