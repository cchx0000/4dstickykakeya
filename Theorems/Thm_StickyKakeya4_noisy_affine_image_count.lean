import Mathlib

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace NoisyAffineImageCount

open scoped BigOperators

/-- Equal actual output cells have coordinate difference below the cell width. -/
lemma same_floor_difference {ρ y z : ℝ} (hρ : 0 < ρ)
    (hcell : ⌊y / ρ⌋ = ⌊z / ρ⌋) : |y - z| < ρ := by
  have hylo := (le_div_iff₀ hρ).mp (Int.floor_le (y / ρ))
  have hyhi := (div_lt_iff₀ hρ).mp (Int.lt_floor_add_one (y / ρ))
  have hzlo := (le_div_iff₀ hρ).mp (Int.floor_le (z / ρ))
  have hzhi := (div_lt_iff₀ hρ).mp (Int.lt_floor_add_one (z / ρ))
  rw [hcell] at hylo hyhi
  exact abs_lt.mpr ⟨by nlinarith, by nlinarith⟩

/-- Two actual noisy affine witnesses in one cell control their integer gap. -/
theorem noisy_pair_gap (δ ρ E b x₀ q y z : ℝ) (n m : ℤ)
    (hδ : 0 < δ) (hρ : 0 < ρ)
    (hy : |y - q - b * (x₀ + δ * (n : ℝ))| ≤ E * δ)
    (hz : |z - q - b * (x₀ + δ * (m : ℝ))| ≤ E * δ)
    (hcell : ⌊y / ρ⌋ = ⌊z / ρ⌋) :
    |b| * δ * |(n : ℝ) - (m : ℝ)| ≤ ρ + 2 * E * δ := by
  have hout := (same_floor_difference hρ hcell).le
  let en := y - q - b * (x₀ + δ * (n : ℝ))
  let em := z - q - b * (x₀ + δ * (m : ℝ))
  have heq : b * δ * ((n : ℝ) - (m : ℝ)) = (y - z) - (en - em) := by
    dsimp [en, em]
    ring
  have htri : |b * δ * ((n : ℝ) - (m : ℝ))| ≤ |y - z| + |en| + |em| := by
    rw [heq]
    exact (abs_sub _ _).trans (by linarith [abs_sub en em])
  rw [abs_mul, abs_mul, abs_of_pos hδ] at htri
  dsimp [en, em] at htri
  linarith

/-- The cardinality of any finite integer set is bounded by its ACTUAL extremes.
No interval-filling assumption is made. -/
lemma integer_card_le_span (J : Finset ℤ) (hJ : J.Nonempty) :
    (J.card : ℝ) ≤ (J.max' hJ : ℝ) - (J.min' hJ : ℝ) + 1 := by
  have hminmax : J.min' hJ ≤ J.max' hJ := Finset.min'_le _ _ (Finset.max'_mem _ _)
  have hsub : J ⊆ Finset.Icc (J.min' hJ) (J.max' hJ) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hn, Finset.le_max' _ _ hn⟩
  have hc := Finset.card_le_card hsub
  have hi := Int.card_Icc_of_le (a := J.min' hJ) (b := J.max' hJ) (by omega)
  have hreal : ((Finset.Icc (J.min' hJ) (J.max' hJ)).card : ℝ) =
      (J.max' hJ : ℝ) + 1 - (J.min' hJ : ℝ) := by exact_mod_cast hi
  have hcle : (J.card : ℝ) ≤ ((Finset.Icc (J.min' hJ) (J.max' hJ)).card : ℝ) :=
    Nat.cast_le.mpr hc
  linarith

/-- A witnessed pairwise integer-gap bound implies the sharp additive-one cap. -/
theorem integer_card_bound (J : Finset ℤ) (β C : ℝ) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hgap : ∀ n ∈ J, ∀ m ∈ J, β * |(n : ℝ) - (m : ℝ)| ≤ C) :
    β * (J.card : ℝ) ≤ C + β := by
  classical
  by_cases hJ : J.Nonempty
  · have hminmax : (J.min' hJ : ℝ) ≤ (J.max' hJ : ℝ) :=
      Int.cast_le.mpr (Finset.min'_le _ _ (Finset.max'_mem _ _))
    have hg := hgap (J.max' hJ) (Finset.max'_mem _ _) (J.min' hJ) (Finset.min'_mem _ _)
    rw [abs_of_nonneg (sub_nonneg.mpr hminmax)] at hg
    have hc := mul_le_mul_of_nonneg_left (integer_card_le_span J hJ) hβ
    nlinarith
  · have he : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    simp only [he, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact add_nonneg hC hβ

/-- At arbitrary positive output mesh rho, the actual noisy image has bounded
inverse fibers. The additive |b|*delta term is the integer endpoint cost. -/
theorem noisy_fiber_bound (J : Finset ℤ) (y : ℤ → ℝ) (δ ρ E b x₀ q : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hE : 0 ≤ E)
    (herror : ∀ n ∈ J, |y n - q - b * (x₀ + δ * (n : ℝ))| ≤ E * δ)
    (c : ℤ) :
    |b| * δ * ((J.filter (fun n => ⌊y n / ρ⌋ = c)).card : ℝ) ≤
      ρ + 2 * E * δ + |b| * δ := by
  apply integer_card_bound _ (|b| * δ) (ρ + 2 * E * δ) (by positivity) (by positivity)
  intro n hn m hm
  obtain ⟨hnJ, hnc⟩ := Finset.mem_filter.mp hn
  obtain ⟨hmJ, hmc⟩ := Finset.mem_filter.mp hm
  exact noisy_pair_gap δ ρ E b x₀ q (y n) (y m) n m hδ hρ
    (herror n hnJ) (herror m hmJ) (hnc.trans hmc.symm)

/-- Sum the proved caps over the actual occupied output cells. -/
theorem noisy_image_count (J : Finset ℤ) (y : ℤ → ℝ) (δ ρ E b x₀ q : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hE : 0 ≤ E)
    (herror : ∀ n ∈ J, |y n - q - b * (x₀ + δ * (n : ℝ))| ≤ E * δ) :
    |b| * δ * (J.card : ℝ) ≤
      (ρ + 2 * E * δ + |b| * δ) * ((J.image (fun n => ⌊y n / ρ⌋)).card : ℝ) := by
  classical
  have hsum : (J.card : ℝ) =
      ∑ c ∈ J.image (fun n => ⌊y n / ρ⌋), ((J.filter (fun n => ⌊y n / ρ⌋ = c)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (fun n => ⌊y n / ρ⌋) J
  calc
    _ = ∑ c ∈ J.image (fun n => ⌊y n / ρ⌋),
        |b| * δ * ((J.filter (fun n => ⌊y n / ρ⌋ = c)).card : ℝ) := by rw [hsum, Finset.mul_sum]
    _ ≤ ∑ _c ∈ J.image (fun n => ⌊y n / ρ⌋), (ρ + 2 * E * δ + |b| * δ) :=
      Finset.sum_le_sum (fun c _ => noisy_fiber_bound J y δ ρ E b x₀ q hδ hρ hE herror c)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- The requested delta-cell cap, with no unproved inverse-image hypothesis. -/
theorem delta_fiber_bound (J : Finset ℤ) (y : ℤ → ℝ) (δ E b x₀ q : ℝ)
    (hδ : 0 < δ) (hE : 0 ≤ E)
    (herror : ∀ n ∈ J, |y n - q - b * (x₀ + δ * (n : ℝ))| ≤ E * δ)
    (c : ℤ) :
    |b| * ((J.filter (fun n => ⌊y n / δ⌋ = c)).card : ℝ) ≤ 2 * E + 1 + |b| := by
  have h := noisy_fiber_bound J y δ δ E b x₀ q hδ hδ hE herror c
  nlinarith

/-- The requested whole-image count at the original mesh. The proof even
allows b=0; for b nonzero the inequality gives a positive image lower bound. -/
theorem delta_image_count (J : Finset ℤ) (y : ℤ → ℝ) (δ E b x₀ q : ℝ)
    (hδ : 0 < δ) (hE : 0 ≤ E)
    (herror : ∀ n ∈ J, |y n - q - b * (x₀ + δ * (n : ℝ))| ≤ E * δ) :
    |b| * (J.card : ℝ) ≤
      (2 * E + 1 + |b|) * ((J.image (fun n => ⌊y n / δ⌋)).card : ℝ) := by
  have h := noisy_image_count J y δ δ E b x₀ q hδ hδ hE herror
  nlinarith

/-- Original labels are retained when the scalar index is injective on their
actual source set. No injectivity of the noisy output is required. -/
theorem labelled_noisy_fiber_bound {α : Type*} (A : Finset α)
    (index : α → ℤ) (y : α → ℝ) (δ ρ E b x₀ q : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hE : 0 ≤ E)
    (hinj : Set.InjOn index (↑A : Set α))
    (herror : ∀ a ∈ A, |y a - q - b * (x₀ + δ * (index a : ℝ))| ≤ E * δ)
    (c : ℤ) :
    |b| * δ * ((A.filter (fun a => ⌊y a / ρ⌋ = c)).card : ℝ) ≤
      ρ + 2 * E * δ + |b| * δ := by
  classical
  let S := A.filter (fun a => ⌊y a / ρ⌋ = c)
  have hi : Set.InjOn index (↑S : Set α) := by
    intro a ha a' ha' he
    exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha').1 he
  have hc : (S.image index).card = S.card := Finset.card_image_iff.mpr hi
  have hcap := integer_card_bound (S.image index) (|b| * δ) (ρ + 2 * E * δ)
    (by positivity) (by positivity) (by
      intro n hn m hm
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨haA, hay⟩ := Finset.mem_filter.mp ha
      obtain ⟨haA', hay'⟩ := Finset.mem_filter.mp ha'
      exact noisy_pair_gap δ ρ E b x₀ q (y a) (y a') (index a) (index a') hδ hρ
        (herror a haA) (herror a' haA') (hay.trans hay'.symm))
  rw [hc] at hcap
  exact hcap

/-- Whole-image counting with ORIGINAL source labels. -/
theorem labelled_noisy_image_count {α : Type*} (A : Finset α)
    (index : α → ℤ) (y : α → ℝ) (δ ρ E b x₀ q : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hE : 0 ≤ E)
    (hinj : Set.InjOn index (↑A : Set α))
    (herror : ∀ a ∈ A, |y a - q - b * (x₀ + δ * (index a : ℝ))| ≤ E * δ) :
    |b| * δ * (A.card : ℝ) ≤
      (ρ + 2 * E * δ + |b| * δ) * ((A.image (fun a => ⌊y a / ρ⌋)).card : ℝ) := by
  classical
  have hsum : (A.card : ℝ) =
      ∑ c ∈ A.image (fun a => ⌊y a / ρ⌋), ((A.filter (fun a => ⌊y a / ρ⌋ = c)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (fun a => ⌊y a / ρ⌋) A
  calc
    _ = ∑ c ∈ A.image (fun a => ⌊y a / ρ⌋),
        |b| * δ * ((A.filter (fun a => ⌊y a / ρ⌋ = c)).card : ℝ) := by rw [hsum, Finset.mul_sum]
    _ ≤ ∑ _c ∈ A.image (fun a => ⌊y a / ρ⌋), (ρ + 2 * E * δ + |b| * δ) :=
      Finset.sum_le_sum (fun c _ =>
        labelled_noisy_fiber_bound A index y δ ρ E b x₀ q hδ hρ hE hinj herror c)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Freeze actual other-coordinate labels. Joint grid-label injectivity derives
scalar-index injectivity within each fiber; a full interval is never assumed. -/
theorem coordinate_fiber_image_count {α β : Type*} [DecidableEq β]
    (A : Finset α) (other : α → β) (index : α → ℤ) (y : α → ℝ)
    (δ ρ E b : ℝ) (x₀ q : β → ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hE : 0 ≤ E)
    (hinj : Set.InjOn (fun a => (other a, index a)) (↑A : Set α))
    (herror : ∀ a ∈ A,
      |y a - q (other a) - b * (x₀ (other a) + δ * (index a : ℝ))| ≤ E * δ)
    (c : β) :
    |b| * δ * ((A.filter (fun a => other a = c)).card : ℝ) ≤
      (ρ + 2 * E * δ + |b| * δ) *
        (((A.filter (fun a => other a = c)).image (fun a => ⌊y a / ρ⌋)).card : ℝ) := by
  apply labelled_noisy_image_count _ index y δ ρ E b (x₀ c) (q c) hδ hρ hE
  · intro a ha a' ha' he
    obtain ⟨haA, hac⟩ := Finset.mem_filter.mp ha
    obtain ⟨haA', hac'⟩ := Finset.mem_filter.mp ha'
    exact hinj haA haA' (Prod.ext (hac.trans hac'.symm) he)
  · intro a ha
    obtain ⟨haA, hac⟩ := Finset.mem_filter.mp ha
    simpa only [hac] using herror a haA

/-- The direct coarse-mesh count used before the tube Katz--Tao comparison.
The source error and affine step are each at most rho, so the sharp cap costs
at most 4*rho. No slope conclusion or output-cell estimate is an assumption. -/
theorem coarse_noisy_image_count (J : Finset ℤ) (y : ℤ → ℝ) (δ ρ E b x₀ q : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hE : 0 ≤ E)
    (herror : ∀ n ∈ J, |y n - q - b * (x₀ + δ * (n : ℝ))| ≤ E * δ)
    (hsmallError : E * δ ≤ ρ) (hsmallStep : |b| * δ ≤ ρ) :
    |b| * δ * (J.card : ℝ) ≤
      4 * ρ * ((J.image (fun n => ⌊y n / ρ⌋)).card : ℝ) := by
  have hcap : ρ + 2 * E * δ + |b| * δ ≤ 4 * ρ := by linarith
  exact (noisy_image_count J y δ ρ E b x₀ q hδ hρ hE herror).trans
    (mul_le_mul_of_nonneg_right hcap (Nat.cast_nonneg _))

end NoisyAffineImageCount
