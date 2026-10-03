import Theorems.Thm_StickyKakeya4_grid_quotient_ad
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace SpineColumnCounting

noncomputable section

open scoped BigOperators
abbrev Point (l : ℕ) := ℝ × (Fin l → ℝ)
abbrev Cell (l : ℕ) := ℤ × (Fin l → ℤ)

def shear {l : ℕ} (alpha : Fin l → ℝ) (p : Point l) (i : Fin l) : ℝ :=
  p.2 i - alpha i * p.1

def cell {l : ℕ} (a : ℝ) (p : Point l) : Cell l :=
  (⌊p.1 / a⌋, fun i => ⌊p.2 i / a⌋)

def normalCell {l : ℕ} (alpha : Fin l → ℝ) (q : Cell l) : Fin l → ℤ :=
  fun i => ⌊(q.2 i : ℝ) - alpha i * (q.1 : ℝ)⌋

/-- Actual contact errors and nearby slopes control the SAME fixed shear. -/
lemma shear_close {l : ℕ} (alpha theta : Fin l → ℝ) (p q : Point l)
    {r gamma b : ℝ} (hgamma : 0 ≤ gamma)
    (hphysical : ∀ i, |p.2 i - q.2 i - theta i * (p.1 - q.1)| ≤ r)
    (hslope : ∀ i, |theta i - alpha i| ≤ gamma)
    (htime : |p.1 - q.1| ≤ b) (i : Fin l) :
    |shear alpha p i - shear alpha q i| ≤ r + gamma * b := by
  have hid : shear alpha p i - shear alpha q i =
      (p.2 i - q.2 i - theta i * (p.1 - q.1)) +
        (theta i - alpha i) * (p.1 - q.1) := by simp only [shear]; ring
  rw [hid]
  refine (abs_add_le _ _).trans (add_le_add (hphysical i) ?_)
  rw [abs_mul]
  exact mul_le_mul (hslope i) htime (abs_nonneg _) hgamma

lemma floor_error (x : ℝ) : |(⌊x⌋ : ℝ) - x| ≤ 1 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  apply abs_le.mpr
  constructor <;> linarith

/-- The original axis-grid cell center has a controlled error after shear. -/
lemma grid_shear_error {l : ℕ} (alpha : Fin l → ℝ) (p : Point l) (a : ℝ)
    (i : Fin l) :
    |((cell a p).2 i : ℝ) - alpha i * ((cell a p).1 : ℝ) - shear alpha p i / a|
      ≤ 1 + |alpha i| := by
  have hid : ((cell a p).2 i : ℝ) - alpha i * ((cell a p).1 : ℝ) - shear alpha p i / a =
      ((⌊p.2 i / a⌋ : ℝ) - p.2 i / a) -
        alpha i * ((⌊p.1 / a⌋ : ℝ) - p.1 / a) := by
    simp only [cell, shear]; ring
  rw [hid]
  refine (abs_sub _ _).trans (add_le_add (floor_error _) ?_)
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left (floor_error (p.1 / a)) (abs_nonneg (alpha i))


lemma same_floor_scaled_close {x y a : ℝ} (ha : 0 < a)
    (h : ⌊x / a⌋ = ⌊y / a⌋) : |x - y| < a := by
  have hh := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, abs_div, abs_of_pos ha] at hh
  exact (div_lt_iff₀ ha).mp hh |>.trans_le (by simp)

lemma same_cell_shear_close {l : ℕ} (alpha : Fin l → ℝ)
    {p q : Point l} {a A : ℝ} (ha : 0 < a)
    (hA : ∀ i, |alpha i| ≤ A) (hpq : cell a p = cell a q) (i : Fin l) :
    |shear alpha p i - shear alpha q i| ≤ (1 + A) * a := by
  have ht : |p.1 - q.1| ≤ a := (same_floor_scaled_close ha (congrArg Prod.fst hpq)).le
  have hx : |p.2 i - q.2 i| ≤ a :=
    (same_floor_scaled_close ha (congrFun (congrArg Prod.snd hpq) i)).le
  have hid : shear alpha p i - shear alpha q i =
      (p.2 i - q.2 i) - alpha i * (p.1 - q.1) := by simp only [shear]; ring
  rw [hid]
  calc
    |p.2 i - q.2 i - alpha i * (p.1 - q.1)|
      ≤ |p.2 i - q.2 i| + |alpha i * (p.1 - q.1)| := abs_sub _ _
    _ ≤ a + A * a := add_le_add hx (by
      rw [abs_mul]
      exact mul_le_mul (hA i) ht (abs_nonneg _) ((abs_nonneg _).trans (hA i)))
    _ = (1 + A) * a := by ring

lemma labels_close_of_shared_cell {l : ℕ} (alpha : Fin l → ℝ)
    {p q : Point l} {y z : Fin l → ℤ} {a h R A : ℝ} (M : ℕ)
    (ha : 0 < a) (hh : 0 < h) (hA : ∀ i, |alpha i| ≤ A)
    (hpq : cell a p = cell a q)
    (hp : ∀ i, |shear alpha p i - h * (y i : ℝ)| ≤ R)
    (hq : ∀ i, |shear alpha q i - h * (z i : ℝ)| ≤ R)
    (hbudget : 2 * R + (1 + A) * a ≤ h * M) (i : Fin l) :
    |y i - z i| ≤ (M : ℤ) := by
  have heq : h * ((y i : ℝ) - (z i : ℝ)) =
      -(shear alpha p i - h * (y i : ℝ)) +
        (shear alpha p i - shear alpha q i) +
        (shear alpha q i - h * (z i : ℝ)) := by ring
  have hs : |h * ((y i : ℝ) - (z i : ℝ))| ≤ h * M := by
    rw [heq]
    calc
      |-(shear alpha p i - h * (y i : ℝ)) +
          (shear alpha p i - shear alpha q i) +
          (shear alpha q i - h * (z i : ℝ))|
        ≤ |-(shear alpha p i - h * (y i : ℝ)) +
          (shear alpha p i - shear alpha q i)| +
          |shear alpha q i - h * (z i : ℝ)| := abs_add_le _ _
      _ ≤ (|-(shear alpha p i - h * (y i : ℝ))| +
          |shear alpha p i - shear alpha q i|) + R :=
        add_le_add (abs_add_le _ _) (hq i)
      _ ≤ (R + (1 + A) * a) + R := by
        rw [abs_neg]
        have hsc := same_cell_shear_close alpha ha hA hpq i
        linarith [hp i]
      _ ≤ h * M := by linarith
  rw [abs_mul, abs_of_pos hh] at hs
  have hs' : |(y i : ℝ) - (z i : ℝ)| ≤ M := by nlinarith
  exact_mod_cast hs'

lemma cell_label_count_le {l : ℕ} (alpha : Fin l → ℝ)
    (Z : Finset (Fin l → ℤ)) (S : (Fin l → ℤ) → Finset (Point l))
    {a h R A : ℝ} (M : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hA : ∀ i, |alpha i| ≤ A)
    (hnear : ∀ z ∈ Z, ∀ p ∈ S z, ∀ i, |shear alpha p i - h * (z i : ℝ)| ≤ R)
    (hbudget : 2 * R + (1 + A) * a ≤ h * M) (c : Cell l) :
    (Z.filter (fun z => c ∈ (S z).image (cell a))).card ≤ (2 * M + 1) ^ l := by
  classical
  let F := Z.filter (fun z => c ∈ (S z).image (cell a))
  change F.card ≤ _
  by_cases he : F.Nonempty
  · obtain ⟨z, hz⟩ := he
    obtain ⟨hzZ, hzc⟩ := Finset.mem_filter.mp hz
    obtain ⟨q, hqS, hqc⟩ := Finset.mem_image.mp hzc
    have hsub : F ⊆ GridQuotientAD.box z M := by
      intro y hy
      obtain ⟨hyZ, hyc⟩ := Finset.mem_filter.mp hy
      obtain ⟨p, hpS, hpc⟩ := Finset.mem_image.mp hyc
      apply (GridQuotientAD.mem_box_iff z y M).mpr
      intro i
      exact labels_close_of_shared_cell alpha M ha hh hA (hpc.trans hqc.symm)
        (hnear y hyZ p hpS) (hnear z hzZ q hqS) hbudget i
    exact (Finset.card_le_card hsub).trans_eq (GridQuotientAD.box_card z M)
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp

/-- Actual rich spine-cell images, with the overlap constant derived above,
bound the number of normal columns. No incidence multiplicity is assumed. -/
theorem columns_count_le {l : ℕ} (alpha : Fin l → ℝ)
    (Z : Finset (Fin l → ℤ)) (E : Finset (Point l))
    (S : (Fin l → ℤ) → Finset (Point l))
    {a h R A L : ℝ} (M : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hA : ∀ i, |alpha i| ≤ A) (hSE : ∀ z ∈ Z, S z ⊆ E)
    (hlarge : ∀ z ∈ Z, L ≤ (((S z).image (cell a)).card : ℝ))
    (hnear : ∀ z ∈ Z, ∀ p ∈ S z, ∀ i, |shear alpha p i - h * (z i : ℝ)| ≤ R)
    (hbudget : 2 * R + (1 + A) * a ≤ h * M) :
    L * (Z.card : ℝ) ≤ ((2 * M + 1) ^ l : ℕ) * ((E.image (cell a)).card : ℝ) := by
  classical
  let P := E.image (cell a)
  have hfilter (z : Fin l → ℤ) (hz : z ∈ Z) :
      P.filter (fun q => q ∈ (S z).image (cell a)) = (S z).image (cell a) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hq
      exact ⟨(Finset.image_subset_image (hSE z hz)) hq, hq⟩
  have hsum : (∑ z ∈ Z, ((S z).image (cell a)).card) =
      ∑ q ∈ P, (Z.filter (fun z => q ∈ (S z).image (cell a))).card := by
    calc
      (∑ z ∈ Z, ((S z).image (cell a)).card) =
          ∑ z ∈ Z, (P.filter (fun q => q ∈ (S z).image (cell a))).card := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hfilter z hz]
      _ = _ := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
  have hnat : (∑ z ∈ Z, ((S z).image (cell a)).card) ≤ P.card * (2 * M + 1) ^ l := by
    rw [hsum]
    calc
      (∑ q ∈ P, (Z.filter (fun z => q ∈ (S z).image (cell a))).card) ≤
          ∑ _q ∈ P, (2 * M + 1) ^ l := by
        apply Finset.sum_le_sum
        intro q _hq
        exact cell_label_count_le alpha Z S M ha hh hA hnear hbudget q
      _ = _ := by simp
  calc
    L * (Z.card : ℝ) = ∑ _z ∈ Z, L := by simp [mul_comm]
    _ ≤ ∑ z ∈ Z, (((S z).image (cell a)).card : ℝ) := Finset.sum_le_sum hlarge
    _ ≤ ((2 * M + 1) ^ l : ℕ) * ((E.image (cell a)).card : ℝ) := by
      norm_cast
      simpa only [P, Nat.mul_comm] using hnat

/-- The geometric caller derives the column bound from original physical
spines, actual anchors, slope closeness and original cell quantization. -/
theorem physical_spines_column_count {l : ℕ} (alpha : Fin l → ℝ)
    (Z : Finset (Fin l → ℤ)) (E : Finset (Point l))
    (S : (Fin l → ℤ) → Finset (Point l))
    (anchor : (Fin l → ℤ) → Point l) (theta : (Fin l → ℤ) → Fin l → ℝ)
    {a h r gamma b A seed L : ℝ} (M : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hgamma : 0 ≤ gamma) (hA : ∀ i, |alpha i| ≤ A)
    (hSE : ∀ z ∈ Z, S z ⊆ E)
    (hlarge : ∀ z ∈ Z, L ≤ (((S z).image (cell a)).card : ℝ))
    (hphysical : ∀ z ∈ Z, ∀ p ∈ S z, ∀ i,
      |p.2 i - (anchor z).2 i - theta z i * (p.1 - (anchor z).1)| ≤ r)
    (hslope : ∀ z ∈ Z, ∀ i, |theta z i - alpha i| ≤ gamma)
    (htime : ∀ z ∈ Z, ∀ p ∈ S z, |p.1 - (anchor z).1| ≤ b)
    (hseed : ∀ z ∈ Z, ∀ i, |shear alpha (anchor z) i - h * (z i : ℝ)| ≤ seed)
    (hbudget : 2 * (r + gamma * b + seed) + (1 + A) * a ≤ h * M) :
    L * (Z.card : ℝ) ≤ ((2 * M + 1) ^ l : ℕ) * ((E.image (cell a)).card : ℝ) := by
  apply columns_count_le alpha Z E S M ha hh hA hSE hlarge (R := r + gamma * b + seed)
  · intro z hz p hp i
    have hc := shear_close alpha (theta z) p (anchor z) hgamma
      (hphysical z hz p hp) (hslope z hz) (htime z hz p hp) i
    calc
      |shear alpha p i - h * (z i : ℝ)| ≤
          |shear alpha p i - shear alpha (anchor z) i| +
          |shear alpha (anchor z) i - h * (z i : ℝ)| := abs_sub_le _ _ _
      _ ≤ r + gamma * b + seed := add_le_add hc (hseed z hz i)
  · exact hbudget

end
end SpineColumnCounting
