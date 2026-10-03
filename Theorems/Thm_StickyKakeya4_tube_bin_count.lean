import Mathlib

set_option autoImplicit false
set_option warningAsError true

/-!
Actual coarse-grid bin counting for a bounded-length tube in three space
dimensions and one time dimension.  Every bin is defined using `Int.floor`;
there is no assumed covering or cardinality certificate.
-/

namespace TubeBinCount

abbrev SpaceTime := (Fin 3 → ℝ) × ℝ
abbrev Bin := (Fin 3 → ℤ) × ℤ

noncomputable def gridBin (σ : ℝ) (p : SpaceTime) : Bin :=
  (fun j => ⌊p.1 j / σ⌋, ⌊p.2 / σ⌋)

noncomputable def timeBins (σ : ℝ) : Finset ℤ :=
  Finset.Icc ⌊-1 / σ⌋ ⌊1 / σ⌋

noncomputable def coordinateBins (E : ℕ) (c : ℝ) : Finset ℤ :=
  Finset.Icc (⌊c⌋ - (E + 1 : ℕ)) (⌊c⌋ + (E + 2 : ℕ))

noncomputable def spatialBox (σ : ℝ) (E : ℕ) (a b : Fin 3 → ℝ)
    (k : ℤ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun j => coordinateBins E (b j / σ + a j * k)

noncomputable def tubeBins (σ : ℝ) (E : ℕ) (a b : Fin 3 → ℝ) : Finset Bin :=
  (timeBins σ).biUnion fun k => (spatialBox σ E a b k).product {k}

theorem coordinateBins_card (E : ℕ) (c : ℝ) :
    (coordinateBins E c).card = 2 * E + 4 := by
  unfold coordinateBins
  rw [Int.card_Icc]
  omega

theorem floor_mem_coordinateBins (E : ℕ) (q c : ℝ)
    (h : |q - c| ≤ (E : ℝ) + 1) :
    ⌊q⌋ ∈ coordinateBins E c := by
  rcases abs_le.mp h with ⟨hl, hu⟩
  have hlow : c - ((E + 1 : ℕ) : ℝ) ≤ q := by push_cast; linarith
  have hupp : q ≤ c + ((E + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hlow' := Int.floor_mono hlow
  have hupp' := Int.floor_mono hupp
  simp only [Int.floor_sub_natCast, Int.floor_add_natCast] at hlow' hupp'
  apply Finset.mem_Icc.mpr
  constructor
  · exact hlow'
  · dsimp [coordinateBins]
    omega

theorem normalized_coordinate_bound (σ : ℝ) (E : ℕ) (a b x t : ℝ)
    (hσ : 0 < σ) (ha : |a| ≤ 1)
    (hx : |x - b - a * t| ≤ (E : ℝ) * σ) :
    |x / σ - (b / σ + a * (⌊t / σ⌋ : ℝ))| ≤ (E : ℝ) + 1 := by
  have htime0 : 0 ≤ t / σ - (⌊t / σ⌋ : ℝ) :=
    sub_nonneg.mpr (Int.floor_le _)
  have htime1 : t / σ - (⌊t / σ⌋ : ℝ) ≤ 1 := by
    have := Int.lt_floor_add_one (t / σ)
    linarith
  have htime : |t / σ - (⌊t / σ⌋ : ℝ)| ≤ 1 := by
    rwa [abs_of_nonneg htime0]
  have herror : |(x - b - a * t) / σ| ≤ (E : ℝ) := by
    rw [abs_div, abs_of_pos hσ]
    exact (div_le_iff₀ hσ).mpr hx
  calc
    |x / σ - (b / σ + a * (⌊t / σ⌋ : ℝ))| =
        |(x - b - a * t) / σ + a * (t / σ - (⌊t / σ⌋ : ℝ))| := by
          congr 1
          ring
    _ ≤ |(x - b - a * t) / σ| + |a * (t / σ - (⌊t / σ⌋ : ℝ))| :=
      abs_add_le _ _
    _ ≤ (E : ℝ) + 1 := by
      rw [abs_mul]
      have hmul := mul_le_mul ha htime (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simp only [one_mul] at hmul
      linarith

theorem floor_time_mem (σ t : ℝ) (hσ : 0 < σ) (ht : |t| ≤ 1) :
    ⌊t / σ⌋ ∈ timeBins σ := by
  rcases abs_le.mp ht with ⟨hl, hu⟩
  exact Finset.mem_Icc.mpr
    ⟨Int.floor_mono (div_le_div_of_nonneg_right hl hσ.le),
     Int.floor_mono (div_le_div_of_nonneg_right hu hσ.le)⟩

theorem timeBins_card_mul_scale_le (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ((timeBins σ).card : ℝ) * σ ≤ 4 := by
  have hlohi : ⌊-1 / σ⌋ ≤ ⌊1 / σ⌋ :=
    Int.floor_mono (div_le_div_of_nonneg_right (by norm_num : (-1 : ℝ) ≤ 1) hσ.le)
  have hcard : ((timeBins σ).card : ℤ) = ⌊1 / σ⌋ + 1 - ⌊-1 / σ⌋ :=
    Int.card_Icc_of_le _ _ (by omega)
  have hcardR : ((timeBins σ).card : ℝ) =
      (⌊1 / σ⌋ : ℝ) + 1 - (⌊-1 / σ⌋ : ℝ) := by exact_mod_cast hcard
  have hu := Int.floor_le (1 / σ)
  have hl := Int.lt_floor_add_one (-1 / σ)
  have hbound : ((timeBins σ).card : ℝ) ≤ 2 / σ + 2 := by
    rw [hcardR]
    linarith [show (-1 : ℝ) / σ = -(1 / σ) by ring,
      show (2 : ℝ) / σ = 2 * (1 / σ) by ring]
  have hmul := mul_le_mul_of_nonneg_right hbound hσ.le
  have hcancel : (2 / σ + 2) * σ = 2 + 2 * σ := by field_simp
  rw [hcancel] at hmul
  linarith

theorem spatialBox_card (σ : ℝ) (E : ℕ) (a b : Fin 3 → ℝ) (k : ℤ) :
    (spatialBox σ E a b k).card = (2 * E + 4) ^ 3 := by
  simp [spatialBox, Fintype.card_piFinset, coordinateBins_card]

theorem gridBin_mem_tubeBins (σ : ℝ) (E : ℕ) (a b : Fin 3 → ℝ)
    (p : SpaceTime) (hσ : 0 < σ) (ha : ∀ j, |a j| ≤ 1)
    (ht : |p.2| ≤ 1) (hx : ∀ j, |p.1 j - b j - a j * p.2| ≤ (E : ℝ) * σ) :
    gridBin σ p ∈ tubeBins σ E a b := by
  apply Finset.mem_biUnion.mpr
  refine ⟨⌊p.2 / σ⌋, floor_time_mem σ p.2 hσ ht, ?_⟩
  apply Finset.mem_product.mpr
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro j
    exact floor_mem_coordinateBins E (p.1 j / σ) _
      (normalized_coordinate_bound σ E (a j) (b j) (p.1 j) p.2 hσ (ha j) (hx j))
  · simp [gridBin]

theorem tubeBins_card_le (σ : ℝ) (E : ℕ) (a b : Fin 3 → ℝ) :
    (tubeBins σ E a b).card ≤ (timeBins σ).card * (2 * E + 4) ^ 3 := by
  apply Finset.card_biUnion_le_card_mul
  intro k _hk
  simp [spatialBox_card]

/-- A tube's distinct physical grid bins have the required `O(σ⁻¹)` bound. -/
theorem distinct_gridBins_card_mul_scale_le
    (P : Finset SpaceTime) (σ : ℝ) (E : ℕ) (a b : Fin 3 → ℝ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (ha : ∀ j, |a j| ≤ 1)
    (ht : ∀ p ∈ P, |p.2| ≤ 1)
    (hx : ∀ p ∈ P, ∀ j, |p.1 j - b j - a j * p.2| ≤ (E : ℝ) * σ) :
    ((P.image (gridBin σ)).card : ℝ) * σ ≤ 4 * ((2 * E + 4 : ℕ) : ℝ) ^ 3 := by
  have hsub : P.image (gridBin σ) ⊆ tubeBins σ E a b := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    exact gridBin_mem_tubeBins σ E a b p hσ ha (ht p hp) (hx p hp)
  have hnat := (Finset.card_le_card hsub).trans (tubeBins_card_le σ E a b)
  have hreal : ((P.image (gridBin σ)).card : ℝ) ≤
      ((timeBins σ).card : ℝ) * ((2 * E + 4 : ℕ) : ℝ) ^ 3 := by exact_mod_cast hnat
  calc
    ((P.image (gridBin σ)).card : ℝ) * σ ≤
        (((timeBins σ).card : ℝ) * ((2 * E + 4 : ℕ) : ℝ) ^ 3) * σ :=
      mul_le_mul_of_nonneg_right hreal hσ.le
    _ = (((timeBins σ).card : ℝ) * σ) * ((2 * E + 4 : ℕ) : ℝ) ^ 3 := by ring
    _ ≤ 4 * ((2 * E + 4 : ℕ) : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right (timeBins_card_mul_scale_le σ hσ hσ1) (by positivity)

/-- The same geometric estimate for any finite label family of points. -/
theorem labels_gridBins_card_mul_scale_le
    {ι : Type*} (S : Finset ι) (p : ι → SpaceTime)
    (σ : ℝ) (E : ℕ) (a b : Fin 3 → ℝ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (ha : ∀ j, |a j| ≤ 1)
    (ht : ∀ i ∈ S, |(p i).2| ≤ 1)
    (hx : ∀ i ∈ S, ∀ j, |(p i).1 j - b j - a j * (p i).2| ≤ (E : ℝ) * σ) :
    ((S.image (fun i => gridBin σ (p i))).card : ℝ) * σ ≤
      4 * ((2 * E + 4 : ℕ) : ℝ) ^ 3 := by
  classical
  have h := distinct_gridBins_card_mul_scale_le (S.image p) σ E a b hσ hσ1 ha
    (by intro q hq; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq; exact ht i hi)
    (by intro q hq; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq; exact hx i hi)
  simpa only [Finset.image_image, Function.comp_def] using h

/-- Equivalently, the number of distinct bins is at most `C_E / σ`. -/
theorem distinct_gridBins_card_le
    (P : Finset SpaceTime) (σ : ℝ) (E : ℕ) (a b : Fin 3 → ℝ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (ha : ∀ j, |a j| ≤ 1)
    (ht : ∀ p ∈ P, |p.2| ≤ 1)
    (hx : ∀ p ∈ P, ∀ j, |p.1 j - b j - a j * p.2| ≤ (E : ℝ) * σ) :
    ((P.image (gridBin σ)).card : ℝ) ≤ 4 * ((2 * E + 4 : ℕ) : ℝ) ^ 3 / σ := by
  exact (le_div_iff₀ hσ).mpr
    (distinct_gridBins_card_mul_scale_le P σ E a b hσ hσ1 ha ht hx)

theorem distinct_gridBins_card_mul_scale_le_6912
    (P : Finset SpaceTime) (σ : ℝ) (a b : Fin 3 → ℝ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (ha : ∀ j, |a j| ≤ 1)
    (ht : ∀ p ∈ P, |p.2| ≤ 1)
    (hx : ∀ p ∈ P, ∀ j, |p.1 j - b j - a j * p.2| ≤ 4 * σ) :
    ((P.image (gridBin σ)).card : ℝ) * σ ≤ 6912 := by
  convert distinct_gridBins_card_mul_scale_le P σ 4 a b hσ hσ1 ha ht hx using 1
  norm_num

end TubeBinCount
