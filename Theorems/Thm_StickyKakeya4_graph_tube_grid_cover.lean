import Theorems.Thm_StickyKakeya4_tube_bin_count

set_option autoImplicit false
set_option warningAsError true

namespace GraphTubeGridCover

noncomputable section
abbrev Point (n : ℕ) := (Fin n → ℝ) × ℝ
abbrev Bin (n : ℕ) := (Fin n → ℤ) × ℤ

def gridBin {n : ℕ} (rho : ℝ) (p : Point n) : Bin n :=
  (fun i => ⌊p.1 i / rho⌋, ⌊p.2 / rho⌋)

def timeBins (rho t0 tau : ℝ) : Finset ℤ :=
  Finset.Icc ⌊t0 / rho⌋ ⌊(t0 + tau) / rho⌋

def spatialBox {n : ℕ} (rho : ℝ) (E : ℕ) (a b : Fin n → ℝ)
    (k : ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => TubeBinCount.coordinateBins E (b i / rho + a i * k)

def tubeBins {n : ℕ} (rho t0 tau : ℝ) (E : ℕ) (a b : Fin n → ℝ) : Finset (Bin n) :=
  (timeBins rho t0 tau).biUnion fun k => (spatialBox rho E a b k).product {k}

lemma spatialBox_card {n : ℕ} (rho : ℝ) (E : ℕ) (a b : Fin n → ℝ) (k : ℤ) :
    (spatialBox rho E a b k).card = (2 * E + 4) ^ n := by
  simp [spatialBox, Fintype.card_piFinset, TubeBinCount.coordinateBins_card]

lemma timeBins_card_mul_rho_le (rho t0 tau : ℝ) (hrho : 0 < rho)
    (hscale : rho ≤ tau) : ((timeBins rho t0 tau).card : ℝ) * rho ≤ 3 * tau := by
  have hlohi : ⌊t0 / rho⌋ ≤ ⌊(t0 + tau) / rho⌋ := by
    apply Int.floor_mono
    exact div_le_div_of_nonneg_right (by linarith) hrho.le
  have hcard : ((timeBins rho t0 tau).card : ℤ) =
      ⌊(t0 + tau) / rho⌋ + 1 - ⌊t0 / rho⌋ := Int.card_Icc_of_le _ _ (by omega)
  have hcardR : ((timeBins rho t0 tau).card : ℝ) =
      (⌊(t0 + tau) / rho⌋ : ℝ) + 1 - (⌊t0 / rho⌋ : ℝ) := by exact_mod_cast hcard
  have hupper := Int.floor_le ((t0 + tau) / rho)
  have hlower := Int.lt_floor_add_one (t0 / rho)
  have hbound : ((timeBins rho t0 tau).card : ℝ) ≤ tau / rho + 2 := by
    rw [hcardR]
    have hdiv : (t0 + tau) / rho = t0 / rho + tau / rho := by ring
    linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrho.le
  have heq : (tau / rho + 2) * rho = tau + 2 * rho := by field_simp
  rw [heq] at hm
  linarith

lemma gridBin_mem_tubeBins {n : ℕ} (rho t0 tau : ℝ) (E : ℕ)
    (a b : Fin n → ℝ) (p : Point n) (hrho : 0 < rho)
    (ha : ∀ i, |a i| ≤ 1) (ht : t0 ≤ p.2 ∧ p.2 ≤ t0 + tau)
    (hp : ∀ i, |p.1 i - b i - a i * p.2| ≤ (E : ℝ) * rho) :
    gridBin rho p ∈ tubeBins rho t0 tau E a b := by
  apply Finset.mem_biUnion.mpr
  refine ⟨⌊p.2 / rho⌋, ?_, ?_⟩
  · exact Finset.mem_Icc.mpr
      ⟨Int.floor_mono (div_le_div_of_nonneg_right ht.1 hrho.le),
       Int.floor_mono (div_le_div_of_nonneg_right ht.2 hrho.le)⟩
  · apply Finset.mem_product.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact TubeBinCount.floor_mem_coordinateBins E _ _
        (TubeBinCount.normalized_coordinate_bound rho E (a i) (b i) (p.1 i) p.2
          hrho (ha i) (hp i))
    · simp [gridBin]

lemma tubeBins_card_le {n : ℕ} (rho t0 tau : ℝ) (E : ℕ) (a b : Fin n → ℝ) :
    (tubeBins rho t0 tau E a b).card ≤
      (timeBins rho t0 tau).card * (2 * E + 4) ^ n := by
  calc
    (tubeBins rho t0 tau E a b).card ≤
        ∑ k ∈ timeBins rho t0 tau, ((spatialBox rho E a b k).product {k}).card :=
      Finset.card_biUnion_le
    _ = _ := by simp [spatialBox_card]

/-- Actual occupied global-grid cells in any translated graph tube. The
constant is independent of location and scale; the grid is never recentered. -/
theorem occupied_cells_bound {alpha : Type*} {n : ℕ} (P : Finset alpha)
    (p : alpha → Point n) (rho t0 tau : ℝ) (E : ℕ) (a b : Fin n → ℝ)
    (hrho : 0 < rho) (hscale : rho ≤ tau) (ha : ∀ i, |a i| ≤ 1)
    (ht : ∀ x ∈ P, t0 ≤ (p x).2 ∧ (p x).2 ≤ t0 + tau)
    (hp : ∀ x ∈ P, ∀ i, |(p x).1 i - b i - a i * (p x).2| ≤ (E : ℝ) * rho) :
    ((P.image (fun x => gridBin rho (p x))).card : ℝ) * rho ≤
      3 * ((2 * E + 4) ^ n : ℕ) * tau := by
  classical
  have hsub : P.image (fun x => gridBin rho (p x)) ⊆ tubeBins rho t0 tau E a b := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    exact gridBin_mem_tubeBins rho t0 tau E a b (p x) hrho ha (ht x hx) (hp x hx)
  have hc := (Finset.card_le_card hsub).trans (tubeBins_card_le rho t0 tau E a b)
  have hcR : ((P.image (fun x => gridBin rho (p x))).card : ℝ) ≤
      ((timeBins rho t0 tau).card : ℝ) * ((2 * E + 4) ^ n : ℕ) := by exact_mod_cast hc
  have hs := timeBins_card_mul_rho_le rho t0 tau hrho hscale
  have hconst : (0 : ℝ) ≤ ((2 * E + 4) ^ n : ℕ) := by positivity
  calc
    ((P.image (fun x => gridBin rho (p x))).card : ℝ) * rho ≤
        (((timeBins rho t0 tau).card : ℝ) * ((2 * E + 4) ^ n : ℕ)) * rho :=
      mul_le_mul_of_nonneg_right hcR hrho.le
    _ = (((timeBins rho t0 tau).card : ℝ) * rho) * ((2 * E + 4) ^ n : ℕ) := by ring
    _ ≤ (3 * tau) * ((2 * E + 4) ^ n : ℕ) := mul_le_mul_of_nonneg_right hs hconst
    _ = _ := by ring

/-- Coordinate permutation only: no rotated or recentered covering grid. -/
def chart {n : ℕ} (j : Fin (n + 1)) (p : Fin (n + 1) → ℝ) : Point n :=
  (fun i => p (j.succAbove i), p j)

def integerChart {n : ℕ} (j : Fin (n + 1)) (q : Fin (n + 1) → ℤ) : Bin n :=
  (fun i => q (j.succAbove i), q j)

lemma integerChart_injective {n : ℕ} (j : Fin (n + 1)) :
    Function.Injective (integerChart j) := by
  intro p q h
  apply (Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℤ) j).symm.injective
  apply Prod.ext
  · exact congrArg Prod.snd h
  · exact congrArg Prod.fst h

lemma chart_gridBin {n : ℕ} (j : Fin (n + 1)) (rho : ℝ) (p : Fin (n + 1) → ℝ) :
    gridBin rho (chart j p) = integerChart j (fun i => ⌊p i / rho⌋) := rfl

lemma exists_graph_chart {n : ℕ} (v : Fin (n + 1) → ℝ)
    (hv : ∃ k, v k ≠ 0) :
    ∃ j, v j ≠ 0 ∧ ∀ i, |v i / v j| ≤ 1 := by
  obtain ⟨j, _hj, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (n + 1)))
    (fun i => |v i|) (Finset.univ_nonempty)
  obtain ⟨k, hk⟩ := hv
  have hpos : 0 < |v j| := (abs_pos.mpr hk).trans_le (hmax k (Finset.mem_univ k))
  refine ⟨j, (abs_pos.mp hpos), ?_⟩
  intro i
  rw [abs_div]
  exact (div_le_iff₀ hpos).mpr (by simpa using hmax i (Finset.mem_univ i))

/-- A genuine coordinatewise thickened segment has a global-grid tube cover.
Euclidean tube membership implies these coordinate error assumptions. -/
theorem segment_occupied_cells_bound {alpha : Type*} {n : ℕ}
    (P : Finset alpha) (p : alpha → Fin (n + 1) → ℝ)
    (center v : Fin (n + 1) → ℝ) (parameter : alpha → ℝ)
    (rho tau : ℝ) (hrho : 0 < rho) (hscale : rho ≤ tau)
    (hv : ∃ k, v k ≠ 0) (hvone : ∀ i, |v i| ≤ 1)
    (hparameter : ∀ x ∈ P, |parameter x| ≤ tau / 2)
    (herror : ∀ x ∈ P, ∀ i, |p x i - center i - parameter x * v i| ≤ rho) :
    ((P.image (fun x => fun i => ⌊p x i / rho⌋)).card : ℝ) * rho ≤
      9 * (8 ^ n : ℕ) * tau := by
  classical
  obtain ⟨j, hj, hratio⟩ := exists_graph_chart v hv
  let a : Fin n → ℝ := fun i => v (j.succAbove i) / v j
  let b : Fin n → ℝ := fun i => center (j.succAbove i) - a i * center j
  let t0 := center j - 3 * tau / 2
  have hphys (x : alpha) (hx : x ∈ P) (i : Fin n) :
      |(chart j (p x)).1 i - b i - a i * (chart j (p x)).2| ≤ (2 : ℝ) * rho := by
    have hid : (chart j (p x)).1 i - b i - a i * (chart j (p x)).2 =
        (p x (j.succAbove i) - center (j.succAbove i) - parameter x * v (j.succAbove i)) -
          a i * (p x j - center j - parameter x * v j) := by
      dsimp [chart, a, b]
      field_simp
      ring
    rw [hid]
    have hm : |a i * (p x j - center j - parameter x * v j)| ≤ rho := by
      rw [abs_mul]
      have ha : |a i| ≤ 1 := hratio _
      simpa using mul_le_mul ha (herror x hx j) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have ht := abs_sub
      (p x (j.succAbove i) - center (j.succAbove i) - parameter x * v (j.succAbove i))
      (a i * (p x j - center j - parameter x * v j))
    linarith [herror x hx (j.succAbove i)]
  have htime (x : alpha) (hx : x ∈ P) :
      t0 ≤ (chart j (p x)).2 ∧ (chart j (p x)).2 ≤ t0 + 3 * tau := by
    have hm : |parameter x * v j| ≤ tau / 2 := by
      rw [abs_mul]
      simpa using mul_le_mul (hparameter x hx) (hvone j) (abs_nonneg _)
        (by linarith : 0 ≤ tau / 2)
    have he := herror x hx j
    have he' := abs_le.mp he
    have hm' := abs_le.mp hm
    dsimp [chart, t0]
    constructor <;> linarith
  have hc := occupied_cells_bound P (fun x => chart j (p x)) rho t0 (3 * tau) 2 a b
    hrho (by linarith) (fun i => hratio _) htime hphys
  have hcard : (P.image (fun x => gridBin rho (chart j (p x)))).card =
      (P.image (fun x => fun i => ⌊p x i / rho⌋)).card := by
    simp only [chart_gridBin]
    simpa only [Finset.image_image, Function.comp_def] using
      (Finset.card_image_of_injective (P.image (fun x => fun i => ⌊p x i / rho⌋))
        (integerChart_injective j))
  rw [hcard] at hc
  norm_num at hc ⊢
  nlinarith

end
end GraphTubeGridCover
