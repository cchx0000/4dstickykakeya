import Theorems.Thm_StickyKakeya4_native_angular_chart_selection
import Theorems.Thm_StickyKakeya4_tube_perturbation_grid_transfer

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace RealScaleTubeProfileTransfer

open NativeDyadicTubeStopping ActualTubeFootprintProfiles FiniteCoverProfileEpochs
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

def comparisonBox {d : ℕ} (ρ r : ℝ) (c : GridLabel d) : Finset (GridLabel d) :=
  Fintype.piFinset fun i => Finset.Icc ⌊(r * (c i : ℝ)) / ρ⌋ (⌊(r * (c i : ℝ)) / ρ⌋ + 2)

lemma comparisonBox_card {d : ℕ} (ρ r : ℝ) (c : GridLabel d) :
    (comparisonBox ρ r c).card = 3 ^ (d + 1) := by
  have hc : ∀ i : Fin (d + 1),
      (Finset.Icc ⌊(r * (c i : ℝ)) / ρ⌋ (⌊(r * (c i : ℝ)) / ρ⌋ + 2)).card = 3 := by
    intro i
    rw [Int.card_Icc]
    omega
  simp only [comparisonBox, Fintype.card_piFinset, hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma grid_mem_comparisonBox {α : Type*} {d : ℕ} (p : α → Point d)
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r ≤ 2 * ρ) (a : α) :
    grid p ρ a ∈ comparisonBox ρ r (grid p r a) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hlo : r * (grid p r a i : ℝ) ≤ p a i := by
    have h := (le_div_iff₀ hr).mp (Int.floor_le (p a i / r))
    simpa only [grid, mul_comm] using h
  have hup : p a i < r * (grid p r a i : ℝ) + r := by
    have h := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one (p a i / r))
    change p a i < ((grid p r a i : ℝ) + 1) * r at h
    nlinarith only [h]
  have hdiv : p a i / ρ ≤ (r * (grid p r a i : ℝ)) / ρ + 2 := by
    apply (div_le_iff₀ hρ).mpr
    have he : ((r * (grid p r a i : ℝ)) / ρ + 2) * ρ = r * (grid p r a i : ℝ) + 2 * ρ := by
      field_simp
    rw [he]
    linarith only [hup, hrρ]
  apply Finset.mem_Icc.mpr
  constructor
  · exact Int.floor_mono (div_le_div_of_nonneg_right hlo hρ.le)
  · have hh := Int.floor_mono hdiv
    simpa only [grid, Int.floor_add_ofNat] using hh

/-- Literal absolute grids at comparable real scales. No nesting or moving
coordinate system is assumed, and boundary cells are counted explicitly. -/
theorem grid_card_comparison {α : Type*} {d : ℕ} (p : α → Point d) (S : Finset α)
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r ≤ 2 * ρ) :
    (S.image (grid p ρ)).card ≤ 3 ^ (d + 1) * (S.image (grid p r)).card := by
  classical
  have hsub : S.image (grid p ρ) ⊆ (S.image (grid p r)).biUnion (comparisonBox ρ r) := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_image_of_mem _ ha, grid_mem_comparisonBox p hρ hr hrρ a⟩
  calc
    _ ≤ ((S.image (grid p r)).biUnion (comparisonBox ρ r)).card := Finset.card_le_card hsub
    _ ≤ ∑ c ∈ S.image (grid p r), (comparisonBox ρ r c).card := Finset.card_biUnion_le
    _ = _ := by simp only [comparisonBox_card, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

lemma inTube_mono {d : ℕ} (T : TubeData d) {ρ r τ u : ℝ} (hρr : ρ ≤ r) (hτu : τ ≤ u)
    {p : Point d} (hp : InTube T ρ τ p) : InTube T r u p := by
  obtain ⟨s, hs, he⟩ := hp
  exact ⟨s, hs.trans (by linarith only [hτu]), fun i => (he i).trans hρr⟩

/-- The tested real tube is transported using its original labels and one
eligible larger query. This holds without injectivity of the motion map. -/
theorem moved_real_tube_le_profile {α : Type*} [Fintype α] [DecidableEq α] {d : ℕ}
    (p q : α → Point d) (E : Finset α) (T : TubeData d) {ρ r τ u : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hrρ : r ≤ 2 * ρ) (hτu : τ ≤ u)
    (hmove : ∀ a ∈ E, ∀ i, |q a i - p a i| ≤ r) :
    coverCount (grid q ρ) E (trace q ρ τ T) ≤ 45 ^ (d + 1) * coverProfile p r u E := by
  classical
  have hr : 0 < r := hρ.trans_le hρr
  have hsub : E ∩ trace q ρ τ T ⊆ E ∩ trace q r u T := by
    intro a ha
    obtain ⟨haE, haT⟩ := Finset.mem_inter.mp ha
    exact Finset.mem_inter.mpr ⟨haE, (mem_trace q r u T a).mpr
      (inTube_mono T hρr hτu ((mem_trace q ρ τ T a).mp haT))⟩
  calc
    _ ≤ 3 ^ (d + 1) * ((E ∩ trace q ρ τ T).image (grid q r)).card :=
      grid_card_comparison q _ hρ hr hrρ
    _ ≤ 3 ^ (d + 1) * coverCount (grid q r) E (trace q r u T) :=
      Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.image_subset_image hsub))
    _ ≤ 3 ^ (d + 1) * (15 ^ (d + 1) * coverProfile p r u E) :=
      Nat.mul_le_mul_left _ (TubePerturbationGridTransfer.moved_tube_le_original_profile p q E T hr hmove)
    _ = _ := by rw [← mul_assoc, ← mul_pow]; norm_num

lemma exists_minimal_upper_level {δ x : ℝ} (hδ : 0 < δ) (lo hi : ℕ)
    (hlohi : lo ≤ hi) (hlo : scale δ lo ≤ x) (hhi : x ≤ scale δ hi) :
    ∃ k, lo ≤ k ∧ k ≤ hi ∧ x ≤ scale δ k ∧ scale δ k ≤ 2 * x ∧
      ∀ j, lo ≤ j → j ≤ hi → x ≤ scale δ j → k ≤ j := by
  classical
  let S := (Finset.Icc lo hi).filter (fun k => x ≤ scale δ k)
  have hS : S.Nonempty := ⟨hi, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlohi, le_rfl⟩, hhi⟩⟩
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image S id hS
  obtain ⟨hkIcc, hxk⟩ := Finset.mem_filter.mp hk
  obtain ⟨hlok, hkhi⟩ := Finset.mem_Icc.mp hkIcc
  have hminimal : ∀ j, lo ≤ j → j ≤ hi → x ≤ scale δ j → k ≤ j := by
    intro j hlj hjh hxj
    exact hmin j (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlj, hjh⟩, hxj⟩)
  refine ⟨k, hlok, hkhi, hxk, ?_, hminimal⟩
  by_cases hkl : k = lo
  · rw [hkl]
    have hxpos : 0 < x := (scale_pos hδ lo).trans_le hlo
    linarith only [hlo, hxpos]
  · have hkpos : 0 < k := by omega
    have hprev : scale δ (k - 1) < x := by
      by_contra hh
      have hh' : x ≤ scale δ (k - 1) := le_of_not_gt hh
      have hm := hminimal (k - 1) (by omega) (by omega) hh'
      omega
    have hkstep : k = (k - 1) + 1 := by omega
    rw [hkstep, scale_add]
    norm_num
    linarith only [hprev]

/-- Eligible real widths and lengths have ordered ACTUAL dyadic upper
brackets within the stopped interval, including its endpoints. -/
theorem exists_nested_upper_levels {δ ρ τ : ℝ} (hδ : 0 < δ) (lo hi : ℕ)
    (hlohi : lo ≤ hi) (hlo : scale δ lo ≤ ρ) (hρτ : ρ ≤ τ) (hhi : τ ≤ scale δ hi) :
    ∃ i j, lo ≤ i ∧ i ≤ j ∧ j ≤ hi ∧
      ρ ≤ scale δ i ∧ scale δ i ≤ 2 * ρ ∧ τ ≤ scale δ j ∧ scale δ j ≤ 2 * τ := by
  obtain ⟨i, hli, _hih, hρi, hiρ, hmin⟩ := exists_minimal_upper_level hδ lo hi hlohi hlo (hρτ.trans hhi)
  obtain ⟨j, hlj, hjh, hτj, hjτ, _hmin⟩ := exists_minimal_upper_level hδ lo hi hlohi (hlo.trans hρτ) hhi
  exact ⟨i, j, hli, hmin j hlj hjh (hρτ.trans hτj), hjh, hρi, hiρ, hτj, hjτ⟩

/-- All-direction tube control at every real eligible scale after arbitrary
bounded point motion. The source is the SAME stopped residual E0, and the
output counts actual occupied absolute-grid cells of the moved labels. -/
theorem stopped_moved_real_tube {α : Type*} [Fintype α] [DecidableEq α]
    (p q : α → Plane) {δ ε K t : ℝ} {N : ℕ} {E₀ : Finset α}
    (D : StoppedProfile p δ ε K t N E₀) (E : Finset α) (hE : E ⊆ E₀)
    (T : TubeData 1) {ρ τ : ℝ} (hδ : 0 < δ) (hH : 0 ≤ D.loss)
    (hlo : scale δ D.pair.1 ≤ ρ) (hρτ : ρ ≤ τ) (hhi : τ ≤ scale δ D.pair.2)
    (hmove : ∀ a ∈ E, ∀ i, |q a i - p a i| ≤ ρ) :
    (coverCount (grid q ρ) E (trace q ρ τ T) : ℝ) ≤
      2025 * D.loss * (2 : ℝ) ^ D.exponent * (τ / ρ) ^ D.exponent := by
  obtain ⟨i, j, hli, hij, hjh, hρi, hiρ, hτj, hjτ⟩ :=
    exists_nested_upper_levels hδ D.pair.1 D.pair.2 D.valid.1 hlo hρτ hhi
  have hρ : 0 < ρ := (scale_pos hδ _).trans_le hlo
  have hτ : 0 < τ := hρ.trans_le hρτ
  have hbound := moved_real_tube_le_profile p q E T hρ hρi hiρ hτj
    (fun a ha k => (hmove a ha k).trans hρi)
  have hmono := coverProfile_mono p (scale δ i) (scale δ j) hE
  have hprofile := (D.nested_upper (i, j) ⟨hli, hjh, hij⟩).le
  change (coverProfile p (scale δ i) (scale δ j) E₀ : ℝ) ≤
    D.loss * (scale δ j / scale δ i) ^ D.exponent at hprofile
  have hratio : scale δ j / scale δ i ≤ 2 * (τ / ρ) := by
    calc
      _ ≤ (2 * τ) / ρ := div_le_div₀ (by positivity : 0 ≤ 2 * τ) hjτ hρ hρi
      _ = _ := by ring
  have hpower := Real.rpow_le_rpow (div_nonneg (scale_pos hδ j).le (scale_pos hδ i).le) hratio D.exponent_nonneg
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (div_nonneg hτ.le hρ.le)] at hpower
  have hcard : (coverCount (grid q ρ) E (trace q ρ τ T) : ℝ) ≤
      2025 * (coverProfile p (scale δ i) (scale δ j) E₀ : ℝ) := by
    exact_mod_cast hbound.trans (Nat.mul_le_mul_left _ hmono)
  calc
    _ ≤ 2025 * (D.loss * (scale δ j / scale δ i) ^ D.exponent) :=
      hcard.trans (mul_le_mul_of_nonneg_left hprofile (by norm_num))
    _ ≤ 2025 * (D.loss * ((2 : ℝ) ^ D.exponent * (τ / ρ) ^ D.exponent)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpower hH) (by norm_num)
    _ = _ := by ring

def shiftedBox {d : ℕ} (ρ : ℝ) (c : Point d) (k : GridLabel d) : Finset (GridLabel d) :=
  Fintype.piFinset fun i => Finset.Icc (k i - ⌊c i / ρ⌋ - 1) (k i - ⌊c i / ρ⌋)

lemma shiftedBox_card {d : ℕ} (ρ : ℝ) (c : Point d) (k : GridLabel d) :
    (shiftedBox ρ c k).card = 2 ^ (d + 1) := by
  have hc : ∀ i : Fin (d + 1),
      (Finset.Icc (k i - ⌊c i / ρ⌋ - 1) (k i - ⌊c i / ρ⌋)).card = 2 := by
    intro i
    rw [Int.card_Icc]
    omega
  simp only [shiftedBox, Fintype.card_piFinset, hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma shifted_grid_mem {α : Type*} {d : ℕ} (p : α → Point d) (c : Point d)
    (ρ : ℝ) (a : α) : grid (fun a i => p a i - c i) ρ a ∈ shiftedBox ρ c (grid p ρ a) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hl := Int.le_floor_add_floor ((p a i - c i) / ρ) (c i / ρ)
  have hu := Int.le_floor_add ((p a i - c i) / ρ) (c i / ρ)
  have he : (p a i - c i) / ρ + c i / ρ = p a i / ρ := by ring
  rw [he] at hl hu
  apply Finset.mem_Icc.mpr
  change grid p ρ a i - ⌊c i / ρ⌋ - 1 ≤ ⌊(p a i - c i) / ρ⌋ ∧
    ⌊(p a i - c i) / ρ⌋ ≤ grid p ρ a i - ⌊c i / ρ⌋
  change ⌊p a i / ρ⌋ - ⌊c i / ρ⌋ - 1 ≤ _ ∧ _ ≤ ⌊p a i / ρ⌋ - ⌊c i / ρ⌋
  omega

/-- Arbitrary recentering can split an absolute-grid cell. The exact bounded
split is paid rather than assuming translation commutes with floor labels. -/
theorem shifted_grid_card_le {α : Type*} {d : ℕ} (p : α → Point d) (c : Point d)
    (ρ : ℝ) (S : Finset α) :
    (S.image (grid (fun a i => p a i - c i) ρ)).card ≤
      2 ^ (d + 1) * (S.image (grid p ρ)).card := by
  classical
  have hsub : S.image (grid (fun a i => p a i - c i) ρ) ⊆
      (S.image (grid p ρ)).biUnion (shiftedBox ρ c) := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_image_of_mem _ ha, shifted_grid_mem p c ρ a⟩
  calc
    _ ≤ ((S.image (grid p ρ)).biUnion (shiftedBox ρ c)).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ S.image (grid p ρ), (shiftedBox ρ c k).card := Finset.card_biUnion_le
    _ = _ := by simp only [shiftedBox_card, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

def normalized {α : Type*} {d : ℕ} (p : α → Point d) (c : Point d) (L : ℝ) : α → Point d :=
  fun a i => (p a i - c i) / L

lemma normalized_grid {α : Type*} {d : ℕ} (p : α → Point d) (c : Point d) (L ρ : ℝ) :
    grid (normalized p c L) ρ = grid (fun a i => p a i - c i) (L * ρ) := by
  funext a i
  simp only [grid, normalized, div_div]

def physicalTube {d : ℕ} (c : Point d) (L : ℝ) (T : TubeData d) : TubeData d where
  center := fun i => c i + L * T.center i
  direction := T.direction
  unit := T.unit

lemma normalized_inTube {d : ℕ} (c : Point d) {L : ℝ} (hL : 0 < L)
    (T : TubeData d) {ρ τ : ℝ} {p : Point d}
    (hp : InTube T ρ τ (fun i => (p i - c i) / L)) :
    InTube (physicalTube c L T) (L * ρ) (L * τ) p := by
  obtain ⟨s, hs, he⟩ := hp
  refine ⟨L * s, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hL]
    nlinarith only [mul_le_mul_of_nonneg_left hs hL.le]
  · intro i
    have hh := mul_le_mul_of_nonneg_left (he i) hL.le
    have hid : p i - (c i + L * T.center i) - L * s * T.direction i =
        L * ((p i - c i) / L - T.center i - s * T.direction i) := by field_simp; ring
    change |p i - (c i + L * T.center i) - L * s * T.direction i| ≤ L * ρ
    rw [hid, abs_mul, abs_of_pos hL]
    exact hh

/-- Normalized all-direction tube control, allowing recentering at ANY
original point. The fixed factor 4 pays for the shifted absolute grid. -/
theorem normalized_stopped_moved_real_tube {α : Type*} [Fintype α] [DecidableEq α]
    (p q : α → Plane) {δ ε K t : ℝ} {N : ℕ} {E₀ : Finset α}
    (D : StoppedProfile p δ ε K t N E₀) (E : Finset α) (hE : E ⊆ E₀)
    (c : Plane) {L : ℝ} (hL : 0 < L) (T : TubeData 1) {ρ τ : ℝ}
    (hδ : 0 < δ) (hH : 0 ≤ D.loss)
    (hlo : scale δ D.pair.1 ≤ L * ρ) (hρτ : ρ ≤ τ) (hhi : L * τ ≤ scale δ D.pair.2)
    (hmove : ∀ a ∈ E, ∀ i, |q a i - p a i| ≤ L * ρ) :
    (coverCount (grid (normalized q c L) ρ) E (trace (normalized q c L) ρ τ T) : ℝ) ≤
      8100 * D.loss * (2 : ℝ) ^ D.exponent * (τ / ρ) ^ D.exponent := by
  classical
  let S := E ∩ trace (normalized q c L) ρ τ T
  have hsub : S ⊆ E ∩ trace q (L * ρ) (L * τ) (physicalTube c L T) := by
    intro a ha
    obtain ⟨haE, haT⟩ := Finset.mem_inter.mp ha
    exact Finset.mem_inter.mpr ⟨haE, (mem_trace q _ _ _ a).mpr
      (normalized_inTube c hL T ((mem_trace (normalized q c L) ρ τ T a).mp haT))⟩
  have hcard : coverCount (grid (normalized q c L) ρ) E (trace (normalized q c L) ρ τ T) ≤
      4 * coverCount (grid q (L * ρ)) E (trace q (L * ρ) (L * τ) (physicalTube c L T)) := by
    change (S.image (grid (normalized q c L) ρ)).card ≤ _
    rw [normalized_grid]
    exact (shifted_grid_card_le q c (L * ρ) S).trans
      (Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.image_subset_image hsub)))
  have hbound := stopped_moved_real_tube p q D E hE (physicalTube c L T) hδ hH hlo
    (mul_le_mul_of_nonneg_left hρτ hL.le) hhi hmove
  have hratio : (L * τ) / (L * ρ) = τ / ρ := mul_div_mul_left _ _ hL.ne'
  rw [hratio] at hbound
  have hcardR : (coverCount (grid (normalized q c L) ρ) E (trace (normalized q c L) ρ τ T) : ℝ) ≤
      4 * (coverCount (grid q (L * ρ)) E (trace q (L * ρ) (L * τ) (physicalTube c L T)) : ℝ) := by
    exact_mod_cast hcard
  nlinarith only [hcardR, hbound]

end
end RealScaleTubeProfileTransfer
