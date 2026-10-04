import Theorems.Thm_StickyKakeya4_real_scale_tube_profile_transfer
import Theorems.Thm_StickyKakeya4_native_separated_fractional_patches

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace ParentAllRealTubeControl

open NativeDyadicTubeStopping ActualTubeFootprintProfiles FiniteCoverProfileEpochs
open RealScaleTubeProfileTransfer TubePerturbationGridTransfer

noncomputable section
attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A long tested tube is localized using the ACTUAL original parent cell.
Its fine width is unchanged except for the fixed bounded-motion factor. -/
theorem local_moved_tube_le_profile (p q : α → Plane) (E₀ E : Finset α) (hE : E ⊆ E₀)
    (T : TubeData 1) {ρ r b τ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (hrρ : r ≤ 2 * ρ)
    (hrb : r ≤ b) (c : GridLabel 1) (hcell : ∀ a ∈ E, grid p b a = c)
    (hmove : ∀ a ∈ E, ∀ i, |q a i - p a i| ≤ r) :
    coverCount (grid q ρ) E (trace q ρ τ T) ≤ 42525 * coverProfile p r b E₀ := by
  classical
  let S := E ∩ trace q ρ τ T
  have hSE : S ⊆ E := Finset.inter_subset_left
  have hr : 0 < r := hρ.trans_le hρr
  have htube : ∀ a ∈ S, InTube T ((2 : ℝ) * r) τ (p a) := by
    intro a ha
    have hh := moved_tube_pullback T (p a) (q a) (hmove a (hSE ha))
      ((mem_trace q ρ τ T a).mp (Finset.mem_inter.mp ha).2)
    exact inTube_mono T (by linarith only [hρr]) le_rfl hh
  have hlocal := TubeExpansionCover.local_cell_image_le_actual_profile p E₀ S T 2 hr hrb
    (hSE.trans hE) htube c (fun a ha => hcell a (hSE ha))
  have hcomp := grid_card_comparison q S hρ hr hrρ
  have hmotion := moved_grid_card_le p q S hr (fun a ha => hmove a (hSE ha))
  change (S.image (grid p r)).card ≤ 525 * coverProfile p r b E₀ at hlocal
  change (S.image (grid q ρ)).card ≤ _
  calc
    _ ≤ 9 * (S.image (grid q r)).card := hcomp
    _ ≤ 9 * (9 * (S.image (grid p r)).card) := Nat.mul_le_mul_left _ hmotion
    _ ≤ 9 * (9 * (525 * coverProfile p r b E₀)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlocal)
    _ = _ := by ring

theorem stopped_parent_long_tube (p q : α → Plane) {δ ε K t : ℝ} {N : ℕ} {E₀ : Finset α}
    (D : StoppedProfile p δ ε K t N E₀) (E : Finset α) (hE : E ⊆ E₀)
    (k : ℕ) (hklo : D.pair.1 ≤ k) (hkhi : k ≤ D.pair.2)
    (c : GridLabel 1) (hcell : ∀ a ∈ E, grid p (scale δ k) a = c)
    (T : TubeData 1) {ρ τ : ℝ} (hδ : 0 < δ) (hH : 0 ≤ D.loss)
    (hlo : scale δ D.pair.1 ≤ ρ) (hρb : ρ ≤ scale δ k) (hbτ : scale δ k ≤ τ)
    (hmove : ∀ a ∈ E, ∀ i, |q a i - p a i| ≤ ρ) :
    (coverCount (grid q ρ) E (trace q ρ τ T) : ℝ) ≤
      42525 * D.loss * (τ / ρ) ^ D.exponent := by
  obtain ⟨i, hli, hik, hρi, hiρ, _hmin⟩ :=
    exists_minimal_upper_level hδ D.pair.1 k hklo hlo hρb
  have hρ : 0 < ρ := (scale_pos hδ _).trans_le hlo
  have hτ : 0 < τ := (scale_pos hδ _).trans_le hbτ
  have hcard := local_moved_tube_le_profile p q E₀ E hE T (τ := τ) hρ hρi hiρ
    (scale_mono hδ.le hik) c hcell (fun a ha j => (hmove a ha j).trans hρi)
  have hprofile := (D.nested_upper (i, k) ⟨hli, hkhi, hik⟩).le
  change (coverProfile p (scale δ i) (scale δ k) E₀ : ℝ) ≤
    D.loss * (scale δ k / scale δ i) ^ D.exponent at hprofile
  have hratio : scale δ k / scale δ i ≤ τ / ρ := div_le_div₀ hτ.le hbτ hρ hρi
  have hpow := Real.rpow_le_rpow
    (div_nonneg (scale_pos hδ k).le (scale_pos hδ i).le) hratio D.exponent_nonneg
  have hc : (coverCount (grid q ρ) E (trace q ρ τ T) : ℝ) ≤
      42525 * (coverProfile p (scale δ i) (scale δ k) E₀ : ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ 42525 * (D.loss * (scale δ k / scale δ i) ^ D.exponent) :=
      hc.trans (mul_le_mul_of_nonneg_left hprofile (by norm_num))
    _ ≤ 42525 * (D.loss * (τ / ρ) ^ D.exponent) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hH) (by norm_num)
    _ = _ := by ring

omit [Fintype α] in
/-- Above the parent width, an actual moved parent has only a fixed number
of occupied cells, independently of tube length or direction. -/
lemma wide_parent_grid_card (p q : α → Plane) (E : Finset α) {b ρ : ℝ}
    (hb : 0 < b) (hbρ : b ≤ ρ) (c : GridLabel 1) (hcell : ∀ a ∈ E, grid p b a = c)
    (hmove : ∀ a ∈ E, ∀ i, |q a i - p a i| ≤ ρ) :
    (E.image (grid q ρ)).card ≤ 81 := by
  have hρ := hb.trans_le hbρ
  have hmotion := moved_grid_card_le p q E hρ hmove
  have hcomp := grid_card_comparison p E hρ hb (by linarith only [hbρ, hρ])
  have hone : (E.image (grid p b)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hv
    exact (hcell a ha).trans (hcell a' ha').symm
  calc
    _ ≤ 9 * (E.image (grid p ρ)).card := hmotion
    _ ≤ 9 * (9 * (E.image (grid p b)).card) := Nat.mul_le_mul_left _ hcomp
    _ ≤ 9 * (9 * 1) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hone)
    _ = 81 := by norm_num

/-- One actual dyadic parent supplies the endpoint extension at ALL real
widths above the stopped lower scale and ALL lengths above the tested width.
No query beyond the stopped top is made. -/
theorem stopped_parent_all_real_tube (p q : α → Plane) {δ ε K t : ℝ} {N : ℕ} {E₀ : Finset α}
    (D : StoppedProfile p δ ε K t N E₀) (E : Finset α) (hE : E ⊆ E₀)
    (k : ℕ) (hklo : D.pair.1 ≤ k) (hkhi : k ≤ D.pair.2)
    (c : GridLabel 1) (hcell : ∀ a ∈ E, grid p (scale δ k) a = c)
    (T : TubeData 1) {ρ τ : ℝ} (hδ : 0 < δ) (hH : 1 ≤ D.loss)
    (hlo : scale δ D.pair.1 ≤ ρ) (hρτ : ρ ≤ τ)
    (hmove : ∀ a ∈ E, ∀ i, |q a i - p a i| ≤ ρ) :
    (coverCount (grid q ρ) E (trace q ρ τ T) : ℝ) ≤
      42525 * D.loss * (2 : ℝ) ^ D.exponent * (τ / ρ) ^ D.exponent := by
  have hH0 : 0 ≤ D.loss := zero_le_one.trans hH
  have hρ : 0 < ρ := (scale_pos hδ _).trans_le hlo
  have hτ : 0 < τ := hρ.trans_le hρτ
  have htwo : 1 ≤ (2 : ℝ) ^ D.exponent := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2) D.exponent_nonneg
  have hpow0 : 0 ≤ (τ / ρ) ^ D.exponent := Real.rpow_nonneg (div_nonneg hτ.le hρ.le) _
  by_cases hρb : ρ ≤ scale δ k
  · by_cases hτb : τ ≤ scale δ k
    · have h := stopped_moved_real_tube p q D E hE T hδ hH0 hlo hρτ
        (hτb.trans (scale_mono hδ.le hkhi)) hmove
      have hnonneg : 0 ≤ D.loss * (2 : ℝ) ^ D.exponent * (τ / ρ) ^ D.exponent := by positivity
      nlinarith only [h, hnonneg]
    · have h := stopped_parent_long_tube p q D E hE k hklo hkhi c hcell T hδ hH0 hlo hρb
        (le_of_not_ge hτb) hmove
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htwo hH0) hpow0
      nlinarith only [h, hh]
  · have hcard := wide_parent_grid_card p q E (scale_pos hδ k) (le_of_not_ge hρb) c hcell hmove
    have hsub : coverCount (grid q ρ) E (trace q ρ τ T) ≤ (E.image (grid q ρ)).card :=
      Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left)
    have h81 : (coverCount (grid q ρ) E (trace q ρ τ T) : ℝ) ≤ 81 := by exact_mod_cast hsub.trans hcard
    have hratio : 1 ≤ τ / ρ := (le_div_iff₀ hρ).mpr (by simpa using hρτ)
    have hpow : 1 ≤ (τ / ρ) ^ D.exponent := by
      simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hratio D.exponent_nonneg
    have hprod : 1 ≤ D.loss * (2 : ℝ) ^ D.exponent * (τ / ρ) ^ D.exponent :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hH htwo) hpow
    nlinarith only [h81, hprod]

/-- Parent localization also survives arbitrary affine recentering, with the
literal shifted-grid factor four. There is no upper restriction on tube length. -/
theorem normalized_parent_all_real_tube (p q : α → Plane) {δ ε K t : ℝ} {N : ℕ} {E₀ : Finset α}
    (D : StoppedProfile p δ ε K t N E₀) (E : Finset α) (hE : E ⊆ E₀)
    (k : ℕ) (hklo : D.pair.1 ≤ k) (hkhi : k ≤ D.pair.2)
    (parent : GridLabel 1) (hcell : ∀ a ∈ E, grid p (scale δ k) a = parent)
    (c : Plane) {L : ℝ} (hL : 0 < L) (T : TubeData 1) {ρ τ : ℝ}
    (hδ : 0 < δ) (hH : 1 ≤ D.loss) (hlo : scale δ D.pair.1 ≤ L * ρ) (hρτ : ρ ≤ τ)
    (hmove : ∀ a ∈ E, ∀ i, |q a i - p a i| ≤ L * ρ) :
    (coverCount (grid (normalized q c L) ρ) E (trace (normalized q c L) ρ τ T) : ℝ) ≤
      170100 * D.loss * (2 : ℝ) ^ D.exponent * (τ / ρ) ^ D.exponent := by
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
  have hbound := stopped_parent_all_real_tube p q D E hE k hklo hkhi parent hcell
    (physicalTube c L T) hδ hH hlo (mul_le_mul_of_nonneg_left hρτ hL.le) hmove
  have hratio : (L * τ) / (L * ρ) = τ / ρ := mul_div_mul_left _ _ hL.ne'
  rw [hratio] at hbound
  have hcardR : (coverCount (grid (normalized q c L) ρ) E (trace (normalized q c L) ρ τ T) : ℝ) ≤
      4 * (coverCount (grid q (L * ρ)) E (trace q (L * ρ) (L * τ) (physicalTube c L T)) : ℝ) := by
    exact_mod_cast hcard
  nlinarith only [hcardR, hbound]

open NativeAngularChartSelection NativeSeparatedFractionalPatches

/-- A coordinate chart transports the already constructed stop exactly. -/
def chartStoppedProfile (p : α → Plane) {δ ε K t : ℝ} {N : ℕ} {E : Finset α}
    (D : StoppedProfile p δ ε K t N E) (j : Fin 2) :
    StoppedProfile (chartPoint j ∘ p) δ ε K t N E where
  pair := D.pair
  valid := D.valid
  length_pos := D.length_pos
  exponent := D.exponent
  exponent_nonneg := D.exponent_nonneg
  exponent_le := D.exponent_le
  separation := D.separation
  selected_lower := by simpa only [counts, chart_profile] using D.selected_lower
  selected_upper := by simpa only [counts, chart_profile] using D.selected_upper
  nested_upper := by intro v hv; simpa only [counts, chart_profile] using D.nested_upper v hv

/-- Tube-KT on the actual normalized quantized IMAGE, including every real
width above the output mesh and arbitrary tube lengths. Original point labels
are used throughout its proof, so quantizer collisions need no injectivity. -/
theorem quantized_chart_parent_trace_bound (p : α → Plane) {δ ε K t : ℝ} {N : ℕ} {E₀ : Finset α}
    (D : StoppedProfile p δ ε K t N E₀) (E : Finset α) (hE : E ⊆ E₀)
    (k : ℕ) (hklo : D.pair.1 ≤ k) (hkhi : k ≤ D.pair.2)
    (parent : GridLabel 1) (hcell : ∀ a ∈ E, grid p (scale δ k) a = parent)
    (j : Fin 2) (c : Plane) {μ angle L ρ τ : ℝ}
    (hμ : 0 < μ) (hL : 0 < L) (hδ : 0 < δ) (hH : 1 ≤ D.loss)
    (hlo : scale δ D.pair.1 ≤ L * ρ) (hμρ : μ ≤ L * ρ) (hρτ : ρ ≤ τ) :
    ShearedGridTubeReference.TraceBound
      (E.image (normalized (quantized μ angle ∘ chartPoint j ∘ p) c L)) ρ τ
      (170100 * D.loss * (2 : ℝ) ^ D.exponent * (τ / ρ) ^ D.exponent) := by
  intro T
  rw [trace_grid_image]
  apply normalized_parent_all_real_tube (chartPoint j ∘ p)
    (quantized μ angle ∘ chartPoint j ∘ p) (chartStoppedProfile p D j) E hE k hklo hkhi
    (parent ∘ chartPerm j) ?_ c hL T hδ hH hlo hρτ ?_
  · intro a ha
    rw [chart_grid, hcell a ha]
  · intro a _ha i
    exact (quantized_coordinate_movement μ angle hμ (chartPoint j (p a)) i).le.trans hμρ

end
end ParentAllRealTubeControl
