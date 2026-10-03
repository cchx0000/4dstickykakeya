import Theorems.Thm_StickyKakeya4_cover_profile_clipping
import Theorems.Thm_StickyKakeya4_sheared_grid_tube_reference

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace NativeDyadicTubeStopping

open CoverProfileStopping CoverProfileClipping
open ActualTubeFootprintProfiles
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev Plane := Fin 2 → ℝ

def scale (δ : ℝ) (i : ℕ) : ℝ := δ * (2 : ℝ) ^ i

lemma scale_pos {δ : ℝ} (hδ : 0 < δ) (i : ℕ) : 0 < scale δ i := by
  unfold scale
  positivity

@[simp] lemma scale_zero (δ : ℝ) : scale δ 0 = δ := by simp [scale]

lemma scale_mono {δ : ℝ} (hδ : 0 ≤ δ) : Monotone (scale δ) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hij) hδ

lemma scale_strictMono {δ : ℝ} (hδ : 0 < δ) : StrictMono (scale δ) := by
  intro i j hij
  exact mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (by norm_num) hij) hδ

lemma scale_le_iff {δ : ℝ} (hδ : 0 < δ) (i j : ℕ) : scale δ i ≤ scale δ j ↔ i ≤ j :=
  (scale_strictMono hδ).le_iff_le

lemma scale_add (δ : ℝ) (i k : ℕ) : scale δ (i + k) = scale δ i * (2 : ℝ) ^ k := by
  simp only [scale, pow_add]
  ring

lemma scale_ratio {δ : ℝ} (hδ : 0 < δ) {i j : ℕ} (hij : i ≤ j) :
    scale δ j / scale δ i = (2 : ℝ) ^ (j - i) := by
  have hsplit : j = i + (j - i) := by omega
  conv_lhs => rw [hsplit, scale_add]
  exact mul_div_cancel_left₀ _ (scale_pos hδ i).ne'

lemma scale_min (δ : ℝ) (hδ : 0 ≤ δ) (i j : ℕ) :
    scale δ (min i j) = min (scale δ i) (scale δ j) := by
  rcases le_total i j with h | h
  · rw [min_eq_left h, min_eq_left (scale_mono hδ h)]
  · rw [min_eq_right h, min_eq_right (scale_mono hδ h)]

def adProfileConstant (K t : ℝ) : ℝ := (9 : ℝ) ^ 2 * (18 : ℝ) ^ t * K ^ 2

lemma adProfileConstant_ge_one {K t : ℝ} (hK : 1 ≤ K) (ht : 0 ≤ t) :
    1 ≤ adProfileConstant K t := by
  have hpow : (1 : ℝ) ≤ (18 : ℝ) ^ t := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 18) ht
  have hKsq : (1 : ℝ) ≤ K ^ 2 := by nlinarith only [hK, sq_nonneg (K - 1)]
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by norm_num : (1 : ℝ) ≤ (9 : ℝ) ^ 2) hpow) hKsq

variable {α : Type*} [Fintype α] [DecidableEq α]

def counts (p : α → Plane) (δ : ℝ) (E : Finset α) (q : ScalePair) : ℕ :=
  coverProfile p (scale δ q.1) (scale δ q.2) E

/-- Constructed stopped data, all expressed with the literal original scales
and actual finite family of genuine tube traces. -/
structure StoppedProfile (p : α → Plane) (δ ε K t : ℝ) (N : ℕ) (E : Finset α) where
  pair : ScalePair
  valid : Valid N pair
  length_pos : 0 < length pair
  exponent : ℝ
  exponent_nonneg : 0 ≤ exponent
  exponent_le : exponent ≤ min t 1
  separation : ((2 : ℝ) ^ N) ^ separationExponent ε ≤ scale δ pair.2 / scale δ pair.1
  selected_lower : (scale δ pair.2 / scale δ pair.1) ^ exponent ≤ (counts p δ E pair : ℝ)
  selected_upper : (counts p δ E pair : ℝ) ≤
    (72 * adProfileConstant K t) * (scale δ pair.2 / scale δ pair.1) ^ exponent
  nested_upper : ∀ q, Nested q pair → (counts p δ E q : ℝ) <
    (72 * adProfileConstant K t) * (scale δ pair.2 / scale δ pair.1) ^ ε *
      (scale δ q.2 / scale δ q.1) ^ exponent

/-- The actual geometry and original AD instantiate the finite improving-score
stopping theorem. No selected pair, exponent or upper-profile property is given. -/
theorem exists_stopped_profile (A : Finset Plane) (p : α → Plane)
    (hpositions : ∀ a, p a ∈ A) (δ ε K t : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hN : 0 < N) (htop : scale δ N ≤ 1)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hlarge : 4 * (Real.log 72 / Real.log 2) < ε ^ stepBudget ε * (N : ℝ))
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) (hAD : ADBounds A δ K t)
    (E : Finset α) (hE : E.Nonempty) : Nonempty (StoppedProfile p δ ε K t N E) := by
  have hscale (q : ScalePair) (hq : Valid N q) :
      δ ≤ scale δ q.1 ∧ scale δ q.1 ≤ scale δ q.2 ∧ scale δ q.2 ≤ 1 := by
    exact ⟨by simpa only [scale_zero] using scale_mono hδ.le (Nat.zero_le q.1),
      scale_mono hδ.le hq.1, (scale_mono hδ.le hq.2).trans htop⟩
  have hM (q : ScalePair) (hq : Valid N q) :
      0 < counts p δ E q ∧ (counts p δ E q : ℝ) ≤ 72 * dyadicRatio q := by
    have hqscale := hscale q hq
    refine ⟨coverProfile_positive p (scale_pos hδ q.1).le (scale_pos hδ q.2).le hE, ?_⟩
    have hline := coverProfile_linear_bound p E (scale_pos hδ q.1) hqscale.2.1
    simpa only [counts, scale_ratio hδ hq.1, dyadicRatio, pow_one, Nat.cast_ofNat, show (9 : ℝ) * 8 = 72 by norm_num] using hline
  have hD (q : ScalePair) (hq : Valid N q) :
      (counts p δ E q : ℝ) ≤ adProfileConstant K t * (dyadicRatio q) ^ t := by
    have hqscale := hscale q hq
    have hbound := coverProfile_AD_bound A p hpositions E hδ hqscale.1 hqscale.2.1 hqscale.2.2
      hK ht ht2 hdiam hAD
    simpa only [counts, scale_ratio hδ hq.1, adProfileConstant, dyadicRatio] using hbound
  obtain ⟨q, hq, hlen, hsep, hs, hst, hlo, hup, hnested⟩ :=
    exists_clipped_dyadic_cover_profile N ε 72 (adProfileConstant K t) t (counts p δ E)
      hN hε hεhalf (by norm_num) (adProfileConstant_ge_one hK ht) ht hlarge hM hD
  refine ⟨⟨q, hq, hlen, clippedSlope (slope (counts p δ E) q) t, hs, hst, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [scale_ratio hδ hq.1, dyadicRatio] using hsep
  · simpa only [scale_ratio hδ hq.1, dyadicRatio] using hlo
  · simpa only [scale_ratio hδ hq.1, dyadicRatio] using hup
  · intro r hr
    simpa only [scale_ratio hδ hq.1, scale_ratio hδ hr.2.2, dyadicRatio] using hnested r hr

/-- Exact finite index menu for the epoch selector, including equal scales. -/
def pairMenu (N : ℕ) : Finset ScalePair :=
  ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter (fun q => q.1 ≤ q.2)

lemma mem_pairMenu (N : ℕ) (q : ScalePair) : q ∈ pairMenu N ↔ Valid N q := by
  constructor
  · intro hq
    obtain ⟨hmem, hij⟩ := Finset.mem_filter.mp hq
    have hj := Finset.mem_range.mp (Finset.mem_product.mp hmem).2
    exact ⟨hij, by omega⟩
  · intro hq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, hq.1⟩
    · have := hq.1
      have := hq.2
      omega
    · have := hq.2
      omega

abbrev Index (N : ℕ) := {q : ScalePair // q ∈ pairMenu N}

def origin (N : ℕ) : Index N := ⟨(0, 0), (mem_pairMenu N (0, 0)).mpr ⟨by omega, by omega⟩⟩

def StoppedProfile.index {p : α → Plane} {δ ε K t : ℝ} {N : ℕ} {E : Finset α}
    (D : StoppedProfile p δ ε K t N E) : Index N := ⟨D.pair, (mem_pairMenu N D.pair).mpr D.valid⟩

/-- One actual finite selector simultaneously available on every residual.
It can be passed directly to the disjoint whole-cell epoch constructor. -/
theorem exists_stopping_selector (A : Finset Plane) (p : α → Plane)
    (hpositions : ∀ a, p a ∈ A) (δ ε K t : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hN : 0 < N) (htop : scale δ N ≤ 1)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hlarge : 4 * (Real.log 72 / Real.log 2) < ε ^ stepBudget ε * (N : ℝ))
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) (hAD : ADBounds A δ K t) :
    ∃ select : Finset α → Index N, ∀ E, E.Nonempty →
      ∃ D : StoppedProfile p δ ε K t N E, D.pair = (select E).val := by
  classical
  let chooseData (E : Finset α) (hE : E.Nonempty) : StoppedProfile p δ ε K t N E :=
    Classical.choice (exists_stopped_profile A p hpositions δ ε K t N hδ hN htop hε hεhalf hK ht ht2
      hlarge hdiam hAD E hE)
  let select (E : Finset α) : Index N := if hE : E.Nonempty then (chooseData E hE).index else origin N
  refine ⟨select, ?_⟩
  intro E hE
  exact ⟨chooseData E hE, by simp [select, hE, StoppedProfile.index]⟩


lemma trace_grid_image (p : α → Plane) (E : Finset α) (ρ τ : ℝ) (T : TubeData 1) :
    (((E.image p).filter (fun x => InTube T ρ τ x)).image (ADGridCoverMenus.gridLabel ρ)) =
      (E ∩ trace p ρ τ T).image (grid p ρ) := by
  classical
  ext c
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter, mem_trace]
  constructor
  · rintro ⟨x, ⟨⟨a, ha, rfl⟩, hT⟩, hgrid⟩
    exact ⟨a, ⟨ha, hT⟩, hgrid⟩
  · rintro ⟨a, ⟨ha, hT⟩, hgrid⟩
    exact ⟨p a, ⟨⟨a, ha, rfl⟩, hT⟩, hgrid⟩

/-- Actual profile bounds pass to the exact original position image; no
injectivity or cover-number inheritance certificate is needed. -/
lemma traceBound_image_of_profile (p : α → Plane) (E : Finset α) (ρ τ B : ℝ)
    (hprofile : (coverProfile p ρ τ E : ℝ) ≤ B) :
    ShearedGridTubeReference.TraceBound (E.image p) ρ τ B := by
  classical
  intro T
  rw [trace_grid_image]
  have hmax : ((E ∩ trace p ρ τ T).image (grid p ρ)).card ≤ coverProfile p ρ τ E := by
    unfold coverProfile
    exact Finset.le_sup (f := fun W : Finset α => ((E ∩ W).image (grid p ρ)).card)
      (trace_mem_footprints p ρ τ T)
  exact (Nat.cast_le.mpr hmax).trans hprofile

lemma position_image_profile (p : α → Plane) (E : Finset α) (ρ τ : ℝ) :
    coverProfile (fun x : E.image p => (x : Plane)) ρ τ Finset.univ = coverProfile p ρ τ E := by
  classical
  let pos : E.image p → Plane := fun x => x.val
  have hposition : Finset.univ.image pos = E.image p := by
    ext x
    simp [pos]
  have hsame (T : TubeData 1) :
      ((Finset.univ ∩ trace pos ρ τ T).image (grid pos ρ)).card =
        ((E ∩ trace p ρ τ T).image (grid p ρ)).card := by
    rw [← trace_grid_image pos Finset.univ ρ τ T, hposition, trace_grid_image]
  apply le_antisymm
  · obtain ⟨T, hmax⟩ := exists_maximizing_tube pos ρ τ Finset.univ
    change coverProfile pos ρ τ Finset.univ ≤ _
    rw [← hmax, hsame]
    exact Finset.le_sup (f := fun W : Finset α => ((E ∩ W).image (grid p ρ)).card)
      (trace_mem_footprints p ρ τ T)
  · obtain ⟨T, hmax⟩ := exists_maximizing_tube p ρ τ E
    rw [← hmax, ← hsame]
    exact Finset.le_sup (f := fun W : Finset (E.image p) =>
      ((Finset.univ ∩ W).image (grid pos ρ)).card) (trace_mem_footprints pos ρ τ T)

variable {p : α → Plane} {δ ε K t : ℝ} {N : ℕ} {E : Finset α}

def StoppedProfile.loss (D : StoppedProfile p δ ε K t N E) : ℝ :=
  (72 * adProfileConstant K t) * (scale δ D.pair.2 / scale δ D.pair.1) ^ ε

lemma StoppedProfile.loss_ge_one (D : StoppedProfile p δ ε K t N E)
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hK : 1 ≤ K) (ht : 0 ≤ t) : 1 ≤ D.loss := by
  have hratio : (1 : ℝ) ≤ scale δ D.pair.2 / scale δ D.pair.1 := by
    apply (le_div_iff₀ (scale_pos hδ _)).mpr
    simpa only [one_mul] using scale_mono hδ.le D.valid.1
  have hpow : (1 : ℝ) ≤ (scale δ D.pair.2 / scale δ D.pair.1) ^ ε := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hratio hε
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by norm_num : (1 : ℝ) ≤ 72) (adProfileConstant_ge_one hK ht)) hpow

lemma StoppedProfile.nested_trace_bound (D : StoppedProfile p δ ε K t N E)
    {q : ScalePair} (hq : Nested q D.pair) :
    ShearedGridTubeReference.TraceBound (E.image p) (scale δ q.1) (scale δ q.2)
      (D.loss * (scale δ q.2 / scale δ q.1) ^ D.exponent) :=
  traceBound_image_of_profile p E _ _ _ (D.nested_upper q hq).le

/-- Literal dyadic membership and all three native profile queries. For the
raw quantizer μ=a/64 and R=2^k, the physical comparison width is aR. The min
endpoint is the scale with index min(i+k,j), which remains inside the stop. -/
theorem StoppedProfile.native_queries (D : StoppedProfile p δ ε K t N E)
    (hδ : 0 < δ) (i j k : ℕ)
    (hlo : D.pair.1 ≤ i) (hij : i ≤ j) (hhi : j ≤ D.pair.2) :
    (coverProfile (fun x : E.image p => (x : Plane)) (scale δ D.pair.1) (scale δ i) Finset.univ : ℝ) ≤
        D.loss * (scale δ i / scale δ D.pair.1) ^ D.exponent ∧
    (scale δ i * (2 : ℝ) ^ k ≤ scale δ j →
      ShearedGridTubeReference.TraceBound (E.image p) (scale δ i * (2 : ℝ) ^ k) (scale δ j)
        (D.loss * (scale δ j / (scale δ i * (2 : ℝ) ^ k)) ^ D.exponent)) ∧
    ShearedGridTubeReference.TraceBound (E.image p) (scale δ i)
      (min (scale δ i * (2 : ℝ) ^ k) (scale δ j))
      (D.loss * (min (scale δ i * (2 : ℝ) ^ k) (scale δ j) / scale δ i) ^ D.exponent) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [position_image_profile]
    exact (D.nested_upper (D.pair.1, i) ⟨le_refl _, hij.trans hhi, hlo⟩).le
  · intro hwidth
    have hikj : i + k ≤ j := (scale_le_iff hδ _ _).mp (by rwa [scale_add])
    have hbound := D.nested_trace_bound (q := (i + k, j)) ⟨by omega, hhi, hikj⟩
    simpa only [scale_add] using hbound
  · have hbound := D.nested_trace_bound (q := (i, min (i + k) j))
      ⟨hlo, (min_le_right _ _).trans hhi, le_min (by omega) hij⟩
    simpa only [scale_min δ hδ.le, scale_add] using hbound


/-- The raw quantizer grid has N=64b/a, an actual positive integral power of
 two. Its physical step is μ=a/64. -/
lemma native_grid_extent (δ : ℝ) (hδ : 0 < δ) (i j : ℕ) (hij : i ≤ j) :
    0 < scale δ i / 64 ∧
    (scale δ i / 64) * ((2 ^ (j - i + 6) : ℕ) : ℝ) = scale δ j := by
  refine ⟨div_pos (scale_pos hδ i) (by norm_num), ?_⟩
  have hj : j = i + (j - i) := by omega
  conv_rhs => rw [hj, scale_add]
  push_cast
  rw [pow_add]
  norm_num
  ring

/-- Exact conversion to the quantizer convention used by the native
fractional constructor. R is explicitly a dyadic integer, not an arbitrary
real scale for which stopped-profile membership would need interpolation. -/
theorem StoppedProfile.native_quantizer_queries (D : StoppedProfile p δ ε K t N E)
    (hδ : 0 < δ) (μ b : ℝ) (i j k : ℕ)
    (hmesh : 64 * μ = scale δ i) (hparent : b = scale δ j)
    (hlo : D.pair.1 ≤ i) (hij : i ≤ j) (hhi : j ≤ D.pair.2) :
    (coverProfile (fun x : E.image p => (x : Plane)) (scale δ D.pair.1) (64 * μ) Finset.univ : ℝ) ≤
        D.loss * ((64 * μ) / scale δ D.pair.1) ^ D.exponent ∧
    (64 * μ * ((2 ^ k : ℕ) : ℝ) ≤ b →
      ShearedGridTubeReference.TraceBound (E.image p) (64 * μ * ((2 ^ k : ℕ) : ℝ)) b
        (D.loss * (b / (64 * μ * ((2 ^ k : ℕ) : ℝ))) ^ D.exponent)) ∧
    ShearedGridTubeReference.TraceBound (E.image p) (64 * μ)
      (min (64 * μ * ((2 ^ k : ℕ) : ℝ)) b)
      (D.loss * (min (64 * μ * ((2 ^ k : ℕ) : ℝ)) b / (64 * μ)) ^ D.exponent) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat, hmesh, hparent] using
    D.native_queries hδ i j k hlo hij hhi

end
end NativeDyadicTubeStopping
