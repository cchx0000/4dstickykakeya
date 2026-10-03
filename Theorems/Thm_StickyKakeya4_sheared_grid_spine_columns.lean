import Theorems.Thm_StickyKakeya4_sheared_grid_tube_reference
import Theorems.Thm_StickyKakeya4_tube_expansion_cover
import Theorems.Thm_StickyKakeya4_spine_column_counting

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace ShearedGridSpineColumns

open ShearedGridADReference SmallFiberAlignment ShearedGridTubeReference
open ActualTubeFootprintProfiles (TubeData InTube)
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening

noncomputable section

attribute [local instance] Classical.propDecidable

def pairPoint (p : Point) : SpineColumnCounting.Point 1 := (p 0, fun _ => p 1)
def pairLabel (c : Fin 2 → ℤ) : SpineColumnCounting.Cell 1 := (c 0, fun _ => c 1)

lemma pairLabel_injective : Function.Injective pairLabel := by
  intro c d h
  have h0 := congrArg Prod.fst h
  have h1 := congrFun (congrArg Prod.snd h) 0
  funext i
  fin_cases i
  · exact h0
  · exact h1

lemma pair_cell_image_card (S : Finset Point) (a : ℝ) :
    ((S.image pairPoint).image (SpineColumnCounting.cell a)).card =
      (S.image (ADGridCoverMenus.gridLabel a)).card := by
  classical
  have heq : (S.image pairPoint).image (SpineColumnCounting.cell a) =
      (S.image (ADGridCoverMenus.gridLabel a)).image pairLabel := by
    rw [Finset.image_image, Finset.image_image]
    rfl
  rw [heq, Finset.card_image_of_injective _ pairLabel_injective]

def columns (Ω : Finset Point) (μ α : ℝ) : Finset (Normal 1) :=
  Ω.image (fun p => (vertex μ α p).2)

def anchor (Ω : Finset Point) (μ α : ℝ) (y : Normal 1) : Point :=
  if hy : y ∈ columns Ω μ α then Classical.choose (Finset.mem_image.mp hy) else 0

lemma anchor_spec (Ω : Finset Point) (μ α : ℝ) {y : Normal 1}
    (hy : y ∈ columns Ω μ α) :
    anchor Ω μ α y ∈ Ω ∧ (vertex μ α (anchor Ω μ α y)).2 = y := by
  classical
  simp only [anchor, dif_pos hy]
  exact Classical.choose_spec (Finset.mem_image.mp hy)

def slope (T : TubeData 1) : ℝ := T.direction 1 / T.direction 0

lemma slope_bound (T : TubeData 1) (hchart : |T.direction 0| = 1) : |slope T| ≤ 1 := by
  simp only [slope, abs_div, hchart, div_one]
  exact T.unit.1 1

lemma slope_mul (T : TubeData 1) (hchart : |T.direction 0| = 1) :
    slope T * T.direction 0 = T.direction 1 := by
  have hv : T.direction 0 ≠ 0 := by intro hz; simp [hz] at hchart
  exact div_mul_cancel₀ _ hv

/-- A genuine unit-coordinate tube supplies the graph residual between any
spine point and its actual original anchor. -/
lemma tube_pair_residual (T : TubeData 1) (hchart : |T.direction 0| = 1)
    {ρ τ : ℝ} {p q : Point}
    (hp : InTube T ρ τ p) (hq : InTube T ρ τ q) :
    |p 1 - q 1 - slope T * (p 0 - q 0)| ≤ 4 * ρ := by
  obtain ⟨u, _hu, hp⟩ := hp
  obtain ⟨v, _hv, hq⟩ := hq
  have hs := slope_bound T hchart
  have hmul := slope_mul T hchart
  have h0 : |(p 0 - T.center 0 - u * T.direction 0) -
      (q 0 - T.center 0 - v * T.direction 0)| ≤ 2 * ρ := by
    exact (abs_sub _ _).trans (by linarith [hp 0, hq 0])
  have h1 : |(p 1 - T.center 1 - u * T.direction 1) -
      (q 1 - T.center 1 - v * T.direction 1)| ≤ 2 * ρ := by
    exact (abs_sub _ _).trans (by linarith [hp 1, hq 1])
  have hprod : |slope T * ((p 0 - T.center 0 - u * T.direction 0) -
      (q 0 - T.center 0 - v * T.direction 0))| ≤ 2 * ρ := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hs h0 (abs_nonneg _) zero_le_one
  have hid : p 1 - q 1 - slope T * (p 0 - q 0) =
      ((p 1 - T.center 1 - u * T.direction 1) - (q 1 - T.center 1 - v * T.direction 1)) -
      slope T * ((p 0 - T.center 0 - u * T.direction 0) - (q 0 - T.center 0 - v * T.direction 0)) := by
    rw [← hmul]
    ring
  rw [hid]
  exact (abs_sub _ _).trans (by linarith)

def overlapBudget (C : ℕ) : ℕ := 512 * C + 260

lemma overlap_budget (C : ℕ) {μ ρ γ b : ℝ} (_hμ : 0 < μ) (hρa : ρ ≤ 64 * μ)
    (hangle : γ * b ≤ 64 * μ) :
    2 * (4 * (C : ℝ) * ρ + γ * b + 2 * μ) + (1 + 1) * (64 * μ) ≤
      μ * (overlapBudget C : ℝ) := by
  have hscaled := mul_le_mul_of_nonneg_left hρa (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  simp only [overlapBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith only [hscaled, hangle]

/-- Original rich spines and genuine tube geometry derive a column bound.
Anchor existence, anchor shear error, parent time control, and overlap are
all constructed here for the literal two-stage quantizer. -/
theorem columns_from_coarse_spines (E Ω : Finset Point) (μ α x₀ b ρ τ γ L : ℝ)
    (S : Point → Finset Point) (T : Point → TubeData 1) (C : ℕ)
    (hμ : 0 < μ) (_hρ : 0 ≤ ρ) (hρa : ρ ≤ 64 * μ) (hα : |α| ≤ 1)
    (hγ : 0 ≤ γ) (hangle : γ * b ≤ 64 * μ) (hΩ : Ω ⊆ E)
    (hparent : ∀ p ∈ E, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b)
    (hS : ∀ q ∈ Ω, S q ⊆ E)
    (hlarge : ∀ q ∈ Ω, L ≤ (((S q).image (ADGridCoverMenus.gridLabel (64 * μ))).card : ℝ))
    (hchart : ∀ q ∈ Ω, |(T q).direction 0| = 1)
    (hslope : ∀ q ∈ Ω, |slope (T q) - α| ≤ γ)
    (hanchor : ∀ q ∈ Ω, InTube (T q) ((C : ℝ) * ρ) τ q)
    (htube : ∀ q ∈ Ω, ∀ p ∈ S q, InTube (T q) ((C : ℝ) * ρ) τ p) :
    L * ((columns Ω μ α).card : ℝ) ≤
      (2 * overlapBudget C + 1 : ℕ) * ((E.image (ADGridCoverMenus.gridLabel (64 * μ))).card : ℝ) := by
  classical
  let anch := anchor Ω μ α
  have ha (y : Normal 1) (hy : y ∈ columns Ω μ α) : anch y ∈ Ω ∧ (vertex μ α (anch y)).2 = y :=
    anchor_spec Ω μ α hy
  have hcount := SpineColumnCounting.physical_spines_column_count
    (fun _ : Fin 1 => α) (columns Ω μ α) (E.image pairPoint)
    (fun y => (S (anch y)).image pairPoint) (fun y => pairPoint (anch y))
    (fun y _ => slope (T (anch y))) (overlapBudget C)
    (a := 64 * μ) (h := μ) (r := 4 * (C : ℝ) * ρ) (gamma := γ) (b := b)
    (A := 1) (seed := 2 * μ) (L := L) (by positivity) hμ hγ (fun _ => hα)
    (fun y hy => Finset.image_subset_image (hS _ (ha y hy).1))
    (fun y hy => by rw [pair_cell_image_card]; exact hlarge _ (ha y hy).1)
    (by
      intro y hy p hp i
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
      change |z 1 - anch y 1 - slope (T (anch y)) * (z 0 - anch y 0)| ≤ _
      simpa only [mul_assoc] using tube_pair_residual (T (anch y)) (hchart _ (ha y hy).1)
        (htube _ (ha y hy).1 z hz) (hanchor _ (ha y hy).1))
    (fun y hy _ => hslope _ (ha y hy).1)
    (by
      intro y hy p hp
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
      have hpbox := hparent z (hS _ (ha y hy).1 hz)
      have hqbox := hparent (anch y) (hΩ (ha y hy).1)
      change |z 0 - anch y 0| ≤ b
      exact abs_le.mpr ⟨by linarith [hpbox.1, hqbox.2], by linarith [hpbox.2, hqbox.1]⟩)
    (by
      intro y hy i
      have he := normal_error μ α hμ hα (anch y)
      rw [(ha y hy).2] at he
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact he)
    (overlap_budget C hμ hρa hangle)
  simpa only [pow_one, pair_cell_image_card] using hcount


/-- Lift an actual subset only to use the finite original source universe;
projection recovers every original point and every original floor label. -/
def lift (E S : Finset Point) : Finset E := Finset.univ.filter (fun p => p.val ∈ S)

lemma lift_image (E S : Finset Point) (hS : S ⊆ E) {β : Type*} [DecidableEq β]
    (f : Point → β) : (lift E S).image (fun p => f p.val) = S.image f := by
  classical
  ext c
  simp only [lift, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.val, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hS hp⟩, hp, rfl⟩

def originalProfile (E : Finset Point) (ρ a : ℝ) : ℕ :=
  ActualTubeFootprintProfiles.coverProfile (fun p : E => (p : Point)) ρ a Finset.univ

def localCapacity (C : ℕ) : ℕ := (2 * C + 1) ^ 2 * (2 * (2 + 4 * C) + 1)

lemma localCapacity_pos (C : ℕ) : 0 < localCapacity C := by
  unfold localCapacity
  positivity

/-- Genuine tube localization gives the fine-grid capacity of an actual
coarse original cell, from the SAME original source's (ρ,a) profile. -/
lemma local_fine_grid_card (E S : Finset Point) (T : TubeData 1) (C : ℕ)
    {ρ a τ : ℝ} (hρ : 0 < ρ) (hscale : ρ ≤ a) (hSE : S ⊆ E)
    (htube : ∀ p ∈ S, InTube T ((C : ℝ) * ρ) τ p)
    (c : Fin 2 → ℤ) (hcell : ∀ p ∈ S, ADGridCoverMenus.gridLabel a p = c) :
    (S.image (ADGridCoverMenus.gridLabel ρ)).card ≤ localCapacity C * originalProfile E ρ a := by
  classical
  let pos : E → Point := fun p => p.val
  have hlocal := TubeExpansionCover.local_cell_image_le_actual_profile pos
    Finset.univ (lift E S) T C hρ hscale (Finset.subset_univ _)
    (by
      intro p hp
      exact htube p.val (Finset.mem_filter.mp hp).2)
    c (by
      intro p hp
      exact hcell p.val (Finset.mem_filter.mp hp).2)
  have himage : (lift E S).image (ActualTubeFootprintProfiles.grid pos ρ) =
      S.image (ADGridCoverMenus.gridLabel ρ) := lift_image E S hSE (ADGridCoverMenus.gridLabel ρ)
  rw [himage] at hlocal
  exact hlocal

lemma fine_grid_card_le_coarse (E S : Finset Point) (T : TubeData 1) (C : ℕ)
    {ρ a τ : ℝ} (hρ : 0 < ρ) (hscale : ρ ≤ a) (hSE : S ⊆ E)
    (htube : ∀ p ∈ S, InTube T ((C : ℝ) * ρ) τ p) :
    (S.image (ADGridCoverMenus.gridLabel ρ)).card ≤
      (S.image (ADGridCoverMenus.gridLabel a)).card * (localCapacity C * originalProfile E ρ a) := by
  classical
  apply image_card_le_reference_mul
  intro c
  apply local_fine_grid_card E _ T C hρ hscale
    (fun p hp => hSE (Finset.mem_filter.mp hp).1)
    (fun p hp => htube p (Finset.mem_filter.mp hp).1) c
  intro p hp
  exact (Finset.mem_filter.mp hp).2

/-- Coarse richness is derived by dividing actual fine occupied cells by
actual localized tube capacity. It is not an additional spine certificate. -/
lemma coarse_spine_richness (E S : Finset Point) (T : TubeData 1) (C : ℕ)
    {ρ a τ H s L : ℝ} (hρ : 0 < ρ) (hscale : ρ ≤ a) (hSE : S ⊆ E)
    (htube : ∀ p ∈ S, InTube T ((C : ℝ) * ρ) τ p)
    (hH : 0 < H) (hprofile : (originalProfile E ρ a : ℝ) ≤ H * (a / ρ) ^ s)
    (hrich : L ≤ ((S.image (ADGridCoverMenus.gridLabel ρ)).card : ℝ)) :
    L / ((localCapacity C : ℝ) * H * (a / ρ) ^ s) ≤
      ((S.image (ADGridCoverMenus.gridLabel a)).card : ℝ) := by
  have ha : 0 < a := hρ.trans_le hscale
  have hC : (0 : ℝ) < localCapacity C := by exact_mod_cast localCapacity_pos C
  have hD : 0 < (localCapacity C : ℝ) * H * (a / ρ) ^ s := by positivity
  apply (div_le_iff₀ hD).mpr
  have hcount : ((S.image (ADGridCoverMenus.gridLabel ρ)).card : ℝ) ≤
      ((S.image (ADGridCoverMenus.gridLabel a)).card : ℝ) *
        ((localCapacity C : ℝ) * (originalProfile E ρ a : ℝ)) := by
    exact_mod_cast fine_grid_card_le_coarse E S T C hρ hscale hSE htube
  have hnonneg : (0 : ℝ) ≤ (S.image (ADGridCoverMenus.gridLabel a)).card := Nat.cast_nonneg _
  calc
    L ≤ ((S.image (ADGridCoverMenus.gridLabel ρ)).card : ℝ) := hrich
    _ ≤ _ := hcount
    _ ≤ _ := by
      have hcap := mul_le_mul_of_nonneg_left hprofile hC.le
      have hprod := mul_le_mul_of_nonneg_left hcap hnonneg
      simpa only [mul_assoc] using hprod

/-- Column counting with its coarse-spine richness derived from actual fine
spines and one localized query of the original source's genuine profile. -/
theorem columns_from_fine_spines (E₀ E Ω : Finset Point) (μ α x₀ b ρ τ γ H s L : ℝ)
    (S : Point → Finset Point) (T : Point → TubeData 1) (C : ℕ)
    (hμ : 0 < μ) (hρ : 0 < ρ) (hρa : ρ ≤ 64 * μ) (hα : |α| ≤ 1)
    (hγ : 0 ≤ γ) (hangle : γ * b ≤ 64 * μ) (hΩ : Ω ⊆ E) (hE : E ⊆ E₀)
    (hparent : ∀ p ∈ E, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b)
    (hS : ∀ q ∈ Ω, S q ⊆ E)
    (hrich : ∀ q ∈ Ω, L ≤ (((S q).image (ADGridCoverMenus.gridLabel ρ)).card : ℝ))
    (hchart : ∀ q ∈ Ω, |(T q).direction 0| = 1)
    (hslope : ∀ q ∈ Ω, |slope (T q) - α| ≤ γ)
    (hanchor : ∀ q ∈ Ω, InTube (T q) ((C : ℝ) * ρ) τ q)
    (htube : ∀ q ∈ Ω, ∀ p ∈ S q, InTube (T q) ((C : ℝ) * ρ) τ p)
    (hH : 0 < H) (hprofile : (originalProfile E₀ ρ (64 * μ) : ℝ) ≤ H * ((64 * μ) / ρ) ^ s) :
    L / ((localCapacity C : ℝ) * H * ((64 * μ) / ρ) ^ s) * ((columns Ω μ α).card : ℝ) ≤
      (2 * overlapBudget C + 1 : ℕ) * ((E.image (ADGridCoverMenus.gridLabel (64 * μ))).card : ℝ) := by
  apply columns_from_coarse_spines E Ω μ α x₀ b ρ τ γ _ S T C hμ hρ.le hρa hα hγ hangle hΩ hparent hS
  · intro q hq
    exact coarse_spine_richness E₀ (S q) (T q) C hρ hρa ((hS q hq).trans hE)
      (htube q hq) hH hprofile (hrich q hq)
  · exact hchart
  · exact hslope
  · exact hanchor
  · exact htube


lemma richness_div_capacity {ρ a b H ell D s : ℝ} (hρ : 0 < ρ) (ha : 0 < a)
    (hb : 0 < b) (hH : 0 < H) (hD : 0 < D) :
    (ell * (b / ρ) ^ s) / (D * H * (a / ρ) ^ s) =
      (ell / (D * H)) * (b / a) ^ s := by
  have hratio : b / ρ = (b / a) * (a / ρ) := by field_simp
  rw [hratio, Real.mul_rpow (by positivity : 0 ≤ b / a) (by positivity : 0 ≤ a / ρ)]
  have hpow : (a / ρ) ^ s ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  field_simp

lemma column_power_of_weighted {n ell cap A Z s t : ℝ}
    (hn : 0 < n) (hell : 0 < ell) (hcap : 0 < cap)
    (h : (ell / cap) * n ^ s * Z ≤ A * n ^ t) :
    Z ≤ (A * cap / ell) * n ^ (t - s) := by
  have hweight : 0 < (ell / cap) * n ^ s := mul_pos (div_pos hell hcap) (Real.rpow_pos_of_pos hn _)
  have hz : Z ≤ (A * n ^ t) / ((ell / cap) * n ^ s) :=
    (le_div_iff₀ hweight).mpr (by simpa only [mul_comm Z] using h)
  convert hz using 1
  rw [Real.rpow_sub hn]
  field_simp

/-- The actual AD carrier supplies the numerator menu; fine original spines,
genuine selected tubes and the common stopped profile supply the denominator.
This derives hcolumns with public raw-grid N=b/μ and no count certificate. -/
theorem columns_card_le_from_AD_fine_spines
    (A E₀ E Ω : Finset Point) (δ μ α x₀ b ρ τ γ K H t s ell : ℝ)
    (S : Point → Finset Point) (T : Point → TubeData 1) (C N : ℕ)
    (hδ : 0 < δ) (hμ : 0 < μ) (hδa : δ ≤ 64 * μ) (hab : 64 * μ ≤ b) (hbone : b ≤ 1)
    (hρ : 0 < ρ) (hρa : ρ ≤ 64 * μ) (hα : |α| ≤ 1)
    (hγ : 0 ≤ γ) (hangle : γ * b ≤ 64 * μ) (hΩ : Ω ⊆ E) (hE : E ⊆ E₀) (hEA : E ⊆ A)
    (hparent : ∀ p ∈ E, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b)
    (hEdiam : ∀ p ∈ E, ∀ q ∈ E, dist p q ≤ b)
    (hS : ∀ q ∈ Ω, S q ⊆ E)
    (hrich : ∀ q ∈ Ω, ell * (b / ρ) ^ s ≤ (((S q).image (ADGridCoverMenus.gridLabel ρ)).card : ℝ))
    (hchart : ∀ q ∈ Ω, |(T q).direction 0| = 1)
    (hslope : ∀ q ∈ Ω, |slope (T q) - α| ≤ γ)
    (hanchor : ∀ q ∈ Ω, InTube (T q) ((C : ℝ) * ρ) τ q)
    (htube : ∀ q ∈ Ω, ∀ p ∈ S q, InTube (T q) ((C : ℝ) * ρ) τ p)
    (hH : 0 < H) (hell : 0 < ell)
    (hprofile : (originalProfile E₀ ρ (64 * μ) : ℝ) ≤ H * ((64 * μ) / ρ) ^ s)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2) (hst : s ≤ t)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) (hAD : ADBounds A δ K t)
    (hNscale : μ * (N : ℝ) = b) :
    ((Ω.image (fun p => (vertex μ α p).2)).card : ℝ) ≤
      (((2 * overlapBudget C + 1 : ℕ) : ℝ) * ((9 : ℝ) ^ 2 * (6 : ℝ) ^ t * K ^ 2) *
        (localCapacity C : ℝ) * H / ell) * (N : ℝ) ^ (t - s) := by
  have ha : 0 < 64 * μ := by positivity
  have hb : 0 < b := ha.trans_le hab
  have hcap : 0 < (localCapacity C : ℝ) * H := by
    exact mul_pos (by exact_mod_cast localCapacity_pos C) hH
  have hcount := columns_from_fine_spines E₀ E Ω μ α x₀ b ρ τ γ H s
    (ell * (b / ρ) ^ s) S T C hμ hρ hρa hα hγ hangle hΩ hE hparent hS hrich
    hchart hslope hanchor htube hH hprofile
  rw [richness_div_capacity hρ ha hb hH (by exact_mod_cast localCapacity_pos C)] at hcount
  have hgrid := ADGridCoverMenus.diameter_subset_occupied_grid_cells_le A E hδ hδa
    (hab.trans hbone) hab hK ht ht2 hdiam hAD hEA hEdiam
  have hboth : (ell / ((localCapacity C : ℝ) * H)) * (b / (64 * μ)) ^ s *
      ((columns Ω μ α).card : ℝ) ≤
      (((2 * overlapBudget C + 1 : ℕ) : ℝ) * ((9 : ℝ) ^ 2 * (6 : ℝ) ^ t * K ^ 2)) *
        (b / (64 * μ)) ^ t := by
    calc
      _ ≤ _ := hcount
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left hgrid
          (show (0 : ℝ) ≤ (2 * overlapBudget C + 1 : ℕ) by positivity)
        simpa only [mul_assoc] using hm
  have hp := column_power_of_weighted (by positivity : 0 < b / (64 * μ)) hell hcap hboth
  have hnratio : b / (64 * μ) ≤ (N : ℝ) := by
    apply (div_le_iff₀ ha).mpr
    rw [← hNscale]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith only [mul_nonneg hμ.le hN]
  have hpower := Real.rpow_le_rpow (by positivity : 0 ≤ b / (64 * μ)) hnratio (sub_nonneg.mpr hst)
  have hfactor : 0 ≤ (((2 * overlapBudget C + 1 : ℕ) : ℝ) *
      ((9 : ℝ) ^ 2 * (6 : ℝ) ^ t * K ^ 2)) * ((localCapacity C : ℝ) * H) / ell := by positivity
  have hlast := mul_le_mul_of_nonneg_left hpower hfactor
  change ((columns Ω μ α).card : ℝ) ≤ _
  exact hp.trans (by simpa only [mul_assoc] using hlast)

end
end ShearedGridSpineColumns
