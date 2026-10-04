import Theorems.Thm_StickyKakeya4_sheared_grid_spine_columns

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace NativeContactSpineColumns

open ShearedGridADReference ShearedGridSpineColumns ShearedGridTubeReference SmallFiberAlignment
open ActualTubeFootprintProfiles (TubeData InTube)
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening

noncomputable section

/-- Sharing an ORIGINAL a-cell changes a bounded-slope graph residual by at
most 2a. This is an anchor comparison; it does not thicken the fine spine. -/
lemma same_cell_graph_residual {a θ : ℝ} (ha : 0 < a) (hθ : |θ| ≤ 1)
    {z q : Point} (hcell : ADGridCoverMenus.gridLabel a z = ADGridCoverMenus.gridLabel a q) :
    |z 1 - q 1 - θ * (z 0 - q 0)| ≤ 2 * a := by
  have hp : SpineColumnCounting.cell a (pairPoint z) = SpineColumnCounting.cell a (pairPoint q) :=
    congrArg pairLabel hcell
  have hs := SpineColumnCounting.same_cell_shear_close (fun _ : Fin 1 => θ) ha (fun _ => hθ) hp 0
  change |(z 1 - θ * z 0) - (q 1 - θ * q 0)| ≤ (1 + 1) * a at hs
  have hid : z 1 - q 1 - θ * (z 0 - q 0) = (z 1 - θ * z 0) - (q 1 - θ * q 0) := by ring
  rw [hid]
  linarith only [hs]

/-- The contact z stays in the genuine Cρ tube and shares q's a-cell. Only
the comparison to q uses 4Cρ+2a; all local grid capacity retains width Cρ. -/
lemma tube_contact_residual (T : TubeData 1) (hchart : |T.direction 0| = 1)
    {a ρ τ : ℝ} (ha : 0 < a) {p z q : Point}
    (hp : InTube T ρ τ p) (hz : InTube T ρ τ z)
    (hcell : ADGridCoverMenus.gridLabel a z = ADGridCoverMenus.gridLabel a q) :
    |p 1 - q 1 - slope T * (p 0 - q 0)| ≤ 4 * ρ + 2 * a := by
  have hpz := tube_pair_residual T hchart hp hz
  have hzq := same_cell_graph_residual ha (slope_bound T hchart) hcell
  have hid : p 1 - q 1 - slope T * (p 0 - q 0) =
      (p 1 - z 1 - slope T * (p 0 - z 0)) + (z 1 - q 1 - slope T * (z 0 - q 0)) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hpz hzq)

def contactOverlapBudget (C : ℕ) : ℕ := 512 * C + 516

lemma contact_overlap_budget (C : ℕ) {μ ρ γ b : ℝ} (hμ : 0 < μ)
    (hρa : ρ ≤ 64 * μ) (hangle : γ * b ≤ 64 * μ) :
    2 * (4 * (C : ℝ) * ρ + 2 * (64 * μ) + γ * b + 2 * μ) + (1 + 1) * (64 * μ) ≤
      μ * (contactOverlapBudget C : ℝ) := by
  have h := overlap_budget C hμ hρa hangle
  simp only [overlapBudget, contactOverlapBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h ⊢
  linarith only [h]

/-- Actual column anchors are selected from the quantizer image. Their spine
contact may be another original point in the same a-cell. -/
theorem columns_from_coarse_contact_spines (E Ω : Finset Point) (μ α x₀ b ρ τ γ L : ℝ)
    (S : Point → Finset Point) (T : Point → TubeData 1) (C : ℕ)
    (hμ : 0 < μ) (_hρ : 0 ≤ ρ) (hρa : ρ ≤ 64 * μ) (hα : |α| ≤ 1)
    (hγ : 0 ≤ γ) (hangle : γ * b ≤ 64 * μ) (hΩ : Ω ⊆ E)
    (hparent : ∀ p ∈ E, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b)
    (hS : ∀ q ∈ Ω, S q ⊆ E)
    (hlarge : ∀ q ∈ Ω, L ≤ (((S q).image (ADGridCoverMenus.gridLabel (64 * μ))).card : ℝ))
    (hchart : ∀ q ∈ Ω, |(T q).direction 0| = 1)
    (hslope : ∀ q ∈ Ω, |slope (T q) - α| ≤ γ)
    (hcontact : ∀ q ∈ Ω, ∃ z ∈ E,
      ADGridCoverMenus.gridLabel (64 * μ) z = ADGridCoverMenus.gridLabel (64 * μ) q ∧
      InTube (T q) ((C : ℝ) * ρ) τ z)
    (htube : ∀ q ∈ Ω, ∀ p ∈ S q, InTube (T q) ((C : ℝ) * ρ) τ p) :
    L * ((columns Ω μ α).card : ℝ) ≤
      (2 * contactOverlapBudget C + 1 : ℕ) * ((E.image (ADGridCoverMenus.gridLabel (64 * μ))).card : ℝ) := by
  classical
  let anch := anchor Ω μ α
  have ha (y : Normal 1) (hy : y ∈ columns Ω μ α) : anch y ∈ Ω ∧ (vertex μ α (anch y)).2 = y :=
    anchor_spec Ω μ α hy
  have hcount := SpineColumnCounting.physical_spines_column_count
    (fun _ : Fin 1 => α) (columns Ω μ α) (E.image pairPoint)
    (fun y => (S (anch y)).image pairPoint) (fun y => pairPoint (anch y))
    (fun y _ => slope (T (anch y))) (contactOverlapBudget C)
    (a := 64 * μ) (h := μ) (r := 4 * (C : ℝ) * ρ + 2 * (64 * μ)) (gamma := γ) (b := b)
    (A := 1) (seed := 2 * μ) (L := L) (by positivity) hμ hγ (fun _ => hα)
    (fun y hy => Finset.image_subset_image (hS _ (ha y hy).1))
    (fun y hy => by rw [pair_cell_image_card]; exact hlarge _ (ha y hy).1)
    (by
      intro y hy p hp i
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
      change |z 1 - anch y 1 - slope (T (anch y)) * (z 0 - anch y 0)| ≤ _
      obtain ⟨u, _huE, hcell, huT⟩ := hcontact _ (ha y hy).1
      simpa only [mul_assoc] using tube_contact_residual (T (anch y)) (hchart _ (ha y hy).1)
        (by positivity : 0 < 64 * μ) (htube _ (ha y hy).1 z hz) huT hcell)
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
    (contact_overlap_budget C hμ hρa hangle)
  simpa only [pow_one, pair_cell_image_card] using hcount


theorem columns_from_fine_contact_spines (E₀ E Ω : Finset Point) (μ α x₀ b ρ τ γ H s L : ℝ)
    (S : Point → Finset Point) (T : Point → TubeData 1) (C : ℕ)
    (hμ : 0 < μ) (hρ : 0 < ρ) (hρa : ρ ≤ 64 * μ) (hα : |α| ≤ 1)
    (hγ : 0 ≤ γ) (hangle : γ * b ≤ 64 * μ) (hΩ : Ω ⊆ E) (hE : E ⊆ E₀)
    (hparent : ∀ p ∈ E, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b)
    (hS : ∀ q ∈ Ω, S q ⊆ E)
    (hrich : ∀ q ∈ Ω, L ≤ (((S q).image (ADGridCoverMenus.gridLabel ρ)).card : ℝ))
    (hchart : ∀ q ∈ Ω, |(T q).direction 0| = 1)
    (hslope : ∀ q ∈ Ω, |slope (T q) - α| ≤ γ)
    (hcontact : ∀ q ∈ Ω, ∃ z ∈ E,
      ADGridCoverMenus.gridLabel (64 * μ) z = ADGridCoverMenus.gridLabel (64 * μ) q ∧
      InTube (T q) ((C : ℝ) * ρ) τ z)
    (htube : ∀ q ∈ Ω, ∀ p ∈ S q, InTube (T q) ((C : ℝ) * ρ) τ p)
    (hH : 0 < H) (hprofile : (originalProfile E₀ ρ (64 * μ) : ℝ) ≤ H * ((64 * μ) / ρ) ^ s) :
    L / ((localCapacity C : ℝ) * H * ((64 * μ) / ρ) ^ s) * ((columns Ω μ α).card : ℝ) ≤
      (2 * contactOverlapBudget C + 1 : ℕ) * ((E.image (ADGridCoverMenus.gridLabel (64 * μ))).card : ℝ) := by
  apply columns_from_coarse_contact_spines E Ω μ α x₀ b ρ τ γ _ S T C hμ hρ.le hρa hα hγ hangle hΩ hparent hS
  · intro q hq
    exact coarse_spine_richness E₀ (S q) (T q) C hρ hρa ((hS q hq).trans hE)
      (htube q hq) hH hprofile (hrich q hq)
  · exact hchart
  · exact hslope
  · exact hcontact
  · exact htube


theorem columns_card_le_from_AD_contact_spines
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
    (hcontact : ∀ q ∈ Ω, ∃ z ∈ E,
      ADGridCoverMenus.gridLabel (64 * μ) z = ADGridCoverMenus.gridLabel (64 * μ) q ∧
      InTube (T q) ((C : ℝ) * ρ) τ z)
    (htube : ∀ q ∈ Ω, ∀ p ∈ S q, InTube (T q) ((C : ℝ) * ρ) τ p)
    (hH : 0 < H) (hell : 0 < ell)
    (hprofile : (originalProfile E₀ ρ (64 * μ) : ℝ) ≤ H * ((64 * μ) / ρ) ^ s)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2) (hst : s ≤ t)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) (hAD : ADBounds A δ K t)
    (hNscale : μ * (N : ℝ) = b) :
    ((Ω.image (fun p => (vertex μ α p).2)).card : ℝ) ≤
      (((2 * contactOverlapBudget C + 1 : ℕ) : ℝ) * ((9 : ℝ) ^ 2 * (6 : ℝ) ^ t * K ^ 2) *
        (localCapacity C : ℝ) * H / ell) * (N : ℝ) ^ (t - s) := by
  have ha : 0 < 64 * μ := by positivity
  have hb : 0 < b := ha.trans_le hab
  have hcap : 0 < (localCapacity C : ℝ) * H := by
    exact mul_pos (by exact_mod_cast localCapacity_pos C) hH
  have hcount := columns_from_fine_contact_spines E₀ E Ω μ α x₀ b ρ τ γ H s
    (ell * (b / ρ) ^ s) S T C hμ hρ hρa hα hγ hangle hΩ hE hparent hS hrich
    hchart hslope hcontact htube hH hprofile
  rw [richness_div_capacity hρ ha hb hH (by exact_mod_cast localCapacity_pos C)] at hcount
  have hgrid := ADGridCoverMenus.diameter_subset_occupied_grid_cells_le A E hδ hδa
    (hab.trans hbone) hab hK ht ht2 hdiam hAD hEA hEdiam
  have hboth : (ell / ((localCapacity C : ℝ) * H)) * (b / (64 * μ)) ^ s *
      ((columns Ω μ α).card : ℝ) ≤
      (((2 * contactOverlapBudget C + 1 : ℕ) : ℝ) * ((9 : ℝ) ^ 2 * (6 : ℝ) ^ t * K ^ 2)) *
        (b / (64 * μ)) ^ t := by
    calc
      _ ≤ _ := hcount
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left hgrid
          (show (0 : ℝ) ≤ (2 * contactOverlapBudget C + 1 : ℕ) by positivity)
        simpa only [mul_assoc] using hm
  have hp := column_power_of_weighted (by positivity : 0 < b / (64 * μ)) hell hcap hboth
  have hnratio : b / (64 * μ) ≤ (N : ℝ) := by
    apply (div_le_iff₀ ha).mpr
    rw [← hNscale]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith only [mul_nonneg hμ.le hN]
  have hpower := Real.rpow_le_rpow (by positivity : 0 ≤ b / (64 * μ)) hnratio (sub_nonneg.mpr hst)
  have hfactor : 0 ≤ (((2 * contactOverlapBudget C + 1 : ℕ) : ℝ) *
      ((9 : ℝ) ^ 2 * (6 : ℝ) ^ t * K ^ 2)) * ((localCapacity C : ℝ) * H) / ell := by positivity
  have hlast := mul_le_mul_of_nonneg_left hpower hfactor
  change ((columns Ω μ α).card : ℝ) ≤ _
  exact hp.trans (by simpa only [mul_assoc] using hlast)


end
end NativeContactSpineColumns
