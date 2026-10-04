import Theorems.Thm_StickyKakeya4_native_contact_spine_columns
import Theorems.Thm_StickyKakeya4_native_fractional_reference_composition

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace NativeContactFractionalComposition

open ShearedGridADReference ShearedGridTubeReference ShearedGridSpineColumns
open NativeContactSpineColumns NativeFractionalReferenceComposition
open SmallFiberAlignment FractionalFiberAlignment SelfUniform
open ActualTubeFootprintProfiles (TubeData InTube)
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening

noncomputable section

def contactColumnConstant (C : ℕ) (K H t ell : ℝ) : ℝ :=
  (((2 * contactOverlapBudget C + 1 : ℕ) : ℝ) * ((9 : ℝ) ^ 2 * (6 : ℝ) ^ t * K ^ 2) *
    (localCapacity C : ℝ) * H / ell)

/-- Native fractional refinement allowing genuine same-a-cell contacts after
whole-child angular selection. Only the anchor overlap changes; every fine
spine remains inside its original Cρ tube, and the rho-profile capacity uses
that exact fixed C rather than an artificial a/rho enlargement. -/
theorem exists_native_contact_fractional_refinement {d Q L : ℕ}
    (A E₀ E Ω : Finset Point) (δ μ α x₀ b ρ τ γ K H t s ell : ℝ)
    (S : Point → Finset Point) (T : Point → TubeData 1) (C N : ℕ) (R : Fin d → ℕ)
    (hQ : 4 ≤ Q) (hne : Ω.Nonempty) (hheight : Ω.card ≤ Q ^ L)
    (hδ : 0 < δ) (hμ : 0 < μ) (hδa : δ ≤ 64 * μ) (hab : 64 * μ ≤ b) (hb : b ≤ 1 / 64)
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
    (hH : 1 ≤ H) (hell : 0 < ell)
    (hprofile : (originalProfile E₀ ρ (64 * μ) : ℝ) ≤ H * ((64 * μ) / ρ) ^ s)
    (hwide : ∀ j, 64 * μ * (R j : ℝ) ≤ b →
      TraceBound E₀ (64 * μ * (R j : ℝ)) b (H * (b / (64 * μ * (R j : ℝ))) ^ s))
    (hshort : ∀ j, TraceBound E₀ (64 * μ) (min (64 * μ * (R j : ℝ)) b)
      (H * (min (64 * μ * (R j : ℝ)) b / (64 * μ)) ^ s))
    (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2) (hs : 0 ≤ s) (hst : s ≤ t)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) (hAD : ADBounds A δ K t)
    (hNscale : μ * (N : ℝ) = b) (hR : ∀ j, 0 < R j ∧ R j ≤ N) :
    ∃ U : ℕ, 0 < U ∧ (U : ℝ) ≤ 2 * K * ((64 * μ) / δ) ^ t ∧
      0 < density Ω U N t ∧
      (∀ z : Vertex, mass (fun _ : Point => 1) (Ω.filter (fun p => vertex μ α p = z)) ≤ U) ∧
      ∃ Ω' ⊆ Ω, Ω'.Nonempty ∧
        Ω.card ≤ retentionCost (d + (d + 1)) L * Ω'.card ∧
        RefinedCounts (Ω'.image (vertex μ α)) R N Q L t s (density Ω U N t)
          (adConstant K t) (contactColumnConstant C K H t ell) (tubeConstant H) := by
  classical
  have hbone : b ≤ 1 := le_trans hb (by norm_num)
  have haone : 64 * μ ≤ 1 := hab.trans hbone
  have hbpos : 0 < b := lt_of_lt_of_le (by positivity : 0 < 64 * μ) hab
  have hN : 0 < N := by
    by_contra hn
    have hz : N = 0 := by omega
    simp [hz] at hNscale
    linarith only [hbpos, hNscale]
  have hΩA : Ω ⊆ A := hΩ.trans hEA
  obtain ⟨U, hU, hUbound, hvertex⟩ := exists_integer_vertex_cap A Ω hΩA hδ hμ hδa haone hα hK ht hAD
  have hden : 0 < (U : ℝ) * (N : ℝ) ^ t := by positivity
  have hdens : 0 < density Ω U N t := div_pos (by exact_mod_cast hne.card_pos) hden
  have hmass : density Ω U N t * (U : ℝ) * (N : ℝ) ^ t = (mass (fun _ : Point => 1) Ω : ℝ) := by
    simp only [density, mass, Finset.sum_const, smul_eq_mul, mul_one]
    field_simp
  have had : 0 ≤ adConstant K t := by unfold adConstant referenceFactor; positivity
  have hcol : 0 ≤ contactColumnConstant C K H t ell := by unfold contactColumnConstant; positivity
  have htu : 0 ≤ tubeConstant H := by unfold tubeConstant; positivity
  have hspace (j : Fin d) : ((Ω.image (fun p => spatialCell (R j) (vertex μ α p))).card : ℝ) ≤
      adConstant K t * ((N : ℝ) / (R j : ℝ)) ^ t := by
    have hRb : μ * (R j : ℝ) ≤ b := by
      rw [← hNscale]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (hR j).2) hμ.le
    have hbound := spatial_menu_card_le A Ω hΩA hδ hμ hδa hb hα hK ht ht2 hdiam hAD
      (fun p hp q hq => hEdiam p (hΩ hp) q (hΩ hq)) (hR j).1 hRb
    have hratio : b / (μ * (R j : ℝ)) = (N : ℝ) / (R j : ℝ) := by rw [← hNscale]; field_simp
    simpa only [hratio, adConstant] using hbound
  have hcolumns := columns_card_le_from_AD_contact_spines A E₀ E Ω δ μ α x₀ b ρ τ γ K H t s ell S T C N
    hδ hμ hδa hab hbone hρ hρa hα hγ hangle hΩ hE hEA hparent hEdiam hS hrich hchart hslope
    hcontact htube (zero_lt_one.trans_le hH) hell hprofile hK ht ht2 hst hdiam hAD hNscale
  have hthree (j : Fin d) := three_profile_reference_bounds E₀ Ω μ α x₀ b H s N (R j)
    (hΩ.trans hE) hμ hα (hR j).1 (hR j).2 hNscale hH hs
    (fun p hp => hparent p (hΩ hp)) (hwide j) (hshort j)
  obtain ⟨Ω', hsub, hne', hret, hcounts⟩ := fractional_column_alignment hQ
    (fun _ : Point => 1) Ω (vertex μ α) R U N t s (density Ω U N t)
    (adConstant K t) (contactColumnConstant C K H t ell) (tubeConstant H)
    (adConstant K t) (tubeConstant H) (tubeConstant H)
    hne (fun _ _ => Nat.zero_lt_one) (by simpa [mass] using hheight) hR hU hN hdens
    had hcol htu had htu htu hvertex (le_of_eq hmass) hspace hcolumns
    (fun j => (hthree j).1)
    (fun j c => spatial_cell_card_le A Ω hΩA hδ hμ hδa haone hα hK ht ht2 hdiam hAD (hR j).1 c)
    (fun j => (hthree j).2.1) (fun j => (hthree j).2.2)
  refine ⟨U, hU, hUbound, hdens, hvertex, Ω', hsub, hne', ?_, ?_⟩
  · simpa [mass] using hret
  · simpa only [RefinedCounts, show (3 : ℝ) ^ (1 + 1) = 9 by norm_num] using hcounts


end
end NativeContactFractionalComposition
