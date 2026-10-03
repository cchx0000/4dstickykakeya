import Theorems.Thm_StickyKakeya4_physical_rescaling_incidence_transfer

set_option autoImplicit false
set_option warningAsError true

/-!
# Density on the complete original tube backbone

The backbone `B` may contain tubes with no original incidences at all. Its
cardinality is never replaced by the projection of either the original or
retained incidence set. The genuine initial total-density condition on `B`
supplies the existing physical rescaling density hypothesis by inclusion.
-/

noncomputable section
open Classical IncidenceBinTransfer

namespace PhysicalRescalingIncidenceTransfer.Data

variable {T : Type*} (P : PhysicalRescalingIncidenceTransfer.Data T)

/-- Full original-backbone density implies the used-tube density required by the
existing geometric rescaling construction. All physical assumptions are unchanged. -/
theorem hypotheses_of_full_backbone_density
    (B : Finset T) (hused : usedTubes P.incidences ⊆ B)
    (hδ : 0 < P.δ) (hN : 0 < P.N) (hσ : P.σ ≤ 1)
    (hlam : 0 < P.lam) (hlamOne : P.lam ≤ 1)
    (hslope : ∀ t ∈ usedTubes P.incidences, ∀ j, |P.slope t j| ≤ 1)
    (htime : ∀ p ∈ P.incidences, |(P.center p.2).2| ≤ 1)
    (hphysical : ∀ p ∈ P.incidences, ∀ j,
      |P.residual p.1 p.2 j| ≤ (P.E : ℝ) * P.σ)
    (hdensity : P.lam * B.card ≤ P.δ * P.incidences.card) : P.Hypotheses := by
  refine ⟨hδ, hN, hσ, hlam, hlamOne, hslope, htime, hphysical, ?_⟩
  have hcard : ((usedTubes P.incidences).card : ℝ) ≤ B.card := by
    exact_mod_cast Finset.card_le_card hused
  exact (mul_le_mul_of_nonneg_left hcard hlam.le).trans hdensity

/-- Both endpoint densities retain the cardinality of the COMPLETE original
backbone, including rows whose shading was already empty before selection. -/
theorem endpoint_densities_full_backbone
    (B : Finset T) (hused : usedTubes P.incidences ⊆ B)
    (hδ : 0 < P.δ) (hN : 0 < P.N) (hσ : P.σ ≤ 1)
    (hlam : 0 < P.lam) (hlamOne : P.lam ≤ 1)
    (hslope : ∀ t ∈ usedTubes P.incidences, ∀ j, |P.slope t j| ≤ 1)
    (htime : ∀ p ∈ P.incidences, |(P.center p.2).2| ≤ 1)
    (hphysical : ∀ p ∈ P.incidences, ∀ j,
      |P.residual p.1 p.2 j| ≤ (P.E : ℝ) * P.σ)
    (hdensity : P.lam * B.card ≤ P.δ * P.incidences.card) :
    P.lam * B.card ≤ 2 * P.σ * P.newIncidences.card ∧
      P.lam * B.card ≤ 2 * P.δ * P.keptIncidences.card := by
  have h := P.hypotheses_of_full_backbone_density B hused hδ hN hσ
    hlam hlamOne hslope htime hphysical hdensity
  have hmass : (P.incidences.card : ℝ) ≤ 2 * P.keptIncidences.card := by
    exact_mod_cast P.half_mass h
  have hcapacity : (P.keptIncidences.card : ℝ) ≤ P.N * P.newIncidences.card := by
    exact_mod_cast P.retained_capacity h
  have hretained : P.lam * B.card ≤ 2 * P.δ * P.keptIncidences.card := by
    calc
      P.lam * B.card ≤ P.δ * P.incidences.card := hdensity
      _ ≤ P.δ * (2 * P.keptIncidences.card) :=
        mul_le_mul_of_nonneg_left hmass hδ.le
      _ = 2 * P.δ * P.keptIncidences.card := by ring
  refine ⟨?_, hretained⟩
  calc
    P.lam * B.card ≤ 2 * P.δ * P.keptIncidences.card := hretained
    _ ≤ (2 * P.δ) * (P.N * P.newIncidences.card) :=
      mul_le_mul_of_nonneg_left hcapacity (by positivity)
    _ = 2 * P.σ * P.newIncidences.card := by dsimp [σ]; ring

end PhysicalRescalingIncidenceTransfer.Data
