import Theorems.Thm_StickyKakeya4_physical_rescaling_incidence_transfer

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open Classical IncidenceBinTransfer

namespace PhysicalRescalingIncidenceTransfer.Data

variable {T : Type*} (P : PhysicalRescalingIncidenceTransfer.Data T)

/-- Endpoint density keeps the entire original tube backbone, including tubes whose
selected shading is empty. The new-incidence count is the only selected quantity. -/
theorem endpoint_density_original_backbone (h : P.Hypotheses) :
    P.lam * (usedTubes P.incidences).card ≤ 2 * P.σ * P.newIncidences.card := by
  have hmass : (P.incidences.card : ℝ) ≤ 2 * P.keptIncidences.card := by
    exact_mod_cast P.half_mass h
  have hcapacity : (P.keptIncidences.card : ℝ) ≤ P.N * P.newIncidences.card := by
    exact_mod_cast P.retained_capacity h
  calc
    P.lam * (usedTubes P.incidences).card ≤ P.δ * P.incidences.card := h.density
    _ ≤ P.δ * (2 * P.keptIncidences.card) :=
      mul_le_mul_of_nonneg_left hmass h.delta_pos.le
    _ ≤ P.δ * (2 * (P.N * P.newIncidences.card)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcapacity (by norm_num)) h.delta_pos.le
    _ = 2 * P.σ * P.newIncidences.card := by dsimp [σ]; ring

/-- At least half the original total incidence survives with the exact old pair labels. -/
theorem retained_total_density (h : P.Hypotheses) :
    P.lam * (usedTubes P.incidences).card ≤ 2 * P.δ * P.keptIncidences.card := by
  have hmass : (P.incidences.card : ℝ) ≤ 2 * P.keptIncidences.card := by
    exact_mod_cast P.half_mass h
  calc
    P.lam * (usedTubes P.incidences).card ≤ P.δ * P.incidences.card := h.density
    _ ≤ P.δ * (2 * P.keptIncidences.card) :=
      mul_le_mul_of_nonneg_left hmass h.delta_pos.le
    _ = 2 * P.δ * P.keptIncidences.card := by ring

end PhysicalRescalingIncidenceTransfer.Data
