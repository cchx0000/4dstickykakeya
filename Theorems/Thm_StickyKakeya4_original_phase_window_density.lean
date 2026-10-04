import Theorems.Thm_StickyKakeya4_native_original_phase_window_graph

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalPhaseWindowDensity
open Classical OriginalPhaseWindowGraph

/-- Relative density in the literal phase/menu product, with the nine-cell
 enlargement charged once. This consumes the graph theorem's proved output. -/
theorem window_graph_relative_density {V L J : Type*} [DecidableEq L] [DecidableEq J]
    (E : Finset V) (grain : V → GrainLabel) (phase : V → L)
    (alphabet : Finset J) (menus : V → Finset J) (next : V → J → V)
    {degree beta : ℝ} (k : GrainLabel) (pick : L → V)
    (hgraph : IsWindowGraph E grain phase alphabet menus next degree k pick)
    (hscale : beta*(alphabet.card : ℝ) ≤ degree) :
    (beta/9)*((expanded E grain phase k).card : ℝ)*(alphabet.card : ℝ) ≤
      ((menuGraph (occupied E grain phase k) pick menus).card : ℝ) := by
  have hh := hgraph.2.2.2.2.2.1
  have hc := mul_le_mul_of_nonneg_right hscale
    (show 0 ≤ ((expanded E grain phase k).card : ℝ) by positivity)
  nlinarith

/-- The exact original angular alphabet, with both original heights, is
 used in the denominator; arbitrary pruned-height counts are never inserted. -/
theorem original_alphabet_degree_lower {H A : Type*} [DecidableEq H] [DecidableEq A]
    (Z : Finset H) (angles : Finset A) {alpha beta D U : ℝ} (hU : 0 < U)
    (hscale : 4*beta*U^2*(angles.card : ℝ)^2 ≤ alpha*D^2) :
    beta*(((Z ×ˢ Z) ×ˢ (angles ×ˢ angles)).card : ℝ) ≤
      ((alpha/4)*D^2*(Z.card : ℝ)^2)/U^2 := by
  rw [Finset.card_product,Finset.card_product,Finset.card_product]
  push_cast
  apply (le_div_iff₀ (sq_pos_of_pos hU)).mpr
  have hh := mul_le_mul_of_nonneg_right hscale (sq_nonneg (Z.card : ℝ))
  nlinarith

end OriginalPhaseWindowDensity
