import Theorems.Thm_StickyKakeya4_actual_planar_rounded_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open Finset
noncomputable section
open Classical

namespace VectorGraphCollisionEnergy
open PlanarShiftedNearEnergy TwoTubePathCollisionCount

lemma same_planar_grid_close {delta : ℝ} (hdelta : 0 < delta) {x y : ℝ × ℝ}
    (h : roundPoint delta x = roundPoint delta y) :
    |x.1 - y.1| ≤ delta ∧ |x.2 - y.2| ≤ delta := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  have hx1 := ActualRoundedAdditiveEnergy.round_error hdelta x.1
  have hy1 := ActualRoundedAdditiveEnergy.round_error hdelta y.1
  have hx2 := ActualRoundedAdditiveEnergy.round_error hdelta x.2
  have hy2 := ActualRoundedAdditiveEnergy.round_error hdelta y.2
  change ActualRoundedAdditiveEnergy.rounded delta x.1 = ActualRoundedAdditiveEnergy.rounded delta y.1 at h1
  change ActualRoundedAdditiveEnergy.rounded delta x.2 = ActualRoundedAdditiveEnergy.rounded delta y.2 at h2
  rw [← h1] at hy1
  rw [← h2] at hy2
  exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- Original graph collisions in an occupied output cell are literal planar
near-sum collisions on the original full labelled source. -/
lemma graph_grid_collisions_near {W : Type*} (A : Finset (ℝ × ℝ)) (P : Finset W)
    (v : W → ℝ × ℝ) (G : Finset ((ℝ × ℝ) × W)) {delta : ℝ}
    (hdelta : 0 < delta) (hG : G ⊆ A ×ˢ P) :
    collisions G (fun e => roundPoint delta (e.1 + v e.2)) ⊆
      coordinateNearPairs (A ×ˢ P) (fun e => e.1 + v e.2) delta := by
  intro ee hee
  obtain ⟨he, he', hsame⟩ := (mem_collisions _ _ ee).mp hee
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hG he, hG he'⟩,
    same_planar_grid_close hdelta hsame⟩

/-- Genuine occupied-grid-cover to original graph energy. The existing finite
Cauchy theorem is applied to the actual graph, before any pair labels are lost. -/
theorem original_graph_cover_near_energy {W : Type*}
    (A : Finset (ℝ × ℝ)) (P : Finset W) (v : W → ℝ × ℝ)
    (G : Finset ((ℝ × ℝ) × W)) {delta beta M : ℝ}
    (hA : A.Nonempty) (hdelta : 0 < delta) (hb : 0 ≤ beta) (hM : 0 < M)
    (hG : G ⊆ A ×ˢ P) (hdense : beta * A.card * P.card ≤ (G.card : ℝ))
    (hcover : ((G.image (fun e => roundPoint delta (e.1 + v e.2))).card : ℝ) ≤ M * A.card) :
    (beta ^ 2 / M) * A.card * (P.card : ℝ) ^ 2 ≤
      ((coordinateNearPairs (A ×ˢ P) (fun e => e.1 + v e.2) delta).card : ℝ) := by
  have hAc : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hCS : (G.card : ℝ) ^ 2 ≤
      ((G.image (fun e => roundPoint delta (e.1 + v e.2))).card : ℝ) *
        (collisions G (fun e => roundPoint delta (e.1 + v e.2))).card := by
    exact_mod_cast square_card_le_image_mul_collisions G (fun e => roundPoint delta (e.1 + v e.2))
  have hnear : ((collisions G (fun e => roundPoint delta (e.1 + v e.2))).card : ℝ) ≤
      (coordinateNearPairs (A ×ˢ P) (fun e => e.1 + v e.2) delta).card :=
    Nat.cast_le.mpr (Finset.card_le_card (graph_grid_collisions_near A P v G hdelta hG))
  have hupper := hCS.trans (mul_le_mul hcover hnear (by positivity) (by positivity))
  have hlower := pow_le_pow_left₀ (show 0 ≤ beta * A.card * P.card by positivity) hdense 2
  have hcancel : beta ^ 2 * A.card * (P.card : ℝ) ^ 2 ≤
      M * (coordinateNearPairs (A ×ˢ P) (fun e => e.1 + v e.2) delta).card := by
    apply (mul_le_mul_iff_left₀ hAc).mp
    nlinarith [hlower.trans hupper]
  calc
    _ = (beta ^ 2 * A.card * (P.card : ℝ) ^ 2) / M := by ring
    _ ≤ _ := (div_le_iff₀ hM).mpr (by nlinarith)

/-- The literal vector product value; pair labels, not merely values, are kept. -/
def productValue (p : (ℝ × ℝ) × ℝ) : ℝ × ℝ := p.2 • p.1

/-- Specialization to Theorem21.2's original A x B x C graph. -/
theorem original_ABC_cover_near_energy
    (A B : Finset (ℝ × ℝ)) (C : Finset ℝ) (G : Finset ((ℝ × ℝ) × ((ℝ × ℝ) × ℝ)))
    {delta beta M : ℝ} (hA : A.Nonempty) (hdelta : 0 < delta) (hb : 0 ≤ beta) (hM : 0 < M)
    (hG : G ⊆ A ×ˢ (B ×ˢ C))
    (hdense : beta * A.card * (B ×ˢ C).card ≤ (G.card : ℝ))
    (hcover : ((G.image (fun e => roundPoint delta (e.1 + e.2.2 • e.2.1))).card : ℝ) ≤ M * A.card) :
    (beta ^ 2 / M) * A.card * ((B ×ˢ C).card : ℝ) ^ 2 ≤
      ((coordinateNearPairs (A ×ˢ (B ×ˢ C)) (fun e => e.1 + e.2.2 • e.2.1) delta).card : ℝ) :=
  original_graph_cover_near_energy A (B ×ˢ C) productValue G hA hdelta hb hM hG hdense hcover

end VectorGraphCollisionEnergy
