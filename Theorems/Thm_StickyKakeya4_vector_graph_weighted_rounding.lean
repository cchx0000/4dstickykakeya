import Theorems.Thm_StickyKakeya4_vector_graph_collision_energy
import Theorems.Thm_StickyKakeya4_vector_integer_bin_real_bsg
import Theorems.Thm_StickyKakeya4_graph_weighted_original_fiber_bin
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
open Finset
noncomputable section
open Classical

namespace VectorGraphWeightedRounding
open PlanarShiftedNearEnergy ActualPlanarRoundedEnergy TwoTubePathCollisionCount
open DyadicOriginalFiberSelection VectorGraphCollisionEnergy

/-- Finite Cauchy is applied to the actual graph and its literal output grid. -/
lemma original_graph_cover_grid_energy {W : Type*}
    (A : Finset (ℝ × ℝ)) (P : Finset W) (v : W → ℝ × ℝ)
    (G : Finset ((ℝ × ℝ) × W)) {delta beta M : ℝ}
    (hA : A.Nonempty) (hb : 0 ≤ beta) (hM : 0 < M)
    (hdense : beta * A.card * P.card ≤ (G.card : ℝ))
    (hcover : ((G.image (fun e => roundPoint delta (e.1 + v e.2))).card : ℝ) ≤ M * A.card) :
    (beta ^ 2 / M) * A.card * (P.card : ℝ) ^ 2 ≤
      ((collisions G (fun e => roundPoint delta (e.1 + v e.2))).card : ℝ) := by
  have hAc : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hCS : (G.card : ℝ) ^ 2 ≤
      ((G.image (fun e => roundPoint delta (e.1 + v e.2))).card : ℝ) *
        (collisions G (fun e => roundPoint delta (e.1 + v e.2))).card := by
    exact_mod_cast square_card_le_image_mul_collisions G (fun e => roundPoint delta (e.1 + v e.2))
  have hupper := hCS.trans (mul_le_mul_of_nonneg_right hcover
    (show 0 ≤ ((collisions G (fun e => roundPoint delta (e.1 + v e.2))).card : ℝ) by positivity))
  have hlower := pow_le_pow_left₀ (show 0 ≤ beta * A.card * P.card by positivity) hdense 2
  have hcancel : beta ^ 2 * A.card * (P.card : ℝ) ^ 2 ≤
      M * (collisions G (fun e => roundPoint delta (e.1 + v e.2))).card := by
    apply (mul_le_mul_iff_left₀ hAc).mp
    nlinarith [hlower.trans hupper]
  calc
    _ = (beta ^ 2 * A.card * (P.card : ℝ) ^ 2) / M := by ring
    _ ≤ _ := (div_le_iff₀ hM).mpr (by nlinarith)

/-- Same-output-cell pairs stay on the actual graph during the near-energy step. -/
lemma graph_grid_collisions_near_graph {W : Type*}
    (v : W → ℝ × ℝ) (G : Finset ((ℝ × ℝ) × W)) {delta : ℝ}
    (hdelta : 0 < delta) :
    collisions G (fun e => roundPoint delta (e.1 + v e.2)) ⊆
      coordinateNearPairs G (fun e => e.1 + v e.2) delta := by
  intro ee hee
  obtain ⟨he, he', hsame⟩ := (mem_collisions _ _ ee).mp hee
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he, he'⟩,
    same_planar_grid_close hdelta hsame⟩

/-- Rounding only A is injective on the actual graph and preserves all its
split-sum collision energy. Every original W label is retained. -/
lemma rounded_graph_collisions_card {W : Type*}
    (A : Finset (ℝ × ℝ)) (P : Finset W) (v : W → ℝ × ℝ)
    (G : Finset ((ℝ × ℝ) × W)) {delta : ℝ} (hdelta : 0 < delta)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → delta / 2 ≤ ‖a - b‖)
    (hG : G ⊆ A ×ˢ P) :
    (collisions G (fun e => roundPoint (delta / 2) e.1 + roundPoint (delta / 2) (v e.2))).card =
      (collisions (G.image (fun e => (roundPoint (delta / 2) e.1, e.2)))
        (fun e => e.1 + roundPoint (delta / 2) (v e.2))).card := by
  let g : (ℝ × ℝ) × W → (ℤ × ℤ) × W := fun e => (roundPoint (delta / 2) e.1, e.2)
  have hg : Set.InjOn g (↑G) := by
    intro e he d hd hed
    have ha := (planar_rounding_injOn A hdelta hsep)
      (Finset.mem_product.mp (hG he)).1 (Finset.mem_product.mp (hG hd)).1
      (congrArg (fun q : (ℤ × ℤ) × W => q.1) hed)
    have hp : e.2 = d.2 := congrArg (fun q : (ℤ × ℤ) × W => q.2) hed
    exact Prod.ext ha hp
  exact VectorIntegerBinRealBSG.collisions_image_card G g
    (fun e => e.1 + roundPoint (delta / 2) (v e.2)) hg

/-- The actual output cover yields actual rounded-graph energy, with the
canonical factor 49 and without enlarging the graph to the full product. -/
theorem original_graph_cover_rounded_energy {W : Type*}
    (A : Finset (ℝ × ℝ)) (P : Finset W) (v : W → ℝ × ℝ)
    (G : Finset ((ℝ × ℝ) × W)) {delta beta M : ℝ}
    (hA : A.Nonempty) (hdelta : 0 < delta) (hb : 0 ≤ beta) (hM : 0 < M)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → delta / 2 ≤ ‖a - b‖)
    (hG : G ⊆ A ×ˢ P) (hdense : beta * A.card * P.card ≤ (G.card : ℝ))
    (hcover : ((G.image (fun e => roundPoint delta (e.1 + v e.2))).card : ℝ) ≤ M * A.card) :
    ((beta ^ 2 / M) / 49) * (A.image (roundPoint (delta / 2))).card * (P.card : ℝ) ^ 2 ≤
      ((collisions (G.image (fun e => (roundPoint (delta / 2) e.1, e.2)))
        (fun e => e.1 + roundPoint (delta / 2) (v e.2))).card : ℝ) := by
  have hgrid := original_graph_cover_grid_energy A P v G hA hb hM hdense hcover
  have hnear : ((collisions G (fun e => roundPoint delta (e.1 + v e.2))).card : ℝ) ≤
      (coordinateNearPairs G (fun e => e.1 + v e.2) delta).card :=
    Nat.cast_le.mpr (Finset.card_le_card (graph_grid_collisions_near_graph v G hdelta))
  have hround : ((coordinateNearPairs G (fun e => e.1 + v e.2) delta).card : ℝ) ≤
      49 * (collisions G (fun e => roundPoint (delta / 2) e.1 + roundPoint (delta / 2) (v e.2))).card := by
    exact_mod_cast original_labelled_planar_rounding G Prod.fst (fun e => v e.2) hdelta
  rw [rounded_graph_collisions_card A P v G hdelta hsep hG] at hround
  rw [planar_rounded_card A hdelta hsep]
  nlinarith only [hgrid.trans (hnear.trans hround)]

/-- Select a bin by actual graph energy, retain every original label in each
selected value fiber, and pull a selected graph edge back to the original G. -/
theorem exists_vector_graph_energy_bin {W : Type*}
    (A : Finset (ℝ × ℝ)) (P : Finset W) (v : W → ℝ × ℝ) (G : Finset ((ℝ × ℝ) × W))
    (hA : A.Nonempty) (hP : P.Nonempty) {delta beta M : ℝ}
    (hdelta : 0 < delta) (hb : 0 < beta) (hM : 0 < M)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → delta / 2 ≤ ‖a - b‖)
    (hG : G ⊆ A ×ˢ P) (hdense : beta * A.card * P.card ≤ (G.card : ℝ))
    (hcover : ((G.image (fun e => roundPoint delta (e.1 + v e.2))).card : ℝ) ≤ M * A.card) :
    ∃ j < levelCount P,
      let nu := beta ^ 2 / M
      let f := fun p => roundPoint (delta / 2) (v p)
      let S := (bin P f j).image f
      (bin P f j).Nonempty ∧ S.Nonempty ∧
      nu * P.card ≤ 98 * (levelCount P : ℝ) * (bin P f j).card ∧
      nu * A.card * (S.card : ℝ) ^ 2 ≤
        392 * (levelCount P : ℝ) ^ 2 * (Finset.addEnergy (A.image (roundPoint (delta / 2))) S : ℝ) ∧
      (G.filter (fun e => level P f e.2 = j)).Nonempty ∧
      (∀ p ∈ bin P f j, ∀ q ∈ P, f q = f p → q ∈ bin P f j) ∧
      ∀ s ∈ S, fiber (bin P f j) f s = fiber P f s ∧
        2 ^ j ≤ (fiber P f s).card ∧ (fiber P f s).card < 2 ^ (j + 1) := by
  let f := fun p => roundPoint (delta / 2) (v p)
  let Abar := A.image (roundPoint (delta / 2))
  let g : (ℝ × ℝ) × W → (ℤ × ℤ) × W := fun e => (roundPoint (delta / 2) e.1, e.2)
  let E := G.image g
  have hE : E ⊆ Abar ×ˢ P := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨haa, hap⟩ := Finset.mem_product.mp (hG ha)
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ haa, hap⟩
  have he := original_graph_cover_rounded_energy A P v G hA hdelta hb.le hM hsep hG hdense hcover
  obtain ⟨j, hj, hbin, hgraph, hmass, _hgraphenergy, henergy⟩ :=
    GraphWeightedOriginalFiberBin.exists_graph_weighted_energy_bin Abar P f E
      (hA.image _) hP hE (by positivity : 0 < (beta ^ 2 / M) / 49) he
  have hAc : Abar.card = A.card := planar_rounded_card A hdelta hsep
  rw [hAc] at henergy
  refine ⟨j, hj, hbin, hbin.image f, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hmass]
  · nlinarith only [henergy]
  · obtain ⟨e, he⟩ := hgraph
    obtain ⟨heE, heLevel⟩ := Finset.mem_filter.mp he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp heE
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, heLevel⟩⟩
  · exact fun p hp q hq heq => bin_saturated P f j hp hq heq
  · intro s hs
    have heq := fiber_bin_eq P f j hs
    exact ⟨heq, by simpa only [heq] using bin_fiber_bounds P f j hs⟩

end VectorGraphWeightedRounding
