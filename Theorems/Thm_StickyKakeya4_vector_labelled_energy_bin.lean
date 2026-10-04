import Theorems.Thm_StickyKakeya4_vector_graph_collision_energy
import Theorems.Thm_StickyKakeya4_energy_preserving_original_fiber_bin

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
open Finset
noncomputable section
open Classical

namespace VectorLabelledEnergyBin
open PlanarShiftedNearEnergy ActualPlanarRoundedEnergy TwoTubePathCollisionCount
open DyadicOriginalFiberSelection VectorGraphCollisionEnergy

/-- Round only A and preserve every original vector-product pair label. -/
lemma labelled_integer_collisions_le {W : Type*}
    (A : Finset (ℝ × ℝ)) (P : Finset W) (v : W → ℝ × ℝ) {delta : ℝ}
    (hdelta : 0 < delta)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → delta / 2 ≤ ‖a - b‖) :
    (collisions (A ×ˢ P) (fun e => roundPoint (delta / 2) e.1 + roundPoint (delta / 2) (v e.2))).card ≤
      (collisions ((A.image (roundPoint (delta / 2))) ×ˢ P)
        (fun e => e.1 + roundPoint (delta / 2) (v e.2))).card := by
  let g : (ℝ × ℝ) × W → (ℤ × ℤ) × W := fun e => (roundPoint (delta / 2) e.1, e.2)
  have hg : Set.InjOn g (↑(A ×ˢ P)) := by
    intro e he d hd hed
    have ha := (planar_rounding_injOn A hdelta hsep)
      (Finset.mem_product.mp he).1 (Finset.mem_product.mp hd).1
      (congrArg (fun q : (ℤ × ℤ) × W => q.1) hed)
    have hp : e.2 = d.2 := congrArg (fun q : (ℤ × ℤ) × W => q.2) hed
    exact Prod.ext ha hp
  apply Finset.card_le_card_of_injOn (fun ee => (g ee.1, g ee.2))
  · intro ee hee
    obtain ⟨he, hd, hsame⟩ := (mem_collisions _ _ ee).mp hee
    obtain ⟨hea, hep⟩ := Finset.mem_product.mp he
    obtain ⟨hda, hdp⟩ := Finset.mem_product.mp hd
    exact (mem_collisions _ _ _).mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hea, hep⟩,
        Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hda, hdp⟩, hsame⟩
  · intro ee hee dd hdd heq
    obtain ⟨he1, he2, _⟩ := (mem_collisions _ _ ee).mp hee
    obtain ⟨hd1, hd2, _⟩ := (mem_collisions _ _ dd).mp hdd
    have h1 : g ee.1 = g dd.1 := congrArg (fun q : ((ℤ × ℤ) × W) × ((ℤ × ℤ) × W) => q.1) heq
    have h2 : g ee.2 = g dd.2 := congrArg (fun q : ((ℤ × ℤ) × W) × ((ℤ × ℤ) × W) => q.2) heq
    exact Prod.ext (hg he1 hd1 h1) (hg he2 hd2 h2)

lemma labelled_planar_near_energy_le_fortynine {W : Type*}
    (A : Finset (ℝ × ℝ)) (P : Finset W) (v : W → ℝ × ℝ) {delta : ℝ}
    (hdelta : 0 < delta)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → delta / 2 ≤ ‖a - b‖) :
    (coordinateNearPairs (A ×ˢ P) (fun e => e.1 + v e.2) delta).card ≤
      49 * (collisions ((A.image (roundPoint (delta / 2))) ×ˢ P)
        (fun e => e.1 + roundPoint (delta / 2) (v e.2))).card := by
  have hh := original_labelled_planar_rounding (A ×ˢ P) Prod.fst (fun e => v e.2) hdelta
  exact hh.trans (Nat.mul_le_mul_left 49 (labelled_integer_collisions_le A P v hdelta hsep))

/-- A coupled Z² bin with actual original pair weight and unweighted vector
additive energy. Generic group fiber selection supplies all fiber bounds. -/
theorem exists_vector_energy_preserving_bin {W : Type*}
    (A : Finset (ℝ × ℝ)) (P : Finset W) (v : W → ℝ × ℝ)
    (hA : A.Nonempty) (hP : P.Nonempty) {delta nu : ℝ} (hdelta : 0 < delta) (hnu : 0 < nu)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → delta / 2 ≤ ‖a - b‖)
    (he : nu * A.card * (P.card : ℝ) ^ 2 ≤
      ((coordinateNearPairs (A ×ˢ P) (fun e => e.1 + v e.2) delta).card : ℝ)) :
    ∃ j < levelCount P,
      let f := fun p => roundPoint (delta / 2) (v p)
      let S := (bin P f j).image f
      (bin P f j).Nonempty ∧ S.Nonempty ∧
      nu * P.card ≤ 98 * (levelCount P : ℝ) * (bin P f j).card ∧
      nu * A.card * (S.card : ℝ) ^ 2 ≤
        392 * (levelCount P : ℝ) ^ 2 * (Finset.addEnergy (A.image (roundPoint (delta / 2))) S : ℝ) ∧
      (∀ p ∈ bin P f j, ∀ q ∈ P, f q = f p → q ∈ bin P f j) ∧
      ∀ s ∈ S, fiber (bin P f j) f s = fiber P f s ∧
        2 ^ j ≤ (fiber P f s).card ∧ (fiber P f s).card < 2 ^ (j + 1) := by
  let f := fun p => roundPoint (delta / 2) (v p)
  let Abar := A.image (roundPoint (delta / 2))
  have hAc : Abar.card = A.card := planar_rounded_card A hdelta hsep
  have hround : ((coordinateNearPairs (A ×ˢ P) (fun e => e.1 + v e.2) delta).card : ℝ) ≤
      49 * (collisions (Abar ×ˢ P) (fun e => e.1 + f e.2)).card := by
    exact_mod_cast labelled_planar_near_energy_le_fortynine A P v hdelta hsep
  have he' : (nu / 49) * Abar.card * (P.card : ℝ) ^ 2 ≤
      ((collisions (Abar ×ˢ P) (fun e => e.1 + f e.2)).card : ℝ) := by
    rw [hAc]
    nlinarith only [he.trans hround]
  obtain ⟨j, hj, hbin, hmass, henergy⟩ := EnergyPreservingOriginalFiberBin.exists_energy_preserving_bin
    Abar P f (hA.image _) hP (div_pos hnu (by norm_num)) he'
  rw [hAc] at henergy
  refine ⟨j, hj, hbin, hbin.image f, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hmass]
  · nlinarith only [henergy]
  · exact fun p hp q hq heq => bin_saturated P f j hp hq heq
  · intro s hs
    have heq := fiber_bin_eq P f j hs
    exact ⟨heq, by simpa only [heq] using bin_fiber_bounds P f j hs⟩

/-- The graph's literal small output cover DERIVES the energy fed into the
coupled vector bin; no desired collision energy is assumed at this interface. -/
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
      (∀ p ∈ bin P f j, ∀ q ∈ P, f q = f p → q ∈ bin P f j) ∧
      ∀ s ∈ S, fiber (bin P f j) f s = fiber P f s ∧
        2 ^ j ≤ (fiber P f s).card ∧ (fiber P f s).card < 2 ^ (j + 1) := by
  have he := original_graph_cover_near_energy A P v G hA hdelta hb.le hM hG hdense hcover
  exact exists_vector_energy_preserving_bin A P v hA hP hdelta (by positivity) hsep he

end VectorLabelledEnergyBin
