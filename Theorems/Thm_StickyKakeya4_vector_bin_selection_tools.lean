import Theorems.Thm_StickyKakeya4_vector_integer_bin_real_bsg
import Theorems.Thm_StickyKakeya4_vector_whole_fiber_lift
import Theorems.Thm_StickyKakeya4_partitioned_collision_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000
open Finset
noncomputable section
open Classical

namespace VectorBinSelectionTools
open PlanarShiftedNearEnergy PlanarRoundedSumsetCover VectorIntegerBinRealBSG
open TwoTubePathCollisionCount DyadicOriginalFiberSelection

def selectedCodes (S : Finset (ℤ × ℤ)) (X : Finset (ℝ × ℝ)) (eta : ℝ) : Finset (ℤ × ℤ) :=
  S.filter (fun s => synthesis eta s ∈ X)

lemma selectedCodes_subset (S : Finset (ℤ × ℤ)) (X : Finset (ℝ × ℝ)) (eta : ℝ) :
    selectedCodes S X eta ⊆ S := Finset.filter_subset _ _

lemma selectedCodes_image (S : Finset (ℤ × ℤ)) (X : Finset (ℝ × ℝ)) (eta : ℝ)
    (hX : X ⊆ realGrid eta S) : (selectedCodes S X eta).image (synthesis eta) = X := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hs).2
  · intro hx
    obtain ⟨s, hs, hsx⟩ := Finset.mem_image.mp (hX hx)
    exact Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, hsx ▸ hx⟩, hsx⟩

lemma selectedCodes_card (S : Finset (ℤ × ℤ)) (X : Finset (ℝ × ℝ)) {eta : ℝ}
    (heta : 0 < eta) (hX : X ⊆ realGrid eta S) : (selectedCodes S X eta).card = X.card := by
  have him := congrArg Finset.card (selectedCodes_image S X eta hX)
  have hinj := Finset.card_image_of_injective (selectedCodes S X eta) (synthesis_injective heta)
  exact hinj.symm.trans him

lemma integer_addEnergy_cap (A S : Finset (ℤ × ℤ)) :
    (Finset.addEnergy A S : ℝ) ≤ (A.card : ℝ) * (S.card : ℝ) ^ 2 := by
  have hh := PartitionedCollisionEnergy.translated_pair_energy_cap A S id
  have he : (collisions (A ×ˢ S) (fun e => e.1 + e.2)).card = Finset.addEnergy A S := by
    simpa only [collisions, Finset.product_eq_sprod] using (Finset.addEnergy_eq_card_filter A S).symm
  change (collisions (A ×ˢ S) (fun e => e.1 + e.2)).card ≤ A.card * S.card ^ 2 at hh
  rw [he] at hh
  exact_mod_cast hh

/-- The BSG energy parameter is automatically at most one, from the actual
unweighted energy cap. It is not an additional source-level certificate. -/
lemma normalized_bin_density (A S : Finset (ℤ × ℤ)) {nu H : ℝ}
    (hA : A.Nonempty) (hS : S.Nonempty) (hnu : 0 < nu) (hH : 0 < H)
    (he : nu * A.card * (S.card : ℝ) ^ 2 ≤ 392 * H ^ 2 * (Finset.addEnergy A S : ℝ)) :
    0 < nu / (392 * H ^ 2) ∧ nu / (392 * H ^ 2) ≤ 1 ∧
      (nu / (392 * H ^ 2)) * A.card * (S.card : ℝ) ^ 2 ≤ (Finset.addEnergy A S : ℝ) := by
  have hAc : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hSc : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hden : 0 < 392 * H ^ 2 := by positivity
  have hcap := integer_addEnergy_cap A S
  have hupper := he.trans (mul_le_mul_of_nonneg_left hcap hden.le)
  have hnu1 : nu ≤ 392 * H ^ 2 := by
    apply (mul_le_mul_iff_left₀ (show 0 < (A.card : ℝ) * (S.card : ℝ) ^ 2 by positivity)).mp
    nlinarith only [hupper]
  refine ⟨by positivity, (div_le_one hden).mpr hnu1, ?_⟩
  calc
    _ = (nu * A.card * (S.card : ℝ) ^ 2) / (392 * H ^ 2) := by ring
    _ ≤ _ := (div_le_iff₀ hden).mpr (by nlinarith only [he])

lemma rounded_point_box_four {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (x : ℝ × ℝ) (hx : |x.1| ≤ 1 ∧ |x.2| ≤ 1) :
    |(synthesis eta (roundPoint eta x)).1| ≤ 4 ∧ |(synthesis eta (roundPoint eta x)).2| ≤ 4 := by
  have he1 := ActualRoundedAdditiveEnergy.round_error heta x.1
  have he2 := ActualRoundedAdditiveEnergy.round_error heta x.2
  have hx1 := abs_le.mp hx.1
  have hx2 := abs_le.mp hx.2
  change |eta * (ActualRoundedAdditiveEnergy.rounded eta x.1 : ℝ)| ≤ 4 ∧
    |eta * (ActualRoundedAdditiveEnergy.rounded eta x.2 : ℝ)| ≤ 4
  exact ⟨abs_le.mpr ⟨by nlinarith only [he1.2, hx1.1, heta1], by nlinarith only [he1.1, hx1.2]⟩,
    abs_le.mpr ⟨by nlinarith only [he2.2, hx2.1, heta1], by nlinarith only [he2.1, hx2.2]⟩⟩

lemma coupled_bin_grid_box {W : Type*} (P : Finset W) (v : W → ℝ × ℝ) (j : ℕ)
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hv : ∀ p ∈ P, |(v p).1| ≤ 1 ∧ |(v p).2| ≤ 1) :
    ∀ x ∈ realGrid eta ((bin P (fun p => roundPoint eta (v p)) j).image
      (fun p => roundPoint eta (v p))), |x.1| ≤ 4 ∧ |x.2| ≤ 4 := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
  exact rounded_point_box_four heta heta1 (v p) (hv p (Finset.mem_filter.mp hp).1)

end VectorBinSelectionTools
