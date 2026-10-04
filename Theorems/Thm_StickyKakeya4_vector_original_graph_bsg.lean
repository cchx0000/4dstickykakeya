import Theorems.Thm_StickyKakeya4_vector_labelled_energy_bin
import Theorems.Thm_StickyKakeya4_vector_graph_weighted_rounding
import Theorems.Thm_StickyKakeya4_vector_bin_selection_tools
import Theorems.Thm_StickyKakeya4_vector_product_cover
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000
open Finset
open scoped Pointwise
noncomputable section
open Classical

namespace VectorOriginalGraphBSG
open PlanarShiftedNearEnergy PlanarRoundedSumsetCover ActualPlanarRoundedEnergy
open DyadicOriginalFiberSelection VectorGraphCollisionEnergy VectorLabelledEnergyBin
open VectorIntegerBinRealBSG VectorWholeFiberLift VectorBinSelectionTools VectorProductCover

/-- Explicit source-derived BSG density, including the vector rounding and
original whole-fiber logarithmic losses. -/
def sourceDensity {W : Type*} (P : Finset W) (beta M : ℝ) : ℝ :=
  (beta ^ 2 / M) / (392 * (levelCount P : ℝ) ^ 2)

lemma dyadic_half_le_one (n : ℕ) : ((2 : ℝ) ^ n)⁻¹ / 2 ≤ 1 := by
  have hp : 0 < (2 : ℝ) ^ n := by positivity
  have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hpow (show 0 ≤ ((2 : ℝ) ^ n)⁻¹ by positivity)
  rw [one_mul, mul_inv_cancel₀ hp.ne'] at hm
  linarith

/-- Original graph cover -> coupled vector energy bin -> genuine planar BSG
-> ORIGINAL weighted labels and actual value triple cover. K and n0 are chosen
before graph density, cover constant, sets and original pair-value map. -/
theorem original_vector_graph_dyadic_bsg {W : Type*} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ K n0 : ℕ, 0 < K ∧ ∀ n : ℕ, n0 ≤ n →
      ∀ beta M : ℝ, 0 < beta → 0 < M →
      ∀ A : Finset (ℝ × ℝ), ∀ P : Finset W, ∀ v : W → ℝ × ℝ,
      ∀ G : Finset ((ℝ × ℝ) × W), A.Nonempty → P.Nonempty →
      (∀ a ∈ A, |a.1| ≤ 1 ∧ |a.2| ≤ 1) →
      (∀ p ∈ P, |(v p).1| ≤ 1 ∧ |(v p).2| ≤ 1) →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ((2 : ℝ) ^ n)⁻¹ / 2 ≤ ‖a - b‖) →
      G ⊆ A ×ˢ P → beta * A.card * P.card ≤ (G.card : ℝ) →
      ((G.image (fun e => roundPoint (((2 : ℝ) ^ n)⁻¹) (e.1 + v e.2))).card : ℝ) ≤ M * A.card →
      let delta : ℝ := ((2 : ℝ) ^ n)⁻¹
      let f := fun p => roundPoint (delta / 2) (v p)
      let alpha := sourceDensity P beta M
      let r := alpha ^ K * delta ^ epsilon
      ∃ j < levelCount P, ∃ A' : Finset (ℝ × ℝ), ∃ F : Finset W,
        A' ⊆ A ∧ F ⊆ P ∧ F ⊆ bin P f j ∧
        (bin P f j).Nonempty ∧ (G.filter (fun e => level P f e.2 = j)).Nonempty ∧
        r * A.card ≤ A'.card ∧
        (r * (beta ^ 2 / M) / (196 * (levelCount P : ℝ))) * P.card ≤ F.card ∧
        (∀ p ∈ F, ∀ q ∈ P, f q = f p → q ∈ F) ∧
        (((A' + F.image v - F.image v).image (roundPoint (delta / 2))).card : ℝ) ≤
          49 * (delta ^ (-2 * epsilon) / alpha ^ (2 * K)) * A.card := by
  obtain ⟨K, n0, hK, hBSG⟩ := integer_bin_planar_dyadic_bsg hepsilon
  refine ⟨K, n0, hK, ?_⟩
  intro n hn beta M hb hM A P v G hA hP hAbound hv hAsep hG hdense hcover
  let delta : ℝ := ((2 : ℝ) ^ n)⁻¹
  let f := fun p => roundPoint (delta / 2) (v p)
  let alpha := sourceDensity P beta M
  let r := alpha ^ K * delta ^ epsilon
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have heta : 0 < delta / 2 := by positivity
  have hnu : 0 < beta ^ 2 / M := by positivity
  have hH : 0 < (levelCount P : ℝ) := by exact_mod_cast Nat.zero_lt_succ (Nat.log 2 P.card)
  obtain ⟨j, hj, hbin, hSnon, hmass, henergy, hGraphBin, _hwhole, _hfibers⟩ :=
    VectorGraphWeightedRounding.exists_vector_graph_energy_bin A P v G hA hP hdelta hb hM hAsep hG hdense hcover
  let S := (bin P f j).image f
  let Abar := A.image (roundPoint (delta / 2))
  have hAc : Abar.card = A.card := planar_rounded_card A hdelta hAsep
  have henergy' : (beta ^ 2 / M) * Abar.card * (S.card : ℝ) ^ 2 ≤
      392 * (levelCount P : ℝ) ^ 2 * (Finset.addEnergy Abar S : ℝ) := by
    rw [hAc]
    exact henergy
  obtain ⟨ha0, ha1, heNormalized⟩ := normalized_bin_density Abar S (hA.image _) hSnon hnu hH henergy'
  have ha0' : 0 < alpha := ha0
  have ha1' : alpha ≤ 1 := ha1
  have heBSG : alpha * A.card * (S.card : ℝ) ^ 2 ≤ (Finset.addEnergy Abar S : ℝ) := by
    simpa only [hAc, alpha, sourceDensity] using heNormalized
  obtain ⟨X', A', hX', hA', hXmass, hAmass, hBSGcover⟩ :=
    hBSG n hn alpha ha0' ha1' A S hA hSnon hAbound
      (coupled_bin_grid_box P v j heta (dyadic_half_le_one n) hv) hAsep heBSG
  let U := selectedCodes S X' (delta / 2)
  have hUS : U ⊆ S := selectedCodes_subset S X' (delta / 2)
  have hUcard : U.card = X'.card := selectedCodes_card S X' heta hX'
  have hUimage : U.image (synthesis (delta / 2)) = X' := selectedCodes_image S X' (delta / 2) hX'
  have hUret : r * S.card ≤ U.card := by rw [hUcard]; exact hXmass
  let F := selectedPairs P f j U
  have hFP : F ⊆ P := selectedPairs_subset P f j U
  have hFbin : F ⊆ bin P f j := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hFmass := selectedPairs_original_mass P f j U hr hbin hUS hUret hmass
  have hFimage : (F.image v).image (roundPoint (delta / 2)) = U := by
    have hh := selectedPairs_image P f j U hUS
    rw [Finset.image_image]
    ext s
    simpa only [Finset.mem_image, f, Function.comp_def] using Finset.ext_iff.mp hh s
  refine ⟨j, hj, A', F, hA', hFP, hFbin, hbin, hGraphBin, hAmass, hFmass, ?_, ?_⟩
  · exact fun p hp q hq heq => selectedPairs_whole_fiber P f j U hp hq heq
  · have htransfer := actual_product_triple_cover A' (F.image v) U heta hFimage
    rw [hUimage] at htransfer
    have hcover11 := hBSGcover 1 1
    norm_num only [one_nsmul, Nat.reduceAdd, Nat.cast_ofNat] at hcover11
    have hexp : -epsilon * (2 : ℝ) = -2 * epsilon := by ring
    rw [hexp, Nat.mul_comm K 2] at hcover11
    have htR : (((A' + F.image v - F.image v).image (roundPoint (delta / 2))).card : ℝ) ≤
        49 * ((A' + X' - X').image (roundPoint (delta / 2))).card := by exact_mod_cast htransfer
    exact htR.trans (by nlinarith only [hcover11])

/-- Scalar multiplication gives a genuinely planar original pair-value map. -/
lemma original_product_value_box (B : Finset (ℝ × ℝ)) (C : Finset ℝ)
    (hB : ∀ b ∈ B, |b.1| ≤ 1 ∧ |b.2| ≤ 1) (hC : ∀ c ∈ C, |c| ≤ 1) :
    ∀ p ∈ B ×ˢ C, |(productValue p).1| ≤ 1 ∧ |(productValue p).2| ≤ 1 := by
  intro p hp
  obtain ⟨hpB, hpC⟩ := Finset.mem_product.mp hp
  have hb := hB p.1 hpB
  have hc := hC p.2 hpC
  change |p.2 * p.1.1| ≤ 1 ∧ |p.2 * p.1.2| ≤ 1
  constructor
  · rw [abs_mul]
    exact (mul_le_mul hc hb.1 (abs_nonneg _) (by norm_num)).trans (by norm_num)
  · rw [abs_mul]
    exact (mul_le_mul hc hb.2 (abs_nonneg _) (by norm_num)).trans (by norm_num)

/-- Literal scalar-times-vector ABC caller, preserving original B x C pair weights. -/
theorem original_ABC_dyadic_bsg {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ K n0 : ℕ, 0 < K ∧ ∀ n : ℕ, n0 ≤ n →
      ∀ beta M : ℝ, 0 < beta → 0 < M →
      ∀ A B : Finset (ℝ × ℝ), ∀ C : Finset ℝ,
      ∀ G : Finset ((ℝ × ℝ) × ((ℝ × ℝ) × ℝ)), A.Nonempty → B.Nonempty → C.Nonempty →
      (∀ a ∈ A, |a.1| ≤ 1 ∧ |a.2| ≤ 1) →
      (∀ b ∈ B, |b.1| ≤ 1 ∧ |b.2| ≤ 1) → (∀ c ∈ C, |c| ≤ 1) →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ((2 : ℝ) ^ n)⁻¹ / 2 ≤ ‖a - b‖) →
      G ⊆ A ×ˢ (B ×ˢ C) → beta * A.card * (B ×ˢ C).card ≤ (G.card : ℝ) →
      ((G.image (fun e => roundPoint (((2 : ℝ) ^ n)⁻¹) (e.1 + productValue e.2))).card : ℝ) ≤ M * A.card →
      let delta : ℝ := ((2 : ℝ) ^ n)⁻¹
      let f := fun p => roundPoint (delta / 2) (productValue p)
      let alpha := sourceDensity (B ×ˢ C) beta M
      let r := alpha ^ K * delta ^ epsilon
      ∃ j < levelCount (B ×ˢ C), ∃ A' : Finset (ℝ × ℝ), ∃ F : Finset ((ℝ × ℝ) × ℝ),
        A' ⊆ A ∧ F ⊆ (B ×ˢ C) ∧ F ⊆ bin (B ×ˢ C) f j ∧
        (bin (B ×ˢ C) f j).Nonempty ∧
        (G.filter (fun e => level (B ×ˢ C) f e.2 = j)).Nonempty ∧
        r * A.card ≤ A'.card ∧
        (r * (beta ^ 2 / M) / (196 * (levelCount (B ×ˢ C) : ℝ))) * (B ×ˢ C).card ≤ F.card ∧
        (∀ p ∈ F, ∀ q ∈ (B ×ˢ C), f q = f p → q ∈ F) ∧
        (((A' + F.image productValue - F.image productValue).image (roundPoint (delta / 2))).card : ℝ) ≤
          49 * (delta ^ (-2 * epsilon) / alpha ^ (2 * K)) * A.card := by
  obtain ⟨K, n0, hK, hmain⟩ := original_vector_graph_dyadic_bsg (W := (ℝ × ℝ) × ℝ) hepsilon
  refine ⟨K, n0, hK, ?_⟩
  intro n hn beta M hb hM A B C G hA hB hC hAbound hBbound hCbound hsep hG hdense hcover
  exact hmain n hn beta M hb hM A (B ×ˢ C) productValue G hA (hB.product hC)
    hAbound (original_product_value_box B C hBbound hCbound) hsep hG hdense hcover

end VectorOriginalGraphBSG
