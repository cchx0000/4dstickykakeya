import Theorems.Thm_StickyKakeya4_native_contact_fractional_composition
import Theorems.Thm_StickyKakeya4_tube_perturbation_grid_transfer
import Theorems.Thm_StickyKakeya4_euclidean_alignment_patches

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace NativeSeparatedFractionalPatches

open ShearedGridADReference ShearedGridTubeReference ShearedGridSpineColumns
open NativeContactSpineColumns NativeContactFractionalComposition NativeFractionalReferenceComposition
open SmallFiberAlignment FractionalFiberAlignment SelfUniform
open ActualTubeFootprintProfiles (TubeData InTube)
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

def quantized (μ α : ℝ) (p : Point) : Point := realized μ α (vertex μ α p)

lemma pairPoint_dist (p q : Point) : dist (pairPoint p) (pairPoint q) = dist p q := by
  apply le_antisymm
  · rw [Prod.dist_eq]
    apply max_le
    · exact dist_le_pi_dist p q 0
    · apply (dist_pi_le_iff dist_nonneg).mpr
      intro i
      exact dist_le_pi_dist p q 1
  · apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    fin_cases i
    · exact (le_max_left _ _ : dist (p 0) (q 0) ≤ max (dist (p 0) (q 0)) (dist (pairPoint p).2 (pairPoint q).2))
    · exact (dist_le_pi_dist (pairPoint p).2 (pairPoint q).2 0).trans (le_max_right _ _)

lemma pairPoint_injective : Function.Injective pairPoint := by
  intro p q h
  have hd : dist p q = 0 := by rw [← pairPoint_dist, h, dist_self]
  exact dist_eq_zero.mp hd

lemma pairPoint_realized (μ α : ℝ) (k : Vertex) :
    pairPoint (realized μ α k) = SeparatedAlignmentPatches.realize μ (fun _ : Fin 1 => α) k := by
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i
    rfl

lemma pairPoint_quantized (μ α : ℝ) (p : Point) :
    pairPoint (quantized μ α p) =
      SeparatedAlignmentPatches.quantize μ (fun _ : Fin 1 => α) (pairPoint p) :=
  pairPoint_realized μ α (vertex μ α p)

lemma quantized_coordinate_movement (μ α : ℝ) (hμ : 0 < μ) (p : Point) (i : Fin 2) :
    |quantized μ α p i - p i| < μ := by
  have hm := coordinate_movement μ α hμ p
  rw [abs_sub_comm]
  fin_cases i
  · exact (abs_of_nonneg hm.1.1).trans_lt hm.1.2
  · exact (abs_of_nonneg hm.2.1).trans_lt hm.2.2

lemma quantized_euclidean_movement (μ α : ℝ) (hμ : 0 < μ) (p : Point) :
    dist (EuclideanAlignmentPatches.euclidean p)
      (EuclideanAlignmentPatches.euclidean (quantized μ α p)) < (64 * μ) / 10 := by
  have hm := EuclideanAlignmentPatches.euclidean_dist_le_card_mul p (quantized μ α p) μ hμ.le
    (fun i => by simpa only [abs_sub_comm] using (quantized_coordinate_movement μ α hμ p i).le)
  norm_num at hm
  linarith only [hm, hμ]

/-- The residue is chosen by ORIGINAL point mass. Collapsed quantizer fibers
remain honest preimages; injectivity of the source quantizer is not required. -/
theorem exists_separated_source_residue (Ω : Finset Point) (μ α : ℝ)
    (hμ : 0 < μ) (hne : Ω.Nonempty) :
    ∃ Ω₀ ⊆ Ω, Ω₀.Nonempty ∧ Ω.card ≤ 64 ^ 2 * Ω₀.card ∧
      ∀ p ∈ Ω₀.image (quantized μ α), ∀ q ∈ Ω₀.image (quantized μ α), p ≠ q →
        64 * μ ≤ dist p q := by
  classical
  obtain ⟨Ω₀, hsub, hmass, _hf, _hb, hsep⟩ :=
    SeparatedAlignmentPatches.weighted_quantized_residue Ω (fun _ => 1) pairPoint μ hμ
      (fun _ : Fin 1 => α) 64 (by norm_num)
  have hret : Ω.card ≤ 64 ^ 2 * Ω₀.card := by simpa using hmass
  have hne₀ : Ω₀.Nonempty := by
    apply Finset.card_pos.mp
    have hpos := hne.card_pos
    by_contra h
    have hz : Ω₀.card = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.mul_zero] at hret
    omega
  refine ⟨Ω₀, hsub, hne₀, hret, ?_⟩
  intro p hp q hq hpq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
  have hpx : pairPoint (quantized μ α x) ∈ Ω₀.image
      (fun x => SeparatedAlignmentPatches.quantize μ (fun _ : Fin 1 => α) (pairPoint x)) := by
    rw [pairPoint_quantized]
    exact Finset.mem_image_of_mem _ hx
  have hpy : pairPoint (quantized μ α y) ∈ Ω₀.image
      (fun x => SeparatedAlignmentPatches.quantize μ (fun _ : Fin 1 => α) (pairPoint x)) := by
    rw [pairPoint_quantized]
    exact Finset.mem_image_of_mem _ hy
  have hh := hsep _ hpx _ hpy (fun he => hpq (pairPoint_injective he))
  simpa only [pairPoint_dist, Nat.cast_ofNat, mul_comm] using hh

/-- Every later restriction keeps two-way proximity to its OWN actual image. -/
lemma quantized_image_proximity (Ω : Finset Point) (μ α : ℝ) (hμ : 0 < μ) :
    (∀ p ∈ Ω, ∃ q ∈ Ω.image (quantized μ α),
      dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q) < (64 * μ) / 10) ∧
    (∀ q ∈ Ω.image (quantized μ α), ∃ p ∈ Ω,
      dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q) < (64 * μ) / 10) := by
  constructor
  · intro p hp
    exact ⟨_, Finset.mem_image_of_mem _ hp, quantized_euclidean_movement μ α hμ p⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨p, hp, quantized_euclidean_movement μ α hμ p⟩

/-- Literal whole-parent Euclidean neighborhoods of the retained ORIGINAL
source. The right side is the final source patch before periodic isolation. -/
theorem isolate_original_parent_patches (F : Finset Point) {b : ℝ} (hb : 0 < b) :
    ∃ A' ⊆ F, F.card ≤ 260 ^ 2 * A'.card ∧
      ∀ p ∈ A',
        A'.filter (fun q => dist (EuclideanAlignmentPatches.euclidean q)
          (EuclideanAlignmentPatches.euclidean p) < 64 * b) =
        F.filter (fun q => ADGridCoverMenus.gridLabel b q = ADGridCoverMenus.gridLabel b p) := by
  obtain ⟨A', hsub, hmass, hpatch⟩ := EuclideanAlignmentPatches.euclidean_periodic_patch_at_multiplier
    F (fun _ => 1) id b hb 64 (by norm_num)
  refine ⟨A', hsub, ?_, ?_⟩
  · simpa using hmass
  · intro p hp
    apply Finset.ext
    intro q
    have hh := Finset.ext_iff.mp (hpatch p hp) q
    have he : ∀ x : Point, SeparatedAlignmentPatches.cell b x = ADGridCoverMenus.gridLabel b x := fun _ => rfl
    simpa only [Finset.mem_filter, id_eq, Nat.cast_ofNat, he] using hh

/-- Actual residue choice precedes fractional refinement, so the retained original
source has a separated physical image with two-way Euclidean proximity. -/
theorem exists_native_separated_fractional_refinement {d Q L : ℕ}
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
    ∃ Ω₀ ⊆ Ω, Ω₀.Nonempty ∧ Ω.card ≤ 64 ^ 2 * Ω₀.card ∧
      ∃ U : ℕ, 0 < U ∧ (U : ℝ) ≤ 2 * K * ((64 * μ) / δ) ^ t ∧
      0 < density Ω₀ U N t ∧
      (∀ z : Vertex, mass (fun _ : Point => 1) (Ω₀.filter (fun p => vertex μ α p = z)) ≤ U) ∧
      ∃ Ω' ⊆ Ω₀, Ω'.Nonempty ∧
        Ω.card ≤ (64 ^ 2 * retentionCost (d + (d + 1)) L) * Ω'.card ∧
        RefinedCounts (Ω'.image (vertex μ α)) R N Q L t s (density Ω₀ U N t)
          (adConstant K t) (contactColumnConstant C K H t ell) (tubeConstant H) ∧
        (∀ p ∈ Ω'.image (quantized μ α), ∀ q ∈ Ω'.image (quantized μ α), p ≠ q →
          64 * μ ≤ dist p q) ∧
        (∀ p ∈ Ω', ∃ q ∈ Ω'.image (quantized μ α),
          dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q) < (64 * μ) / 10) ∧
        (∀ q ∈ Ω'.image (quantized μ α), ∃ p ∈ Ω',
          dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q) < (64 * μ) / 10) := by
  classical
  obtain ⟨Ω₀, hΩ₀, hne₀, hresidue, hseparated⟩ := exists_separated_source_residue Ω μ α hμ hne
  obtain ⟨U, hU, hUb, hden, hcap, Ω', hsub, hne', hret, hcounts⟩ :=
    exists_native_contact_fractional_refinement A E₀ E Ω₀ δ μ α x₀ b ρ τ γ K H t s ell S T C N R
      hQ hne₀ ((Finset.card_le_card hΩ₀).trans hheight) hδ hμ hδa hab hb hρ hρa hα hγ hangle
      (hΩ₀.trans hΩ) hE hEA hparent hEdiam (fun q hq => hS q (hΩ₀ hq))
      (fun q hq => hrich q (hΩ₀ hq)) (fun q hq => hchart q (hΩ₀ hq))
      (fun q hq => hslope q (hΩ₀ hq)) (fun q hq => hcontact q (hΩ₀ hq))
      (fun q hq => htube q (hΩ₀ hq)) hH hell hprofile hwide hshort hK ht ht2 hs hst hdiam hAD hNscale hR
  refine ⟨Ω₀, hΩ₀, hne₀, hresidue, U, hU, hUb, hden, hcap, Ω', hsub, hne', ?_, hcounts, ?_,
    (quantized_image_proximity Ω' μ α hμ).1, (quantized_image_proximity Ω' μ α hμ).2⟩
  · exact hresidue.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (64 ^ 2) hret)
  · intro p hp q hq hpq
    exact hseparated p (Finset.image_subset_image hsub hp) q (Finset.image_subset_image hsub hq) hpq

end
end NativeSeparatedFractionalPatches
