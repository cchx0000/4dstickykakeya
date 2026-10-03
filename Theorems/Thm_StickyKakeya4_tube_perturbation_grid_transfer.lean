import Theorems.Thm_StickyKakeya4_tube_expansion_cover

set_option autoImplicit false
set_option warningAsError true

namespace TubePerturbationGridTransfer

open ActualTubeFootprintProfiles FiniteCoverProfileEpochs TubeExpansionCover
noncomputable section

lemma close_floor_labels {x y rho : ℝ} (hrho : 0 < rho)
    (hxy : |x - y| ≤ rho) : |⌊x / rho⌋ - ⌊y / rho⌋| ≤ (1 : ℤ) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hxy
  have hupper : x / rho ≤ y / rho + 1 := by
    apply (div_le_iff₀ hrho).mpr
    have heq : (y / rho + 1) * rho = y + rho := by field_simp
    rw [heq]
    linarith
  have hlower : y / rho ≤ x / rho + 1 := by
    apply (div_le_iff₀ hrho).mpr
    have heq : (x / rho + 1) * rho = x + rho := by field_simp
    rw [heq]
    linarith
  have hu' := Int.floor_mono hupper
  have hl' := Int.floor_mono hlower
  simp only [Int.floor_add_one] at hu' hl'
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- Every moved grid cell has a literal neighboring original cell. -/
lemma moved_grid_in_box {alpha : Type*} {d : ℕ} (p q : alpha → Point d)
    {rho : ℝ} (hrho : 0 < rho) (a : alpha)
    (hmove : ∀ i, |q a i - p a i| ≤ rho) :
    grid q rho a ∈ GridQuotientAD.box (grid p rho a) 1 := by
  apply (GridQuotientAD.mem_box_iff _ _ 1).mpr
  intro i
  exact close_floor_labels hrho (hmove i)

/-- A bounded movement upper bound transfers ACTUAL occupied-cell counts.
No injectivity, disjointness or covering certificate is required. -/
theorem moved_grid_card_le {alpha : Type*} [DecidableEq alpha] {d : ℕ}
    (p q : alpha → Point d) (S : Finset alpha) {rho : ℝ} (hrho : 0 < rho)
    (hmove : ∀ a ∈ S, ∀ i, |q a i - p a i| ≤ rho) :
    (S.image (grid q rho)).card ≤ 3 ^ (d + 1) * (S.image (grid p rho)).card := by
  classical
  have hsub : S.image (grid q rho) ⊆
      (S.image (grid p rho)).biUnion (fun k => GridQuotientAD.box k 1) := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_biUnion.mpr ⟨grid p rho a, Finset.mem_image_of_mem _ ha,
      moved_grid_in_box p q hrho a (hmove a ha)⟩
  calc
    (S.image (grid q rho)).card ≤
        ((S.image (grid p rho)).biUnion (fun k => GridQuotientAD.box k 1)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ k ∈ S.image (grid p rho), (GridQuotientAD.box k 1).card := Finset.card_biUnion_le
    _ = 3 ^ (d + 1) * (S.image (grid p rho)).card := by
      simp [GridQuotientAD.box_card, Nat.mul_comm]

/-- Point motion increases only tube width; the actual segment parameter and
its length window stay unchanged. -/
lemma moved_tube_pullback {d : ℕ} (T : TubeData d) (p q : Point d)
    {rho tau eps : ℝ} (hmove : ∀ i, |q i - p i| ≤ eps)
    (hq : InTube T rho tau q) : InTube T (rho + eps) tau p := by
  obtain ⟨s, hs, he⟩ := hq
  refine ⟨s, hs, ?_⟩
  intro i
  have hid : p i - T.center i - s * T.direction i =
      (q i - T.center i - s * T.direction i) + (p i - q i) := by ring
  rw [hid]
  refine (abs_add_le _ _).trans (add_le_add (he i) ?_)
  simpa only [abs_sub_comm] using hmove i

/-- The new tube's original-label preimage is controlled by the SAME original
source's thin-tube profile. This is the quantified tube-KT transport used after
quantization, rather than an assertion that subset bounds survive motion. -/
theorem moved_tube_le_original_profile {alpha : Type*} [Fintype alpha]
    [DecidableEq alpha] {d : ℕ} (p q : alpha → Point d) (E : Finset alpha)
    (T : TubeData d) {rho tau : ℝ} (hrho : 0 < rho)
    (hmove : ∀ a ∈ E, ∀ i, |q a i - p a i| ≤ rho) :
    coverCount (grid q rho) E (trace q rho tau T) ≤
      15 ^ (d + 1) * (footprints p rho tau).sup (fun W => coverCount (grid p rho) E W) := by
  classical
  let S := E ∩ trace q rho tau T
  have hSE : S ⊆ E := Finset.inter_subset_left
  have hsub : S ⊆ E ∩ trace p ((2 : ℝ) * rho) tau T := by
    intro a ha
    obtain ⟨haE, haT⟩ := Finset.mem_inter.mp ha
    refine Finset.mem_inter.mpr ⟨haE, (mem_trace p _ _ T a).mpr ?_⟩
    have h := moved_tube_pullback T (p a) (q a) (hmove a haE)
      ((mem_trace q _ _ T a).mp haT)
    simpa only [two_mul] using h
  have hgrid := moved_grid_card_le p q S hrho (fun a ha => hmove a (hSE ha))
  have hprofile := expanded_tube_le_actual_profile p (grid p rho) E T (tau := tau) hrho 2
  calc
    coverCount (grid q rho) E (trace q rho tau T) ≤
        3 ^ (d + 1) * (S.image (grid p rho)).card := hgrid
    _ ≤ 3 ^ (d + 1) * coverCount (grid p rho) E (trace p ((2 : ℝ) * rho) tau T) :=
      Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.image_subset_image hsub))
    _ ≤ 3 ^ (d + 1) * ((2 * 2 + 1) ^ (d + 1) *
        (footprints p rho tau).sup (fun W => coverCount (grid p rho) E W)) :=
      Nat.mul_le_mul_left _ hprofile
    _ = _ := by rw [← mul_assoc, ← mul_pow]; norm_num

end
end TubePerturbationGridTransfer
