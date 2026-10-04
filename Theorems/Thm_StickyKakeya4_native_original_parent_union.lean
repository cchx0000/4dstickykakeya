import Theorems.Thm_StickyKakeya4_native_selected_parent_preparation

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace NativeOriginalParentUnion

open NativeOriginalParentAssembly NativeParentRefinement NativeSelectedParentPreparation
open NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeParentSpines NativeAngularChartSelection
open ActualTubeFootprintProfiles NativeSeparatedFractionalPatches SmallFiberAlignment
open NativeFractionalReferenceComposition
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pullback through the injective chart only. No quantizer inverse is used. -/
def originalPullback (A : Finset Plane) (j : Fin 2) (F : Finset Plane) : Finset A :=
  Finset.univ.filter (fun q => chartPosition A j q ∈ F)

lemma originalPullback_image (A : Finset Plane) (j : Fin 2) (F : Finset Plane)
    (hF : F ⊆ A.image (chartPoint j)) :
    (originalPullback A j F).image (chartPosition A j) = F := by
  ext p
  constructor
  · rintro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hq).2
  · intro hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp (hF hp)
    refine Finset.mem_image.mpr ⟨⟨q, hq⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hqp⟩
    change chartPoint j q ∈ F
    rwa [hqp]

lemma originalPullback_subset (A : Finset Plane) (j : Fin 2) (F : Finset Plane) (S : Finset A)
    (hF : F ⊆ S.image (chartPosition A j)) : originalPullback A j F ⊆ S := by
  intro q hq
  obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp (hF (Finset.mem_filter.mp hq).2)
  have he := chartPosition_injective A j heq
  exact he ▸ hr

lemma originalPullback_card (A : Finset Plane) (j : Fin 2) (F : Finset Plane)
    (hF : F ⊆ A.image (chartPoint j)) : (originalPullback A j F).card = F.card := by
  calc
    _ = ((originalPullback A j F).image (chartPosition A j)).card :=
      (Finset.card_image_of_injective _ (chartPosition_injective A j)).symm
    _ = F.card := congrArg Finset.card (originalPullback_image A j F hF)

/-- Gluing disjoint ORIGINAL parents preserves the sum of their original
point populations and recovers every parent exactly. -/
theorem glue_parent_subsets (A : Finset Plane) (Ω : Finset A) (b : ℝ)
    (G : GridLabel 1 → Finset A) (C : ℕ)
    (hG : ∀ c, G c ⊆ parent A Ω b c)
    (hret : ∀ c, (parent A Ω b c).card ≤ C * (G c).card) :
    ∃ F ⊆ Ω, Ω.card ≤ C * F.card ∧ ∀ c, parent A F b c = G c := by
  let menu := Ω.image (grid (position A) b)
  let F := menu.biUnion G
  have hsub : F ⊆ Ω := by
    intro q hq
    obtain ⟨c, _hc, hq⟩ := Finset.mem_biUnion.mp hq
    exact (parent_subset A Ω b c) (hG c hq)
  have hparents : ∀ c, parent A F b c = G c := by
    intro c
    ext q
    constructor
    · intro hq
      obtain ⟨hqF, hqc⟩ := Finset.mem_filter.mp hq
      obtain ⟨k, _hk, hqG⟩ := Finset.mem_biUnion.mp hqF
      have hqk := (Finset.mem_filter.mp (hG k hqG)).2
      have hkc : k = c := hqk.symm.trans hqc
      exact hkc ▸ hqG
    · intro hq
      have hqΩ := (parent_subset A Ω b c) (hG c hq)
      have hqc := (Finset.mem_filter.mp (hG c hq)).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨c, ?_, hq⟩, hqc⟩
      exact Finset.mem_image.mpr ⟨q, hqΩ, hqc⟩
  refine ⟨F, hsub, ?_, hparents⟩
  have hsum : F.card = ∑ c ∈ menu, (G c).card := by
    apply Finset.card_biUnion
    intro c _hc d _hd hcd
    apply Finset.disjoint_left.mpr
    intro q hqc hqd
    exact hcd ((Finset.mem_filter.mp (hG c hqc)).2.symm.trans (Finset.mem_filter.mp (hG d hqd)).2)
  calc
    Ω.card = ∑ c ∈ menu, (parent A Ω b c).card := Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ c ∈ menu, C * (G c).card := Finset.sum_le_sum (fun c _hc => hret c)
    _ = C * F.card := by rw [← Finset.mul_sum, hsum]

/-- The final periodic cut retains entire constructed parents. Its balls are
literal original-source Euclidean balls; source labels are never collapsed. -/
theorem isolate_labelled_parents (A : Finset Plane) (F : Finset A) {b : ℝ} (hb : 0 < b) :
    ∃ A' ⊆ F, F.card ≤ 260 ^ 2 * A'.card ∧
      ∀ p ∈ A', A'.filter (fun q =>
        dist (EuclideanAlignmentPatches.euclidean (position A q))
          (EuclideanAlignmentPatches.euclidean (position A p)) < 64 * b) =
        parent A F b (grid (position A) b p) := by
  obtain ⟨A', hsub, hret, hpatch⟩ := EuclideanAlignmentPatches.euclidean_periodic_patch_at_multiplier
    F (fun _ => 1) (position A) b hb 64 (by norm_num)
  refine ⟨A', hsub, ?_, ?_⟩
  · simpa using hret
  · intro p hp
    exact hpatch p hp

/-- All constructed parent refinements are glued and isolated on original
point labels, with an explicit multiplication of the four retention losses. -/
theorem Selection.retain_original_points {A : Finset Plane} {δ ε K t : ℝ} {Nold : ℕ} {E₀ : Finset A}
    {D : StoppedProfile (position A) δ ε K t Nold E₀} {j : Fin 2} {m Q₁ L₁ Q₂ L₂ Hwork : ℕ}
    (S : Selection A D j m Q₁ L₁ Q₂ L₂ Hwork) (hδ : 0 < δ) :
    let ia := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m S.index
    let ib := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (S.index + 1)
    let b := scale δ ib
    let μ := scale δ ia / 64
    let R := ActualScalarADProfiles.workingRadii (ib - ia + 6) Hwork
    let N := 2 ^ (ib - ia + 6)
    ∃ F ⊆ S.points, ∃ A' ⊆ F, A'.Nonempty ∧
      A.card ≤ (epochCost A Nold * refinementCost (m + 1) L₁ * Q₁ ^ 2 * Q₁ ^ 2 *
        angularCost D.pair.1 D.pair.2 m * (64 ^ 2 * retentionCost ((Hwork + 1) + ((Hwork + 1) + 1)) L₂) * 260 ^ 2) * A'.card ∧
      ∀ p ∈ A', ∃ G : RefinedParent ((parent A S.points b (grid (position A) b p)).image (chartPosition A j))
        μ (S.angle (grid (position A) b p)) R N Q₂ L₂ δ K t D.exponent D.loss
        (spineConstant Nold (m + 1) Q₁ L₁ K t D.loss),
        (parent A F b (grid (position A) b p)).image (chartPosition A j) = G.points ∧
        (A'.filter (fun q => dist (EuclideanAlignmentPatches.euclidean (position A q))
          (EuclideanAlignmentPatches.euclidean (position A p)) < 64 * b)).image (chartPosition A j) = G.points := by
  classical
  dsimp only
  let ia := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m S.index
  let ib := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (S.index + 1)
  let b := scale δ ib
  let μ := scale δ ia / 64
  let R := ActualScalarADProfiles.workingRadii (ib - ia + 6) Hwork
  let N := 2 ^ (ib - ia + 6)
  let ell := spineConstant Nold (m + 1) Q₁ L₁ K t D.loss
  let selected (c : GridLabel 1) (hc : (parent A S.points b c).Nonempty) :
      RefinedParent ((parent A S.points b c).image (chartPosition A j))
        μ (S.angle c) R N Q₂ L₂ δ K t D.exponent D.loss ell := Classical.choice (S.refined c hc)
  let G (c : GridLabel 1) : Finset A := if hc : (parent A S.points b c).Nonempty then
    originalPullback A j (selected c hc).points else ∅
  have hpointsub (c : GridLabel 1) (hc : (parent A S.points b c).Nonempty) :
      (selected c hc).points ⊆ (parent A S.points b c).image (chartPosition A j) :=
    (selected c hc).subset.trans (selected c hc).residue_subset
  have hpointA (c : GridLabel 1) (hc : (parent A S.points b c).Nonempty) :
      (selected c hc).points ⊆ A.image (chartPoint j) := by
    intro q hq
    obtain ⟨r, _hr, rfl⟩ := Finset.mem_image.mp (hpointsub c hc hq)
    exact chartPosition_mem A j r
  have hG (c : GridLabel 1) : G c ⊆ parent A S.points b c := by
    by_cases hc : (parent A S.points b c).Nonempty
    · simpa only [G, dif_pos hc] using originalPullback_subset A j _ _ (hpointsub c hc)
    · simp only [G, dif_neg hc, Finset.empty_subset]
  let C := 64 ^ 2 * retentionCost ((Hwork + 1) + ((Hwork + 1) + 1)) L₂
  have hret (c : GridLabel 1) : (parent A S.points b c).card ≤ C * (G c).card := by
    by_cases hc : (parent A S.points b c).Nonempty
    · have h := (selected c hc).retained
      rw [Finset.card_image_of_injective _ (chartPosition_injective A j)] at h
      simpa only [G, dif_pos hc, originalPullback_card A j _ (hpointA c hc)] using h
    · rw [Finset.not_nonempty_iff_eq_empty.mp hc, Finset.card_empty]
      exact Nat.zero_le _
  obtain ⟨F, hF, hretF, hparents⟩ := glue_parent_subsets A S.points b G C hG hret
  obtain ⟨A', hA', hretA', hpatch⟩ := isolate_labelled_parents A F (scale_pos hδ ib)
  have htotal : A.card ≤ (epochCost A Nold * refinementCost (m + 1) L₁ * Q₁ ^ 2 * Q₁ ^ 2 *
      angularCost D.pair.1 D.pair.2 m * C * 260 ^ 2) * A'.card := by
    have h₁ := Nat.mul_le_mul_left (epochCost A Nold * refinementCost (m + 1) L₁ * Q₁ ^ 2 * Q₁ ^ 2 *
      angularCost D.pair.1 D.pair.2 m) hretF
    have h₂ := Nat.mul_le_mul_left (epochCost A Nold * refinementCost (m + 1) L₁ * Q₁ ^ 2 * Q₁ ^ 2 *
      angularCost D.pair.1 D.pair.2 m * C) hretA'
    exact S.retained.trans (h₁.trans (by simpa only [Nat.mul_assoc] using h₂))
  have hne : A'.Nonempty := by
    apply Finset.card_pos.mp
    have hA : 0 < A.card := by
      have hScard : 0 < S.points.card := S.nonempty.card_pos
      have hh := Finset.card_le_card (Finset.subset_univ S.points)
      simp only [source_card] at hh
      omega
    by_contra hn
    have hz : A'.card = 0 := by omega
    rw [hz, Nat.mul_zero] at htotal
    omega
  refine ⟨F, hF, A', hA', hne, htotal, ?_⟩
  intro q hq
  let c := grid (position A) b q
  have hc : (parent A S.points b c).Nonempty := ⟨q, Finset.mem_filter.mpr ⟨hF (hA' hq), rfl⟩⟩
  refine ⟨selected c hc, ?_, ?_⟩
  · rw [hparents c]
    simpa only [G, dif_pos hc] using originalPullback_image A j _ (hpointA c hc)
  · rw [hpatch q hq, hparents c]
    simpa only [G, dif_pos hc] using originalPullback_image A j _ (hpointA c hc)

end
end NativeOriginalParentUnion
