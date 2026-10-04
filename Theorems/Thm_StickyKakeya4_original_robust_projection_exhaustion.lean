import Theorems.Thm_StickyKakeya4_original_disjoint_support_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalRobustProjectionExhaustion
variable {X : Type*} [DecidableEq X]

/-- Repeated local extraction is represented by a maximal family of
disjoint ACTUAL original subsets. Its uncovered source is smaller than the
prescribed cutoff, independent of the number of selected pieces. -/
theorem exists_original_local_exhaustion (P : Finset X) (cutoff : ℝ)
    (Valid : Finset X → Prop)
    (hlocal : ∀ R : Finset X, R⊆P → cutoff≤(R.card:ℝ) →
      ∃ F : Finset X, F⊆R ∧ F.Nonempty ∧ Valid F) :
    ∃ Pieces : Finset (Finset X),
      (Pieces : Set (Finset X)).PairwiseDisjoint id ∧
      (∀ F∈Pieces, F⊆P ∧ F.Nonempty ∧ Valid F) ∧
      (((P \ Pieces.biUnion id).card):ℝ)<cutoff := by
  let I := P.powerset.filter (fun F => F.Nonempty ∧ Valid F)
  have hne : ∀ F∈I, (id F).Nonempty := by
    intro F hF
    exact (Finset.mem_filter.mp hF).2.1
  obtain ⟨Pieces,hPI,hdis,hcover⟩ :=
    OriginalDisjointSupportSelection.exists_maximal_disjoint_original_supports I id hne
  have hpieces : ∀ F∈Pieces, F⊆P ∧ F.Nonempty ∧ Valid F := by
    intro F hF
    obtain ⟨hFP,hFne,hFvalid⟩ := Finset.mem_filter.mp (hPI hF)
    exact ⟨Finset.mem_powerset.mp hFP,hFne,hFvalid⟩
  refine ⟨Pieces,hdis,hpieces,?_⟩
  by_contra h
  obtain ⟨F,hFR,hFne,hFV⟩ := hlocal (P \ Pieces.biUnion id) Finset.sdiff_subset (le_of_not_gt h)
  have hFI : F∈I := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (hFR.trans Finset.sdiff_subset),hFne,hFV⟩
  obtain ⟨G,hG,p,hp⟩ := hcover F hFI
  have hpF := (Finset.mem_inter.mp hp).1
  have hpG := (Finset.mem_inter.mp hp).2
  have hpnot := (Finset.mem_sdiff.mp (hFR hpF)).2
  exact hpnot (Finset.mem_biUnion.mpr ⟨G,hG,hpG⟩)

lemma original_disjoint_piece_mass (P : Finset X) (Pieces : Finset (Finset X))
    (hdis : (Pieces:Set (Finset X)).PairwiseDisjoint id)
    (hsub : ∀ F∈Pieces,F⊆P) :
    (∑ F∈Pieces,(F.card:ℝ))≤P.card := by
  have hc : ((Pieces.biUnion id).card:ℝ)=∑ F∈Pieces,(F.card:ℝ) := by
    exact_mod_cast Finset.card_biUnion (fun F hF G hG hne => hdis hF hG hne)
  rw [← hc]
  exact Nat.cast_le.mpr (Finset.card_le_card (by
    intro p hp
    obtain ⟨F,hF,hpF⟩ := Finset.mem_biUnion.mp hp
    exact hsub F hF hpF))

/-- Every original query is charged to its uncovered points and its
actual intersections with the selected original pieces. -/
theorem original_query_piece_mass (P Q : Finset X) (Pieces : Finset (Finset X))
    (hQP : Q⊆P) :
    (Q.card:ℝ)≤(P \ Pieces.biUnion id).card+∑ F∈Pieces,((Q∩F).card:ℝ) := by
  let U := Pieces.biUnion id
  have hres : Q \ U⊆P \ U := by
    intro p hp
    obtain ⟨hpQ,hpnot⟩ := Finset.mem_sdiff.mp hp
    exact Finset.mem_sdiff.mpr ⟨hQP hpQ,hpnot⟩
  have he : Q∩U=Pieces.biUnion (fun F => Q∩F) := by
    ext p
    simp only [U,Finset.mem_inter,Finset.mem_biUnion]
    constructor
    · rintro ⟨hpQ,F,hF,hpF⟩
      exact ⟨F,hF,hpQ,hpF⟩
    · rintro ⟨F,hF,hpQ,hpF⟩
      exact ⟨hpQ,F,hF,hpF⟩
  have hc : ((Q \ U).card:ℝ)+(Q∩U).card=Q.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter Q U
  have hi : ((Q∩U).card:ℝ)≤∑ F∈Pieces,((Q∩F).card:ℝ) := by
    rw [he]
    exact_mod_cast Finset.card_biUnion_le
  have hr : ((Q \ U).card:ℝ)≤(P \ U).card := Nat.cast_le.mpr (Finset.card_le_card hres)
  dsimp only [U] at hr hc hi
  linarith only [hr,hc,hi]

end OriginalRobustProjectionExhaustion
