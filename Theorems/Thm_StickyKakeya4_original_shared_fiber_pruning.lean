import Theorems.Thm_StickyKakeya4_original_separated_packing

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalSharedFiberPruning

def fiber {X Y : Type*} [DecidableEq Y] (P : Finset X) (f : X → Y) (y : Y) : Finset X :=
  P.filter (fun p => f p=y)

def rich {X Y : Type*} [DecidableEq Y] (P : Finset X) (f : X → Y) (m : ℝ) : Finset X :=
  P.filter (fun p => m ≤ (fiber P f (f p)).card)

lemma rich_subset {X Y : Type*} [DecidableEq Y] (P : Finset X) (f : X → Y) (m : ℝ) :
    rich P f m ⊆ P := Finset.filter_subset _ _

/-- The discarded original points are bounded by the threshold times the
number of original occupied classes. -/
theorem original_light_fiber_budget {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (P : Finset X) (f : X → Y) {m : ℝ} (hm : 0 ≤ m) :
    ((P \ rich P f m).card : ℝ) ≤ m*(P.image f).card := by
  let L := P \ rich P f m
  have hLP : L ⊆ P := Finset.sdiff_subset
  have hfiber : ∀ y∈L.image f, ((L.filter (fun p => f p=y)).card : ℝ) ≤ m := by
    intro y hy
    obtain ⟨p,hp,hpy⟩ := Finset.mem_image.mp hy
    obtain ⟨hpP,hpnot⟩ := Finset.mem_sdiff.mp hp
    have hthin : ((fiber P f (f p)).card : ℝ) < m := by
      apply lt_of_not_ge
      intro h
      exact hpnot (Finset.mem_filter.mpr ⟨hpP,h⟩)
    rw [hpy] at hthin
    have hsub : L.filter (fun p => f p=y) ⊆ fiber P f y :=
      Finset.filter_subset_filter _ hLP
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hthin.le
  have hc := OriginalSeparatedPacking.card_le_real_mul_image L f hfiber
  have hi : ((L.image f).card : ℝ) ≤ (P.image f).card :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hLP))
  exact hc.trans (mul_le_mul_of_nonneg_left hi hm)

/-- A selected label charges its entire original fiber, even after a second
restriction removes some representatives of that fiber. -/
theorem original_rich_label_charge {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (P : Finset X) (f : X → Y) (m : ℝ) (S : Finset Y)
    (hS : S ⊆ (rich P f m).image f) :
    m*(S.card : ℝ) ≤ (P.filter (fun p => f p∈S)).card := by
  have hlower : ∀ y∈S, m ≤ ((fiber P f y).card : ℝ) := by
    intro y hy
    obtain ⟨p,hp,hpy⟩ := Finset.mem_image.mp (hS hy)
    have hh := (Finset.mem_filter.mp hp).2
    simpa only [hpy] using hh
  calc
    _ = ∑ _y∈S, m := by simp [mul_comm]
    _ ≤ ∑ y∈S, ((fiber P f y).card : ℝ) := Finset.sum_le_sum hlower
    _ = _ := by
      unfold fiber
      exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter P S f

/-- Original fiber charging for any queried family of retained labels. -/
theorem original_rich_window_charge {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (P R : Finset X) (f : X → Y) (m : ℝ) (pred : Y → Prop) [DecidablePred pred]
    (hR : R ⊆ rich P f m) :
    m*(((R.image f).filter pred).card : ℝ) ≤ (P.filter (fun p => pred (f p))).card := by
  have hlabels : (R.image f).filter pred ⊆ (rich P f m).image f :=
    (Finset.filter_subset _ _).trans (Finset.image_subset_image hR)
  have hc := original_rich_label_charge P f m ((R.image f).filter pred) hlabels
  have hsub : P.filter (fun p => f p∈(R.image f).filter pred) ⊆
      P.filter (fun p => pred (f p)) := by
    intro p hp
    obtain ⟨hpP,hpS⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpP,(Finset.mem_filter.mp hpS).2⟩
  exact hc.trans (Nat.cast_le.mpr (Finset.card_le_card hsub))

/-- One shared source pruning protects every original subquery. Its loss is
charged to original point mass, rather than separately to alphabet populations. -/
theorem original_two_fiber_query_retention {X Y Z : Type*}
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (P Q : Finset X) (f : X → Y) (g : X → Z) {m : ℝ}
    (hm : 0 ≤ m) (hQP : Q ⊆ P) :
    (Q.card : ℝ) ≤ (Q ∩ (rich P f m ∩ rich P g m)).card +
      m*((P.image f).card+(P.image g).card) := by
  let R := rich P f m ∩ rich P g m
  have hsub : Q \ R ⊆ (P \ rich P f m) ∪ (P \ rich P g m) := by
    intro p hp
    obtain ⟨hpQ,hpnot⟩ := Finset.mem_sdiff.mp hp
    by_cases hf : p∈rich P f m
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨hQP hpQ,fun hg => hpnot (Finset.mem_inter.mpr ⟨hf,hg⟩)⟩
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hQP hpQ,hf⟩)
  have hdelN := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hdel : ((Q \ R).card : ℝ) ≤ (P \ rich P f m).card+(P \ rich P g m).card := by
    exact_mod_cast hdelN
  have hf := original_light_fiber_budget P f hm
  have hg := original_light_fiber_budget P g hm
  have hsplit : ((Q \ R).card : ℝ)+(Q ∩ R).card=Q.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter Q R
  change (Q.card : ℝ) ≤ (Q∩R).card + _
  nlinarith only [hdel,hf,hg,hsplit]

end OriginalSharedFiberPruning
