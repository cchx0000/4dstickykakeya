import Mathlib
import Theorems.Thm_StickyKakeya4_two_tube_path_collision_count

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace RichWitnessCore

variable {Ω ν : Type*} [DecidableEq ν]

/-- Keep the ORIGINAL ordered labels whose two endpoints remain. -/
def retained (W : Finset Ω) (left right : Ω → ν) (S : Finset ν) : Finset Ω :=
  W.filter (fun w => left w ∈ S ∧ right w ∈ S)

def outgoing (U : Finset Ω) (left : Ω → ν) (v : ν) : Finset Ω :=
  U.filter (fun w => left w = v)

def incoming (U : Finset Ω) (right : Ω → ν) (v : ν) : Finset Ω :=
  U.filter (fun w => right w = v)

lemma retained_subset (W : Finset Ω) (left right : Ω → ν) (S : Finset ν) :
    retained W left right S ⊆ W := Finset.filter_subset _ _

lemma retained_eq_of_endpoints (W : Finset Ω) (left right : Ω → ν) (V : Finset ν)
    (hends : ∀ w ∈ W, left w ∈ V ∧ right w ∈ V) :
    retained W left right V = W := by
  apply Finset.Subset.antisymm (retained_subset W left right V)
  intro w hw
  exact Finset.mem_filter.mpr ⟨hw, hends w hw⟩

/-- The actual involution preserves the retained original labels. -/
lemma swap_mem_retained (W : Finset Ω) (left right : Ω → ν) (swap : Ω → Ω)
    (hW : ∀ w ∈ W, swap w ∈ W)
    (hends : ∀ w ∈ W, left (swap w) = right w ∧ right (swap w) = left w)
    (S : Finset ν) {w : Ω} (hw : w ∈ retained W left right S) :
    swap w ∈ retained W left right S := by
  obtain ⟨hwW, hl, hr⟩ := Finset.mem_filter.mp hw
  obtain ⟨hleft, hright⟩ := hends w hwW
  exact Finset.mem_filter.mpr ⟨hW w hwW, by rwa [hleft], by rwa [hright]⟩

/-- Incoming/outgoing symmetry is proved by the ORIGINAL witness swap,
including fixed points and loops. It is not a count-symmetry hypothesis. -/
theorem outgoing_card_eq_incoming (W : Finset Ω) (left right : Ω → ν) (swap : Ω → Ω)
    (hswap : Function.Involutive swap) (hW : ∀ w ∈ W, swap w ∈ W)
    (hends : ∀ w ∈ W, left (swap w) = right w ∧ right (swap w) = left w)
    (S : Finset ν) (v : ν) :
    (outgoing (retained W left right S) left v).card =
      (incoming (retained W left right S) right v).card := by
  apply Finset.card_bij (fun w _ => swap w)
  · intro w hw
    obtain ⟨hwS, hwv⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨swap_mem_retained W left right swap hW hends S hwS,
      (hends w (retained_subset W left right S hwS)).2.trans hwv⟩
  · intro w _ w' _ he
    exact hswap.injective he
  · intro w hw
    obtain ⟨hwS, hwv⟩ := Finset.mem_filter.mp hw
    refine ⟨swap w, Finset.mem_filter.mpr ⟨swap_mem_retained W left right swap hW hends S hwS,
      (hends w (retained_subset W left right S hwS)).1.trans hwv⟩, hswap w⟩

/-- Removing a vertex loses at most its outgoing plus incoming witnesses.
A loop belongs to their union and is removed once, so an inequality is used. -/
lemma erase_vertex_loss (W : Finset Ω) (left right : Ω → ν) (S : Finset ν) (v : ν) :
    (retained W left right S).card ≤
      (retained W left right (S.erase v)).card +
      (outgoing (retained W left right S) left v).card +
      (incoming (retained W left right S) right v).card := by
  classical
  have hsub : retained W left right S ⊆ retained W left right (S.erase v) ∪
      (outgoing (retained W left right S) left v ∪ incoming (retained W left right S) right v) := by
    intro w hw
    obtain ⟨hwW, hl, hr⟩ := Finset.mem_filter.mp hw
    by_cases hleft : left w = v
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hw, hleft⟩))
    · by_cases hright : right w = v
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hw, hright⟩))
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwW,
          Finset.mem_erase.mpr ⟨hleft, hl⟩, Finset.mem_erase.mpr ⟨hright, hr⟩⟩)
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hu := Finset.card_union_le
    (outgoing (retained W left right S) left v) (incoming (retained W left right S) right v)
  omega

/-- Maximize an integer potential over actual subsets of V. This constructs a
rich core with a linear original-witness loss and no logarithmic factor. -/
theorem exists_rich_core (W : Finset Ω) (V : Finset ν) (left right : Ω → ν)
    (swap : Ω → Ω) (hswap : Function.Involutive swap)
    (hW : ∀ w ∈ W, swap w ∈ W)
    (hends : ∀ w ∈ W, left (swap w) = right w ∧ right (swap w) = left w)
    (hV : ∀ w ∈ W, left w ∈ V ∧ right w ∈ V) (m : ℕ) :
    ∃ S ⊆ V,
      (∀ v ∈ S, m ≤ (outgoing (retained W left right S) left v).card) ∧
      W.card + 2 * m * S.card ≤ (retained W left right S).card + 2 * m * V.card ∧
      W.card ≤ (retained W left right S).card + 2 * m * V.card ∧
      W.card - 2 * m * V.card ≤ (retained W left right S).card := by
  classical
  let potential : Finset ν → ℤ := fun S =>
    ((retained W left right S).card : ℤ) - 2 * (m : ℤ) * (S.card : ℤ)
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image V.powerset potential
    ⟨∅, by simp⟩
  have hSV : S ⊆ V := Finset.mem_powerset.mp hS
  have hdegree : ∀ v ∈ S, m ≤ (outgoing (retained W left right S) left v).card := by
    intro v hv
    have herase := hmax (S.erase v)
      (Finset.mem_powerset.mpr ((Finset.erase_subset v S).trans hSV))
    have hcard : (S.erase v).card + 1 = S.card := Finset.card_erase_add_one hv
    have hcardZ : ((S.erase v).card : ℤ) + 1 = (S.card : ℤ) := by exact_mod_cast hcard
    have hloss := erase_vertex_loss W left right S v
    rw [← outgoing_card_eq_incoming W left right swap hswap hW hends S v] at hloss
    have hlossZ : ((retained W left right S).card : ℤ) ≤
        ((retained W left right (S.erase v)).card : ℤ) +
          2 * ((outgoing (retained W left right S) left v).card : ℤ) := by
      exact_mod_cast (show (retained W left right S).card ≤
        (retained W left right (S.erase v)).card +
          2 * (outgoing (retained W left right S) left v).card by omega)
    dsimp [potential] at herase
    have hdegreeZ : (m : ℤ) ≤ ((outgoing (retained W left right S) left v).card : ℤ) := by
      nlinarith
    exact_mod_cast hdegreeZ
  have hmaxV := hmax V (by simp)
  dsimp [potential] at hmaxV
  rw [retained_eq_of_endpoints W left right V hV] at hmaxV
  have hstrongZ : (W.card : ℤ) + 2 * (m : ℤ) * (S.card : ℤ) ≤
      ((retained W left right S).card : ℤ) + 2 * (m : ℤ) * (V.card : ℤ) := by omega
  have hstrong : W.card + 2 * m * S.card ≤
      (retained W left right S).card + 2 * m * V.card := by exact_mod_cast hstrongZ
  have hret : W.card ≤ (retained W left right S).card + 2 * m * V.card := by omega
  exact ⟨S, hSV, hdegree, hstrong, hret, by omega⟩

/-- A positive original witness set and the displayed finite budget construct
both a nonempty vertex core and a nonempty retained witness family of at least
half the ORIGINAL ordered labels. -/
theorem exists_half_mass_rich_core (W : Finset Ω) (V : Finset ν) (left right : Ω → ν)
    (swap : Ω → Ω) (hswap : Function.Involutive swap)
    (hW : ∀ w ∈ W, swap w ∈ W)
    (hends : ∀ w ∈ W, left (swap w) = right w ∧ right (swap w) = left w)
    (hV : ∀ w ∈ W, left w ∈ V ∧ right w ∈ V) (m : ℕ)
    (hbudget : 4 * m * V.card ≤ W.card) (hpositive : 0 < W.card) :
    ∃ S ⊆ V, S.Nonempty ∧ (retained W left right S).Nonempty ∧
      (∀ v ∈ S, m ≤ (outgoing (retained W left right S) left v).card) ∧
      W.card ≤ 2 * (retained W left right S).card ∧
      W.card - 2 * m * V.card ≤ (retained W left right S).card := by
  obtain ⟨S, hSV, hdegree, _, hret, hsub⟩ :=
    exists_rich_core W V left right swap hswap hW hends hV m
  have hhalf : W.card ≤ 2 * (retained W left right S).card := by nlinarith
  have hpos : 0 < (retained W left right S).card := by omega
  have hne : (retained W left right S).Nonempty := Finset.card_pos.mp hpos
  have hS : S.Nonempty := by
    obtain ⟨w, hw⟩ := hne
    exact ⟨left w, (Finset.mem_filter.mp hw).2.1⟩
  exact ⟨S, hSV, hS, hne, hdegree, hhalf, hsub⟩

/-- Same-label ordered collision pairs carry their actual exchange involution. -/
theorem collision_swap_mem {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (label : α → β) {w : α × α}
    (hw : w ∈ TwoTubePathCollisionCount.collisions A label) :
    w.swap ∈ TwoTubePathCollisionCount.collisions A label := by
  obtain ⟨hl, hr, he⟩ := (TwoTubePathCollisionCount.mem_collisions A label w).mp hw
  exact (TwoTubePathCollisionCount.mem_collisions A label w.swap).mpr ⟨hr, hl, he.symm⟩

/-- Native ordered collision labels specialize the core construction. Endpoint
fibers remain fibers of ORIGINAL pairs; no quotient/relabeling is performed.
The collision label and endpoint map may be the actual path collision label
and terminal (height,tube) map from Section 19. -/
theorem exists_collision_rich_core {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (label : α → β) (endpoint : α → ν) (V : Finset ν)
    (hV : ∀ a ∈ A, endpoint a ∈ V) (m : ℕ) :
    ∃ S ⊆ V,
      (∀ v ∈ S, m ≤ (outgoing
        (retained (TwoTubePathCollisionCount.collisions A label)
          (fun w => endpoint w.1) (fun w => endpoint w.2) S)
        (fun w => endpoint w.1) v).card) ∧
      (TwoTubePathCollisionCount.collisions A label).card ≤
        (retained (TwoTubePathCollisionCount.collisions A label)
          (fun w => endpoint w.1) (fun w => endpoint w.2) S).card + 2 * m * V.card := by
  obtain ⟨S, hSV, hdeg, _, hmass, _⟩ := exists_rich_core
    (TwoTubePathCollisionCount.collisions A label) V
    (fun w => endpoint w.1) (fun w => endpoint w.2) Prod.swap
    (fun w => Prod.swap_swap w) (fun _ hw => collision_swap_mem A label hw)
    (fun _ _ => ⟨rfl, rfl⟩) (by
      intro w hw
      obtain ⟨hl, hr, _⟩ := (TwoTubePathCollisionCount.mem_collisions A label w).mp hw
      exact ⟨hV w.1 hl, hV w.2 hr⟩) m
  exact ⟨S, hSV, hdeg, hmass⟩

end RichWitnessCore
