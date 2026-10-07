import Theorems.Thm_StickyKakeya4_native_incidence_multiplicity_tower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section

namespace NativePointMenuTransfer
open Classical Finset
open scoped BigOperators

/-- A subset of an incidence set is bounded by its number of occupied point
labels times a uniform point-degree bound for the ambient set. -/
lemma subset_card_le_support_mul_degree {P Y : Type*} [DecidableEq P]
    [DecidableEq Y] (S C : Finset (P × Y)) (hSC : S ⊆ C) (M : ℝ)
    (hdegree : ∀ q : Y, ((C.filter (fun b => b.2 = q)).card : ℝ) ≤ M) :
    (S.card : ℝ) ≤ ((S.image Prod.snd).card : ℝ) * M := by
  have hsum : (S.card : ℝ) =
      ∑ q ∈ S.image Prod.snd, ((S.filter (fun b => b.2 = q)).card : ℝ) := by
    exact_mod_cast card_eq_sum_card_image Prod.snd S
  calc
    _ = ∑ q ∈ S.image Prod.snd,
        ((S.filter (fun b => b.2 = q)).card : ℝ) := hsum
    _ ≤ ∑ _q ∈ S.image Prod.snd, M := by
      apply sum_le_sum
      intro q _hq
      have hc : ((S.filter (fun b => b.2 = q)).card : ℝ) ≤
          ((C.filter (fun b => b.2 = q)).card : ℝ) := by
        exact_mod_cast card_le_card (filter_subset_filter (fun b => b.2 = q) hSC)
      exact hc.trans (hdegree q)
    _ = _ := by simp

/-- Preserving the parent label makes the point map injective on each old
point fiber, so a bounded menu controls every old point degree. -/
lemma point_degree_le_menu_mul_degree {P X Y : Type*} [DecidableEq P]
    [DecidableEq X] [DecidableEq Y] (A : Finset (P × X))
    (g : P × X → P × Y) (H : ℕ) (M : ℝ)
    (hparent : ∀ z ∈ A, (g z).1 = z.1)
    (hmenu : ∀ k : X, (((A.filter (fun z => z.2 = k)).image g).image Prod.snd).card ≤ H)
    (hM : 0 ≤ M)
    (hdegree : ∀ q : Y, (((A.image g).filter (fun b => b.2 = q)).card : ℝ) ≤ M)
    (k : X) : ((A.filter (fun z => z.2 = k)).card : ℝ) ≤ (H : ℝ) * M := by
  have hinj : Set.InjOn g (A.filter (fun z => z.2 = k)) := by
    intro a ha b hb hab
    obtain ⟨ha, hak⟩ := mem_filter.mp ha
    obtain ⟨hb, hbk⟩ := mem_filter.mp hb
    apply Prod.ext
    · simpa only [hparent a ha, hparent b hb] using congrArg Prod.fst hab
    · exact hak.trans hbk.symm
  have hc := subset_card_le_support_mul_degree
    ((A.filter (fun z => z.2 = k)).image g) (A.image g)
    (image_subset_image (filter_subset _ _)) M hdegree
  rw [card_image_of_injOn hinj] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hmenu k) hM)

/-- A parent-preserving point map with at most H coarse labels over each
old point transfers a uniform coarse point-degree bound to old average
multiplicity, including the empty incidence set. -/
theorem multiplicity_le_menu_mul_degree {P X Y : Type*} [DecidableEq P]
    [DecidableEq X] [DecidableEq Y] (A : Finset (P × X))
    (g : P × X → P × Y) (H : ℕ) (M : ℝ)
    (hparent : ∀ z ∈ A, (g z).1 = z.1)
    (hmenu : ∀ k : X, (((A.filter (fun z => z.2 = k)).image g).image Prod.snd).card ≤ H)
    (hM : 0 ≤ M)
    (hdegree : ∀ q : Y, (((A.image g).filter (fun b => b.2 = q)).card : ℝ) ≤ M) :
    NativeIncidenceMultiplicityTower.multiplicity A ≤ (H : ℝ) * M := by
  have hc : (A.card : ℝ) ≤ ((A.image Prod.snd).card : ℝ) * ((H : ℝ) * M) :=
    subset_card_le_support_mul_degree A A (Subset.refl A) ((H : ℝ) * M)
      (point_degree_le_menu_mul_degree A g H M hparent hmenu hM hdegree)
  by_cases hA : A.Nonempty
  · have hs : (0 : ℝ) < (A.image Prod.snd).card := by
      exact_mod_cast card_pos.mpr (hA.image Prod.snd)
    apply (div_le_iff₀ hs).mpr
    simpa only [mul_comm] using hc
  · rw [not_nonempty_iff_eq_empty.mp hA]
    simpa only [NativeIncidenceMultiplicityTower.multiplicity, card_empty, image_empty,
      Nat.cast_zero, zero_div] using mul_nonneg (Nat.cast_nonneg H) hM

end NativePointMenuTransfer
