import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Finset
open scoped Pointwise BigOperators

noncomputable section

namespace DisjointRichTranslateCover

def translate {G : Type*} [AddCommGroup G] [DecidableEq G]
    (H : Finset G) (x : G) : Finset G := H.image (fun h => h + x)

theorem exists_disjoint_translate_cover
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (Centers H : Finset G) (hH : H.Nonempty) :
    ∃ F : Finset G, F ⊆ Centers ∧
      (F : Set G).PairwiseDisjoint (translate H) ∧
      Centers ⊆ F + (H - H) := by
  classical
  let Family := Centers.powerset.filter
    (fun (F : Finset G) => (F : Set G).PairwiseDisjoint (translate H))
  have hFamily : Family.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩⟩
    simp
  obtain ⟨F, hFmax⟩ := Family.exists_maximal hFamily
  simp only [Family, Finset.mem_filter, Finset.mem_powerset] at hFmax
  obtain ⟨hFsub, hFdis⟩ := hFmax.1
  refine ⟨F, hFsub, hFdis, ?_⟩
  intro c hc
  by_cases hcF : c ∈ F
  · obtain ⟨h0, hh0⟩ := hH
    have hz : (0 : G) ∈ H - H := by simpa using Finset.sub_mem_sub hh0 hh0
    simpa using Finset.add_mem_add hcF hz
  by_cases hdis : ∀ b ∈ F, Disjoint (translate H c) (translate H b)
  · refine (hFmax.not_gt ?_ (Finset.ssubset_insert hcF)).elim
    rw [Finset.insert_subset_iff, Finset.coe_insert]
    exact ⟨⟨hc, hFsub⟩, hFdis.insert (fun _ hb _ => hdis _ hb)⟩
  push Not at hdis
  obtain ⟨b, hb, hnd⟩ := hdis
  obtain ⟨z, hzc, hzb⟩ := Finset.not_disjoint_iff.mp hnd
  obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp hzc
  obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hzb
  have heq : u + c = v + b := huz.trans hvz.symm
  refine Finset.mem_add.mpr ⟨b, hb, v - u, Finset.sub_mem_sub hv hu, ?_⟩
  apply add_left_cancel (a := u)
  calc
    u + (b + (v - u)) = v + b := by abel
    _ = u + c := heq.symm

/-- The maximal disjoint original translates retain rich intersections with
the original large set, and give both covering and disjoint-mass bounds. -/
theorem exists_rich_translate_selection
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A Centers H : Finset G) (eta : ℝ) (hH : H.Nonempty)
    (hrich : ∀ x ∈ Centers,
      eta * (H.card : ℝ) ≤ ((A ∩ translate H x).card : ℝ)) :
    ∃ F Y : Finset G, F ⊆ Centers ∧ Y ⊆ A ∧ Y ⊆ F + H ∧
      Centers ⊆ F + (H - H) ∧
      eta * (H.card : ℝ) * F.card ≤ Y.card ∧
      (Centers.card : ℝ) ≤ (F.card : ℝ) * (H - H).card := by
  classical
  obtain ⟨F, hFsub, hFdis, hcover⟩ := exists_disjoint_translate_cover Centers H hH
  let Y := F.biUnion (fun x => A ∩ translate H x)
  have hYsub : Y ⊆ A := by
    intro y hy
    obtain ⟨x, _hx, hy⟩ := Finset.mem_biUnion.mp hy
    exact (Finset.mem_inter.mp hy).1
  have hYadd : Y ⊆ F + H := by
    intro y hy
    obtain ⟨x, hx, hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨h, hh, hhy⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).2
    exact Finset.mem_add.mpr ⟨x, hx, h, hh, (add_comm x h).trans hhy⟩
  have hdis : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      Disjoint (A ∩ translate H x) (A ∩ translate H y) := by
    intro x hx y hy hxy
    exact (hFdis hx hy hxy).mono Finset.inter_subset_right Finset.inter_subset_right
  have hYcard : (Y.card : ℝ) = ∑ x ∈ F, ((A ∩ translate H x).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion hdis
  have hmass : eta * (H.card : ℝ) * F.card ≤ (Y.card : ℝ) := by
    calc
      _ = ∑ _x ∈ F, eta * (H.card : ℝ) := by simp [mul_comm]
      _ ≤ ∑ x ∈ F, ((A ∩ translate H x).card : ℝ) := by
        exact Finset.sum_le_sum (fun x hx => hrich x (hFsub hx))
      _ = _ := hYcard.symm
  have hCcard : Centers.card ≤ F.card * (H - H).card :=
    (Finset.card_le_card hcover).trans Finset.card_add_le
  exact ⟨F, Y, hFsub, hYsub, hYadd, hcover, hmass, by exact_mod_cast hCcard⟩

theorem exists_rich_translate_selection_quantitative
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A Centers H : Finset G) (eta lambda K : ℝ)
    (hH : H.Nonempty) (heta : 0 < eta) (hK : 0 < K)
    (hCenters : lambda * (A.card : ℝ) ≤ Centers.card)
    (hrich : ∀ x ∈ Centers,
      eta * (H.card : ℝ) ≤ ((A ∩ translate H x).card : ℝ))
    (hGrowth : ((H - H).card : ℝ) ≤ K * H.card) :
    ∃ F Y : Finset G, F ⊆ Centers ∧ Y ⊆ A ∧ Y ⊆ F + H ∧
      (F.card : ℝ) ≤ (A.card : ℝ) / (eta * H.card) ∧
      (eta * lambda / K) * (A.card : ℝ) ≤ Y.card := by
  obtain ⟨F, Y, hFC, hYA, hYFH, _hcover, hmass, hCcard⟩ :=
    exists_rich_translate_selection A Centers H eta hH hrich
  have hHpos : 0 < (H.card : ℝ) := by exact_mod_cast hH.card_pos
  have hYcard : (Y.card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hYA
  have hFcard : (F.card : ℝ) ≤ (A.card : ℝ) / (eta * H.card) := by
    apply (le_div_iff₀ (mul_pos heta hHpos)).2
    nlinarith only [hmass, hYcard]
  have hcovbound : lambda * (A.card : ℝ) ≤ (F.card : ℝ) * (K * H.card) :=
    hCenters.trans (hCcard.trans
      (mul_le_mul_of_nonneg_left hGrowth (Nat.cast_nonneg _)))
  have hlow : (eta * lambda / K) * (A.card : ℝ) ≤ Y.card := by
    apply (mul_le_mul_iff_left₀ hK).mp
    have h1 := mul_le_mul_of_nonneg_left hcovbound heta.le
    have h2 := mul_le_mul_of_nonneg_left hmass hK.le
    have heq : ((eta * lambda / K) * (A.card : ℝ)) * K = eta * lambda * A.card := by
      field_simp
    rw [heq]
    nlinarith only [h1, h2]
  exact ⟨F, Y, hFC, hYA, hYFH, hFcard, hlow⟩

end DisjointRichTranslateCover
