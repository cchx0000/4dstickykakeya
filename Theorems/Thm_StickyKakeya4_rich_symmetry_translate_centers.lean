import Theorems.Thm_StickyKakeya4_symmetry_set_difference_step
import Theorems.Thm_StickyKakeya4_disjoint_rich_translate_cover

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace RichSymmetryTranslateCenters

open scoped Pointwise BigOperators
open SymmetrySetDifferenceStep DisjointRichTranslateCover

noncomputable section

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

lemma translate_eq_add_singleton (H : Finset G) (x : G) :
    translate H x = H + {x} := by
  ext y
  simp only [translate, Finset.mem_image, Finset.mem_add, Finset.mem_singleton]
  constructor
  · rintro ⟨h, hh, he⟩
    exact ⟨h, hh, x, rfl, he⟩
  · rintro ⟨h, hh, z, rfl, he⟩
    exact ⟨h, hh, he⟩

lemma translate_card (H : Finset G) (x : G) : (translate H x).card = H.card := by
  apply Finset.card_image_of_injective
  intro u v h
  exact add_right_cancel h

lemma translated_intersection_card_le (A H : Finset G) (x : G) :
    (A ∩ translate H x).card ≤ H.card := by
  calc
    _ ≤ (translate H x).card := Finset.card_le_card Finset.inter_subset_right
    _ = _ := translate_card H x

/-- Count the original `(y,c)` incidences, then inject them into actual
center-point incidences by `(y,c) ↦ (y-c+c0,y)`. -/
theorem original_incidence_sum_le (A C H : Finset G) (c0 : G)
    (hContain : C ⊆ H + {c0}) :
    (∑ c ∈ C, (overlap A c).card) ≤
      ∑ x ∈ translate A c0, (A ∩ translate H x).card := by
  classical
  let I := (A.product C).filter (fun p => p.1 - p.2 ∈ A)
  let T := ((translate A c0).product A).filter (fun p => p.2 ∈ translate H p.1)
  have hI : I.card = ∑ c ∈ C, (overlap A c).card := by
    simp only [I, overlap, Finset.card_eq_sum_ones, Finset.sum_filter,
      Finset.product_eq_sprod, Finset.sum_product]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : y - c ∈ A <;> simp [h]
  have hT : T.card = ∑ x ∈ translate A c0, (A ∩ translate H x).card := by
    simp only [T, ← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones,
      Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  rw [← hI, ← hT]
  apply Finset.card_le_card_of_injOn (fun p => (p.1 - p.2 + c0, p.1))
  · intro p hp
    obtain ⟨hpp, hpDiff⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpA, hpC⟩ := Finset.mem_product.mp hpp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, hpA⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨p.1 - p.2, hpDiff, rfl⟩
    · have hpc : p.2 ∈ translate H c0 := by
        rw [translate_eq_add_singleton]
        exact hContain hpC
      obtain ⟨h, hh, hhc⟩ := Finset.mem_image.mp hpc
      apply Finset.mem_image.mpr
      refine ⟨h, hh, ?_⟩
      dsimp
      rw [← hhc]
      abel
  · intro p _ q _ he
    have hy := congrArg Prod.snd he
    have hx := congrArg Prod.fst he
    dsimp at hy hx
    apply Prod.ext hy
    rw [hy] at hx
    have hdiff := add_right_cancel hx
    simpa only [sub_right_inj] using hdiff

/-- Literal original symmetry incidences imply the translated-overlap sum. -/
theorem symmetry_overlap_sum_lower (A C H : Finset G) (c0 : G) {a : ℝ}
    (ha : 0 < a) (hA : A.Nonempty)
    (hSym : C ⊆ symmetrySet A a) (hContain : C ⊆ H + {c0}) :
    a * (A.card : ℝ) * (C.card : ℝ) ≤
      ∑ x ∈ translate A c0, ((A ∩ translate H x).card : ℝ) := by
  have hlow : a * (A.card : ℝ) * (C.card : ℝ) ≤
      ∑ c ∈ C, ((overlap A c).card : ℝ) := by
    calc
      _ = ∑ _c ∈ C, a * (A.card : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun c hc => (mem_symmetrySet_iff ha hA c).mp (hSym hc))
  have hupp : (∑ c ∈ C, ((overlap A c).card : ℝ)) ≤
      ∑ x ∈ translate A c0, ((A ∩ translate H x).card : ℝ) := by
    exact_mod_cast original_incidence_sum_le A C H c0 hContain
  exact hlow.trans hupp

def richCenters (A H : Finset G) (c0 : G) (eta : ℝ) : Finset G :=
  (translate A c0).filter (fun x => eta * (H.card : ℝ) ≤ (A ∩ translate H x).card)

/-- A direct finite threshold bound for actual translated intersections. -/
theorem overlap_sum_upper (A H : Finset G) (c0 : G) {eta : ℝ} (heta : 0 ≤ eta) :
    (∑ x ∈ translate A c0, ((A ∩ translate H x).card : ℝ)) ≤
      (H.card : ℝ) * ((richCenters A H c0 eta).card : ℝ) +
        eta * (H.card : ℝ) * (A.card : ℝ) := by
  classical
  have hpoint (x : G) : ((A ∩ translate H x).card : ℝ) ≤
      (if eta * (H.card : ℝ) ≤ (A ∩ translate H x).card then (H.card : ℝ) else 0) +
        eta * (H.card : ℝ) := by
    by_cases h : eta * (H.card : ℝ) ≤ (A ∩ translate H x).card
    · simp only [h, if_true]
      exact (Nat.cast_le.mpr (translated_intersection_card_le A H x)).trans
        (le_add_of_nonneg_right (mul_nonneg heta (Nat.cast_nonneg _)))
    · simp only [h, if_false, zero_add]
      exact (lt_of_not_ge h).le
  have hs := Finset.sum_le_sum (fun x (_hx : x ∈ translate A c0) => hpoint x)
  have heq : (∑ x ∈ translate A c0,
      if eta * (H.card : ℝ) ≤ (A ∩ translate H x).card then (H.card : ℝ) else 0) =
      (H.card : ℝ) * ((richCenters A H c0 eta).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [richCenters, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [Finset.sum_add_distrib, heq] at hs
  simpa only [Finset.sum_const, nsmul_eq_mul, translate_card,
    mul_assoc, mul_comm, mul_left_comm] using hs

/-- Construct rich original translates directly from source symmetry incidences. -/
theorem exists_rich_centers (A C H : Finset G) (c0 : G) {a K : ℝ}
    (ha : 0 < a) (hK : 0 < K) (hA : A.Nonempty) (hC : C.Nonempty)
    (hSym : C ⊆ symmetrySet A a) (hContain : C ⊆ H + {c0})
    (hSize : (H.card : ℝ) ≤ K * (C.card : ℝ)) :
    ∃ Centers : Finset G, Centers ⊆ A + {c0} ∧ Centers.Nonempty ∧
      (a / (2 * K)) * (A.card : ℝ) ≤ (Centers.card : ℝ) ∧
      ∀ x ∈ Centers,
        (a / (2 * K)) * (H.card : ℝ) ≤ ((A ∩ (H + {x})).card : ℝ) := by
  classical
  let eta := a / (2 * K)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hH : H.Nonempty := by
    obtain ⟨c, hc⟩ := hC
    have hct : c ∈ translate H c0 := by rw [translate_eq_add_singleton]; exact hContain hc
    obtain ⟨h, hh, _⟩ := Finset.mem_image.mp hct
    exact ⟨h, hh⟩
  have hHpos : (0 : ℝ) < H.card := Nat.cast_pos.mpr hH.card_pos
  have hApos : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  have hetaK : 2 * eta * K = a := by dsimp [eta]; field_simp
  have hlow := symmetry_overlap_sum_lower A C H c0 ha hA hSym hContain
  have hupp := overlap_sum_upper A H c0 heta.le
  have hsize := mul_le_mul_of_nonneg_left hSize (show 0 ≤ 2 * eta * (A.card : ℝ) by positivity)
  have hscaled : 2 * eta * (A.card : ℝ) * (H.card : ℝ) ≤
      a * (A.card : ℝ) * (C.card : ℝ) := by
    calc
      _ ≤ (2 * eta * (A.card : ℝ)) * (K * (C.card : ℝ)) := hsize
      _ = _ := by nlinarith only [congrArg (fun z => z * (A.card : ℝ) * (C.card : ℝ)) hetaK]
  have hret : eta * (A.card : ℝ) ≤ ((richCenters A H c0 eta).card : ℝ) := by
    apply (mul_le_mul_iff_left₀ hHpos).mp
    nlinarith only [hscaled.trans (hlow.trans hupp)]
  refine ⟨richCenters A H c0 eta, ?_, ?_, hret, ?_⟩
  · rw [← translate_eq_add_singleton]
    exact Finset.filter_subset _ _
  · exact Finset.card_pos.mp (Nat.cast_pos.mp ((mul_pos heta hApos).trans_le hret))
  · intro x hx
    have h := (Finset.mem_filter.mp hx).2
    simpa only [translate_eq_add_singleton] using h

/-- The same construction in the exact translate API of the maximal-disjoint cover. -/
theorem exists_rich_centers_translate (A C H : Finset G) (c0 : G) {a K : ℝ}
    (ha : 0 < a) (hK : 0 < K) (hA : A.Nonempty) (hC : C.Nonempty)
    (hSym : C ⊆ symmetrySet A a) (hContain : C ⊆ H + {c0})
    (hSize : (H.card : ℝ) ≤ K * (C.card : ℝ)) :
    ∃ Centers : Finset G, Centers ⊆ A + {c0} ∧ Centers.Nonempty ∧
      (a / (2 * K)) * (A.card : ℝ) ≤ (Centers.card : ℝ) ∧
      ∀ x ∈ Centers,
        (a / (2 * K)) * (H.card : ℝ) ≤ ((A ∩ translate H x).card : ℝ) := by
  simpa only [translate_eq_add_singleton] using
    exists_rich_centers A C H c0 ha hK hA hC hSym hContain hSize

end

end RichSymmetryTranslateCenters
