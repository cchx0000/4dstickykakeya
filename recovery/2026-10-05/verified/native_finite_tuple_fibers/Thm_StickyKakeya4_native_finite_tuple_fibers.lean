import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeFiniteTupleFibers
open Classical Finset
open scoped BigOperators

/-- All literal original-label lists above one prescribed coarse-label list. -/
def tupleLifts {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) : List β → Finset (List α)
  | [] => {[]}
  | b::bs => ((A.filter (fun a => f a=b)) ×ˢ tupleLifts A f bs).image
      (fun z => z.1::z.2)

lemma cons_pair_injective {α : Type*} :
    Function.Injective (fun z : α × List α => z.1::z.2) := by
  intro x y h
  exact Prod.ext (List.cons.inj h).1 (List.cons.inj h).2

theorem mem_tupleLifts {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) (bs : List β) (xs : List α) :
    xs∈tupleLifts A f bs ↔ (∀a∈xs,a∈A) ∧ xs.map f=bs := by
  induction bs generalizing xs with
  | nil => cases xs <;> simp [tupleLifts]
  | cons b bs ih =>
    cases xs with
    | nil => simp [tupleLifts]
    | cons a xs =>
      constructor
      · intro hx
        obtain ⟨⟨c,cs⟩,hp,he⟩ := mem_image.mp hx
        obtain ⟨rfl,rfl⟩ := List.cons.inj he
        obtain ⟨hc,hcs⟩ := mem_product.mp hp
        obtain ⟨hcA,hcf⟩ := mem_filter.mp hc
        obtain ⟨hlabels,hmap⟩ := (ih cs).mp hcs
        refine ⟨?_,by simp only [List.map_cons,hcf,hmap]⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hcA
        · exact hlabels z hz
      · rintro ⟨hlabels,hmap⟩
        have hm : f a=b ∧ xs.map f=bs := by simpa only [List.map_cons,List.cons.injEq] using hmap
        refine mem_image.mpr ⟨(a,xs),mem_product.mpr ⟨?_,?_⟩,rfl⟩
        · exact mem_filter.mpr ⟨hlabels a (by simp),hm.1⟩
        · exact (ih xs).mpr ⟨fun z hz => hlabels z (List.mem_cons_of_mem a hz),hm.2⟩

/-- A tuple-map fiber is bounded by the product of the actual original-label
fiber bounds, even when only a subfamily of fine tuples is later retained. -/
theorem tupleLifts_card_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) (B : ℝ) (hB : 0 ≤ B)
    (H : ∀b,((A.filter (fun a => f a=b)).card:ℝ) ≤ B) (bs : List β) :
    ((tupleLifts A f bs).card:ℝ) ≤ B^bs.length := by
  induction bs with
  | nil => simp [tupleLifts]
  | cons b bs ih =>
    rw [tupleLifts,card_image_of_injective _ cons_pair_injective,card_product,
      Nat.cast_mul,List.length_cons,pow_succ]
    exact (mul_le_mul (H b) ih (Nat.cast_nonneg _) hB).trans_eq (mul_comm _ _)

theorem list_map_fiber_card_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (C : Finset (List α)) (f : α → β)
    (hlabels : ∀xs∈C,∀a∈xs,a∈A) (B : ℝ) (hB : 0 ≤ B)
    (H : ∀b,((A.filter (fun a => f a=b)).card:ℝ) ≤ B) (bs : List β) :
    ((C.filter (fun xs => xs.map f=bs)).card:ℝ) ≤ B^bs.length := by
  have hs : C.filter (fun xs => xs.map f=bs) ⊆ tupleLifts A f bs := by
    intro xs hxs
    obtain ⟨hxC,hmap⟩ := mem_filter.mp hxs
    exact (mem_tupleLifts A f bs xs).mpr ⟨hlabels xs hxC,hmap⟩
  exact (show ((C.filter (fun xs => xs.map f=bs)).card:ℝ) ≤
      (tupleLifts A f bs).card by exact_mod_cast card_le_card hs).trans
    (tupleLifts_card_le A f B hB H bs)

theorem card_le_coarse_tuple_card_mul {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (C : Finset (List α)) (f : α → β) (ell : ℕ)
    (hlen : ∀xs∈C,xs.length=ell) (hlabels : ∀xs∈C,∀a∈xs,a∈A)
    (B : ℝ) (hB : 0 ≤ B) (H : ∀b,((A.filter (fun a => f a=b)).card:ℝ) ≤ B) :
    (C.card:ℝ) ≤ ((C.image (List.map f)).card:ℝ)*B^ell := by
  have he : (C.card:ℝ) = ∑bs∈C.image (List.map f),
      ((C.filter (fun xs => xs.map f=bs)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image (List.map f) C
  rw [he]
  calc
    _ ≤ ∑_bs∈C.image (List.map f),B^ell := by
      apply sum_le_sum
      intro bs hbs
      obtain ⟨xs,hxs,rfl⟩ := mem_image.mp hbs
      simpa only [List.length_map,hlen xs hxs] using
        list_map_fiber_card_le A C f hlabels B hB H (xs.map f)
    _ = _ := by simp

theorem coarse_tuple_card_lower {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (C : Finset (List α)) (f : α → β) (ell : ℕ)
    (hlen : ∀xs∈C,xs.length=ell) (hlabels : ∀xs∈C,∀a∈xs,a∈A)
    (B : ℝ) (hB : 0 < B) (H : ∀b,((A.filter (fun a => f a=b)).card:ℝ) ≤ B)
    (L : ℝ) (hL : L ≤ C.card) :
    L/B^ell ≤ ((C.image (List.map f)).card:ℝ) := by
  apply (div_le_iff₀ (pow_pos hB ell)).mpr
  exact hL.trans (card_le_coarse_tuple_card_mul A C f ell hlen hlabels B hB.le H)

end NativeFiniteTupleFibers
