import Theorems.Thm_StickyKakeya4_partitioned_collision_energy
import Theorems.Thm_StickyKakeya4_dyadic_original_fiber_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped Pointwise BigOperators
noncomputable section

namespace OriginalFiberEnergyCollapse
open TwoTubePathCollisionCount DyadicOriginalFiberSelection

/-- At a fixed output, the original A point is uniquely determined by the
original label p. This is a literal histogram identity. -/
theorem translated_histogram_card
    {G P : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq P]
    (A : Finset G) (W : Finset P) (f : P → G) (u : G) :
    ((A.product W).filter (fun p => p.1+f p.2=u)).card =
      (W.filter (fun p => u-f p∈A)).card := by
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha,hw⟩ := Finset.mem_product.mp hp
    exact Finset.mem_filter.mpr ⟨hw,by simpa only [← he,add_sub_cancel_right] using ha⟩
  · intro p hp q hq heq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    apply Prod.ext ?_ heq
    apply add_right_cancel (b := f p.2)
    simpa only [← heq] using hp'.trans hq'.symm
  · intro p hp
    obtain ⟨hw,ha⟩ := Finset.mem_filter.mp hp
    exact ⟨(u-f p,p),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hw⟩,
      sub_add_cancel _ _⟩,rfl⟩

/-- Collapse an actual source fiber with its supplied original cardinal
bound. The final dyadic caller derives this bound from its constructed bin. -/
theorem original_filter_fiber_bound
    {P G : Type*} [DecidableEq P] [DecidableEq G]
    (W : Finset P) (f : P → G) (q : G → Prop) [DecidablePred q] (U : ℕ)
    (hf : ∀ s∈W.image f, (fiber W f s).card≤U) :
    (W.filter (fun p => q (f p))).card ≤ U*((W.image f).filter q).card := by
  have heq : (∑ s∈(W.image f).filter q, (fiber W f s).card) =
      (W.filter (fun p => q (f p))).card := by
    unfold fiber
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · intro h
      exact ⟨h.1,Finset.mem_image_of_mem f h.1,h.2⟩
  rw [← heq]
  calc
    _ ≤ ∑ _s∈(W.image f).filter q, U :=
      Finset.sum_le_sum (fun s hs => hf s (Finset.mem_filter.mp hs).1)
    _ = _ := by simp only [Finset.sum_const,Nat.nsmul_eq_mul,Nat.mul_comm]

theorem translated_histogram_bound
    {G P : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq P]
    (A : Finset G) (W : Finset P) (f : P → G) (U : ℕ)
    (hf : ∀ s∈W.image f, (fiber W f s).card≤U) (u : G) :
    ((A.product W).filter (fun p => p.1+f p.2=u)).card ≤
      U*((A.product (W.image f)).filter (fun p => p.1+p.2=u)).card := by
  rw [translated_histogram_card A W f u]
  have hs := translated_histogram_card A (W.image f) id u
  simp only [id_eq] at hs
  rw [hs]
  exact original_filter_fiber_bound W f (fun s => u-s∈A) U hf

theorem translated_output_image
    {G P : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq P]
    (A : Finset G) (W : Finset P) (f : P → G) :
    (A.product W).image (fun p => p.1+f p.2)=A+W.image f := by
  ext u
  simp only [Finset.mem_image,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_add]
  constructor
  · rintro ⟨⟨a,p⟩,⟨ha,hp⟩,he⟩
    exact ⟨a,ha,f p,⟨p,hp,rfl⟩,he⟩
  · rintro ⟨a,ha,s,⟨p,hp,rfl⟩,he⟩
    exact ⟨(a,p),⟨ha,hp⟩,he⟩

/-- The ordinary additive energy controls the labelled energy with the
square of the derived original fiber cap. -/
theorem labelled_sum_energy_le
    {G P : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq P]
    (A : Finset G) (W : Finset P) (f : P → G) (U : ℕ)
    (hf : ∀ s∈W.image f, (fiber W f s).card≤U) :
    (collisions (A.product W) (fun p => p.1+f p.2)).card ≤
      U^2 * Finset.addEnergy A (W.image f) := by
  have heq : (collisions (A.product (W.image f)) (fun p => p.1+p.2)).card =
      Finset.addEnergy A (W.image f) := by
    simpa only [collisions,Finset.product_eq_sprod] using
      (Finset.addEnergy_eq_card_filter A (W.image f)).symm
  rw [← heq,card_collisions_eq_sum_fiber_sq,card_collisions_eq_sum_fiber_sq]
  rw [translated_output_image,show (fun p : G × G => p.1+p.2)=(fun p => p.1+id p.2) from rfl,
    translated_output_image]
  simp only [Finset.image_id]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  have h := Nat.pow_le_pow_left (translated_histogram_bound A W f U hf u) 2
  simpa only [Nat.mul_pow] using h

end OriginalFiberEnergyCollapse
