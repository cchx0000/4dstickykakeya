import Theorems.Thm_StickyKakeya4_original_bourgain_graph_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace OriginalSlabOverlap
open OriginalBourgainGraphTransfer

/-- If each individual translated copy uses at most D representatives of a
cell, excessive total mass forces a collision between DIFFERENT copies. -/
theorem exists_original_cross_fiber_collision {X Y Z : Type*}
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (P : Finset X) (label : X → Y) (f : X → Z) {D : ℝ}
    (hfiber : ∀ y z,
      ((P.filter (fun p => f p=z ∧ label p=y)).card:ℝ) ≤ D)
    (hlarge : D*(P.image f).card < (P.card:ℝ)) :
    ∃ x∈P, ∃ y∈P, f x=f y ∧ label x≠label y := by
  by_contra hnone
  push Not at hnone
  have hf : ∀ z∈P.image f, ((P.filter (fun p => f p=z)).card:ℝ) ≤ D := by
    intro z hz
    obtain ⟨p,hp,hpz⟩ := Finset.mem_image.mp hz
    have hsub : P.filter (fun q => f q=z) ⊆
        P.filter (fun q => f q=z ∧ label q=label p) := by
      intro q hq
      obtain ⟨hqP,hqz⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hqP,hqz,hnone q hqP p hp (hqz.trans hpz.symm)⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hfiber (label p) z)
  exact (not_lt_of_ge (OriginalSeparatedPacking.card_le_real_mul_image P f hf)) hlarge

/-- Literal floor labels of original representatives have at most two
preimages per translated copy. A large collection of translated copies thus
forces an actual cross-copy floor collision. -/
theorem exists_original_translated_floor_collision {T : Type*} [DecidableEq T]
    (S : Finset T) (I : Finset ℤ) (shift : T → ℝ) (value : ℤ → ℝ)
    (hvalue : ∀ i∈I, ⌊value i⌋=i)
    (hlarge : 2*(((S.product I).image (fun p => ⌊value p.2+shift p.1⌋)).card:ℝ) <
      (S.card:ℝ)*I.card) :
    ∃ s∈S, ∃ t∈S, s≠t ∧ ∃ i∈I, ∃ j∈I,
      ⌊value i+shift s⌋=⌊value j+shift t⌋ := by
  let P := S.product I
  let f : T × ℤ → ℤ := fun p => ⌊value p.2+shift p.1⌋
  have hfiber (s : T) (z : ℤ) :
      ((P.filter (fun p => f p=z ∧ p.1=s)).card:ℝ) ≤ 2 := by
    let lo := ⌊(z:ℝ)-shift s⌋
    have hc : (P.filter (fun p => f p=z ∧ p.1=s)).card ≤ (Finset.Icc lo (lo+1)).card := by
      apply Finset.card_le_card_of_injOn (fun p : T × ℤ => p.2)
      · intro p hp
        obtain ⟨hp,hpf,hps⟩ := Finset.mem_filter.mp hp
        obtain ⟨_hs,hi⟩ := Finset.mem_product.mp hp
        change ⌊value p.2+shift p.1⌋=z at hpf
        rw [hps] at hpf
        have hh := floor_translation_pair hpf
        apply Finset.mem_Icc.mpr
        simpa only [hvalue p.2 hi,lo] using (Finset.mem_Icc.mp hh)
      · intro p hp q hq he
        change p.2=q.2 at he
        have hp1 := (Finset.mem_filter.mp hp).2.2
        have hq1 := (Finset.mem_filter.mp hq).2.2
        exact Prod.ext (hp1.trans hq1.symm) he
    have htwo : (Finset.Icc lo (lo+1)).card=2 := by
      rw [Int.card_Icc]
      have he : lo+1+1-lo=2 := by omega
      rw [he]
      rfl
    exact_mod_cast hc.trans_eq htwo
  have hPcard : (P.card:ℝ)=(S.card:ℝ)*I.card := by
    simp only [P,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul]
  have hlarge' : 2*(P.image f).card < (P.card:ℝ) := by
    rw [hPcard]
    exact hlarge
  obtain ⟨p,hp,q,hq,hpq,hneq⟩ := exists_original_cross_fiber_collision P Prod.fst f hfiber hlarge'
  obtain ⟨hs,hi⟩ := Finset.mem_product.mp hp
  obtain ⟨ht,hj⟩ := Finset.mem_product.mp hq
  exact ⟨p.1,hs,q.1,ht,hneq,p.2,hi,q.2,hj,hpq⟩

end OriginalSlabOverlap
