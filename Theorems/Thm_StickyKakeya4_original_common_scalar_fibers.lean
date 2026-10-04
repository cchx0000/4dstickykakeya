import Theorems.Thm_StickyKakeya4_two_tube_path_collision_count
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open Finset
open scoped BigOperators
noncomputable section
open Classical
namespace OriginalCommonScalarFibers
variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

/-- Literal shared original scalar labels of two retained product fibers. -/
def commonFiber (F : Finset (X × Y)) (C : Finset Y) (b b' : X) : Finset Y :=
  C.filter (fun c => (b,c) ∈ F ∧ (b',c) ∈ F)

lemma commonFiber_subset (F : Finset (X × Y)) (C : Finset Y) (b b' : X) :
    commonFiber F C b b' ⊆ C := Finset.filter_subset _ _

lemma commonFiber_card_le (F : Finset (X × Y)) (C : Finset Y) (b b' : X) :
    (commonFiber F C b b').card ≤ C.card := Finset.card_le_card (commonFiber_subset F C b b')

lemma commonFiber_eq_collision_fiber (B : Finset X) (C : Finset Y) (F : Finset (X × Y))
    (hF : F ⊆ B ×ˢ C) (b b' : X) :
    (commonFiber F C b b').card =
      ((TwoTubePathCollisionCount.collisions F Prod.snd).filter
        (fun e => (e.1.1,e.2.1)=(b,b'))).card := by
  apply Finset.card_bij (fun c _ => ((b,c),(b',c)))
  · intro c hc
    obtain ⟨_,hbc,hb'c⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨TwoTubePathCollisionCount.mem_collisions _ _ _ |>.mpr
      ⟨hbc,hb'c,rfl⟩,rfl⟩
  · intro c _ d _ hcd
    exact congrArg (fun e : (X × Y) × (X × Y) => e.1.2) hcd
  · rintro ⟨⟨x,c⟩,⟨x',c'⟩⟩ he
    obtain ⟨he,hxx⟩ := Finset.mem_filter.mp he
    obtain ⟨hc,hc',hcc⟩ := (TwoTubePathCollisionCount.mem_collisions _ _ _).mp he
    change c=c' at hcc
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hxx
    subst c'
    exact ⟨c,Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (hF hc)).2,hc,hc'⟩,rfl⟩

lemma sum_commonFiber_eq_collisions (B : Finset X) (C : Finset Y) (F : Finset (X × Y))
    (hF : F ⊆ B ×ˢ C) :
    (∑ bb ∈ B ×ˢ B, (commonFiber F C bb.1 bb.2).card) =
      (TwoTubePathCollisionCount.collisions F Prod.snd).card := by
  simp_rw [commonFiber_eq_collision_fiber B C F hF]
  symm
  exact Finset.card_eq_sum_card_fiberwise (fun e he => by
    obtain ⟨he1,he2,_⟩ := (TwoTubePathCollisionCount.mem_collisions _ _ _).mp he
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp (hF he1)).1,(Finset.mem_product.mp (hF he2)).1⟩)

/-- Finite Cauchy counts actual common original scalar labels. -/
theorem commonFiber_second_moment (B : Finset X) (C : Finset Y) (F : Finset (X × Y))
    (hF : F ⊆ B ×ˢ C) :
    F.card^2 ≤ C.card * (∑ bb ∈ B ×ˢ B, (commonFiber F C bb.1 bb.2).card) := by
  rw [sum_commonFiber_eq_collisions B C F hF]
  have himage : F.image Prod.snd ⊆ C := by
    intro c hc
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_product.mp (hF he)).2
  exact (TwoTubePathCollisionCount.square_card_le_image_mul_collisions F Prod.snd).trans
    (Nat.mul_le_mul_right _ (Finset.card_le_card himage))

/-- Select original ordered B pairs by their literal common-C populations. -/
def richPairs (B : Finset X) (C : Finset Y) (F : Finset (X × Y)) (q : ℝ) : Finset (X × X) :=
  (B ×ˢ B).filter (fun bb => q*C.card ≤ (commonFiber F C bb.1 bb.2).card)

lemma richPairs_subset (B : Finset X) (C : Finset Y) (F : Finset (X × Y)) (q : ℝ) :
    richPairs B C F q ⊆ B ×ˢ B := Finset.filter_subset _ _

lemma richPairs_common_lower (B : Finset X) (C : Finset Y) (F : Finset (X × Y)) (q : ℝ)
    {bb : X × X} (hbb : bb ∈ richPairs B C F q) :
    q*C.card ≤ (commonFiber F C bb.1 bb.2).card := (Finset.mem_filter.mp hbb).2

lemma commonFiber_sum_upper (B : Finset X) (C : Finset Y) (F : Finset (X × Y))
    {q : ℝ} (hq : 0 ≤ q) :
    (∑ bb ∈ B ×ˢ B, ((commonFiber F C bb.1 bb.2).card : ℝ)) ≤
      (richPairs B C F q).card*C.card + q*(B.card : ℝ)^2*C.card := by
  have hterm : ∀ bb ∈ B ×ˢ B,
      ((commonFiber F C bb.1 bb.2).card : ℝ) ≤
        (if bb ∈ richPairs B C F q then (C.card : ℝ) else 0) + q*C.card := by
    intro bb hbb
    by_cases hr : bb ∈ richPairs B C F q
    · rw [if_pos hr]
      have hc : ((commonFiber F C bb.1 bb.2).card : ℝ) ≤ C.card := by
        exact_mod_cast commonFiber_card_le F C bb.1 bb.2
      nlinarith only [hc, mul_nonneg hq (Nat.cast_nonneg C.card)]
    · rw [if_neg hr,zero_add]
      exact le_of_lt (lt_of_not_ge (fun hh => hr (Finset.mem_filter.mpr ⟨hbb,hh⟩)))
  have hfilter : (B ×ˢ B).filter (fun bb => bb ∈ richPairs B C F q) = richPairs B C F q := by
    ext bb
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨richPairs_subset B C F q h,h⟩⟩
  calc
    _ ≤ ∑ bb ∈ B ×ˢ B, ((if bb ∈ richPairs B C F q then (C.card : ℝ) else 0)+q*C.card) :=
      Finset.sum_le_sum hterm
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, hfilter]
      simp only [Finset.sum_const, Finset.card_product, nsmul_eq_mul, Nat.cast_mul]
      ring

/-- A positive-density subset of ORIGINAL B×C has many pairs with large
literal common original C fibers. No energy or codegree premise is supplied. -/
theorem richPairs_card_lower (B : Finset X) (C : Finset Y) (F : Finset (X × Y))
    {tau : ℝ} (hC : C.Nonempty) (htau : 0 ≤ tau) (hF : F ⊆ B ×ˢ C)
    (hmass : tau*B.card*C.card ≤ (F.card : ℝ)) :
    (tau^2/2)*(B.card : ℝ)^2 ≤ (richPairs B C F (tau^2/2)).card := by
  have hCc : 0 < (C.card : ℝ) := by exact_mod_cast hC.card_pos
  have hcs : (F.card : ℝ)^2 ≤ C.card *
      (∑ bb ∈ B ×ˢ B, ((commonFiber F C bb.1 bb.2).card : ℝ)) := by
    exact_mod_cast commonFiber_second_moment B C F hF
  have hs := commonFiber_sum_upper B C F (show 0 ≤ tau^2/2 by positivity)
  have hmass2 := pow_le_pow_left₀ (show 0 ≤ tau*B.card*C.card by positivity) hmass 2
  have henergy := hmass2.trans (hcs.trans (mul_le_mul_of_nonneg_left hs hCc.le))
  apply (mul_le_mul_iff_left₀ (show 0 < (C.card : ℝ)^2 by positivity)).mp
  nlinarith only [henergy]

/-- Remove the actual bad radial pairs using their original missing-pair
count. All surviving pairs keep the same common original scalar fibers. -/
theorem richPairs_inter_card_lower (B : Finset X) (C : Finset Y) (F : Finset (X × Y))
    (H : Finset (X × X)) {tau : ℝ} (hC : C.Nonempty) (htau : 0 ≤ tau)
    (hF : F ⊆ B ×ˢ C) (hmass : tau*B.card*C.card ≤ (F.card : ℝ))
    (hbad : (((B ×ˢ B) \ H).card : ℝ) ≤ (tau^2/4)*(B.card : ℝ)^2) :
    (tau^2/4)*(B.card : ℝ)^2 ≤ ((richPairs B C F (tau^2/2)) ∩ H).card := by
  have hr := richPairs_card_lower B C F hC htau hF hmass
  have hsub : richPairs B C F (tau^2/2) \ H ⊆ (B ×ˢ B) \ H :=
    Finset.sdiff_subset_sdiff (richPairs_subset B C F (tau^2/2)) (Finset.Subset.refl _)
  have hdel := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hbad
  have hsplit : ((richPairs B C F (tau^2/2) \ H).card : ℝ) +
      ((richPairs B C F (tau^2/2)) ∩ H).card = (richPairs B C F (tau^2/2)).card := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℝ))
      (Finset.card_sdiff_add_card_inter (richPairs B C F (tau^2/2)) H)
  linarith
end OriginalCommonScalarFibers
