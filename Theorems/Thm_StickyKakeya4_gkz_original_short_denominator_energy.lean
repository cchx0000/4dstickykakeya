import Theorems.Thm_StickyKakeya4_gkz_original_dense_ratio_selection
import Theorems.Thm_StickyKakeya4_original_separated_packing

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical

namespace GKZOriginalShortDenominatorEnergy
open GKZOriginalRatioGap GKZOriginalGapEnergy ActualRoundedAdditiveEnergy OriginalSeparatedPacking
open TwoTubePathCollisionCount

private lemma collision_affine_close {delta e1 e2 : ℝ} (hd : 0 < delta) (he2 : e2≠0)
    {p p' : ℝ × ℝ} (he : linearCode delta e1 e2 p=linearCode delta e1 e2 p') :
    |p'.1-(e2*p.1+e1*p.2-e1*p'.2)/e2| ≤ delta/|e2| := by
  have hc := ProjectionHeavyCells.same_floor_difference hd he
  have hid : p'.1-(e2*p.1+e1*p.2-e1*p'.2)/e2=
      -((e2*p.1+e1*p.2)-(e2*p'.1+e1*p'.2))/e2 := by
    field_simp
    ring
  rw [hid,abs_div,abs_neg]
  exact div_le_div_of_nonneg_right hc.le (abs_nonneg _)

private lemma final_coordinate_fiber_card
    (A A1 : Finset ℝ) {delta e1 e2 R M : ℝ} (hd : 0 < delta) (he2 : e2≠0)
    (hA1 : A1 ⊆ A) (hR : delta/|e2| ≤ R)
    (hball : ∀ z : ℝ, ((A.filter (fun x => |x-z|≤R)).card : ℝ) ≤ M)
    (z : (ℝ × ℝ) × ℝ) :
    (((collisions (A1.product A1) (linearCode delta e1 e2)).filter
      (fun e => (e.1,e.2.2)=z)).card : ℝ) ≤ M := by
  let E := collisions (A1.product A1) (linearCode delta e1 e2)
  let c := (e2*z.1.1+e1*z.1.2-e1*z.2)/e2
  have hc : (E.filter (fun e => (e.1,e.2.2)=z)).card ≤
      (A.filter (fun x => |x-c|≤R)).card := by
    apply Finset.card_le_card_of_injOn (fun e : (ℝ × ℝ) × (ℝ × ℝ) => e.2.1)
    · intro e he
      obtain ⟨heE,hez⟩ := Finset.mem_filter.mp he
      obtain ⟨_hep,heq,hcell⟩ := (mem_collisions _ _ _).mp heE
      have hpz : e.1=z.1 := congrArg Prod.fst hez
      have hyz : e.2.2=z.2 := congrArg Prod.snd hez
      have ha := collision_affine_close hd he2 hcell
      refine Finset.mem_filter.mpr ⟨hA1 (Finset.mem_product.mp heq).1,?_⟩
      have hh : |e.2.1-c| ≤ delta/|e2| := by simpa only [c,hpz,hyz] using ha
      exact hh.trans hR
    · intro e he f hf hef
      have hez := (Finset.mem_filter.mp he).2
      have hfz := (Finset.mem_filter.mp hf).2
      have hp : e.1=f.1 := (congrArg Prod.fst hez).trans (congrArg Prod.fst hfz).symm
      have hy : e.2.2=f.2.2 := (congrArg Prod.snd hez).trans (congrArg Prod.snd hfz).symm
      exact Prod.ext hp (Prod.ext hef hy)
  exact (Nat.cast_le.mpr hc).trans (hball c)

private lemma denominator_label_fiber_card
    (A A1 : Finset ℝ) (E : Finset ((ℝ × ℝ) × (ℝ × ℝ))) {h M : ℝ}
    (hA1 : A1 ⊆ A) (hE : E ⊆ (A1.product A1).product (A1.product A1))
    (hclose : ∀ e ∈ E, |e.1.2-e.2.2| ≤ h)
    (hball : ∀ z : ℝ, ((A.filter (fun x => |x-z|≤h)).card : ℝ) ≤ M)
    (p : ℝ × ℝ) :
    ((Finset.filter (fun z => z.1=p) (E.image (fun e => (e.1,e.2.2)))).card : ℝ) ≤ M := by
  have hc : (((E.image (fun e => (e.1,e.2.2))).filter (fun z => z.1=p))).card ≤
      (A.filter (fun y => |y-p.2|≤h)).card := by
    apply Finset.card_le_card_of_injOn (fun z : (ℝ × ℝ) × ℝ => z.2)
    · intro z hz
      obtain ⟨hzE,hzp⟩ := Finset.mem_filter.mp hz
      obtain ⟨e,he,hez⟩ := Finset.mem_image.mp hzE
      have heP := Finset.mem_product.mp (hE he)
      have hy : e.2.2=z.2 := congrArg Prod.snd hez
      have hp : e.1=p := (congrArg Prod.fst hez).trans hzp
      refine Finset.mem_filter.mpr ⟨?_,?_⟩
      · change z.2 ∈ A
        rw [← hy]
        exact hA1 (Finset.mem_product.mp heP.2).2
      · have hh := hclose e he
        simpa only [hy,hp,abs_sub_comm] using hh
    · intro z hz w hw hzw
      have hz1 := (Finset.mem_filter.mp hz).2
      have hw1 := (Finset.mem_filter.mp hw).2
      exact Prod.ext (hz1.trans hw1.symm) hzw
  exact (Nat.cast_le.mpr hc).trans (hball p.2)

private theorem close_energy_with_ball_caps
    (A A1 : Finset ℝ) (E : Finset ((ℝ × ℝ) × (ℝ × ℝ)))
    {delta h e1 e2 R MH MR : ℝ}
    (hd : 0 < delta) (he2 : e2≠0) (hA1 : A1 ⊆ A)
    (hcollision : E ⊆ collisions (A1.product A1) (linearCode delta e1 e2))
    (hclose : ∀ e ∈ E, |e.1.2-e.2.2| ≤ h)
    (hR : delta/|e2| ≤ R) (hMH : 0 ≤ MH) (hMR : 0 ≤ MR)
    (hballH : ∀ z : ℝ, ((A.filter (fun x => |x-z|≤h)).card : ℝ) ≤ MH)
    (hballR : ∀ z : ℝ, ((A.filter (fun x => |x-z|≤R)).card : ℝ) ≤ MR) :
    (E.card : ℝ) ≤ MR*MH*(A1.card : ℝ)^2 := by
  let f := fun e : (ℝ × ℝ) × (ℝ × ℝ) => (e.1,e.2.2)
  let B := E.image f
  have hE : E ⊆ (A1.product A1).product (A1.product A1) :=
    hcollision.trans (Finset.filter_subset _ _)
  have hfirst : (E.card : ℝ) ≤ MR*B.card := by
    apply card_le_real_mul_image E f
    intro z _
    have hsub : E.filter (fun e => f e=z) ⊆
        (collisions (A1.product A1) (linearCode delta e1 e2)).filter
          (fun e => (e.1,e.2.2)=z) := by
      intro e he
      obtain ⟨he, hez⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨hcollision he, hez⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (final_coordinate_fiber_card A A1 hd he2 hA1 hR hballR z)
  have hsecond : (B.card : ℝ) ≤ MH*(B.image Prod.fst).card := by
    exact card_le_real_mul_image B Prod.fst (fun p _hp =>
      denominator_label_fiber_card A A1 E hA1 hE hclose hballH p)
  have hsource : B.image Prod.fst ⊆ A1.product A1 := by
    intro p hp
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_product.mp (hE he)).1
  have hcard : ((B.image Prod.fst).card : ℝ) ≤ (A1.card : ℝ)^2 := by
    have hn := Finset.card_le_card hsource
    rw [Finset.product_eq_sprod,Finset.card_product] at hn
    exact_mod_cast (show (B.image Prod.fst).card ≤ A1.card^2 by simpa only [pow_two] using hn)
  calc
    _ ≤ MR*(MH*(B.image Prod.fst).card) :=
      hfirst.trans (mul_le_mul_of_nonneg_left hsecond hMR)
    _ ≤ MR*(MH*(A1.card : ℝ)^2) := by gcongr
    _ = _ := by ring

/-- All original collisions with a short denominator obey the original
Frostman product cap, independently of the behavior of the other collisions. -/
theorem original_short_denominator_energy
    (A A1 : Finset ℝ) {delta h e1 e2 K sigma : ℝ}
    (hd : 0 < delta) (hK : 0 ≤ K) (hA1 : A1 ⊆ A)
    (hhlo : delta ≤ h) (hh1 : h ≤ 1)
    (he2lo : 2*delta ≤ |e2|) (he2hi : |e2| ≤ 2)
    (hprofile : ScalarFrostman A delta K sigma) :
    (((collisions (A1.product A1) (linearCode delta e1 e2)).filter
      (fun e => |e.1.2-e.2.2| ≤ h)).card : ℝ) ≤
      (K*(2*delta/|e2|)^sigma*A.card)*(K*h^sigma*A.card)*(A1.card : ℝ)^2 := by
  have he2pos : 0 < |e2| := (by positivity : 0 < 2*delta).trans_le he2lo
  have he2 : e2≠0 := abs_pos.mp he2pos
  have hRlo : delta ≤ 2*delta/|e2| := by
    apply (le_div_iff₀ he2pos).mpr
    nlinarith only [mul_le_mul_of_nonneg_left he2hi hd.le]
  have hRhi : 2*delta/|e2| ≤ 1 := (div_le_one he2pos).mpr he2lo
  have hhpos : 0 < h := hd.trans_le hhlo
  exact close_energy_with_ball_caps A A1 _ hd he2 hA1 (Finset.filter_subset _ _)
    (fun _ he => (Finset.mem_filter.mp he).2)
    (div_le_div_of_nonneg_right (by linarith : delta ≤ 2*delta) (abs_nonneg e2))
    (by positivity) (by positivity)
    (fun z => hprofile z h hhlo hh1)
    (fun z => hprofile z (2*delta/|e2|) hRlo hRhi)

end GKZOriginalShortDenominatorEnergy
