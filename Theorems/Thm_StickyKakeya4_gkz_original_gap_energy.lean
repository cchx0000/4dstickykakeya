import Theorems.Thm_StickyKakeya4_gkz_original_ratio_gap
import Theorems.Thm_StickyKakeya4_original_separated_packing

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical

namespace GKZOriginalGapEnergy
open GKZOriginalRatioGap ActualRoundedAdditiveEnergy OriginalSeparatedPacking
open TwoTubePathCollisionCount

def ScalarFrostman (A : Finset ℝ) (delta K sigma : ℝ) : Prop :=
  ∀ z r : ℝ, delta ≤ r → r ≤ 1 →
    ((A.filter (fun x => |x-z|≤r)).card : ℝ) ≤ K*r^sigma*A.card

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

private theorem gap_energy_with_ball_caps
    (A A1 : Finset ℝ) {delta h gap e1 e2 R MH MR : ℝ}
    (hd : 0 < delta) (hh : 0 ≤ h) (hgap : 0 < gap) (he2 : e2≠0)
    (hA1 : A1 ⊆ A) (hscale : delta ≤ gap * |e2| * h)
    (havoid : ∀ z ∈ cutoffRatios A1 h, gap ≤ |z-e1/e2|)
    (hR : delta/|e2| ≤ R) (hMH : 0 ≤ MH) (hMR : 0 ≤ MR)
    (hballH : ∀ z : ℝ, ((A.filter (fun x => |x-z|≤h)).card : ℝ) ≤ MH)
    (hballR : ∀ z : ℝ, ((A.filter (fun x => |x-z|≤R)).card : ℝ) ≤ MR) :
    ((collisions (A1.product A1) (linearCode delta e1 e2)).card : ℝ) ≤
      MR*MH*(A1.card : ℝ)^2 := by
  let E := collisions (A1.product A1) (linearCode delta e1 e2)
  let f := fun e : (ℝ × ℝ) × (ℝ × ℝ) => (e.1,e.2.2)
  let B := E.image f
  have hE : E ⊆ (A1.product A1).product (A1.product A1) := Finset.filter_subset _ _
  have hclose : ∀ e ∈ E, |e.1.2-e.2.2| ≤ h := by
    intro e he
    obtain ⟨hp,hp',hcell⟩ := (mem_collisions _ _ _).mp he
    exact grid_collision_forces_close_denominator A1 hd hh hgap he2 hscale havoid hp hp' hcell
  have hfirst : (E.card : ℝ) ≤ MR*B.card := by
    exact card_le_real_mul_image E f (fun z _hz =>
      final_coordinate_fiber_card A A1 hd he2 hA1 hR hballR z)
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

/-- The GKZ gap case has a genuine upper collision count from the ORIGINAL
scalar Frostman law, uniformly over every original refinement A1. -/
theorem original_gap_collision_energy
    (A A1 : Finset ℝ) {delta h gap e1 e2 K sigma : ℝ}
    (hd : 0 < delta) (hK : 0 ≤ K) (hA1 : A1 ⊆ A)
    (hhlo : delta ≤ h) (hh1 : h ≤ 1)
    (he2lo : 2*delta ≤ |e2|) (he2hi : |e2| ≤ 2)
    (hgap : 0 < gap) (hscale : delta ≤ gap * |e2| * h)
    (havoid : ∀ z ∈ cutoffRatios A1 h, gap ≤ |z-e1/e2|)
    (hprofile : ScalarFrostman A delta K sigma) :
    ((collisions (A1.product A1) (linearCode delta e1 e2)).card : ℝ) ≤
      (K*(2*delta/|e2|)^sigma*A.card)*(K*h^sigma*A.card)*(A1.card : ℝ)^2 := by
  have he2pos : 0 < |e2| := (by positivity : 0 < 2*delta).trans_le he2lo
  have he2 : e2≠0 := abs_pos.mp he2pos
  have hRlo : delta ≤ 2*delta/|e2| := by
    apply (le_div_iff₀ he2pos).mpr
    nlinarith only [mul_le_mul_of_nonneg_left he2hi hd.le]
  have hRhi : 2*delta/|e2| ≤ 1 := (div_le_one he2pos).mpr he2lo
  have hhpos : 0 < h := hd.trans_le hhlo
  exact gap_energy_with_ball_caps A A1 hd (hd.trans_le hhlo).le hgap he2 hA1 hscale havoid
    (div_le_div_of_nonneg_right (by linarith : delta ≤ 2*delta) (abs_nonneg e2))
    (by positivity) (by positivity)
    (fun z => hprofile z h hhlo hh1)
    (fun z => hprofile z (2*delta/|e2|) hRlo hRhi)

end GKZOriginalGapEnergy
