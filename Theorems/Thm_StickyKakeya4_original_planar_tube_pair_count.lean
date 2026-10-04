import Theorems.Thm_StickyKakeya4_original_three_dimensional_cap_count
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
namespace OriginalPlanarTubePairCount
open Classical OriginalThreeDimensionalCapCount
abbrev Point2 := ℝ × ℝ
abbrev TubeCell := ℤ × ℤ

def boxDistance (x y : Point2) : ℝ := max |y.1-x.1| |y.2-x.2|
def InCellTube (h : ℝ) (z : TubeCell) (x : Point2) : Prop :=
  |x.2-(h*(z.1:ℝ)*x.1+h*(z.2:ℝ))| ≤ 16*h

private theorem offset_fiber_bound (S : Finset TubeCell) (h : ℝ) (x : Point2)
    (hh : 0 < h) (k : ℤ) (hS : ∀ z∈S,InCellTube h z x) :
    ((S.filter (fun z => z.1=k)).card : ℝ) ≤ 34 := by
  let F := S.filter (fun z => z.1=k)
  have hi : Set.InjOn Prod.snd (↑F : Set TubeCell) := by
    intro z hz w hw he
    exact Prod.ext ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2.symm) he
  have hc : (F.image Prod.snd).card=F.card := Finset.card_image_of_injOn hi
  have hm := integer_interval_mass (F.image Prod.snd) h (16*h) (x.2-h*(k:ℝ)*x.1)
    hh (by positivity) (by
      intro l hl
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hl
      have hs := hS z (Finset.mem_filter.mp hz).1
      change |x.2-(h*(z.1:ℝ)*x.1+h*(z.2:ℝ))| ≤ 16*h at hs
      rw [(Finset.mem_filter.mp hz).2] at hs
      rw [abs_sub_comm]
      convert hs using 1
      congr 1
      ring)
  rw [hc] at hm
  apply (mul_le_mul_iff_of_pos_right hh).mp
  change (F.card : ℝ)*h ≤ 34*h
  linarith only [hm]

private theorem pair_residual (h : ℝ) (z : TubeCell) (x y : Point2)
    (hx : InCellTube h z x) (hy : InCellTube h z y) :
    |(y.2-x.2)-h*(z.1:ℝ)*(y.1-x.1)| ≤ 32*h := by
  have ht := abs_sub (y.2-(h*(z.1:ℝ)*y.1+h*(z.2:ℝ)))
    (x.2-(h*(z.1:ℝ)*x.1+h*(z.2:ℝ)))
  have he : (y.2-(h*(z.1:ℝ)*y.1+h*(z.2:ℝ)))-
      (x.2-(h*(z.1:ℝ)*x.1+h*(z.2:ℝ)))=
      (y.2-x.2)-h*(z.1:ℝ)*(y.1-x.1) := by ring
  rw [he] at ht
  change |x.2-(h*(z.1:ℝ)*x.1+h*(z.2:ℝ))| ≤ 16*h at hx
  change |y.2-(h*(z.1:ℝ)*y.1+h*(z.2:ℝ))| ≤ 16*h at hy
  linarith only [ht,hx,hy]

/-- Literal slope/intercept grid tubes through two actual points have an
inverse-distance multiplicity. Distinct cells are counted once; no
unweighted separation of the underlying point source is required. -/
theorem original_planar_two_point_cell_count (S : Finset TubeCell)
    (h : ℝ) (x y : Point2) (hh : 0 < h) (hh1 : h ≤ 1)
    (hd6 : boxDistance x y ≤ 6)
    (hslope : ∀ z∈S,|h*(z.1:ℝ)| ≤ 2)
    (hx : ∀ z∈S,InCellTube h z x) (hy : ∀ z∈S,InCellTube h z y) :
    (S.card : ℝ)*max (boxDistance x y) h ≤ 30000 := by
  by_cases hne : S.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    norm_num
  let D := boxDistance x y
  let B := S.image Prod.fst
  change (S.card : ℝ)*max D h ≤ 30000
  have hB : (B.card : ℝ)*h ≤ 6 := by
    have hm := integer_interval_mass B h 2 0 hh (by norm_num) (by
      intro k hk
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
      simpa only [sub_zero] using hslope z hz)
    linarith only [hm,hh1]
  have hf : (S.card : ℝ) ≤ 34*B.card := by
    have hm := weighted_fiber_count S Prod.fst 1 34 (fun k _ => by
      simpa only [mul_one] using offset_fiber_bound S h x hh k hx)
    simpa only [mul_one] using hm
  have hmul : (S.card : ℝ)*max D h ≤ 34*((B.card : ℝ)*max D h) := by
    have hm := mul_le_mul_of_nonneg_right hf (show 0 ≤ max D h from hh.le.trans (le_max_right D h))
    nlinarith only [hm]
  by_cases hnear : D ≤ 128*h
  · have hm : max D h ≤ 128*h := max_le hnear (by linarith only [hh])
    have ha := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α:=ℝ) B.card)
    nlinarith only [hmul,ha,hB]
  · have hfar : 128*h < D := lt_of_not_ge hnear
    obtain ⟨z,hz⟩ := hne
    have hp := pair_residual h z x y (hx z hz) (hy z hz)
    have ha := abs_add_le ((y.2-x.2)-h*(z.1:ℝ)*(y.1-x.1)) (h*(z.1:ℝ)*(y.1-x.1))
    rw [sub_add_cancel,abs_mul] at ha
    have hs := mul_le_mul_of_nonneg_right (hslope z hz) (abs_nonneg (y.1-x.1))
    have hd : D ≤ 2*|y.1-x.1|+32*h := by
      apply max_le
      · linarith only [abs_nonneg (y.1-x.1),hh]
      · linarith only [ha,hp,hs]
    have hdx : 0 < |y.1-x.1| := by linarith only [hd,hfar,hh]
    have hdxne : y.1-x.1 ≠ 0 := abs_pos.mp hdx
    have hDdx : D ≤ 4*|y.1-x.1| := by linarith only [hd,hfar,hh]
    have hdx6 : |y.1-x.1| ≤ 6 := (le_max_left _ _).trans hd6
    have hbins := integer_interval_mass B h (32*h/|y.1-x.1|)
      ((y.2-x.2)/(y.1-x.1)) hh (by positivity) (by
        intro k hk
        obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hk
        have hwres := pair_residual h w x y (hx w hw) (hy w hw)
        have he : h*(w.1:ℝ)-(y.2-x.2)/(y.1-x.1)=
            -(((y.2-x.2)-h*(w.1:ℝ)*(y.1-x.1))/(y.1-x.1)) := by field_simp; ring
        rw [he,abs_neg,abs_div]
        exact div_le_div_of_nonneg_right hwres hdx.le)
    have hm := mul_le_mul_of_nonneg_right hbins hdx.le
    have he : (2*(32*h/|y.1-x.1|)+2*h)*|y.1-x.1|=64*h+2*h*|y.1-x.1| := by
      field_simp
      ring
    rw [he] at hm
    have hb : (B.card : ℝ)*|y.1-x.1| ≤ 76 := by
      apply (mul_le_mul_iff_of_pos_right hh).mp
      nlinarith only [hm,hdx6,hh]
    have ht := mul_le_mul_of_nonneg_left hDdx (Nat.cast_nonneg (α:=ℝ) B.card)
    have hmax : max D h=D := max_eq_left (by linarith only [hfar,hh])
    rw [hmax] at hmul ⊢
    nlinarith only [hmul,ht,hb]

end OriginalPlanarTubePairCount
