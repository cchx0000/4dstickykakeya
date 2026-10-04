import Theorems.Thm_StickyKakeya4_actual_rounded_additive_energy
import Theorems.Thm_StickyKakeya4_projection_heavy_cells

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
noncomputable section
open Classical

namespace GKZOriginalRatioGap
open ActualRoundedAdditiveEnergy

def cutoffRatios (A : Finset ℝ) (h : ℝ) : Finset ℝ :=
  (((A.product A).product (A.product A)).filter
    (fun z => h < |z.2.1-z.2.2|)).image
      (fun z => (z.1.1-z.1.2)/(z.2.1-z.2.2))

lemma original_ratio_mem (A : Finset ℝ) {h x x' y y' : ℝ}
    (hx : x∈A) (hx' : x'∈A) (hy : y∈A) (hy' : y'∈A)
    (hden : h < |y-y'|) : (x-x')/(y-y') ∈ cutoffRatios A h := by
  exact Finset.mem_image.mpr ⟨((x,x'),(y,y')),Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx,hx'⟩,
      Finset.mem_product.mpr ⟨hy,hy'⟩⟩,hden⟩,rfl⟩

lemma zero_one_mem_of_original_gap (A : Finset ℝ) {h a b : ℝ} (hh : 0 ≤ h)
    (ha : a∈A) (hb : b∈A) (hab : h < |a-b|) :
    (0:ℝ) ∈ cutoffRatios A h ∧ (1:ℝ) ∈ cutoffRatios A h := by
  have hn : a-b≠0 := abs_pos.mp (hh.trans_lt hab)
  constructor
  · simpa only [sub_self,zero_div] using original_ratio_mem A ha ha ha hb hab
  · simpa only [div_self hn] using original_ratio_mem A ha hb ha hb hab

/-- A genuine gap in the actual original cutoff ratio set eliminates every
near collision with a large denominator. This is the nonlinear GKZ gap step. -/
theorem gap_forces_close_denominator (A : Finset ℝ)
    {h gap delta e1 e2 x x' y y' : ℝ}
    (hh : 0 ≤ h) (hgap : 0 < gap) (he2 : e2≠0)
    (hscale : delta ≤ gap * |e2| * h)
    (havoid : ∀ z ∈ cutoffRatios A h, gap ≤ |z-e1/e2|)
    (hx : x∈A) (hx' : x'∈A) (hy : y∈A) (hy' : y'∈A)
    (hcollision : |(e2*x+e1*y)-(e2*x'+e1*y')| ≤ delta) : |y-y'| ≤ h := by
  by_contra hnot
  have hlarge : h < |y-y'| := lt_of_not_ge hnot
  have hlarge' : h < |y'-y| := by simpa only [abs_sub_comm] using hlarge
  have hdy : y'-y≠0 := abs_pos.mp (hh.trans_lt hlarge')
  have hratio := havoid ((x-x')/(y'-y)) (original_ratio_mem A hx hx' hy' hy hlarge')
  have hid : (((x-x')/(y'-y)-e1/e2)*e2)*(y'-y)=
      (e2*x+e1*y)-(e2*x'+e1*y') := by
    field_simp
    ring
  have hres : |(x-x')/(y'-y)-e1/e2| * |e2| * |y'-y| ≤ delta := by
    simpa only [← hid,abs_mul] using hcollision
  have hlo := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hratio (abs_nonneg e2)) (abs_nonneg (y'-y))
  have hstrict : gap * |e2| * h < gap * |e2| * |y'-y| :=
    mul_lt_mul_of_pos_left hlarge' (mul_pos hgap (abs_pos.mpr he2))
  exact (lt_irrefl delta) (hscale.trans_lt (hstrict.trans_le (hlo.trans hres)))

def linearCode (delta e1 e2 : ℝ) (p : ℝ × ℝ) : ℤ :=
  rounded delta (e2*p.1+e1*p.2)

/-- Literal floor collisions are an admissible input to the gap argument. -/
theorem grid_collision_forces_close_denominator (A : Finset ℝ)
    {h gap delta e1 e2 : ℝ} (hd : 0 < delta) (hh : 0 ≤ h)
    (hgap : 0 < gap) (he2 : e2≠0) (hscale : delta ≤ gap * |e2| * h)
    (havoid : ∀ z ∈ cutoffRatios A h, gap ≤ |z-e1/e2|)
    {p p' : ℝ × ℝ} (hp : p∈A.product A) (hp' : p'∈A.product A)
    (hcell : linearCode delta e1 e2 p=linearCode delta e1 e2 p') :
    |p.2-p'.2| ≤ h := by
  have hclose := ProjectionHeavyCells.same_floor_difference hd hcell
  obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨hp1',hp2'⟩ := Finset.mem_product.mp hp'
  exact gap_forces_close_denominator A hh hgap he2 hscale havoid
    hp1 hp1' hp2 hp2' hclose.le

end GKZOriginalRatioGap
