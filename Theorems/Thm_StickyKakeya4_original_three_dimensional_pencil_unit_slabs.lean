import Theorems.Thm_StickyKakeya4_original_three_dimensional_pencil_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalPencilUnitSlabs
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalPencilGeometry

def rawPencilNormal (stem : Pair3) (e : Equiv.Perm (Fin 3)) (chart : Bool) (t : ℝ) : Point3 :=
  let A : ℝ := if chart then t else 1
  let B : ℝ := if chart then 1 else t
  fun j => ![A,B,-(A*slope stem (e 2) (e 0)+B*slope stem (e 2) (e 1))] (e.symm j)

def rawPencilCenter (stem : Pair3) (e : Equiv.Perm (Fin 3)) (chart : Bool) (t : ℝ) : ℝ :=
  (if chart then t else 1)*offset stem (e 2) (e 0)+
    (if chart then 1 else t)*offset stem (e 2) (e 1)

def pencilNormalLength (stem : Pair3) (e : Equiv.Perm (Fin 3)) (chart : Bool) (t : ℝ) : ℝ :=
  Real.sqrt (∑ j, (rawPencilNormal stem e chart t j)^2)

def pencilUnitNormal (stem : Pair3) (e : Equiv.Perm (Fin 3)) (chart : Bool) (t : ℝ) : Point3 :=
  fun j => rawPencilNormal stem e chart t j/pencilNormalLength stem e chart t

/-- The scalar pencil band is exactly an affine plane residual, before
normalization or width enlargement. -/
lemma original_pencil_affine_identity (stem : Pair3) (e : Equiv.Perm (Fin 3))
    (chart : Bool) (t : ℝ) (x : Point3) :
    (∑ j, rawPencilNormal stem e chart t j*x j)-rawPencilCenter stem e chart t=
      pencilValue stem e chart t x := by
  rw [← Equiv.sum_comp e (fun j => rawPencilNormal stem e chart t j*x j)]
  cases chart <;> simp [rawPencilNormal,rawPencilCenter,pencilValue,graphResidual,Fin.sum_univ_three] <;> ring

lemma original_pencil_normal_length (stem : Pair3) (e : Equiv.Perm (Fin 3))
    (chart : Bool) (t : ℝ) : 1 ≤ pencilNormalLength stem e chart t := by
  apply Real.le_sqrt_of_sq_le
  rw [← Equiv.sum_comp e (fun j => (rawPencilNormal stem e chart t j)^2)]
  cases chart <;> simp [rawPencilNormal,Fin.sum_univ_three] <;>
    nlinarith only [sq_nonneg t,
      sq_nonneg (slope stem (e 2) (e 0)+t*slope stem (e 2) (e 1)),
      sq_nonneg (t*slope stem (e 2) (e 0)+slope stem (e 2) (e 1))]

/-- The exact plane contains the entire original stem line. -/
lemma original_pencil_contains_stem (stem : Pair3) (e : Equiv.Perm (Fin 3))
    (chart : Bool) (t l : ℝ) (hs : stem.2 (e 2)-stem.1 (e 2) ≠ 0) :
    pencilValue stem e chart t (linePoint3 stem.1 stem.2 l)=0 := by
  have hr (j : Fin 3) : graphResidual stem (e 2) (linePoint3 stem.1 stem.2 l) j=0 := by
    dsimp [graphResidual]
    rw [original_line_graph stem (e 2) j l hs]
    ring
  cases chart <;> simp [pencilValue,hr]

/-- Only after the exact-band overlap count, the same plane can be stated
with a genuine Euclidean unit normal. Its physical half-width is at most
100rho; the exact raw residual is retained in the equality field. -/
theorem original_pencil_unit_slab (stem : Pair3) (e : Equiv.Perm (Fin 3))
    (chart : Bool) (t : ℝ) :
    (∑ j, (pencilUnitNormal stem e chart t j)^2)=1 ∧
      (∀ x : Point3, (∑ j, pencilUnitNormal stem e chart t j*x j)-
        rawPencilCenter stem e chart t/pencilNormalLength stem e chart t=
        pencilValue stem e chart t x/pencilNormalLength stem e chart t) ∧
      ∀ rho : ℝ, 0 ≤ rho → ∀ x : Point3,
        |pencilValue stem e chart t x| ≤ 100*rho →
        |(∑ j, pencilUnitNormal stem e chart t j*x j)-
          rawPencilCenter stem e chart t/pencilNormalLength stem e chart t| ≤ 100*rho := by
  let L := pencilNormalLength stem e chart t
  have hL : 1 ≤ L := original_pencil_normal_length stem e chart t
  have hpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLsq : L^2=∑ j, (rawPencilNormal stem e chart t j)^2 := by
    exact Real.sq_sqrt (by positivity)
  have hid (x : Point3) : (∑ j, pencilUnitNormal stem e chart t j*x j)-
      rawPencilCenter stem e chart t/L=pencilValue stem e chart t x/L := by
    simp only [pencilUnitNormal,div_mul_eq_mul_div,← Finset.sum_div]
    change (∑ j, rawPencilNormal stem e chart t j*x j)/L-rawPencilCenter stem e chart t/L=_
    rw [← sub_div,original_pencil_affine_identity]
  refine ⟨?_,hid,?_⟩
  · simp only [pencilUnitNormal,div_pow,← Finset.sum_div]
    change (∑ j, (rawPencilNormal stem e chart t j)^2)/L^2=1
    rw [← hLsq,div_self (ne_of_gt (sq_pos_of_pos hpos))]
  · intro rho hrho x hx
    rw [hid,abs_div,abs_of_pos hpos]
    apply (div_le_iff₀ hpos).mpr
    have hh := mul_le_mul_of_nonneg_left hL (show 0 ≤ 100*rho by positivity)
    exact hx.trans (by simpa only [mul_one] using hh)

end OriginalThreeDimensionalPencilUnitSlabs
