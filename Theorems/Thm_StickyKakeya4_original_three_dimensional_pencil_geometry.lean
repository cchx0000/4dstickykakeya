import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_parameters
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
namespace OriginalThreeDimensionalPencilGeometry
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters

def graphResidual (z : Pair3) (i : Fin 3) (x : Point3) (j : Fin 3) : ℝ :=
  x j-(slope z i j*x i+offset z i j)

def slopeDifference (stem z : Pair3) (e : Equiv.Perm (Fin 3)) (j : Fin 3) : ℝ :=
  slope z (e 2) (e j)-slope stem (e 2) (e j)

def pencilChart (stem z : Pair3) (e : Equiv.Perm (Fin 3)) : Bool :=
  if |slopeDifference stem z e 0| ≤ |slopeDifference stem z e 1| then false else true

def pencilScalar (stem z : Pair3) (e : Equiv.Perm (Fin 3)) : ℝ :=
  if |slopeDifference stem z e 0| ≤ |slopeDifference stem z e 1|
  then -slopeDifference stem z e 0/slopeDifference stem z e 1
  else -slopeDifference stem z e 1/slopeDifference stem z e 0

def pencilValue (stem : Pair3) (e : Equiv.Perm (Fin 3)) (chart : Bool)
    (t : ℝ) (x : Point3) : ℝ :=
  if chart then t*graphResidual stem (e 2) x (e 0)+graphResidual stem (e 2) x (e 1)
  else graphResidual stem (e 2) x (e 0)+t*graphResidual stem (e 2) x (e 1)

/-- The transverse coordinates come from the actual original slopes. -/
lemma original_transverse_coordinates (stem z : Pair3) (e : Equiv.Perm (Fin 3))
    (hs : stem.2 (e 2)-stem.1 (e 2) ≠ 0) (hz : z.2 (e 2)-z.1 (e 2) ≠ 0)
    (htrans : ∃ j, slope z (e 2) j ≠ slope stem (e 2) j) :
    slopeDifference stem z e 0 ≠ 0 ∨ slopeDifference stem z e 1 ≠ 0 := by
  by_contra! h
  obtain ⟨j,hj⟩ := htrans
  apply hj
  have h0 := sub_eq_zero.mp h.1
  have h1 := sub_eq_zero.mp h.2
  change slope z (e 2) (e 0)=slope stem (e 2) (e 0) at h0
  change slope z (e 2) (e 1)=slope stem (e 2) (e 1) at h1
  have h2 : slope z (e 2) (e 2)=slope stem (e 2) (e 2) := by simp [OriginalThreeDimensionalTubeParameters.slope,hs,hz]
  have hall (k : Fin 3) : slope z (e 2) (e k)=slope stem (e 2) (e k) := by
    fin_cases k <;> assumption
  simpa using hall (e.symm j)

/-- Two literal scalar charts supply a bounded perpendicular coefficient. -/
theorem original_pencil_scalar_spec (stem z : Pair3) (e : Equiv.Perm (Fin 3))
    (htrans : slopeDifference stem z e 0 ≠ 0 ∨ slopeDifference stem z e 1 ≠ 0) :
    |pencilScalar stem z e| ≤ 1 ∧
      (if pencilChart stem z e then
        pencilScalar stem z e*slopeDifference stem z e 0+slopeDifference stem z e 1
       else slopeDifference stem z e 0+pencilScalar stem z e*slopeDifference stem z e 1)=0 := by
  by_cases h : |slopeDifference stem z e 0| ≤ |slopeDifference stem z e 1|
  · have hn : slopeDifference stem z e 1 ≠ 0 := by
      intro hz
      rw [hz,abs_zero] at h
      have hz0 := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
      exact htrans.elim (fun hh => hh hz0) (fun hh => hh hz)
    simp only [pencilScalar,pencilChart,if_pos h,Bool.false_eq_true,↓reduceIte]
    constructor
    · rw [abs_div,abs_neg]
      exact (div_le_one (abs_pos.mpr hn)).mpr h
    · field_simp
      ring
  · have hn : slopeDifference stem z e 0 ≠ 0 := by
      intro hz
      rw [hz,abs_zero] at h
      exact h (abs_nonneg _)
    simp only [pencilScalar,pencilChart,if_neg h,↓reduceIte]
    constructor
    · rw [abs_div,abs_neg]
      exact (div_le_one (abs_pos.mpr hn)).mpr (le_of_lt (lt_of_not_ge h))
    · field_simp
      ring

private lemma weighted_two_bound (A B u v E : ℝ)
    (hA : |A| ≤ 1) (hB : |B| ≤ 1) (hu : |u| ≤ E) (hv : |v| ≤ E) :
    |A*u+B*v| ≤ 2*E := by
  have h1 := mul_le_mul hA hu (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have h2 := mul_le_mul hB hv (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have h3 := abs_add_le (A*u) (B*v)
  rw [abs_mul,abs_mul] at h3
  linarith only [h1,h2,h3]

/-- A genuine common point of the two original physical tubes anchors the
entire brush tube in the exact stem plane band. No bounded-source or
shading-only containment is substituted for the original tube. -/
theorem original_pencil_band_support (stem z : Pair3) (e : Equiv.Perm (Fin 3))
    (rho : ℝ) (p x : Point3)
    (hs : stem.2 (e 2)-stem.1 (e 2) ≠ 0) (hz : z.2 (e 2)-z.1 (e 2) ≠ 0)
    (hsmax : ∀ j, |stem.2 j-stem.1 j| ≤ |stem.2 (e 2)-stem.1 (e 2)|)
    (hzmax : ∀ j, |z.2 j-z.1 j| ≤ |z.2 (e 2)-z.1 (e 2)|)
    (htrans : slopeDifference stem z e 0 ≠ 0 ∨ slopeDifference stem z e 1 ≠ 0)
    (hps : p ∈ physicalTube3 stem.1 stem.2 (8*rho))
    (hpz : p ∈ physicalTube3 z.1 z.2 (8*rho))
    (hx : x ∈ physicalTube3 z.1 z.2 (8*rho)) :
    |pencilValue stem e (pencilChart stem z e) (pencilScalar stem z e) x| ≤ 96*rho := by
  have hsp := original_tube_graph_residual stem (e 2) p (8*rho) hs hsmax hps
  have hzp := original_tube_graph_residual z (e 2) p (8*rho) hz hzmax hpz
  have hzx := original_tube_graph_residual z (e 2) x (8*rho) hz hzmax hx
  obtain ⟨ht,hort⟩ := original_pencil_scalar_spec stem z e htrans
  let A : ℝ := if pencilChart stem z e then pencilScalar stem z e else 1
  let B : ℝ := if pencilChart stem z e then 1 else pencilScalar stem z e
  have hA : |A| ≤ 1 := by dsimp [A]; split <;> simp_all
  have hB : |B| ≤ 1 := by dsimp [B]; split <;> simp_all
  have horth : A*slopeDifference stem z e 0+B*slopeDifference stem z e 1=0 := by
    dsimp [A,B]
    split <;> simp_all
  have hbase (j : Fin 3) :
      |graphResidual stem (e 2) p j-graphResidual z (e 2) p j| ≤ 32*rho := by
    exact (abs_sub _ _).trans (by dsimp [graphResidual]; linarith only [hsp j,hzp j])
  have hsmall := weighted_two_bound A B (graphResidual z (e 2) x (e 0))
    (graphResidual z (e 2) x (e 1)) (16*rho) hA hB
    (by dsimp [graphResidual]; linarith only [hzx (e 0)])
    (by dsimp [graphResidual]; linarith only [hzx (e 1)])
  have hlarge := weighted_two_bound A B
    (graphResidual stem (e 2) p (e 0)-graphResidual z (e 2) p (e 0))
    (graphResidual stem (e 2) p (e 1)-graphResidual z (e 2) p (e 1))
    (32*rho) hA hB (hbase _) (hbase _)
  have hid : pencilValue stem e (pencilChart stem z e) (pencilScalar stem z e) x=
      (A*graphResidual z (e 2) x (e 0)+B*graphResidual z (e 2) x (e 1))+
      (A*(graphResidual stem (e 2) p (e 0)-graphResidual z (e 2) p (e 0))+
       B*(graphResidual stem (e 2) p (e 1)-graphResidual z (e 2) p (e 1))) := by
    have hval : pencilValue stem e (pencilChart stem z e) (pencilScalar stem z e) x=
        A*graphResidual stem (e 2) x (e 0)+B*graphResidual stem (e 2) x (e 1) := by
      dsimp [pencilValue,A,B]
      split <;> ring
    rw [hval]
    dsimp [graphResidual,slopeDifference] at *
    linear_combination (x (e 2)-p (e 2))*horth
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith only [hsmall,hlarge])

lemma original_bounded_stem_residual (stem : Pair3) (i : Fin 3) (x : Point3)
    (hs : stem.2 i-stem.1 i ≠ 0)
    (hsmax : ∀ j, |stem.2 j-stem.1 j| ≤ |stem.2 i-stem.1 i|)
    (hp : ∀ j, |stem.1 j| ≤ 1) (hx : ∀ j, |x j| ≤ 1) :
    ∀ j, |graphResidual stem i x j| ≤ 4 := by
  intro j
  have ha := original_slope_bound stem i hs hsmax j
  have hm1 := mul_le_mul ha (hp i) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hm2 := mul_le_mul ha (hx i) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hb : |offset stem i j| ≤ 2 := by
    dsimp [offset]
    have ht := abs_sub (stem.1 j) (slope stem i j*stem.1 i)
    rw [abs_mul] at ht
    linarith only [ht,hp j,hm1]
  have ht := abs_sub (x j) (slope stem i j*x i+offset stem i j)
  have ht2 := abs_add_le (slope stem i j*x i) (offset stem i j)
  rw [abs_mul] at ht2
  dsimp [graphResidual]
  linarith only [ht,ht2,hb,hx j,hm2]

/-- Equality of literal scalar bins transfers the full original bounded
population to an actual representative's exact, unnormalized plane band. -/
theorem original_pencil_bin_transfer (stem : Pair3) (e : Equiv.Perm (Fin 3))
    (chart : Bool) (t u rho : ℝ) (x : Point3) (hrho : 0 < rho)
    (hs : stem.2 (e 2)-stem.1 (e 2) ≠ 0)
    (hsmax : ∀ j, |stem.2 j-stem.1 j| ≤ |stem.2 (e 2)-stem.1 (e 2)|)
    (hp : ∀ j, |stem.1 j| ≤ 1) (hx : ∀ j, |x j| ≤ 1)
    (hcell : ⌊t/rho⌋=⌊u/rho⌋)
    (hband : |pencilValue stem e chart t x| ≤ 96*rho) :
    |pencilValue stem e chart u x| ≤ 100*rho := by
  have htu := FiniteTransverseMenuGrowth.same_floor_abs_sub_le hrho hcell
  have hut : |u-t| ≤ rho := by simpa only [abs_sub_comm] using htu
  have hres := original_bounded_stem_residual stem (e 2) x hs hsmax hp hx
  have he : |pencilValue stem e chart u x-pencilValue stem e chart t x| ≤ 4*rho := by
    cases chart <;> dsimp [pencilValue]
    · have hid : graphResidual stem (e 2) x (e 0)+u*graphResidual stem (e 2) x (e 1)-
          (graphResidual stem (e 2) x (e 0)+t*graphResidual stem (e 2) x (e 1))=
          (u-t)*graphResidual stem (e 2) x (e 1) := by ring
      rw [hid,abs_mul]
      nlinarith only [mul_le_mul hut (hres (e 1)) (abs_nonneg _) hrho.le]
    · have hid : u*graphResidual stem (e 2) x (e 0)+graphResidual stem (e 2) x (e 1)-
          (t*graphResidual stem (e 2) x (e 0)+graphResidual stem (e 2) x (e 1))=
          (u-t)*graphResidual stem (e 2) x (e 0) := by ring
      rw [hid,abs_mul]
      nlinarith only [mul_le_mul hut (hres (e 0)) (abs_nonneg _) hrho.le]
  have ht := abs_sub_le (pencilValue stem e chart u x) (pencilValue stem e chart t x) 0
  simp only [sub_zero] at ht
  linarith only [ht,he,hband]

end OriginalThreeDimensionalPencilGeometry
