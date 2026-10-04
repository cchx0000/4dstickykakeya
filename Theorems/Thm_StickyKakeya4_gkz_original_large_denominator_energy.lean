import Theorems.Thm_StickyKakeya4_gkz_original_dense_ratio_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace GKZOriginalLargeDenominatorEnergy
open GKZOriginalRatioGap GKZOriginalDenseRatioSelection TwoTubePathCollisionCount

/-- A literal grid collision with a large original denominator lies in the
selected ratio window at the precise scale delta ≤ s h². -/
theorem original_collision_ratio_close {delta h s e1 e2 : ℝ}
    (hd : 0 < delta) (hh : 0 < h) (hs : 0 < s)
    (he2lo : h ≤ |e2|) (hscale : delta ≤ s*h^2)
    {p p' : ℝ × ℝ} (hcell : linearCode delta e1 e2 p=linearCode delta e1 e2 p')
    (hlarge : h < |p.2-p'.2|) :
    |(p.1-p'.1)/(p'.2-p.2)-e1/e2| ≤ s := by
  have he2 : e2≠0 := abs_pos.mp (hh.trans_le he2lo)
  have hden : p'.2-p.2≠0 := by
    apply abs_pos.mp
    simpa only [abs_sub_comm] using hh.trans hlarge
  have hid : (((p.1-p'.1)/(p'.2-p.2)-e1/e2)*e2)*(p'.2-p.2)=
      (e2*p.1+e1*p.2)-(e2*p'.1+e1*p'.2) := by
    field_simp
    ring
  have hcollision := (ProjectionHeavyCells.same_floor_difference hd hcell).le
  have hres : |(p.1-p'.1)/(p'.2-p.2)-e1/e2| * |e2| * |p'.2-p.2| ≤ delta := by
    simpa only [← hid, abs_mul] using hcollision
  have hdenlo : h ≤ |p'.2-p.2| := by simpa only [abs_sub_comm] using hlarge.le
  have hmul : h^2 ≤ |e2| * |p'.2-p.2| := by
    simpa only [pow_two] using mul_le_mul he2lo hdenlo hh.le (abs_nonneg e2)
  have hmulpos : 0 < |e2| * |p'.2-p.2| :=
    mul_pos (abs_pos.mpr he2) (abs_pos.mpr hden)
  apply (mul_le_mul_iff_left₀ hmulpos).mp
  calc
    _ = |(p.1-p'.1)/(p'.2-p.2)-e1/e2| * |e2| * |p'.2-p.2| := by ring
    _ ≤ delta := hres
    _ ≤ s*h^2 := hscale
    _ ≤ s*(|e2| * |p'.2-p.2|) := mul_le_mul_of_nonneg_left hmul hs.le
    _ = _ := by ring

/-- Count the same original four coordinates, with a reversible permutation;
no quotient cardinality or collapsed ratio weight is substituted. -/
theorem original_large_denominator_energy (A : Finset ℝ) {delta h s e1 e2 : ℝ}
    (hd : 0 < delta) (hh : 0 < h) (hs : 0 < s)
    (he2lo : h ≤ |e2|) (hscale : delta ≤ s*h^2) :
    ((collisions (A.product A) (linearCode delta e1 e2)).filter
      (fun e => h < |e.1.2-e.2.2|)).card ≤
    ((originalLargeDenominators A h).filter
      (fun p => |(p.1.1-p.1.2)/(p.2.1-p.2.2)-e1/e2| ≤ s)).card := by
  apply Finset.card_le_card_of_injOn
    (fun e : (ℝ × ℝ) × (ℝ × ℝ) => ((e.1.1,e.2.1),(e.2.2,e.1.2)))
  · intro e he
    obtain ⟨he, hlarge⟩ := Finset.mem_filter.mp he
    obtain ⟨hp, hp', hcell⟩ := (mem_collisions _ _ _).mp he
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    obtain ⟨hx', hy'⟩ := Finset.mem_product.mp hp'
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hx, hx'⟩, Finset.mem_product.mpr ⟨hy', hy⟩⟩,
        by simpa only [abs_sub_comm] using hlarge⟩
    · exact original_collision_ratio_close hd hh hs he2lo hscale hcell hlarge
  · intro e _ f _ hef
    exact Prod.ext
      (Prod.ext (congrArg (fun v => v.1.1) hef) (congrArg (fun v => v.2.2) hef))
      (Prod.ext (congrArg (fun v => v.1.2) hef) (congrArg (fun v => v.2.1) hef))

end GKZOriginalLargeDenominatorEnergy
