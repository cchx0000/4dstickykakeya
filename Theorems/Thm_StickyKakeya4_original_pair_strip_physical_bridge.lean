import Theorems.Thm_StickyKakeya4_original_physical_pair_tube
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
namespace OriginalPairStripPhysicalBridge
open OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open PlanarStripIntersection NativeRichPairTubeFamily

/-- One-coordinate correction gives an actual original affine-line witness. -/
theorem original_axis_line_witness (z : Pair) (hne : z.1≠z.2) (v : Point) :
    ∃ s : ℝ, euclideanDistance (linePoint z s) v=
      |PlanarStripIntersection.residual (normalX z) (normalY z) (offset z) v| := by
  rcases (original_pair_normalized z hne).2.2 with hx|hy
  · have hdy : z.2.2-z.1.2≠0 := by
      intro h
      simp only [normalX,h,neg_zero,zero_div,abs_zero] at hx
      norm_num at hx
    let s := (v.2-z.1.2)/(z.2.2-z.1.2)
    have hY : (linePoint z s).2=v.2 := by
      dsimp [linePoint,s]
      field_simp
      ring
    have hzero := affine_pair_line_residual z s
    have hres : PlanarStripIntersection.residual (normalX z) (normalY z) (offset z) v=
        normalX z*(v.1-(linePoint z s).1) := by
      unfold PlanarStripIntersection.residual at hzero ⊢
      rw [hY] at hzero
      nlinarith only [hzero]
    refine ⟨s,?_⟩
    unfold euclideanDistance
    rw [hY,sub_self,zero_pow (by decide : 2≠0),add_zero,Real.sqrt_sq_eq_abs,
      hres,abs_mul,hx,one_mul]
  · have hdx : z.2.1-z.1.1≠0 := by
      intro h
      simp only [normalY,h,zero_div,abs_zero] at hy
      norm_num at hy
    let s := (v.1-z.1.1)/(z.2.1-z.1.1)
    have hX : (linePoint z s).1=v.1 := by
      dsimp [linePoint,s]
      field_simp
      ring
    have hzero := affine_pair_line_residual z s
    have hres : PlanarStripIntersection.residual (normalX z) (normalY z) (offset z) v=
        normalY z*(v.2-(linePoint z s).2) := by
      unfold PlanarStripIntersection.residual at hzero ⊢
      rw [hX] at hzero
      nlinarith only [hzero]
    refine ⟨s,?_⟩
    unfold euclideanDistance
    rw [hX,sub_self,zero_pow (by decide : 2≠0),zero_add,Real.sqrt_sq_eq_abs,
      hres,abs_mul,hy,one_mul]

theorem original_strip_subset_physical (Pts : Finset Point) (w : ℝ) (z : Pair)
    (hne : z.1≠z.2) :
    pairSupport Pts w z⊆physicalPairTube Pts w z := by
  classical
  intro v hv
  obtain ⟨hvP,hvstrip⟩ := Finset.mem_filter.mp hv
  obtain ⟨s,hs⟩ := original_axis_line_witness z hne v
  exact Finset.mem_filter.mpr ⟨hvP,s,hs.trans_le hvstrip⟩
end OriginalPairStripPhysicalBridge
