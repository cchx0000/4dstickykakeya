import Theorems.Thm_StickyKakeya4_original_three_dimensional_heavy_slice_graph
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace OriginalThreeDimensionalUnitSlabs
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalHeavySliceGraph

def normalLength (rho : ℝ) (d : DirectionLabel) : ℝ :=
  Real.sqrt ((rho*d.2.1)^2+(rho*d.2.2)^2+1)
def unitValue (rho : ℝ) (d : DirectionLabel) (p : Point3) : ℝ := value rho d p/normalLength rho d

lemma normal_length_one_le (rho : ℝ) (d : DirectionLabel) : 1≤normalLength rho d := by
  have hh : (1:ℝ)≤(rho*d.2.1)^2+(rho*d.2.2)^2+1 := by
    nlinarith only [sq_nonneg (rho*d.2.1),sq_nonneg (rho*d.2.2)]
  simpa only [normalLength,Real.sqrt_one] using Real.sqrt_le_sqrt hh

/-- The three displayed coefficients, in the literal permutation chart,
form a Euclidean unit normal. -/
theorem original_normal_coefficients_unit (rho : ℝ) (d : DirectionLabel) :
    (rho*d.2.1/normalLength rho d)^2+(rho*d.2.2/normalLength rho d)^2+
      (1/normalLength rho d)^2=1 := by
  have hp : 0<normalLength rho d := lt_of_lt_of_le (by norm_num) (normal_length_one_le rho d)
  have hs : (normalLength rho d)^2=(rho*d.2.1)^2+(rho*d.2.2)^2+1 :=
    Real.sq_sqrt (by positivity)
  field_simp
  nlinarith only [hs]

/-- Every actual heavy grid slab is contained in a physical slab with
unit normal and width 6rho. The direction labels are constructive coordinates,
not assumed spherical witnesses. -/
theorem original_slab_in_unit_slab (P : Finset Point3) (rho : ℝ) (d : DirectionLabel)
    (k : ℤ) (hrho : 0≤rho) (p : Point3) (hp : p∈slabPoints P rho d k) :
    |unitValue rho d p-rho*k/normalLength rho d|≤3*rho := by
  have hbound := (Finset.mem_filter.mp hp).2
  have hL := normal_length_one_le rho d
  have hpL : 0<normalLength rho d := lt_of_lt_of_le (by norm_num) hL
  rw [unitValue,← sub_div,abs_div,abs_of_pos hpL]
  apply (div_le_iff₀ hpL).mpr
  have hh := mul_le_mul_of_nonneg_left hL (show 0≤3*rho by positivity)
  linarith only [hbound,hh]

/-- A retained direction carries a genuine original heavy physical slab
containing both endpoints of the original pair. -/
theorem retained_direction_original_slab (P : Finset Point3) (rho H : ℝ)
    (z : Pair3) (d : DirectionLabel) (hrho : 0≤rho)
    (hd : d∈goodDirections P rho H z) :
    ∃ k : ℤ, H≤((slabPoints P rho d k).card : ℝ) ∧
      z.1∈slabPoints P rho d k ∧ z.2∈slabPoints P rho d k ∧
      ∀ p∈slabPoints P rho d k,
        |unitValue rho d p-rho*k/normalLength rho d|≤3*rho := by
  obtain ⟨k,_hk,hmass,h1,h2⟩ := (Finset.mem_filter.mp hd).2
  exact ⟨k,hmass,h1,h2,fun p hp => original_slab_in_unit_slab P rho d k hrho p hp⟩

end OriginalThreeDimensionalUnitSlabs
