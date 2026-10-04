import Theorems.Thm_StickyKakeya4_original_planar_tube_pair_count
import Theorems.Thm_StickyKakeya4_original_tube_parameter_integer_count
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalPlanarTubeParameters
open Classical OriginalPlanarTubePairCount OriginalTubeParameterIntegerCount
abbrev Pair2 := Point2 × Point2

def pairSlope (z : Pair2) : ℝ := (z.2.2-z.1.2)/(z.2.1-z.1.1)
def pairOffset (z : Pair2) : ℝ := z.1.2-pairSlope z*z.1.1
def pairCell (h : ℝ) (z : Pair2) : TubeCell :=
  (⌊pairSlope z/h⌋,⌊pairOffset z/h⌋)
def chart (swap : Bool) (x : Point2) : Point2 := if swap then x.swap else x

theorem original_pair_slope_bound (z : Pair2)
    (hne : z.2.1-z.1.1 ≠ 0) (hmax : |z.2.2-z.1.2| ≤ |z.2.1-z.1.1|) :
    |pairSlope z| ≤ 1 := by
  rw [pairSlope,abs_div]
  exact (div_le_one (abs_pos.mpr hne)).mpr hmax

theorem original_pair_graph_endpoints (z : Pair2) (hne : z.2.1-z.1.1 ≠ 0) :
    z.1.2=pairSlope z*z.1.1+pairOffset z ∧
      z.2.2=pairSlope z*z.2.1+pairOffset z := by
  constructor
  · simp [pairOffset]
  · dsimp [pairSlope,pairOffset]
    field_simp [hne]
    ring

/-- Rounding the actual slope and intercept changes the graph value by
at most four mesh units on the original projected box. -/
theorem original_graph_value_rounding (h : ℝ) (z : Pair2) (x : Point2)
    (hh : 0 < h) (hx : |x.1| ≤ 3) :
    |(h*((pairCell h z).1:ℝ)*x.1+h*((pairCell h z).2:ℝ))-
      (pairSlope z*x.1+pairOffset z)| ≤ 4*h := by
  have hs := floor_mesh_error h (pairSlope z) hh
  have hb := floor_mesh_error h (pairOffset z) hh
  have hm := mul_le_mul hs hx (abs_nonneg x.1) hh.le
  have ht := abs_add_le ((h*(⌊pairSlope z/h⌋:ℤ)-pairSlope z)*x.1)
    (h*(⌊pairOffset z/h⌋:ℤ)-pairOffset z)
  rw [abs_mul] at ht
  have he : (h*(⌊pairSlope z/h⌋:ℤ)-pairSlope z)*x.1+
      (h*(⌊pairOffset z/h⌋:ℤ)-pairOffset z)=
      (h*((pairCell h z).1:ℝ)*x.1+h*((pairCell h z).2:ℝ))-
        (pairSlope z*x.1+pairOffset z) := by dsimp [pairCell]; ring
  rw [he] at ht
  linarith only [ht,hm,hb]

theorem original_pair_cell_slope (h : ℝ) (z : Pair2) (hh : 0 < h) (hh1 : h ≤ 1)
    (hne : z.2.1-z.1.1 ≠ 0) (hmax : |z.2.2-z.1.2| ≤ |z.2.1-z.1.1|) :
    |h*((pairCell h z).1:ℝ)| ≤ 2 := by
  have hs := floor_mesh_error h (pairSlope z) hh
  have hb := original_pair_slope_bound z hne hmax
  have ht := abs_add_le (h*(⌊pairSlope z/h⌋:ℤ)-pairSlope z) (pairSlope z)
  rw [sub_add_cancel] at ht
  change |h*(⌊pairSlope z/h⌋:ℤ)| ≤ 2
  linarith only [hs,hb,ht,hh1]

theorem original_pair_strip_in_cell (h rho : ℝ) (z : Pair2) (x : Point2)
    (hh : 0 < h) (hrho : rho ≤ h) (hx : |x.1| ≤ 3)
    (hstrip : |x.2-(pairSlope z*x.1+pairOffset z)| ≤ 2*rho) :
    InCellTube h (pairCell h z) x := by
  have hv := original_graph_value_rounding h z x hh hx
  have ht := abs_sub_le x.2 (pairSlope z*x.1+pairOffset z)
    (h*((pairCell h z).1:ℝ)*x.1+h*((pairCell h z).2:ℝ))
  rw [abs_sub_comm (pairSlope z*x.1+pairOffset z)] at ht
  change |x.2-(h*((pairCell h z).1:ℝ)*x.1+h*((pairCell h z).2:ℝ))| ≤ 16*h
  linarith only [ht,hv,hstrip,hrho,hh]

theorem original_cell_in_pair_strip (h : ℝ) (z : Pair2) (x : Point2)
    (hh : 0 < h) (hx : |x.1| ≤ 3) (hcell : InCellTube h (pairCell h z) x) :
    |x.2-(pairSlope z*x.1+pairOffset z)| ≤ 20*h := by
  have hv := original_graph_value_rounding h z x hh hx
  have ht := abs_sub_le x.2 (h*((pairCell h z).1:ℝ)*x.1+h*((pairCell h z).2:ℝ))
    (pairSlope z*x.1+pairOffset z)
  change |x.2-(h*((pairCell h z).1:ℝ)*x.1+h*((pairCell h z).2:ℝ))| ≤ 16*h at hcell
  linarith only [ht,hv,hcell]

theorem original_pair_endpoints_in_cell (h : ℝ) (z : Pair2) (hh : 0 < h)
    (hne : z.2.1-z.1.1 ≠ 0) (hx : |z.1.1| ≤ 3) (hy : |z.2.1| ≤ 3) :
    InCellTube h (pairCell h z) z.1 ∧ InCellTube h (pairCell h z) z.2 := by
  have he := original_pair_graph_endpoints z hne
  constructor
  · apply original_pair_strip_in_cell h h z z.1 hh le_rfl hx
    rw [← he.1,sub_self,abs_zero]
    positivity
  · apply original_pair_strip_in_cell h h z z.2 hh le_rfl hy
    rw [← he.2,sub_self,abs_zero]
    positivity

theorem original_chart_distance (swap : Bool) (x y : Point2) :
    boxDistance (chart swap x) (chart swap y)=boxDistance x y := by
  cases swap <;> simp [chart,boxDistance,max_comm]

/-- The chart is selected from the actual endpoint differences. -/
theorem exists_original_pair_chart (x y : Point2) (hne : x ≠ y) :
    ∃ swap : Bool,(chart swap y).1-(chart swap x).1 ≠ 0 ∧
      |(chart swap y).2-(chart swap x).2| ≤ |(chart swap y).1-(chart swap x).1| := by
  by_cases h : |y.2-x.2| ≤ |y.1-x.1|
  · refine ⟨false,?_,h⟩
    change y.1-x.1 ≠ 0
    intro hx
    have hy : y.2-x.2=0 := by
      rw [hx,abs_zero] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    exact hne (Prod.ext (sub_eq_zero.mp hx).symm (sub_eq_zero.mp hy).symm)
  · refine ⟨true,?_,(lt_of_not_ge h).le⟩
    change y.2-x.2 ≠ 0
    intro hy
    have hp := abs_nonneg (y.1-x.1)
    rw [hy,abs_zero] at h
    exact h hp

end OriginalPlanarTubeParameters
