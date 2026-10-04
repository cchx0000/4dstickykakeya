import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_slab
import Theorems.Thm_StickyKakeya4_finite_transverse_menu_growth

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalThreeDimensionalTubeParameters
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalHeavySlabs

def slope (z : Pair3) (i j : Fin 3) : ℝ := (z.2 j-z.1 j)/(z.2 i-z.1 i)
def offset (z : Pair3) (i j : Fin 3) : ℝ := z.1 j-slope z i j*z.1 i

def parameterCell (rho : ℝ) (i : Fin 3) (z : Pair3) :
    (Fin 3→ℤ)×(Fin 3→ℤ) :=
  (fun j => ⌊slope z i j/rho⌋,fun j => ⌊offset z i j/rho⌋)

lemma original_slope_bound (z : Pair3) (i : Fin 3)
    (hne : z.2 i-z.1 i≠0) (hmax : ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|) :
    ∀ j, |slope z i j|≤1 := by
  intro j
  rw [slope,abs_div]
  exact (div_le_one (abs_pos.mpr hne)).mpr (hmax j)

lemma original_line_graph (z : Pair3) (i j : Fin 3) (l : ℝ)
    (hne : z.2 i-z.1 i≠0) :
    linePoint3 z.1 z.2 l j =
      slope z i j*linePoint3 z.1 z.2 l i+offset z i j := by
  unfold linePoint3 offset slope
  field_simp
  ring

lemma original_graph_point (z : Pair3) (i j : Fin 3) (t : ℝ)
    (hne : z.2 i-z.1 i≠0) :
    linePoint3 z.1 z.2 ((t-z.1 i)/(z.2 i-z.1 i)) j=
      slope z i j*t+offset z i j := by
  unfold linePoint3 offset slope
  field_simp
  ring

/-- The original physical tube gives graph residuals in its actual
largest-coordinate chart; there is no inverse pair-length loss. -/
theorem original_tube_graph_residual (z : Pair3) (i : Fin 3) (x : Point3) (rho : ℝ)
    (hne : z.2 i-z.1 i≠0) (hmax : ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hx : x∈physicalTube3 z.1 z.2 rho) :
    ∀ j, |x j-(slope z i j*x i+offset z i j)|≤2*rho := by
  obtain ⟨l,hl⟩ := hx
  have hp : 0≤rho := (Real.sqrt_nonneg _).trans hl
  have he (j : Fin 3) := (original_coordinate_le_distance x (linePoint3 z.1 z.2 l) j).trans hl
  intro j
  have ha := original_slope_bound z i hne hmax j
  have hmul := mul_le_mul ha (he i) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have ht := abs_sub (x j-linePoint3 z.1 z.2 l j)
    (slope z i j*(x i-linePoint3 z.1 z.2 l i))
  rw [abs_mul] at ht
  have hid : x j-(slope z i j*x i+offset z i j)=
      (x j-linePoint3 z.1 z.2 l j)-slope z i j*(x i-linePoint3 z.1 z.2 l i) := by
    rw [original_line_graph z i j l hne]
    ring
  rw [hid]
  linarith only [ht,hmul,he j]

lemma original_parameter_cell_error (rho : ℝ) (i : Fin 3) (z v : Pair3)
    (hrho : 0<rho) (hcell : parameterCell rho i z=parameterCell rho i v) :
    (∀ j, |slope z i j-slope v i j|≤rho) ∧
    (∀ j, |offset z i j-offset v i j|≤rho) := by
  constructor
  · intro j
    apply FiniteTransverseMenuGrowth.same_floor_abs_sub_le hrho
    exact congrFun (congrArg Prod.fst hcell) j
  · intro j
    apply FiniteTransverseMenuGrowth.same_floor_abs_sub_le hrho
    exact congrFun (congrArg Prod.snd hcell) j

/-- Equality of literal original tube-parameter cells transfers every
bounded original shading point into an eight-times wider original tube.
The representative is an actual original endpoint pair. -/
theorem original_parameter_tube_transfer (rho : ℝ) (i : Fin 3) (z v : Pair3)
    (hrho : 0<rho) (hz : z.2 i-z.1 i≠0) (hv : v.2 i-v.1 i≠0)
    (hmax : ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hcell : parameterCell rho i z=parameterCell rho i v)
    (x : Point3) (hbox : ∀ j, |x j|≤1)
    (hx : x∈physicalTube3 z.1 z.2 rho) :
    x∈physicalTube3 v.1 v.2 (8*rho) := by
  have hres := original_tube_graph_residual z i x rho hz hmax hx
  have hc := original_parameter_cell_error rho i z v hrho hcell
  let l := (x i-v.1 i)/(v.2 i-v.1 i)
  have herr (j : Fin 3) : |x j-linePoint3 v.1 v.2 l j|≤4*rho := by
    rw [original_graph_point v i j (x i) hv]
    have hm := mul_le_mul (hc.1 j) (hbox i) (abs_nonneg _) hrho.le
    have ht1 := abs_add_le ((slope z i j-slope v i j)*x i) (offset z i j-offset v i j)
    rw [abs_mul] at ht1
    have ht2 := abs_add_le (x j-(slope z i j*x i+offset z i j))
      ((slope z i j-slope v i j)*x i+(offset z i j-offset v i j))
    have hid : x j-(slope v i j*x i+offset v i j)=
      (x j-(slope z i j*x i+offset z i j))+
      ((slope z i j-slope v i j)*x i+(offset z i j-offset v i j)) := by ring
    rw [hid]
    linarith only [hm,ht1,ht2,hc.2 j,hres j]
  refine ⟨l,?_⟩
  unfold distance3
  apply (Real.sqrt_le_left (by positivity : 0≤8*rho)).mpr
  have hs (j : Fin 3) : (x j-linePoint3 v.1 v.2 l j)^2≤(4*rho)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (herr j) 2
  nlinarith only [hs 0,hs 1,hs 2,sq_nonneg rho]

end OriginalThreeDimensionalTubeParameters
