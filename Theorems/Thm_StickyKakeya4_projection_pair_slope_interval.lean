import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Actual two-point geometry for the finite Kaufman projection argument.
All slope intervals below are derived from the projection residual. -/

open Finset

namespace ProjectionPairSlopeInterval

def pairDistance (dx dy : ℝ) : ℝ := max |dx| |dy|

theorem horizontal_le_radius_add_vertical
    {dx dy lam r : ℝ} (hlam : |lam| ≤ 1)
    (hproj : |dx - lam * dy| ≤ r) :
    |dx| ≤ r + |dy| := by
  calc
    |dx| = |(dx - lam * dy) + lam * dy| := by ring_nf
    _ ≤ |dx - lam * dy| + |lam * dy| := abs_add_le _ _
    _ = |dx - lam * dy| + |lam| * |dy| := by rw [abs_mul]
    _ ≤ r + 1 * |dy| := add_le_add hproj (mul_le_mul_of_nonneg_right hlam (abs_nonneg dy))
    _ = r + |dy| := by ring

theorem vertical_ge_half_distance
    {dx dy lam r : ℝ} (hlam : |lam| ≤ 1) (hr : 0 ≤ r)
    (hfar : 4 * r ≤ pairDistance dx dy)
    (hproj : |dx - lam * dy| ≤ r) :
    pairDistance dx dy / 2 ≤ |dy| := by
  have hx := horizontal_le_radius_add_vertical hlam hproj
  have hd : pairDistance dx dy ≤ r + |dy| := by
    exact max_le hx (by linarith)
  linarith

theorem actual_slope_interval
    {dx dy lam r : ℝ} (hlam : |lam| ≤ 1) (hr : 0 ≤ r)
    (hd : 0 < pairDistance dx dy)
    (hfar : 4 * r ≤ pairDistance dx dy)
    (hproj : |dx - lam * dy| ≤ r) :
    dy ≠ 0 ∧ |lam - dx / dy| ≤ 2 * r / pairDistance dx dy := by
  have hhalf := vertical_ge_half_distance hlam hr hfar hproj
  have hv : 0 < |dy| := by linarith
  have hdy : dy ≠ 0 := abs_pos.mp hv
  refine ⟨hdy, ?_⟩
  have hid : lam - dx / dy = -(dx - lam * dy) / dy := by
    field_simp
    ring
  calc
    |lam - dx / dy| = |dx - lam * dy| / |dy| := by rw [hid, abs_div, abs_neg]
    _ ≤ r / |dy| := div_le_div_of_nonneg_right hproj (le_of_lt hv)
    _ ≤ 2 * r / pairDistance dx dy := by
      apply (div_le_div_iff₀ hv hd).2
      nlinarith [mul_nonneg hr (sub_nonneg.mpr hhalf)]

theorem slope_radius_query_range
    {delta r d : ℝ} (hdelta : 0 < delta) (hdr : delta ≤ r)
    (hfar : 4 * r ≤ d) (hdtop : d ≤ 2) :
    0 < d ∧ delta ≤ 2 * r / d ∧ 2 * r / d ≤ 1 / 2 := by
  have hr : 0 < r := lt_of_lt_of_le hdelta hdr
  have hd : 0 < d := by linarith
  refine ⟨hd, ?_, ?_⟩
  · have hh : r ≤ 2 * r / d := by
      apply (le_div_iff₀ hd).2
      nlinarith [mul_nonneg (le_of_lt hr) (sub_nonneg.mpr hdtop)]
    exact hdr.trans hh
  · apply (div_le_iff₀ hd).2
    linarith

theorem bounded_point_pair_slope_interval
    {x y x' y' lam delta r : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hx' : |x'| ≤ 1) (hy' : |y'| ≤ 1)
    (hlam : |lam| ≤ 1) (hdelta : 0 < delta) (hdr : delta ≤ r)
    (hfar : 4 * r ≤ pairDistance (x - x') (y - y'))
    (hproj : |(x - lam * y) - (x' - lam * y')| ≤ r) :
    y - y' ≠ 0 ∧
      |lam - (x - x') / (y - y')| ≤ 2 * r / pairDistance (x - x') (y - y') ∧
      delta ≤ 2 * r / pairDistance (x - x') (y - y') ∧
      2 * r / pairDistance (x - x') (y - y') ≤ 1 / 2 := by
  have hdx : |x - x'| ≤ 2 := (abs_sub x x').trans (by linarith)
  have hdy : |y - y'| ≤ 2 := (abs_sub y y').trans (by linarith)
  have htop : pairDistance (x - x') (y - y') ≤ 2 := max_le hdx hdy
  obtain ⟨hd, hlo, hhi⟩ := slope_radius_query_range hdelta hdr hfar htop
  have hp : |(x - x') - lam * (y - y')| ≤ r := by
    have heq : (x - x') - lam * (y - y') = (x - lam * y) - (x' - lam * y') := by ring
    rw [heq]
    exact hproj
  obtain ⟨hne, hinterval⟩ := actual_slope_interval hlam
    (le_of_lt (lt_of_lt_of_le hdelta hdr)) hd hfar hp
  exact ⟨hne, hinterval, hlo, hhi⟩

theorem actual_slope_fiber_subset
    (Lambda : Finset ℝ) {dx dy r : ℝ}
    (hLambda : ∀ lam ∈ Lambda, |lam| ≤ 1)
    (hr : 0 ≤ r) (hd : 0 < pairDistance dx dy)
    (hfar : 4 * r ≤ pairDistance dx dy) :
    Lambda.filter (fun lam => |dx - lam * dy| ≤ r) ⊆
      Lambda.filter (fun lam => |lam - dx / dy| ≤ 2 * r / pairDistance dx dy) := by
  classical
  intro lam hmem
  obtain ⟨hl, hp⟩ := mem_filter.mp hmem
  exact mem_filter.mpr ⟨hl, (actual_slope_interval (hLambda lam hl) hr hd hfar hp).2⟩

theorem actual_slope_fiber_card_le
    (Lambda : Finset ℝ) {dx dy delta r K t : ℝ}
    (hLambda : ∀ lam ∈ Lambda, |lam| ≤ 1)
    (hdelta : 0 < delta) (hdr : delta ≤ r)
    (hfar : 4 * r ≤ pairDistance dx dy) (htop : pairDistance dx dy ≤ 2)
    (hFrostman : ∀ c s : ℝ, delta ≤ s → s ≤ 1 →
      ((Lambda.filter (fun lam => |lam - c| ≤ s)).card : ℝ) ≤
        K * s ^ t * (Lambda.card : ℝ)) :
    ((Lambda.filter (fun lam => |dx - lam * dy| ≤ r)).card : ℝ) ≤
      K * (2 * r / pairDistance dx dy) ^ t * (Lambda.card : ℝ) := by
  classical
  obtain ⟨hd, hlo, hhi⟩ := slope_radius_query_range hdelta hdr hfar htop
  have hsub := actual_slope_fiber_subset Lambda hLambda
    (le_of_lt (lt_of_lt_of_le hdelta hdr)) hd hfar
  have hcard : ((Lambda.filter (fun lam => |dx - lam * dy| ≤ r)).card : ℝ) ≤
      ((Lambda.filter (fun lam => |lam - dx / dy| ≤ 2 * r / pairDistance dx dy)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans (hFrostman _ _ hlo (by linarith))

end ProjectionPairSlopeInterval
