import Theorems.Thm_StickyKakeya4_scalar_katz_tao_slope_bound
import Theorems.Thm_StickyKakeya4_nested_plane_quantization

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
namespace NativeSamePointSlopeConsistency
open ScalarKatzTaoSlopeBound NestedPlaneQuantization

/-- This version does not presume that the new lower frame has already
been aligned with the old higher frame. L is the ACTUAL old quotient. -/
lemma functional_witness_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (p origin v : E) (t y eu eh : ℝ)
    (hlower : ‖p - (origin + t • v)‖ ≤ eu) (hhigher : |y - L p| ≤ eh) :
    |y - L origin - L v * t| ≤ eh + ‖L‖ * eu := by
  have hm : |L p - (L origin + t * L v)| ≤ ‖L‖ * eu := by
    have h := (L.le_opNorm (p - (origin + t • v))).trans
      (mul_le_mul_of_nonneg_left hlower (norm_nonneg L))
    simpa only [map_sub, map_add, map_smul, smul_eq_mul, Real.norm_eq_abs] using h
  calc
    _ = |(y - L p) + (L p - (L origin + t * L v))| := by congr 1; ring
    _ ≤ |y - L p| + |L p - (L origin + t * L v)| := abs_add_le _ _
    _ ≤ eh + ‖L‖ * eu := add_le_add hhigher hm

/-- Dense actual lower-line parameters and the actual higher quotient KT
law force small normal component before any simultaneous frame is chosen. -/
theorem from_actual_line_and_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (J : Finset ℤ) (p : ℤ → E) (origin v : E)
    (y : ℤ → ℝ) (Y : Finset ℝ) (delta rho x0 eu eh K gamma lam : ℝ)
    (hd : 0 < delta) (hr : 0 < rho) (hr1 : rho ≤ 1)
    (heu : 0 ≤ eu) (heh : 0 ≤ eh)
    (hsmall : eh + ‖L‖ * eu ≤ rho) (hstep : ‖L‖ * ‖v‖ * delta ≤ rho)
    (hK : 1 ≤ K) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hl : 0 < lam)
    (hdense : lam / delta ≤ (J.card : ℝ))
    (hY : ∀z∈Y,-1 ≤ z ∧ z ≤ 1) (hy : ∀n∈J,y n∈Y)
    (hKT : IntervalKatzTao Y rho K gamma)
    (hx : ∀n∈J,|x0+delta*(n:ℝ)| ≤ 1)
    (hlower : ∀n∈J,‖p n - (origin+(x0+delta*(n:ℝ)) • v)‖ ≤ eu)
    (hhigher : ∀n∈J,|y n - L (p n)| ≤ eh) :
    |L v| ≤ rho * max 1 ((32*K/lam)^(1/gamma)) := by
  let error := eh+‖L‖*eu
  have he : 0 ≤ error := by dsimp [error]; positivity
  have heq : (error/delta)*delta=error := div_mul_cancel₀ error hd.ne'
  apply scalar_slope_bound J y Y delta rho (error/delta) (L v) x0 (L origin)
    K gamma lam hd hr hr1 (div_nonneg he hd.le) hK hg hg1 hl hdense hY hy hKT
  · rw [heq]
    exact hsmall
  · have hv : |L v| ≤ ‖L‖*‖v‖ := by simpa only [Real.norm_eq_abs] using L.le_opNorm v
    exact (mul_le_mul_of_nonneg_right hv hd.le).trans hstep
  · exact hx
  · intro n hn
    rw [heq]
    exact functional_witness_error L (p n) origin v _ (y n) eu eh (hlower n hn) (hhigher n hn)

/-- Both witnesses refer to the SAME physical point. The upper quotient
therefore has slope B-C-FA along the retained lower grain. -/
lemma same_point_error (p : Point) (A B C F c d y eu ev eh : ℝ)
    (hu : |p 1 - (c + A * p 0)| ≤ eu)
    (hv : |p 2 - (d + B * p 0)| ≤ ev)
    (hh : |y - (p 2 - C * p 0 - F * p 1)| ≤ eh) :
    |y - (d - F * c) - (B - correctedSlope A C F) * p 0| ≤
      eh + ev + |F| * eu := by
  have hid : y - (d - F * c) - (B - correctedSlope A C F) * p 0 =
      (y - (p 2 - C * p 0 - F * p 1)) +
        (p 2 - (d + B * p 0)) - F * (p 1 - (c + A * p 0)) := by
    dsimp [correctedSlope]
    ring
  rw [hid]
  calc
    _ ≤ |(y - (p 2 - C * p 0 - F * p 1)) + (p 2 - (d + B * p 0))| +
        |F * (p 1 - (c + A * p 0))| := abs_sub _ _
    _ ≤ (|y - (p 2 - C * p 0 - F * p 1)| + |p 2 - (d + B * p 0)|) +
        |F| * |p 1 - (c + A * p 0)| := by
      rw [abs_mul]
      exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ eh + ev + |F| * eu :=
      add_le_add (add_le_add hh hv) (mul_le_mul_of_nonneg_left hu (abs_nonneg F))

lemma bounded_discrepancy (A B C F : ℝ)
    (hA : |A| ≤ 1) (hB : |B| ≤ 1) (hC : |C| ≤ 1) (hF : |F| ≤ 1) :
    |B - correctedSlope A C F| ≤ 3 := by
  have hprod : |F| * |A| ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hF hA (abs_nonneg A) (by norm_num : (0:ℝ) ≤ 1)
  calc
    _ ≤ |B| + |C + F * A| := abs_sub _ _
    _ ≤ |B| + (|C| + |F| * |A|) := by
      exact add_le_add_left (by simpa only [abs_mul] using abs_add_le C (F * A)) _
    _ ≤ 3 := by linarith

/-- The Step3 coefficient estimate is DERIVED from actual lower-grain points
and higher-quotient witnesses. Density and Katz--Tao apply to their original
finite sets; neither consistency nor a projected image count is an input. -/
theorem from_actual_double_representation
    (J : Finset ℤ) (p : ℤ → Point) (y : ℤ → ℝ) (Y : Finset ℝ)
    (delta rho A B C F c d x0 eu ev eh K gamma lam : ℝ)
    (hd : 0 < delta) (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hA : |A| ≤ 1) (hB : |B| ≤ 1) (hC : |C| ≤ 1) (hF : |F| ≤ 1)
    (heu : 0 ≤ eu) (hev : 0 ≤ ev) (heh : 0 ≤ eh)
    (hsmall : eh + ev + |F| * eu ≤ rho) (hstep : 3 * delta ≤ rho)
    (hK : 1 ≤ K) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hl : 0 < lam)
    (hdense : lam / delta ≤ (J.card : ℝ))
    (hY : ∀z∈Y,-1 ≤ z ∧ z ≤ 1) (hy : ∀n∈J,y n∈Y)
    (hKT : IntervalKatzTao Y rho K gamma)
    (hx : ∀n∈J,p n 0=x0+delta*(n:ℝ)) (hbounded : ∀n∈J,|p n 0| ≤ 1)
    (hu : ∀n∈J,|p n 1 - (c+A*p n 0)| ≤ eu)
    (hv : ∀n∈J,|p n 2 - (d+B*p n 0)| ≤ ev)
    (hh : ∀n∈J,|y n - (p n 2-C*p n 0-F*p n 1)| ≤ eh) :
    |B - correctedSlope A C F| ≤ rho * max 1 ((32*K/lam)^(1/gamma)) := by
  let error := eh+ev+|F|*eu
  have he : 0 ≤ error := by dsimp [error]; positivity
  have heq : (error/delta)*delta=error := div_mul_cancel₀ error hd.ne'
  apply scalar_slope_bound J y Y delta rho (error/delta)
    (B-correctedSlope A C F) x0 (d-F*c) K gamma lam
    hd hr hr1 (div_nonneg he hd.le) hK hg hg1 hl hdense hY hy hKT
  · rw [heq]
    exact hsmall
  · exact (mul_le_mul_of_nonneg_right (bounded_discrepancy A B C F hA hB hC hF) hd.le).trans hstep
  · intro n hn
    rw [←hx n hn]
    exact hbounded n hn
  · intro n hn
    rw [heq,←hx n hn]
    exact same_point_error (p n) A B C F c d (y n) eu ev eh (hu n hn) (hv n hn) (hh n hn)

end NativeSamePointSlopeConsistency
