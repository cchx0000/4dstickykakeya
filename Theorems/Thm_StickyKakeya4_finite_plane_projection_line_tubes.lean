import Theorems.Thm_StickyKakeya4_finite_plane_projection_joint

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Finset
open scoped BigOperators
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

lemma determinant_bound_normal {x y x' y' a b M w : ℝ}
    (hM : 0 ≤ M) (hw : 0 ≤ w)
    (hx : |x| ≤ M) (hy : |y| ≤ M) (hx' : |x'| ≤ M) (hy' : |y'| ≤ M)
    (hnormal : max |a| |b| = 1)
    (hr : |a * x + b * y| ≤ w) (hr' : |a * x' + b * y'| ≤ w) :
    |x * y' - y * x'| ≤ 2 * M * w := by
  have hfirst : |a| = 1 → |x * y' - y * x'| ≤ 2 * M * w := by
    intro ha
    have hid : a * (x * y' - y * x') =
        (a * x + b * y) * y' - y * (a * x' + b * y') := by ring
    calc
      _ = |a * (x * y' - y * x')| := by rw [abs_mul, ha, one_mul]
      _ = |(a * x + b * y) * y' - y * (a * x' + b * y')| := by rw [hid]
      _ ≤ |(a * x + b * y) * y'| + |y * (a * x' + b * y')| := abs_sub _ _
      _ ≤ w * M + M * w := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul hr hy' (abs_nonneg _) hw)
          (mul_le_mul hy hr' (abs_nonneg _) hM)
      _ = _ := by ring
  have hsecond : |b| = 1 → |x * y' - y * x'| ≤ 2 * M * w := by
    intro hb
    have hid : b * (x * y' - y * x') =
        x * (a * x' + b * y') - (a * x + b * y) * x' := by ring
    calc
      _ = |b * (x * y' - y * x')| := by rw [abs_mul, hb, one_mul]
      _ = |x * (a * x' + b * y') - (a * x + b * y) * x'| := by rw [hid]
      _ ≤ |x * (a * x' + b * y')| + |(a * x + b * y) * x'| := abs_sub _ _
      _ ≤ M * w + w * M := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul hx hr' (abs_nonneg _) hM)
          (mul_le_mul hr hx' (abs_nonneg _) hw)
      _ = _ := by ring
  rcases le_total |a| |b| with hab | hba
  · apply hsecond
    rwa [max_eq_right hab] at hnormal
  · apply hfirst
    rwa [max_eq_left hba] at hnormal

lemma secant_line_residual {p q : ℝ × ℝ} {a b c w : ℝ}
    (hp : |a * p.1 + b * p.2 - c| ≤ w)
    (hq : |a * q.1 + b * q.2 - c| ≤ w) :
    |a * (q.1 - p.1) + b * (q.2 - p.2)| ≤ 2 * w := by
  have hid : a * (q.1 - p.1) + b * (q.2 - p.2) =
      (a * q.1 + b * q.2 - c) - (a * p.1 + b * p.2 - c) := by ring
  rw [hid]
  exact (abs_sub _ _).trans (by linarith)

lemma triangle_in_line_strip {p q s : ℝ × ℝ} {a b c w M : ℝ}
    (hM : 0 ≤ M) (hw : 0 ≤ w)
    (hp : |p.1| ≤ M ∧ |p.2| ≤ M) (hq : |q.1| ≤ M ∧ |q.2| ≤ M)
    (hs : |s.1| ≤ M ∧ |s.2| ≤ M) (hnormal : max |a| |b| = 1)
    (hlp : |a * p.1 + b * p.2 - c| ≤ w)
    (hlq : |a * q.1 + b * q.2 - c| ≤ w)
    (hls : |a * s.1 + b * s.2 - c| ≤ w) :
    |(q.1 - p.1) * (s.2 - p.2) - (q.2 - p.2) * (s.1 - p.1)| ≤ 8 * M * w := by
  have hdx : |q.1 - p.1| ≤ 2 * M := (abs_sub _ _).trans (by linarith [hp.1, hq.1])
  have hdy : |q.2 - p.2| ≤ 2 * M := (abs_sub _ _).trans (by linarith [hp.2, hq.2])
  have hdx' : |s.1 - p.1| ≤ 2 * M := (abs_sub _ _).trans (by linarith [hp.1, hs.1])
  have hdy' : |s.2 - p.2| ≤ 2 * M := (abs_sub _ _).trans (by linarith [hp.2, hs.2])
  have hh := determinant_bound_normal (by positivity : 0 ≤ 2 * M) (by positivity : 0 ≤ 2 * w)
    hdx hdy hdx' hdy' hnormal (secant_line_residual hlp hlq) (secant_line_residual hlp hls)
  nlinarith

lemma bounded_projected_point {n : ℕ} {uv : ℝ × ℝ} (huv : uv ∈ parameters n)
    {p : Point3} (hp : |p.1| ≤ 1 ∧ |p.2.1| ≤ 1 ∧ |p.2.2| ≤ 1) :
    |(project uv p).1| ≤ 2 ∧ |(project uv p).2| ≤ 2 := by
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
  have hau := slope_abs_le_one hu
  have hav := slope_abs_le_one hv
  have huz : |uv.1 * p.2.2| ≤ 1 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hau hp.2.2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  have hvz : |uv.2 * p.2.2| ≤ 1 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hav hp.2.2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  exact ⟨(abs_sub _ _).trans (by linarith [hp.1]),
    (abs_sub _ _).trans (by linarith [hp.2.1])⟩

/-- Original B labels whose actual projected locations lie in a literal
normalized affine line strip. No projected resampling is performed. -/
def projectedLineStrip {X : Type*} (B : Finset X) (b : X → Point3)
    (uv : ℝ × ℝ) (a d c w : ℝ) : Finset X :=
  B.filter (fun i => |a * (project uv (b i)).1 + d * (project uv (b i)).2 - c| ≤ w)

/-- Cubic line-tube mass bound, derived by counting actual ordered triples. -/
theorem projected_line_strip_cube {X : Type*} (B : Finset X) (b : X → Point3)
    {n : ℕ} {uv : ℝ × ℝ} (huv : uv ∈ parameters n) {a d c w : ℝ}
    (hw : 0 ≤ w) (hnormal : max |a| |d| = 1)
    (hB : ∀ i ∈ B, |(b i).1| ≤ 1 ∧ |(b i).2.1| ≤ 1 ∧ |(b i).2.2| ≤ 1) :
    ((projectedLineStrip B b uv a d c w).card : ℝ) ^ 3 ≤
      (smallProjectedTriples B b uv (16 * w)).card := by
  let S := projectedLineStrip B b uv a d c w
  have hsub : triples S ⊆ smallProjectedTriples B b uv (16 * w) := by
    intro ijk hijk
    obtain ⟨hi, hjk⟩ := Finset.mem_product.mp hijk
    obtain ⟨hj, hk⟩ := Finset.mem_product.mp hjk
    obtain ⟨hiB, hil⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjB, hjl⟩ := Finset.mem_filter.mp hj
    obtain ⟨hkB, hkl⟩ := Finset.mem_filter.mp hk
    have ht := triangle_in_line_strip (by norm_num : (0 : ℝ) ≤ 2) hw
      (bounded_projected_point huv (hB _ hiB)) (bounded_projected_point huv (hB _ hjB))
      (bounded_projected_point huv (hB _ hkB)) hnormal hil hjl hkl
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hiB, Finset.mem_product.mpr ⟨hjB, hkB⟩⟩, ?_⟩
    dsimp [projectedArea]
    nlinarith
  rw [← triples_card]
  exact Nat.cast_le.mpr (Finset.card_le_card hsub)

end FinitePlaneProjectionGrid
