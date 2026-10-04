import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

noncomputable section
open Classical

namespace NativePlanarSlabNormConversion

abbrev Plane := ℝ × ℝ

/-- The coefficients in the original two real coordinates determine every
continuous linear functional; no point or label is changed. -/
theorem apply_eq_coordinates (f : Plane →L[ℝ] ℝ) (p : Plane) :
    f p = f (1, 0) * p.1 + f (0, 1) * p.2 := by
  have hp : p = p.1 • (1, 0) + p.2 • (0, 1) := by
    ext <;> simp
  conv_lhs => rw [hp]
  rw [map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

/-- The dual norm for the max norm is bounded above by the sum of the
absolute values of the two coefficients. -/
theorem opNorm_le_abs_coefficients (f : Plane →L[ℝ] ℝ) :
    ‖f‖ ≤ |f (1, 0)| + |f (0, 1)| := by
  apply f.opNorm_le_bound (add_nonneg (abs_nonneg _) (abs_nonneg _))
  intro p
  rw [Real.norm_eq_abs, apply_eq_coordinates]
  calc
    |f (1, 0) * p.1 + f (0, 1) * p.2|
        ≤ |f (1, 0)| * |p.1| + |f (0, 1)| * |p.2| := by
          simpa only [abs_mul] using abs_add_le (f (1, 0) * p.1) (f (0, 1) * p.2)
    _ ≤ |f (1, 0)| * ‖p‖ + |f (0, 1)| * ‖p‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (by simpa using norm_fst_le p) (abs_nonneg _)
      · exact mul_le_mul_of_nonneg_left (by simpa using norm_snd_le p) (abs_nonneg _)
    _ = (|f (1, 0)| + |f (0, 1)|) * ‖p‖ := by ring

def coefficientLength (f : Plane →L[ℝ] ℝ) : ℝ :=
  Real.sqrt (f (1, 0) ^ 2 + f (0, 1) ^ 2)

/-- A max-norm unit functional has Euclidean coefficient length at least
one half. This deliberately uses the simple dimension constant 2. -/
theorem coefficientLength_ge_half (f : Plane →L[ℝ] ℝ) (hf : ‖f‖ = 1) :
    (1 : ℝ) / 2 ≤ coefficientLength f := by
  have hsum : 1 ≤ |f (1, 0)| + |f (0, 1)| := by
    simpa only [hf] using opNorm_le_abs_coefficients f
  have hnonneg := Real.sqrt_nonneg (f (1, 0)^2 + f (0, 1)^2)
  have hsquare := Real.sq_sqrt (add_nonneg (sq_nonneg (f (1, 0))) (sq_nonneg (f (0, 1))))
  have ha : |f (1, 0)| ≤ coefficientLength f := by
    dsimp [coefficientLength]
    nlinarith [sq_abs (f (1, 0)), sq_nonneg (f (0, 1)), abs_nonneg (f (1, 0))]
  have hb : |f (0, 1)| ≤ coefficientLength f := by
    dsimp [coefficientLength]
    nlinarith [sq_abs (f (0, 1)), sq_nonneg (f (1, 0)), abs_nonneg (f (0, 1))]
  linarith

theorem coefficientLength_pos (f : Plane →L[ℝ] ℝ) (hf : ‖f‖ = 1) :
    0 < coefficientLength f := by
  linarith [coefficientLength_ge_half f hf]

/-- Dividing the two original coefficients by their Euclidean length gives
a Euclidean unit normal. -/
theorem normalized_coefficients_unit (f : Plane →L[ℝ] ℝ) (hf : ‖f‖ = 1) :
    (f (1, 0) / coefficientLength f) ^ 2 +
      (f (0, 1) / coefficientLength f) ^ 2 = 1 := by
  have hsquare : coefficientLength f ^ 2 = f (1, 0)^2 + f (0, 1)^2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hne := (coefficientLength_pos f hf).ne'
  field_simp
  nlinarith [hsquare]

/-- The original points in a functional slab lie in a Euclidean slab of
at most twice its width. -/
theorem functional_slab_subset (f : Plane →L[ℝ] ℝ) (hf : ‖f‖ = 1)
    (p : Plane) (c r : ℝ) (hr : 0 ≤ r) (hp : |f p - c| ≤ r) :
    |(f (1, 0) / coefficientLength f) * p.1 +
      (f (0, 1) / coefficientLength f) * p.2 - c / coefficientLength f| ≤ 2 * r := by
  have hlen := coefficientLength_ge_half f hf
  have hpos := coefficientLength_pos f hf
  have heq : (f (1, 0) / coefficientLength f) * p.1 +
      (f (0, 1) / coefficientLength f) * p.2 - c / coefficientLength f =
        (f p - c) / coefficientLength f := by
    rw [apply_eq_coordinates f p]
    ring
  rw [heq, abs_div, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  nlinarith

/-- Euclidean unit-normal slab estimates imply unit-functional slab estimates
for the product max norm, with the explicit loss `2^gamma`. The finite set
and all of its original labels remain unchanged. -/
theorem slab_law_conversion (Phi : Finset Plane) (δ F gamma : ℝ)
    (hδ : 0 < δ) (hF : 1 ≤ F) (hgamma : 0 ≤ gamma)
    (hslab : ∀ (n₁ n₂ c r : ℝ), n₁ ^ 2 + n₂ ^ 2 = 1 → δ ≤ r → r ≤ 1 →
      ((Phi.filter (fun p => |n₁ * p.1 + n₂ * p.2 - c| ≤ r)).card : ℝ)
        ≤ F * r ^ gamma * Phi.card) :
    ∀ (f : Plane →L[ℝ] ℝ) (c r : ℝ), ‖f‖ = 1 → δ ≤ r → r ≤ 1 →
      ((Phi.filter (fun p => |f p - c| ≤ r)).card : ℝ)
        ≤ ((2 : ℝ) ^ gamma * F) * r ^ gamma * Phi.card := by
  intro f c r hf hδr _hr1
  have hr : 0 < r := hδ.trans_le hδr
  have hcard : (0 : ℝ) ≤ Phi.card := Nat.cast_nonneg _
  by_cases hsmall : r ≤ 1 / 2
  · have hsub : Phi.filter (fun p => |f p - c| ≤ r) ⊆
        Phi.filter (fun p => |(f (1, 0) / coefficientLength f) * p.1 +
          (f (0, 1) / coefficientLength f) * p.2 - c / coefficientLength f| ≤ 2*r) := by
      intro p hp
      obtain ⟨hpPhi, hpp⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hpPhi, functional_slab_subset f hf p c r hr.le hpp⟩
    calc
      ((Phi.filter (fun p => |f p - c| ≤ r)).card : ℝ) ≤
          ((Phi.filter (fun p => |(f (1, 0) / coefficientLength f) * p.1 +
            (f (0, 1) / coefficientLength f) * p.2 - c / coefficientLength f| ≤ 2*r)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ F * (2*r) ^ gamma * Phi.card :=
        hslab _ _ _ _ (normalized_coefficients_unit f hf) (by linarith) (by linarith)
      _ = ((2 : ℝ) ^ gamma * F) * r ^ gamma * Phi.card := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le]
        ring
  · have hscale : 1 ≤ (2*r) ^ gamma := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 1 ≤ 2*r) hgamma
    have hscale' : 1 ≤ ((2 : ℝ) ^ gamma * F) * r ^ gamma := by
      have hnonneg : 0 ≤ (2*r) ^ gamma := Real.rpow_nonneg (by positivity) _
      have h := mul_le_mul_of_nonneg_right hF hnonneg
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le] at h hscale
      nlinarith
    calc
      ((Phi.filter (fun p => |f p - c| ≤ r)).card : ℝ) ≤ (Phi.card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_filter_le _ _)
      _ ≤ ((2 : ℝ) ^ gamma * F) * r ^ gamma * Phi.card := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hscale' hcard

end NativePlanarSlabNormConversion
