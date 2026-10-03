import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

namespace RootTailMoment

lemma ae_ne_top_of_cubic_root_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ≥0∞) {A : ℝ≥0∞} (hA : A ≠ ∞)
    (htail : ∀ B : ℝ, 0 < B →
      μ {x | ENNReal.ofReal B < f x} ≤ A * (ENNReal.ofReal B) ^ (-1 / 3 : ℝ)) :
    ∀ᵐ x ∂μ, f x ≠ ∞ := by
  have hlim : Tendsto (fun B : ℝ => A * (ENNReal.ofReal B) ^ (-1 / 3 : ℝ))
      atTop (𝓝 0) := by
    have hp := ENNReal.tendsto_ofReal_atTop.ennrpow_const (-1 / 3 : ℝ)
    have hp' : Tendsto (fun B : ℝ => (ENNReal.ofReal B) ^ (-1 / 3 : ℝ))
        atTop (𝓝 0) := by
      simpa only [ENNReal.top_rpow_of_neg (by norm_num : (-1 / 3 : ℝ) < 0)] using hp
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hp' (Or.inr hA)
  have hzero : μ {x | f x = ∞} = 0 := by
    apply le_antisymm _ zero_le
    apply ge_of_tendsto hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    apply le_trans _ (htail B hB)
    apply measure_mono
    intro x hx
    change f x = ∞ at hx
    change ENNReal.ofReal B < f x
    rw [hx]
    exact ENNReal.ofReal_lt_top
  simpa only [ae_iff, not_not] using hzero


def momentConstant (M : ℝ≥0∞) (θ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal θ * (M * (∫⁻ t : ℝ in Ioc 0 1, ENNReal.ofReal (t ^ (θ - 1))) +
    ∫⁻ t : ℝ in Ioi 1, ENNReal.ofReal (t ^ (θ - 1 - 1 / 3)))

lemma momentConstant_ne_top {M : ℝ≥0∞} (hM : M ≠ ∞) {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ < 1/3) : momentConstant M θ ≠ ∞ := by
  have hlo : IntegrableOn (fun t : ℝ => t ^ (θ-1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < θ-1)).1
  have hhi : IntegrableOn (fun t : ℝ => t ^ (θ-1-1/3)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hM hlo.lintegral_lt_top.ne,
      hhi.lintegral_lt_top.ne⟩)

lemma normalized_moment_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} (hf : AEMeasurable f μ)
    (hfn : ∀ᵐ x ∂μ, 0 ≤ f x) {θ : ℝ} (hθ : 0 < θ)
    (htail : ∀ B : ℝ, 0 < B →
      μ {x | B < f x} ≤ ENNReal.ofReal (B ^ (-(1/3:ℝ)))) :
    (∫⁻ x, ENNReal.ofReal (f x ^ θ) ∂μ) ≤ momentConstant (μ univ) θ := by
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ hfn hf hθ]
  unfold momentConstant
  gcongr
  rw [← Ioc_union_Ioi_eq_Ioi (show (0:ℝ) ≤ 1 by norm_num),
    lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  apply add_le_add
  · calc
      _ ≤ ∫⁻ t : ℝ in Ioc 0 1, μ univ * ENNReal.ofReal (t ^ (θ - 1)) :=
        lintegral_mono fun t => mul_le_mul_left (measure_mono (subset_univ {x | t < f x})) _
      _ = _ := lintegral_const_mul _ (by fun_prop)
  · apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    calc
      _ ≤ ENNReal.ofReal (t ^ (-(1/3:ℝ))) * ENNReal.ofReal (t ^ (θ-1)) :=
        by gcongr; exact htail t (lt_trans zero_lt_one ht)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by have := ht; change (1:ℝ) < t at this; linarith) _),
          ← Real.rpow_add (by have := ht; change (1:ℝ) < t at this; linarith)]
        congr 2
        ring

lemma scaled_moment_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} (hf : AEMeasurable f μ)
    (hfn : ∀ᵐ x ∂μ, 0 ≤ f x) {θ A : ℝ} (hθ : 0 < θ) (hA : 0 < A)
    (htail : ∀ B : ℝ, 0 < B →
      μ {x | B < f x} ≤ ENNReal.ofReal (A * B ^ (-(1/3:ℝ)))) :
    (∫⁻ x, ENNReal.ofReal (f x ^ θ) ∂μ) ≤
      momentConstant (μ univ) θ * ENNReal.ofReal (A ^ (3 * θ)) := by
  let c : ℝ := A ^ (3:ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hA _
  let g : α → ℝ := fun x => f x / c
  have hg : AEMeasurable g μ := hf.div_const c
  have hgn : ∀ᵐ x ∂μ, 0 ≤ g x := hfn.mono fun x hx => div_nonneg hx hc.le
  have hgTail : ∀ B : ℝ, 0 < B →
      μ {x | B < g x} ≤ ENNReal.ofReal (B ^ (-(1/3:ℝ))) := by
    intro B hB
    have hset : {x | B < g x} = {x | B * c < f x} := by
      ext x
      exact lt_div_iff₀ hc
    rw [hset]
    calc
      _ ≤ ENNReal.ofReal (A * (B*c)^(-(1/3:ℝ))) := htail (B*c) (mul_pos hB hc)
      _ = _ := by
        congr 1
        rw [Real.mul_rpow hB.le hc.le]
        have hcp : c ^ (-(1/3:ℝ)) = A⁻¹ := by
          dsimp [c]
          rw [← Real.rpow_mul hA.le]
          norm_num [Real.rpow_neg_one]
        rw [hcp]
        calc
          A * (B ^ (-(1/3:ℝ)) * A⁻¹) = (A*A⁻¹) * B ^ (-(1/3:ℝ)) := by ring
          _ = _ := by rw [mul_inv_cancel₀ hA.ne', one_mul]
  have hbound := normalized_moment_le μ hg hgn hθ hgTail
  have heq : (∫⁻ x, ENNReal.ofReal (f x ^ θ) ∂μ) =
      ENNReal.ofReal (A ^ (3*θ)) * ∫⁻ x, ENNReal.ofReal (g x ^ θ) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    filter_upwards [hfn] with x hx
    have hfx : f x = c * g x := by dsimp [g]; field_simp
    rw [hfx, Real.mul_rpow hc.le (div_nonneg hx hc.le)]
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hc.le θ)]
    congr 2
    exact (Real.rpow_mul hA.le 3 θ).symm
  rw [heq, mul_comm (momentConstant _ _)]
  exact mul_le_mul_right hbound _

lemma ennreal_moment_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    {θ : ℝ} (hθ : 0 < θ) {A : ℝ≥0∞} (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (htail : ∀ B : ℝ, 0 < B →
      μ {x | ENNReal.ofReal B < f x} ≤ A * (ENNReal.ofReal B) ^ (-1/3:ℝ)) :
    (∫⁻ x, f x ^ θ ∂μ) ≤ momentConstant (μ univ) θ * A ^ (3*θ) := by
  have hfin := ae_ne_top_of_cubic_root_tail μ f hAtop htail
  have htail' : ∀ B : ℝ, 0 < B →
      μ {x | B < (f x).toReal} ≤ ENNReal.ofReal (A.toReal * B ^ (-(1/3:ℝ))) := by
    intro B hB
    calc
      _ ≤ μ {x | ENNReal.ofReal B < f x} := by
        apply measure_mono
        intro x hx
        exact lt_of_lt_of_le (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hB.le |>.mpr hx)
          ENNReal.ofReal_toReal_le
      _ ≤ A * (ENNReal.ofReal B) ^ (-1/3:ℝ) := htail B hB
      _ = _ := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hAtop,
          ENNReal.ofReal_rpow_of_pos hB]
        norm_num
  have hbound := scaled_moment_le μ hf.ennreal_toReal
    (Filter.Eventually.of_forall (fun x => ENNReal.toReal_nonneg)) hθ
    (ENNReal.toReal_pos hA0 hAtop) htail'
  have heq : (∫⁻ x, f x ^ θ ∂μ) = ∫⁻ x, ENNReal.ofReal ((f x).toReal ^ θ) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hfin] with x hx
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hθ.le,
      ENNReal.ofReal_toReal hx]
  rw [heq]
  convert hbound using 1
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
    ENNReal.ofReal_toReal hAtop]

end RootTailMoment
