import Theorems.Thm_StickyKakeya4_no_frostman_weighted_residual_decay

/-!
# Quantitative short-secant tails and literal angular-shell extraction

The cubic slope-pair sublevel bound controls the inverse-secant short tail.
Finite shell extraction below keeps the collision-time window and residual
indicator from the original weighted residual content. No shell mass premise
is introduced.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4.AngularResidualShell

/-- A cubic sublevel bound gives a quadratic short inverse-distance tail.
The restriction explicitly excludes the singular zero level. -/
theorem short_inverse_tail_le_of_cubic
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Measurable f)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hsub : ∀ r : ℝ, μ {x | f x ≤ r} ≤ C * ENNReal.ofReal r ^ 3)
    (τ : ℝ) (hτ : 0 < τ) :
    (∫⁻ x in {x | 0 < f x ∧ f x ≤ τ}, (ENNReal.ofReal (f x))⁻¹ ∂μ) ≤
      2 * C * ENNReal.ofReal τ ^ 2 := by
  let S : Set X := {x | 0 < f x ∧ f x ≤ τ}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const hf).inter (measurableSet_le hf measurable_const)
  have hpos : ∀ᵐ x ∂μ.restrict S, 0 < f x :=
    (ae_restrict_mem hS).mono (fun _ hx => hx.1)
  have heq : (fun x => (ENNReal.ofReal (f x))⁻¹) =ᵐ[μ.restrict S]
      (fun x => ENNReal.ofReal ((f x)⁻¹)) := by
    filter_upwards [hpos] with x hx
    exact (ENNReal.ofReal_inv_of_pos hx).symm
  change (∫⁻ x, (ENNReal.ofReal (f x))⁻¹ ∂μ.restrict S) ≤ _
  rw [lintegral_congr_ae heq,
    lintegral_eq_lintegral_meas_le (μ.restrict S)
      (hpos.mono (fun _ hx => (inv_pos.mpr hx).le)) hf.inv.aemeasurable]
  have htinv : 0 < τ⁻¹ := inv_pos.mpr hτ
  have hsmall : (∫⁻ z in Ioc (0 : ℝ) τ⁻¹,
      (μ.restrict S) {x | z ≤ (f x)⁻¹}) ≤ C * ENNReal.ofReal τ ^ 2 := by
    calc
      _ ≤ ∫⁻ _z in Ioc (0 : ℝ) τ⁻¹, C * ENNReal.ofReal τ ^ 3 := by
        apply lintegral_mono
        intro z
        calc
          (μ.restrict S) {x | z ≤ (f x)⁻¹} ≤ (μ.restrict S) univ :=
            measure_mono (subset_univ _)
          _ = μ S := by simp
          _ ≤ μ {x | f x ≤ τ} := measure_mono (fun _ hx => hx.2)
          _ ≤ _ := hsub τ
      _ = C * ENNReal.ofReal τ ^ 2 := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
        simp only [sub_zero, ENNReal.ofReal_inv_of_pos hτ]
        have ht0 : ENNReal.ofReal τ ≠ 0 := by simp [hτ.not_ge]
        rw [pow_succ _ 2, mul_assoc C,
          ENNReal.mul_inv_cancel_right ht0 ENNReal.ofReal_ne_top]
  have hlarge : (∫⁻ z in Ioi τ⁻¹,
      (μ.restrict S) {x | z ≤ (f x)⁻¹}) ≤ C * ENNReal.ofReal τ ^ 2 := by
    have hpowint := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) htinv
    have hpow0 : 0 ≤ᵐ[volume.restrict (Ioi τ⁻¹)] (fun z : ℝ => z ^ (-3 : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      exact Real.rpow_nonneg (htinv.trans hz).le _
    have hpow : (∫⁻ z in Ioi τ⁻¹, ENNReal.ofReal (z ^ (-3 : ℝ))) ≤
        ENNReal.ofReal τ ^ 2 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hpowint hpow0,
        integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) htinv]
      norm_num
      rw [← ENNReal.ofReal_pow hτ.le]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [sq_nonneg τ]
    calc
      _ ≤ ∫⁻ z in Ioi τ⁻¹, C * ENNReal.ofReal (z ^ (-3 : ℝ)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
        have hz0 : 0 < z := htinv.trans hz
        calc
          (μ.restrict S) {x | z ≤ (f x)⁻¹} =
              μ ({x | z ≤ (f x)⁻¹} ∩ S) :=
            Measure.restrict_apply (measurableSet_le measurable_const hf.inv)
          _ ≤ μ {x | f x ≤ z⁻¹} := by
            apply measure_mono
            intro x hx
            have hi := (inv_le_inv₀ (inv_pos.mpr hx.2.1) hz0).mpr hx.1
            simpa only [inv_inv, Set.mem_ofPred_eq] using hi
          _ ≤ C * ENNReal.ofReal z⁻¹ ^ 3 := hsub z⁻¹
          _ = C * ENNReal.ofReal (z ^ (-3 : ℝ)) := by
            rw [← ENNReal.ofReal_pow (inv_nonneg.mpr hz0.le),
              show (-3 : ℝ) = -(3 : ℕ) by norm_num, Real.rpow_neg_natCast, inv_pow]
            norm_num
      _ = C * ∫⁻ z in Ioi τ⁻¹, ENNReal.ofReal (z ^ (-3 : ℝ)) :=
        lintegral_const_mul' _ _ hC
      _ ≤ _ := mul_le_mul_right hpow C
  calc
    _ ≤ ∫⁻ z in Ioc (0 : ℝ) τ⁻¹ ∪ Ioi τ⁻¹,
        (μ.restrict S) {x | z ≤ (f x)⁻¹} :=
      lintegral_mono_set Ioi_subset_Ioc_union_Ioi
    _ ≤ (∫⁻ z in Ioc (0 : ℝ) τ⁻¹, (μ.restrict S) {x | z ≤ (f x)⁻¹}) +
        ∫⁻ z in Ioi τ⁻¹, (μ.restrict S) {x | z ≤ (f x)⁻¹} :=
      lintegral_union_le _ _ _
    _ ≤ C * ENNReal.ofReal τ ^ 2 + C * ENNReal.ofReal τ ^ 2 := add_le_add hsmall hlarge
    _ = _ := by ring

/-- The explicit quadratic tail for the actual ordered slope-pair source. -/
theorem slope_pair_short_inverse_tail_le
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (τ : ℝ) (hτ : 0 < τ) :
    (∫⁻ p : E3 × E3 in {p | 0 < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ τ},
      (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹ ∂σ.prod σ) ≤
        2 * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ * ENNReal.ofReal τ ^ 2 := by
  have hC : ENNReal.ofReal (Real.pi * 4 / 3) * σ univ ≠ ⊤ := by finiteness
  simpa only [mul_assoc] using short_inverse_tail_le_of_cubic (σ.prod σ)
    (fun p : E3 × E3 => ‖p.1 - p.2‖) (by fun_prop)
    (ENNReal.ofReal (Real.pi * 4 / 3) * σ univ) hC
    (fun r => by simpa only [one_mul] using
      slope_pair_near_mass_le_cubic σ 1 (by simpa using hσ) r) τ hτ

/-- The diagonal is null for the actual slope-pair source. We infer this
from the already proved finiteness of the genuine infinite inverse weight. -/
theorem slope_pair_secant_pos_ae
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume) :
    ∀ᵐ p : E3 × E3 ∂σ.prod σ, 0 < ‖p.1 - p.2‖ := by
  have hm : Measurable (fun p : E3 × E3 => (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹) := by fun_prop
  filter_upwards [ae_lt_top hm (NoFrostmanWeightedResidualDecay.finite_inverse_secant_integral σ hσ).ne]
    with p hp
  apply (norm_nonneg _).lt_of_ne
  intro hz
  simp [← hz] at hp

/-- Including the diagonal does not change the short-tail integral: its
infinite values lie on a proved null set. -/
theorem slope_pair_short_inverse_tail_including_diagonal_le
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (τ : ℝ) (hτ : 0 < τ) :
    (∫⁻ p : E3 × E3 in {p | ‖p.1 - p.2‖ ≤ τ},
      (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹ ∂σ.prod σ) ≤
        2 * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ * ENNReal.ofReal τ ^ 2 := by
  have heq : (∫⁻ p : E3 × E3 in {p | ‖p.1 - p.2‖ ≤ τ},
      (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹ ∂σ.prod σ) =
      ∫⁻ p : E3 × E3 in {p | 0 < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ τ},
        (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹ ∂σ.prod σ := by
    apply setLIntegral_congr
    filter_upwards [slope_pair_secant_pos_ae σ hσ] with p hp
    apply propext
    change (‖p.1 - p.2‖ ≤ τ) ↔ (0 < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ τ)
    simp only [hp, true_and]
  rw [heq]
  exact slope_pair_short_inverse_tail_le σ hσ τ hτ

/-- An angular shell of the literal residual content, with both original
collision cutoffs untouched. The lower endpoint is open. -/
def angularShellContent {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (α β : X → E3) (J : Set ℝ) (ρ lo hi : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x | lo < ‖α x‖ ∧ ‖α x‖ ≤ hi}, residualContentWeight J (α x) (β x) ρ ∂μ

/-- Every secant between a positive cutoff and a finite dyadic upper endpoint
belongs to one of the actual dyadic shells. -/
theorem exists_dyadic_shell_of_le (u x : ℝ) (N : ℕ)
    (hux : u < x) (hxN : x ≤ u * 2 ^ N) :
    ∃ k ∈ Finset.range N, u * 2 ^ k < x ∧ x ≤ u * 2 ^ (k + 1) := by
  induction N with
  | zero => simp only [pow_zero, mul_one] at hxN; exact (hux.not_ge hxN).elim
  | succ N ih =>
    by_cases hx : x ≤ u * 2 ^ N
    · obtain ⟨k, hk, hkl, hkh⟩ := ih hx
      exact ⟨k, Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hk) (Nat.lt_succ_self _)), hkl, hkh⟩
    · exact ⟨N, Finset.mem_range.mpr (Nat.lt_succ_self _), lt_of_not_ge hx, hxN⟩

/-- A finite dyadic cover bounds the full literal residual content by the
short inverse-secant tail and the sum of its genuine shell integrals. -/
theorem weightedResidualContent_le_short_tail_add_shells
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (α β : X → E3) (hα : Measurable α) (hβ : Measurable β)
    (J : Set ℝ) (hJ : MeasurableSet J) (ρ u : ℝ) (N : ℕ)
    (hupper : ∀ᵐ x ∂μ, ‖α x‖ ≤ u * 2 ^ N) :
    weightedResidualContent μ α β J ρ ≤
      (∫⁻ x in {x | 0 < ‖α x‖ ∧ ‖α x‖ ≤ u}, (ENNReal.ofReal ‖α x‖)⁻¹ ∂μ) +
      ∑ k ∈ Finset.range N,
        angularShellContent μ α β J ρ (u * 2 ^ k) (u * 2 ^ (k + 1)) := by
  classical
  let S : Set X := {x | 0 < ‖α x‖ ∧ ‖α x‖ ≤ u}
  let A : ℕ → Set X := fun k => {x | u * 2 ^ k < ‖α x‖ ∧ ‖α x‖ ≤ u * 2 ^ (k + 1)}
  let w : X → ℝ≥0∞ := fun x => residualContentWeight J (α x) (β x) ρ
  let v : X → ℝ≥0∞ := fun x => (ENNReal.ofReal ‖α x‖)⁻¹
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const hα.norm).inter (measurableSet_le hα.norm measurable_const)
  have hA (k : ℕ) : MeasurableSet (A k) :=
    (measurableSet_lt measurable_const hα.norm).inter (measurableSet_le hα.norm measurable_const)
  have hw : Measurable w := measurable_residualContentWeight α β hα hβ J hJ ρ
  have hv : Measurable v := by dsimp [v]; fun_prop
  have hpoint : ∀ᵐ x ∂μ, w x ≤ S.indicator v x +
      ∑ k ∈ Finset.range N, (A k).indicator w x := by
    filter_upwards [hupper] with x hx
    by_cases hz : α x = 0
    · simp [w, residualContentWeight, hz]
    have hp : 0 < ‖α x‖ := norm_pos_iff.mpr hz
    by_cases hshort : ‖α x‖ ≤ u
    · have hxS : x ∈ S := ⟨hp, hshort⟩
      apply (show w x ≤ v x by dsimp [w, v]; unfold residualContentWeight; split_ifs <;> simp).trans
      simpa only [Set.indicator_of_mem hxS] using
        (le_add_right (le_refl (v x)) : v x ≤ v x + ∑ k ∈ Finset.range N, (A k).indicator w x)
    · obtain ⟨k, hk, hkA⟩ := exists_dyadic_shell_of_le u ‖α x‖ N (lt_of_not_ge hshort) hx
      have hxA : x ∈ A k := hkA
      have hterm : w x ≤ ∑ j ∈ Finset.range N, (A j).indicator w x := by
        simpa only [Set.indicator_of_mem hxA] using
          (Finset.single_le_sum (fun j _ => bot_le : ∀ j ∈ Finset.range N, 0 ≤ (A j).indicator w x) hk)
      exact hterm.trans (le_add_left le_rfl)
  calc
    _ ≤ ∫⁻ x, S.indicator v x + ∑ k ∈ Finset.range N, (A k).indicator w x ∂μ :=
      lintegral_mono_ae hpoint
    _ = (∫⁻ x, S.indicator v x ∂μ) +
        ∑ k ∈ Finset.range N, ∫⁻ x, (A k).indicator w x ∂μ := by
      rw [lintegral_add_left (hv.indicator hS),
        lintegral_finsetSum _ (fun k _ => hw.indicator (hA k))]
    _ = _ := by
      rw [lintegral_indicator hS]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      exact lintegral_indicator (hA k) w

/-- A nonempty finite dyadic cover contains a shell carrying at least the
remaining content divided by the number of shells. The multiplicative form
avoids truncated subtraction in the extended nonnegative reals. -/
theorem exists_shell_carrying_residual_content
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (α β : X → E3) (hα : Measurable α) (hβ : Measurable β)
    (J : Set ℝ) (hJ : MeasurableSet J) (ρ u : ℝ) (N : ℕ) (hN : 0 < N)
    (hupper : ∀ᵐ x ∂μ, ‖α x‖ ≤ u * 2 ^ N) :
    ∃ k ∈ Finset.range N, weightedResidualContent μ α β J ρ ≤
      (∫⁻ x in {x | 0 < ‖α x‖ ∧ ‖α x‖ ≤ u}, (ENNReal.ofReal ‖α x‖)⁻¹ ∂μ) +
      (N : ℝ≥0∞) * angularShellContent μ α β J ρ (u * 2 ^ k) (u * 2 ^ (k + 1)) := by
  classical
  let z : ℕ → ℝ≥0∞ := fun k => angularShellContent μ α β J ρ (u * 2 ^ k) (u * 2 ^ (k + 1))
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range N) z
    ⟨0, Finset.mem_range.mpr hN⟩
  refine ⟨k, hk, (weightedResidualContent_le_short_tail_add_shells μ α β hα hβ J hJ ρ u N hupper).trans ?_⟩
  apply add_le_add_right
  calc
    ∑ j ∈ Finset.range N, z j ≤ ∑ _j ∈ Finset.range N, z k := Finset.sum_le_sum hmax
    _ = (N : ℝ≥0∞) * z k := by simp

/-- The requested quantitative extraction for actual bounded slope sources.
Both the short tail and the shell masses are derived from that same source. -/
theorem exists_slope_shell_carrying_residual_content
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (J : Set ℝ) (hJ : MeasurableSet J) (ρ u : ℝ) (hu : 0 < u)
    (N : ℕ) (hN : 0 < N) (hcover : 2 ≤ u * 2 ^ N) :
    ∃ k ∈ Finset.range N,
      weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
        (fun p => b p.1 - b p.2) J ρ ≤
      2 * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ * ENNReal.ofReal u ^ 2 +
        (N : ℝ≥0∞) * angularShellContent (σ.prod σ) (fun p => p.1 - p.2)
          (fun p => b p.1 - b p.2) J ρ (u * 2 ^ k) (u * 2 ^ (k + 1)) := by
  have hupper : ∀ᵐ p : E3 × E3 ∂σ.prod σ, ‖p.1 - p.2‖ ≤ u * 2 ^ N := by
    apply Measure.ae_prod_iff_ae_ae
      (measurableSet_le (by fun_prop) measurable_const) |>.mpr
    filter_upwards [hslopes] with a ha
    filter_upwards [hslopes] with a' ha'
    exact (norm_sub_le a a').trans ((show ‖a‖ + ‖a'‖ ≤ 2 by linarith).trans hcover)
  obtain ⟨k, hk, hbound⟩ := exists_shell_carrying_residual_content (σ.prod σ)
    (fun p => p.1 - p.2) (fun p => b p.1 - b p.2)
    (measurable_fst.sub measurable_snd)
    ((hb.comp measurable_fst).sub (hb.comp measurable_snd)) J hJ ρ u N hN hupper
  exact ⟨k, hk, hbound.trans (add_le_add_left (slope_pair_short_inverse_tail_le σ hσ u hu) _)⟩

/-- A finite dyadic cover always exists for `0 < u ≤ 1`; all its lower
shell endpoints lie between `u` and `2`, and the shell count is at most
`log (2/u) / log 2 + 1`. No angular mass or covering family is assumed. -/
theorem exists_bounded_dyadic_slope_shell
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (J : Set ℝ) (hJ : MeasurableSet J) (ρ u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
    ∃ N k : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.log (2 / u) / Real.log 2 + 1 ∧
      k < N ∧ u ≤ u * 2 ^ k ∧ u * 2 ^ k ≤ 2 ∧
      weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
        (fun p => b p.1 - b p.2) J ρ ≤
      2 * ENNReal.ofReal (Real.pi * 4 / 3) * σ univ * ENNReal.ofReal u ^ 2 +
        (N : ℝ≥0∞) * angularShellContent (σ.prod σ) (fun p => p.1 - p.2)
          (fun p => b p.1 - b p.2) J ρ (u * 2 ^ k) (2 * (u * 2 ^ k)) := by
  have hratio : 1 ≤ 2 / u := (le_div_iff₀ hu).mpr (by linarith)
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hcover : 2 ≤ u * 2 ^ (n + 1) := by
    have h := (div_lt_iff₀ hu).mp hnhi
    nlinarith
  obtain ⟨k, hk, hbound⟩ := exists_slope_shell_carrying_residual_content σ hσ b hb hslopes
    J hJ ρ u hu (n + 1) (Nat.zero_lt_succ _) hcover
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hnlog : (n : ℝ) * Real.log 2 ≤ Real.log (2 / u) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hnlo
  have hncount : ((n + 1 : ℕ) : ℝ) ≤ Real.log (2 / u) / Real.log 2 + 1 := by
    have h := (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hnlog
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  refine ⟨n + 1, k, Nat.zero_lt_succ _, hncount, Finset.mem_range.mp hk, ?_, ?_, ?_⟩
  · have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  · have hpow : (2 : ℝ) ^ k ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hkn
    have hlo := (le_div_iff₀ hu).mp hnlo
    nlinarith
  · have hhi : u * 2 ^ (k + 1) = 2 * (u * 2 ^ k) := by rw [pow_succ]; ring
    simpa only [hhi] using hbound

end StickyKakeya4.AngularResidualShell
