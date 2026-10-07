import Theorems.Thm_StickyKakeya4_noisy_affine_image_count

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace ScalarKatzTaoSlopeBound

open NoisyAffineImageCount

noncomputable def intervalCells (Y : Finset ℝ) (ρ q τ : ℝ) : Finset ℤ :=
  (Y.filter (fun y => q ≤ y ∧ y ≤ q + τ)).image (fun y => ⌊y / ρ⌋)

/-- The input concerns the ACTUAL finite Y in every admissible interval. -/
def IntervalKatzTao (Y : Finset ℝ) (ρ K γ : ℝ) : Prop :=
  ∀ q τ : ℝ, ρ ≤ τ → τ ≤ 1 →
    ((intervalCells Y ρ q τ).card : ℝ) ≤ K * (τ / ρ) ^ (1 - γ)

lemma four_scale_power {B ρ γ : ℝ} (hB : 0 ≤ B) (hρ : 0 < ρ)
    (hγ : 0 ≤ γ) :
    (4 * B / ρ) ^ (1 - γ) ≤ 4 * (B / ρ) ^ (1 - γ) := by
  have hfour : (4 : ℝ) ^ (1 - γ) ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (show 1 - γ ≤ 1 by linarith)
    simpa only [Real.rpow_one] using h
  rw [show 4 * B / ρ = 4 * (B / ρ) by ring,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (div_nonneg hB hρ.le)]
  exact mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg (div_nonneg hB hρ.le) _)

/-- Two literal unit intervals cover the global source, including endpoints. -/
theorem global_cells_bound (Y : Finset ℝ) (ρ K γ : ℝ)
    (hρone : ρ ≤ 1) (hY : ∀ y ∈ Y, -1 ≤ y ∧ y ≤ 1)
    (hKT : IntervalKatzTao Y ρ K γ) :
    ((Y.image (fun y => ⌊y / ρ⌋)).card : ℝ) ≤ 2 * K * (1 / ρ) ^ (1 - γ) := by
  classical
  have hsub : Y.image (fun y => ⌊y / ρ⌋) ⊆
      intervalCells Y ρ (-1) 1 ∪ intervalCells Y ρ 0 1 := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hylo, hyhi⟩ := hY y hy
    by_cases hz : y ≤ 0
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hylo, by linarith⟩, rfl⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, by linarith, by linarith⟩, rfl⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcard' : ((Y.image (fun y => ⌊y / ρ⌋)).card : ℝ) ≤
      ((intervalCells Y ρ (-1) 1).card : ℝ) + ((intervalCells Y ρ 0 1).card : ℝ) := by
    exact_mod_cast hcard
  have hleft := hKT (-1) 1 hρone le_rfl
  have hright := hKT 0 1 hρone le_rfl
  linarith

/-- The noisy witnesses themselves lie in the required short interval. -/
theorem noisy_witness_interval (J : Finset ℤ) (y : ℤ → ℝ) (δ ρ E b x₀ q : ℝ)
    (hsmallError : E * δ ≤ ρ) (hlarge : ρ < |b|)
    (hx : ∀ n ∈ J, |x₀ + δ * (n : ℝ)| ≤ 1)
    (herror : ∀ n ∈ J, |y n - q - b * (x₀ + δ * (n : ℝ))| ≤ E * δ) :
    ∀ n ∈ J, q - 2 * |b| ≤ y n ∧ y n ≤ q + 2 * |b| := by
  intro n hn
  have hb : |b * (x₀ + δ * (n : ℝ))| ≤ |b| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left (hx n hn) (abs_nonneg b)
  have ht : |y n - q| ≤ E * δ + |b| := by
    have heq : y n - q = (y n - q - b * (x₀ + δ * (n : ℝ))) +
        b * (x₀ + δ * (n : ℝ)) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add (herror n hn) hb)
  have hbound : |y n - q| ≤ 2 * |b| := by linarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp hbound
  constructor <;> linarith

/-- Derive the output-cell upper bound from actual interval KT. Small affine
images use their containing interval; long ones use the two global unit
intervals. No occupied-cell upper bound is supplied as a hypothesis. -/
theorem noisy_cells_upper (J : Finset ℤ) (y : ℤ → ℝ) (Y : Finset ℝ)
    (δ ρ E b x₀ q K γ : ℝ)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1) (hK : 1 ≤ K)
    (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hY : ∀ z ∈ Y, -1 ≤ z ∧ z ≤ 1) (hyY : ∀ n ∈ J, y n ∈ Y)
    (hKT : IntervalKatzTao Y ρ K γ)
    (hsmallError : E * δ ≤ ρ) (hlarge : ρ < |b|)
    (hx : ∀ n ∈ J, |x₀ + δ * (n : ℝ)| ≤ 1)
    (herror : ∀ n ∈ J, |y n - q - b * (x₀ + δ * (n : ℝ))| ≤ E * δ) :
    ((J.image (fun n => ⌊y n / ρ⌋)).card : ℝ) ≤
      8 * K * (|b| / ρ) ^ (1 - γ) := by
  classical
  have hKzero : 0 ≤ K := by linarith
  have hp : 0 ≤ 1 - γ := by linarith
  have hpow := four_scale_power (abs_nonneg b) hρ hγ.le
  by_cases hshort : 4 * |b| ≤ 1
  · have hsub : J.image (fun n => ⌊y n / ρ⌋) ⊆
        intervalCells Y ρ (q - 2 * |b|) (4 * |b|) := by
      intro c hc
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨hlo, hhi⟩ := noisy_witness_interval J y δ ρ E b x₀ q hsmallError hlarge hx herror n hn
      exact Finset.mem_image.mpr ⟨y n,
        Finset.mem_filter.mpr ⟨hyY n hn, hlo, by linarith⟩, rfl⟩
    have hcount : ((J.image (fun n => ⌊y n / ρ⌋)).card : ℝ) ≤
        ((intervalCells Y ρ (q - 2 * |b|) (4 * |b|)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    have hkt := hKT (q - 2 * |b|) (4 * |b|) (by linarith) hshort
    have hupper := (hcount.trans hkt).trans (mul_le_mul_of_nonneg_left hpow hKzero)
    have hn : 0 ≤ K * (|b| / ρ) ^ (1 - γ) := by positivity
    nlinarith
  · have hsub : J.image (fun n => ⌊y n / ρ⌋) ⊆ Y.image (fun z => ⌊z / ρ⌋) := by
      intro c hc
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
      exact Finset.mem_image.mpr ⟨y n, hyY n hn, rfl⟩
    have hcount := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (global_cells_bound Y ρ K γ hρone hY hKT)
    have hbase : 1 / ρ ≤ 4 * |b| / ρ :=
      div_le_div_of_nonneg_right (by linarith) hρ.le
    have hscale := (Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 1 / ρ) hbase hp).trans hpow
    have hupper := hcount.trans (mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 2 * K))
    nlinarith

/-- The noisy image lower count follows from original source density. -/
theorem density_cells_lower (J : Finset ℤ) (y : ℤ → ℝ) (δ ρ E b x₀ q lam : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hE : 0 ≤ E)
    (hdensity : lam / δ ≤ (J.card : ℝ))
    (herror : ∀ n ∈ J, |y n - q - b * (x₀ + δ * (n : ℝ))| ≤ E * δ)
    (hsmallError : E * δ ≤ ρ) (hsmallStep : |b| * δ ≤ ρ) :
    lam * |b| ≤ 4 * ρ * ((J.image (fun n => ⌊y n / ρ⌋)).card : ℝ) := by
  have hden := (div_le_iff₀ hδ).mp hdensity
  have hmul := mul_le_mul_of_nonneg_right hden (abs_nonneg b)
  have hc := coarse_noisy_image_count J y δ ρ E b x₀ q hδ hρ hE herror hsmallError hsmallStep
  nlinarith

/-- Cancel the positive ratio from the two real-power counts. -/
lemma ratio_power_bound {r lam K γ : ℝ} (hr : 0 < r) (hlam : 0 < lam)
    (hcount : lam * r ≤ 32 * K * r ^ (1 - γ)) :
    r ^ γ ≤ 32 * K / lam := by
  have hproduct : r ^ (1 - γ) * r ^ γ = r := by
    rw [← Real.rpow_add hr]
    have he : 1 - γ + γ = 1 := by ring
    rw [he, Real.rpow_one]
  have hmul : r * (lam * r ^ γ) ≤ r * (32 * K) := by
    calc
      r * (lam * r ^ γ) = (lam * r) * r ^ γ := by ring
      _ ≤ (32 * K * r ^ (1 - γ)) * r ^ γ :=
        mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hr.le γ)
      _ = (32 * K) * (r ^ (1 - γ) * r ^ γ) := by ring
      _ = r * (32 * K) := by rw [hproduct]; ring
  have hcancel : lam * r ^ γ ≤ 32 * K := (mul_le_mul_iff_right₀ hr).mp hmul
  exact (le_div_iff₀ hlam).mpr (by nlinarith only [hcancel])

/-- The actual source data imply the quantitative ratio-power bound in the
large-slope branch. No final slope inequality is an input. -/
theorem noisy_slope_power (J : Finset ℤ) (y : ℤ → ℝ) (Y : Finset ℝ)
    (δ ρ E b x₀ q K γ lam : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρone : ρ ≤ 1) (hE : 0 ≤ E)
    (hK : 1 ≤ K) (hγ : 0 < γ) (hγone : γ ≤ 1) (hlam : 0 < lam)
    (hdensity : lam / δ ≤ (J.card : ℝ))
    (hY : ∀ z ∈ Y, -1 ≤ z ∧ z ≤ 1) (hyY : ∀ n ∈ J, y n ∈ Y)
    (hKT : IntervalKatzTao Y ρ K γ)
    (hsmallError : E * δ ≤ ρ) (hsmallStep : |b| * δ ≤ ρ)
    (hx : ∀ n ∈ J, |x₀ + δ * (n : ℝ)| ≤ 1)
    (herror : ∀ n ∈ J, |y n - q - b * (x₀ + δ * (n : ℝ))| ≤ E * δ)
    (hlarge : ρ < |b|) :
    (|b| / ρ) ^ γ ≤ 32 * K / lam := by
  have hlo := density_cells_lower J y δ ρ E b x₀ q lam hδ hρ hE hdensity herror hsmallError hsmallStep
  have hup := noisy_cells_upper J y Y δ ρ E b x₀ q K γ hρ hρone hK hγ hγone
    hY hyY hKT hsmallError hlarge hx herror
  have hcounts := hlo.trans (mul_le_mul_of_nonneg_left hup (by positivity : 0 ≤ 4 * ρ))
  have hr : 0 < |b| / ρ := div_pos (hρ.trans hlarge) hρ
  apply ratio_power_bound hr hlam
  have hid : |b| = ρ * (|b| / ρ) := by field_simp
  rw [hid] at hcounts
  nlinarith

/-- Scalar Katz--Tao slope consistency, including zero and small slopes. -/
theorem scalar_slope_bound (J : Finset ℤ) (y : ℤ → ℝ) (Y : Finset ℝ)
    (δ ρ E b x₀ q K γ lam : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρone : ρ ≤ 1) (hE : 0 ≤ E)
    (hK : 1 ≤ K) (hγ : 0 < γ) (hγone : γ ≤ 1) (hlam : 0 < lam)
    (hdensity : lam / δ ≤ (J.card : ℝ))
    (hY : ∀ z ∈ Y, -1 ≤ z ∧ z ≤ 1) (hyY : ∀ n ∈ J, y n ∈ Y)
    (hKT : IntervalKatzTao Y ρ K γ)
    (hsmallError : E * δ ≤ ρ) (hsmallStep : |b| * δ ≤ ρ)
    (hx : ∀ n ∈ J, |x₀ + δ * (n : ℝ)| ≤ 1)
    (herror : ∀ n ∈ J, |y n - q - b * (x₀ + δ * (n : ℝ))| ≤ E * δ) :
    |b| ≤ ρ * max 1 ((32 * K / lam) ^ (1 / γ)) := by
  by_cases hsmall : |b| ≤ ρ
  · exact hsmall.trans (by simpa using
      mul_le_mul_of_nonneg_left (le_max_left 1 ((32 * K / lam) ^ (1 / γ))) hρ.le)
  · have hlarge : ρ < |b| := lt_of_not_ge hsmall
    have hp := noisy_slope_power J y Y δ ρ E b x₀ q K γ lam
      hδ hρ hρone hE hK hγ hγone hlam hdensity hY hyY hKT hsmallError hsmallStep hx herror hlarge
    have hr : 0 ≤ |b| / ρ := div_nonneg (abs_nonneg b) hρ.le
    have hbase : 0 ≤ 32 * K / lam := by positivity
    have hroot : |b| / ρ ≤ (32 * K / lam) ^ (1 / γ) := by
      simpa only [one_div] using (Real.le_rpow_inv_iff_of_pos hr hbase hγ).mpr hp
    have hbound : |b| ≤ ρ * (32 * K / lam) ^ (1 / γ) := by
      have h := (div_le_iff₀ hρ).mp hroot
      nlinarith only [h]
    exact hbound.trans (mul_le_mul_of_nonneg_left (le_max_right 1 _) hρ.le)

end ScalarKatzTaoSlopeBound
