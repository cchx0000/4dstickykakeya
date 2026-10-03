import Theorems.Thm_StickyKakeya4_triangular_potential_charge
import Theorems.Thm_StickyKakeya4_triangular_uniform_potential_bound
import Theorems.Thm_StickyKakeya4_triangular_borel_front_escape

/-!
# Summable heavy-root events for the original triangular Borel source law

The scalar uniform potential estimate and symmetric-ball charge discharge
every intermediate analytic certificate. The final statements concern the
original unmodified source/time measure and derive a positive small-radius
power followed by dyadic summability. No general triangularization is assumed.
-/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

namespace StickyKakeya4.TriangularHeavyRootPower
open TriangularPotentialEscape TriangularPotentialCharge
open TriangularBorelFrontEscape TriangularUniformPotentialBound

theorem exists_small_power_le_one
    (K : ℝ≥0∞) (hK : K ≠ ⊤) (γ : ℝ) (hγ : 0 < γ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      K * ENNReal.ofReal r ^ γ ≤ 1 := by
  have hc : Continuous (fun r : ℝ => ENNReal.ofReal r ^ γ) :=
    ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal
  have hp : Tendsto (fun r : ℝ => ENNReal.ofReal r ^ γ) (𝓝 0) (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hγ] using hc.tendsto 0
  have hlim : Tendsto (fun r : ℝ => K * ENNReal.ofReal r ^ γ) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hp (Or.inr hK)
  have hev : ∀ᶠ r : ℝ in 𝓝 0, K * ENNReal.ofReal r ^ γ < 1 :=
    hlim.eventually (Iio_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))
  obtain ⟨r₀, hr₀, hh⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr hrr₀
  apply (hh ?_).le
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hr] using hrr₀

theorem cutoff_threshold_identity
    (D : ℝ≥0∞) (s ε β r : ℝ) (hr : 0 < r) :
    2 * (D * (((ENNReal.ofReal r ^ (-ε)) * (2 : ℝ≥0∞) ^ s) *
      ENNReal.ofReal r ^ s) ^ 3) =
      ((2 * D * ((2 : ℝ≥0∞) ^ s) ^ 3) *
        ENNReal.ofReal r ^ (3 * s - 3 * ε - β)) * ENNReal.ofReal r ^ β := by
  let a : ℝ≥0∞ := ENNReal.ofReal r
  have ha₀ : a ≠ 0 := by dsimp [a]; positivity
  have hatop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hi : (a ^ (-ε) * (2 : ℝ≥0∞) ^ s) * a ^ s =
      (2 : ℝ≥0∞) ^ s * a ^ (s - ε) := by
    rw [show s - ε = -ε + s by ring, ENNReal.rpow_add (-ε) s ha₀ hatop]
    simp only [mul_assoc, mul_comm]
  have hp : (a ^ (s - ε)) ^ (3 : ℕ) = a ^ (3 * (s - ε)) := by
    rw [mul_comm (3 : ℝ), ENNReal.rpow_mul]
    norm_num
  change 2 * (D * ((a ^ (-ε) * (2 : ℝ≥0∞) ^ s) * a ^ s) ^ 3) = _
  rw [hi, mul_pow, hp]
  have he : 3 * (s - ε) = (3 * s - 3 * ε - β) + β := by ring
  rw [he, ENNReal.rpow_add (3 * s - 3 * ε - β) β ha₀ hatop]
  dsimp [a]
  simp only [mul_assoc]

def triangularHeavySet (σ : Measure Source)
    (b₁ : ℝ → ℝ) (b₂ : ℝ × ℝ → ℝ) (b₃ : Source → ℝ)
    (r β : ℝ) : Set (ℝ × Source) :=
  {p | ENNReal.ofReal r ^ β <
    (σ.map (fun a => spatialPoint (affine₁ b₁) (affine₂ b₂) (affine₃ b₃) (p.1, a)))
      (Metric.ball (spatialPoint (affine₁ b₁) (affine₂ b₂) (affine₃ b₃) p) r)}

theorem measurableSet_triangularHeavySet
    (σ : Measure Source) [SFinite σ]
    (b₁ : ℝ → ℝ) (b₂ : ℝ × ℝ → ℝ) (b₃ : Source → ℝ)
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) (hb₃ : Measurable b₃)
    (r β : ℝ) : MeasurableSet (triangularHeavySet σ b₁ b₂ b₃ r β) := by
  apply measurableSet_lt measurable_const
  apply measurable_original_root_ball_mass
  apply measurable_spatialPoint
  · unfold affine₁; fun_prop
  · unfold affine₂; fun_prop
  · unfold affine₃; fun_prop

theorem exists_triangular_original_heavy_root_power
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (D₁ D₂ D₃ : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (hμ₁ : μ₁ ≤ ENNReal.ofReal D₁ • volume)
    (hμ₂ : μ₂ ≤ ENNReal.ofReal D₂ • volume)
    (hμ₃ : μ₃ ≤ ENNReal.ofReal D₃ • volume)
    (σ : Measure Source) [IsFiniteMeasure σ]
    (D : ℝ≥0∞) (hD₀ : D ≠ 0) (hDtop : D ≠ ⊤)
    (hdom : σ ≤ D • ((μ₁.prod μ₂).prod μ₃))
    (u v : ℝ) (_huv : u < v)
    (b₁ : ℝ → ℝ) (b₂ : ℝ × ℝ → ℝ) (b₃ : Source → ℝ)
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) (hb₃ : Measurable b₃)
    (β : ℝ) (hβ : 0 < β) (hβ3 : β < 3) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r < r₀ →
        ((volume.restrict (Icc u v)).prod σ) (triangularHeavySet σ b₁ b₂ b₃ r β) ≤
          C * ENNReal.ofReal r ^ ε := by
  let s : ℝ := (β + 3) / 6
  let ε : ℝ := (3 - β) / 12
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hexp : 3 * s - 3 * ε - β = 3 * ε := by dsimp [s, ε]; ring
  let H := uniformTriangularPotentialBound μ₁ μ₂ μ₃ D u v s
  have hHtop : H ≠ ⊤ :=
    (uniformTriangularPotentialBound_lt_top μ₁ μ₂ μ₃ D hDtop u v s hs hs1).ne
  let K : ℝ≥0∞ := 2 * D * ((2 : ℝ≥0∞) ^ s) ^ 3
  have hKtop : K ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hDtop)
      (ENNReal.pow_ne_top (ENNReal.rpow_ne_top_of_nonneg hs.le (by norm_num)))
  obtain ⟨r₀, hr₀, hsmall⟩ := exists_small_power_le_one K hKtop (3 * ε) (by positivity)
  refine ⟨ε, hε, 2 * H, ENNReal.mul_ne_top (by norm_num) hHtop, r₀, hr₀, ?_⟩
  intro r hr hrr₀
  let N : ℝ≥0∞ := ENNReal.ofReal r ^ (-ε)
  have hN₀ : N ≠ 0 :=
    (ENNReal.rpow_pos (by positivity : 0 < ENNReal.ofReal r) ENNReal.ofReal_ne_top).ne'
  have hNtop : N ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero (by positivity) ENNReal.ofReal_ne_top
  have hthreshold : 2 * (D * ((N * (2 : ℝ≥0∞) ^ s) * ENNReal.ofReal r ^ s) ^ 3) ≤
      ENNReal.ofReal r ^ β := by
    rw [show N = ENNReal.ofReal r ^ (-ε) by rfl, cutoff_threshold_identity D s ε β r hr, hexp]
    exact (mul_le_mul_left (hsmall r hr hrr₀) _).trans_eq (one_mul _)
  have hg₁ : Measurable (affine₁ b₁) := by unfold affine₁; fun_prop
  have hg₂ : Measurable (affine₂ b₂) := by unfold affine₂; fun_prop
  have hg₃ : Measurable (affine₃ b₃) := by unfold affine₃; fun_prop
  have hsp := measurable_spatialPoint _ _ _ hg₁ hg₂ hg₃
  have hH := actual_nativePotentialSum_integral_le μ₁ μ₂ μ₃ D₁ D₂ D₃ hD₁ hD₂ hD₃
    hμ₁ hμ₂ hμ₃ σ D hDtop hdom b₁ b₂ b₃ hb₁ hb₂ hb₃ u v s hs hs1
  change ((volume.restrict (Icc u v)).prod σ)
    {p | ENNReal.ofReal r ^ β <
      (σ.map (fun a => spatialPoint (affine₁ b₁) (affine₂ b₂) (affine₃ b₃) (p.1, a)))
        (Metric.ball (spatialPoint (affine₁ b₁) (affine₂ b₂) (affine₃ b₃) p) r)} ≤ _
  rw [original_heavy_event_measure_eq _ σ _ hsp r (ENNReal.ofReal r ^ β)]
  calc
    _ ≤ 2 * (H / N) := triangular_original_heavy_root_charge μ₁ μ₂ μ₃
      (volume.restrict (Icc u v)) σ D hD₀ hDtop hdom
      (affine₁ b₁) (affine₂ b₂) (affine₃ b₃) hg₁ hg₂ hg₃ s hs N hN₀ hNtop
      (measurable_potential₁_affine μ₁ b₁ hb₁ s)
      (measurable_potential₂_affine μ₂ b₂ hb₂ s)
      (measurable_potential₃_affine μ₃ b₃ hb₃ s) H hH r hr _ hthreshold
    _ = (2 * H) * ENNReal.ofReal r ^ ε := by
      dsimp [N]
      rw [ENNReal.rpow_neg, div_eq_mul_inv, inv_inv, mul_assoc]

theorem tsum_lt_top_of_eventually_le_geometric
    (f : ℕ → ℝ≥0∞) (hf : ∀ n, f n < ⊤)
    (C ρ : ℝ≥0∞) (hC : C ≠ ⊤) (hρ : ρ < 1)
    (hbound : ∀ᶠ n in atTop, f n ≤ C * ρ ^ n) :
    (∑' n, f n) < ⊤ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  have hgeom : (∑' n : ℕ, C * ρ ^ n) < ⊤ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top hC.lt_top (tsum_geometric_lt_top.mpr hρ)
  have htail : (∑' n : ℕ, f (n + N)) < ⊤ := by
    apply lt_of_le_of_lt _ hgeom
    calc
      (∑' n : ℕ, f (n + N)) ≤ ∑' n : ℕ, C * ρ ^ (n + N) :=
        ENNReal.tsum_le_tsum (fun n => hN (n + N) (Nat.le_add_left N n))
      _ ≤ ∑' n : ℕ, C * ρ ^ n :=
        ENNReal.tsum_comp_le_tsum_of_injective
          (show Function.Injective (fun n : ℕ => n + N) from fun _ _ h => Nat.add_right_cancel h)
          (fun n => C * ρ ^ n)
  rw [← Summable.sum_add_tsum_nat_add' (f := f) (k := N) ENNReal.summable]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.sum_lt_top.mpr (fun n _ => hf n), htail⟩

theorem dyadic_tsum_lt_top_of_small_power_bound
    (f : ℝ → ℝ≥0∞) (hf : ∀ n : ℕ, f ((1 / 2 : ℝ) ^ n) < ⊤)
    (ε : ℝ) (hε : 0 < ε) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hbound : ∀ r : ℝ, 0 < r → r < r₀ → f r ≤ C * ENNReal.ofReal r ^ ε) :
    (∑' n : ℕ, f ((1 / 2 : ℝ) ^ n)) < ⊤ := by
  let ρ : ℝ≥0∞ := ENNReal.ofReal (1 / 2 : ℝ) ^ ε
  have hρ : ρ < 1 := ENNReal.rpow_lt_one (by norm_num) hε
  apply tsum_lt_top_of_eventually_le_geometric _ hf C ρ hC hρ
  have hrad : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have heq (n : ℕ) : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ^ ε = ρ ^ n := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.rpow_natCast_mul, mul_comm (n : ℝ) ε, ENNReal.rpow_mul_natCast]
  filter_upwards [hrad.eventually (Iio_mem_nhds hr₀)] with n hn
  simpa only [heq] using hbound ((1 / 2 : ℝ) ^ n) (by positivity) hn

theorem triangular_original_heavy_root_dyadic_sum_lt_top
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (D₁ D₂ D₃ : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (hμ₁ : μ₁ ≤ ENNReal.ofReal D₁ • volume)
    (hμ₂ : μ₂ ≤ ENNReal.ofReal D₂ • volume)
    (hμ₃ : μ₃ ≤ ENNReal.ofReal D₃ • volume)
    (σ : Measure Source) [IsFiniteMeasure σ]
    (D : ℝ≥0∞) (hD₀ : D ≠ 0) (hDtop : D ≠ ⊤)
    (hdom : σ ≤ D • ((μ₁.prod μ₂).prod μ₃))
    (u v : ℝ) (huv : u < v)
    (b₁ : ℝ → ℝ) (b₂ : ℝ × ℝ → ℝ) (b₃ : Source → ℝ)
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) (hb₃ : Measurable b₃)
    (β : ℝ) (hβ : 0 < β) (hβ3 : β < 3) :
    (∑' n : ℕ, ((volume.restrict (Icc u v)).prod σ)
      (triangularHeavySet σ b₁ b₂ b₃ ((1 / 2 : ℝ) ^ n) β)) < ⊤ := by
  obtain ⟨ε, hε, C, hC, r₀, hr₀, hbound⟩ :=
    exists_triangular_original_heavy_root_power μ₁ μ₂ μ₃ D₁ D₂ D₃ hD₁ hD₂ hD₃
      hμ₁ hμ₂ hμ₃ σ D hD₀ hDtop hdom u v huv b₁ b₂ b₃ hb₁ hb₂ hb₃ β hβ hβ3
  exact dyadic_tsum_lt_top_of_small_power_bound _
    (fun _ => measure_lt_top _ _) ε hε C hC r₀ hr₀ hbound

end StickyKakeya4.TriangularHeavyRootPower
