import Theorems.Thm_StickyKakeya4_triangular_potential_charge
import Theorems.Thm_StickyKakeya4_triangular_uniform_potential_bound
import Theorems.Thm_StickyKakeya4_triangular_borel_front_escape
import Theorems.Thm_StickyKakeya4_root_tail_moment

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

namespace StickyKakeya4.TriangularRootMoment
open TriangularPotentialEscape TriangularPotentialCharge
open TriangularBorelFrontEscape TriangularUniformPotentialBound

theorem exists_saturating_cutoff
    (D : ℝ≥0∞) (hD₀ : D ≠ 0) (hDtop : D ≠ ⊤)
    (s r : ℝ) (hr : 0 < r)
    (B : ℝ≥0∞) (hB₀ : B ≠ 0) (hBtop : B ≠ ⊤) :
    ∃ N : ℝ≥0∞, N ≠ 0 ∧ N ≠ ⊤ ∧
      2 * (D * ((N * (2 : ℝ≥0∞) ^ s) * ENNReal.ofReal r ^ s) ^ 3) = B ∧
      ∀ H : ℝ≥0∞, 2 * (H / N) =
        (2 * H * (2 * D) ^ (1 / 3 : ℝ) * (2 : ℝ≥0∞) ^ s) *
          ENNReal.ofReal r ^ s * B ^ (-(1 / 3 : ℝ)) := by
  let L : ℝ≥0∞ := (2 : ℝ≥0∞) ^ s * ENNReal.ofReal r ^ s
  let c : ℝ≥0∞ := 2 * D
  have hL₀ : L ≠ 0 := by
    apply mul_ne_zero
    · exact (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
    · exact (ENNReal.rpow_pos (by positivity) ENNReal.ofReal_ne_top).ne'
  have hLtop : L ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))
      (ENNReal.rpow_ne_top_of_ne_zero (by positivity) ENNReal.ofReal_ne_top)
  have hc₀ : c ≠ 0 := mul_ne_zero (by norm_num) hD₀
  have hctop : c ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hDtop
  have hbc₀ : B / c ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hB₀, hctop⟩
  have hbctop : B / c ≠ ⊤ := ENNReal.div_ne_top hBtop hc₀
  let R : ℝ≥0∞ := (B / c) ^ (1 / 3 : ℝ)
  have hR₀ : R ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hbc₀) hbctop).ne'
  have hRtop : R ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hbc₀ hbctop
  refine ⟨R / L, ?_, ENNReal.div_ne_top hRtop hL₀, ?_, ?_⟩
  · exact ENNReal.div_ne_zero.mpr ⟨hR₀, hLtop⟩
  · have hprod : ((R / L) * (2 : ℝ≥0∞) ^ s) * ENNReal.ofReal r ^ s = R := by
      rw [mul_assoc]
      exact ENNReal.div_mul_cancel hL₀ hLtop
    rw [hprod]
    have hcube : R ^ (3 : ℕ) = B / c := by
      dsimp [R]
      rw [← ENNReal.rpow_mul_natCast]
      norm_num
    rw [hcube, ← mul_assoc]
    exact ENNReal.mul_div_cancel hc₀ hctop
  · intro H
    have hRi : R⁻¹ = c ^ (1 / 3 : ℝ) * B ^ (-(1 / 3 : ℝ)) := by
      dsimp [R]
      rw [ENNReal.div_rpow_of_nonneg B c (by norm_num : (0 : ℝ) ≤ 1 / 3),
        ENNReal.inv_div (Or.inr (ENNReal.rpow_ne_top_of_ne_zero hB₀ hBtop))
          (Or.inr (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hB₀) hBtop).ne'),
        div_eq_mul_inv, ENNReal.rpow_neg]
    rw [div_eq_mul_inv, ENNReal.inv_div (Or.inl hLtop) (Or.inl hL₀),
      div_eq_mul_inv, hRi]
    dsimp [L, c]
    simp only [mul_assoc, mul_comm, mul_left_comm]

def originalRootBallMass
    (σ : Measure Source)
    (b₁ : ℝ → ℝ) (b₂ : ℝ × ℝ → ℝ) (b₃ : Source → ℝ)
    (r : ℝ) (p : ℝ × Source) : ℝ≥0∞ :=
  (σ.map (fun a => spatialPoint (affine₁ b₁) (affine₂ b₂) (affine₃ b₃) (p.1, a)))
    (Metric.ball (spatialPoint (affine₁ b₁) (affine₂ b₂) (affine₃ b₃) p) r)

theorem measurable_originalRootBallMass
    (σ : Measure Source) [SFinite σ]
    (b₁ : ℝ → ℝ) (b₂ : ℝ × ℝ → ℝ) (b₃ : Source → ℝ)
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) (hb₃ : Measurable b₃)
    (r : ℝ) : Measurable (originalRootBallMass σ b₁ b₂ b₃ r) := by
  apply measurable_original_root_ball_mass
  apply measurable_spatialPoint
  · unfold affine₁; fun_prop
  · unfold affine₂; fun_prop
  · unfold affine₃; fun_prop

def triangularTailConstant
    (μ₁ μ₂ μ₃ : Measure ℝ) (D : ℝ≥0∞) (u v s : ℝ) : ℝ≥0∞ :=
  2 * uniformTriangularPotentialBound μ₁ μ₂ μ₃ D u v s *
    (2 * D) ^ (1 / 3 : ℝ) * (2 : ℝ≥0∞) ^ s

theorem triangularTailConstant_ne_top
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (D : ℝ≥0∞) (hDtop : D ≠ ⊤)
    (u v s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    triangularTailConstant μ₁ μ₂ μ₃ D u v s ≠ ⊤ := by
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (uniformTriangularPotentialBound_lt_top μ₁ μ₂ μ₃ D hDtop u v s hs hs1).ne)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.mul_ne_top (by norm_num) hDtop)))
    (ENNReal.rpow_ne_top_of_nonneg hs.le (by norm_num))

theorem triangular_original_root_tail
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
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (r : ℝ) (hr : 0 < r)
    (B : ℝ≥0∞) (hB₀ : B ≠ 0) (hBtop : B ≠ ⊤) :
    ((volume.restrict (Icc u v)).prod σ)
        {p | B < originalRootBallMass σ b₁ b₂ b₃ r p} ≤
      min (((volume.restrict (Icc u v)).prod σ) univ)
        (triangularTailConstant μ₁ μ₂ μ₃ D u v s * ENNReal.ofReal r ^ s *
          B ^ (-(1 / 3 : ℝ))) := by
  apply le_min (measure_mono (subset_univ _))
  obtain ⟨N, hN₀, hNtop, hthreshold, hidentity⟩ :=
    exists_saturating_cutoff D hD₀ hDtop s r hr B hB₀ hBtop
  have hg₁ : Measurable (affine₁ b₁) := by unfold affine₁; fun_prop
  have hg₂ : Measurable (affine₂ b₂) := by unfold affine₂; fun_prop
  have hg₃ : Measurable (affine₃ b₃) := by unfold affine₃; fun_prop
  have hsp := measurable_spatialPoint _ _ _ hg₁ hg₂ hg₃
  let H := uniformTriangularPotentialBound μ₁ μ₂ μ₃ D u v s
  have hH := actual_nativePotentialSum_integral_le μ₁ μ₂ μ₃ D₁ D₂ D₃ hD₁ hD₂ hD₃
    hμ₁ hμ₂ hμ₃ σ D hDtop hdom b₁ b₂ b₃ hb₁ hb₂ hb₃ u v s hs hs1
  unfold originalRootBallMass
  rw [original_heavy_event_measure_eq _ σ _ hsp r B]
  calc
    _ ≤ 2 * (H / N) := triangular_original_heavy_root_charge μ₁ μ₂ μ₃
      (volume.restrict (Icc u v)) σ D hD₀ hDtop hdom
      (affine₁ b₁) (affine₂ b₂) (affine₃ b₃) hg₁ hg₂ hg₃ s hs N hN₀ hNtop
      (measurable_potential₁_affine μ₁ b₁ hb₁ s)
      (measurable_potential₂_affine μ₂ b₂ hb₂ s)
      (measurable_potential₃_affine μ₃ b₃ hb₃ s) H hH r hr B hthreshold.le
    _ = _ := hidentity H

theorem exists_triangular_original_root_moment_bound
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
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (θ : ℝ) (hθ : 0 < θ) (hθ3 : θ < 1 / 3) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ, 0 < r →
      (∫⁻ p, originalRootBallMass σ b₁ b₂ b₃ r p ^ θ
        ∂((volume.restrict (Icc u v)).prod σ)) ≤
      C * ENNReal.ofReal r ^ (3 * s * θ) := by
  let ν := (volume.restrict (Icc u v)).prod σ
  let K : ℝ≥0∞ := triangularTailConstant μ₁ μ₂ μ₃ D u v s + 1
  have hK₀ : K ≠ 0 := by dsimp [K]; positivity
  have hKtop : K ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨triangularTailConstant_ne_top μ₁ μ₂ μ₃ D hDtop u v s hs hs1, by norm_num⟩
  have hMtop : ν univ ≠ ⊤ := measure_ne_top ν univ
  let C : ℝ≥0∞ := RootTailMoment.momentConstant (ν univ) θ * K ^ (3 * θ)
  have hCtop : C ≠ ⊤ := ENNReal.mul_ne_top
    (RootTailMoment.momentConstant_ne_top hMtop hθ hθ3)
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hKtop)
  refine ⟨C, hCtop, ?_⟩
  intro r hr
  let A : ℝ≥0∞ := K * ENNReal.ofReal r ^ s
  have hA₀ : A ≠ 0 := mul_ne_zero hK₀
    (ENNReal.rpow_pos (by positivity) ENNReal.ofReal_ne_top).ne'
  have hAtop : A ≠ ⊤ := ENNReal.mul_ne_top hKtop
    (ENNReal.rpow_ne_top_of_nonneg hs.le ENNReal.ofReal_ne_top)
  have htail (B : ℝ) (hB : 0 < B) :
      ν {p | ENNReal.ofReal B < originalRootBallMass σ b₁ b₂ b₃ r p} ≤
        A * ENNReal.ofReal B ^ (-(1 / 3 : ℝ)) := by
    have ht := triangular_original_root_tail μ₁ μ₂ μ₃ D₁ D₂ D₃ hD₁ hD₂ hD₃
      hμ₁ hμ₂ hμ₃ σ D hD₀ hDtop hdom u v huv b₁ b₂ b₃ hb₁ hb₂ hb₃
      s hs hs1 r hr (ENNReal.ofReal B) (by positivity) ENNReal.ofReal_ne_top
    apply (ht.trans (min_le_right _ _)).trans
    apply mul_le_mul_left
    apply mul_le_mul_left
    exact le_add_right le_rfl
  have hmoment := RootTailMoment.ennreal_moment_le ν
    (measurable_originalRootBallMass σ b₁ b₂ b₃ hb₁ hb₂ hb₃ r).aemeasurable
    hθ hA₀ hAtop (by simpa only [neg_div] using htail)
  calc
    _ ≤ RootTailMoment.momentConstant (ν univ) θ * A ^ (3 * θ) := hmoment
    _ = C * ENNReal.ofReal r ^ (3 * s * θ) := by
      dsimp [A, C]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 3 * θ),
        ← ENNReal.rpow_mul, ← mul_assoc]
      congr 2
      ring

end StickyKakeya4.TriangularRootMoment
