import Theorems.Thm_StickyKakeya4_native_abc_original_loss_budget
import Theorems.Thm_StickyKakeya4_native_planar_abc_fixed_exponent
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeUniformABCInput
open Classical NativePlanarABCInput FinitePlaneProjectionGrid FinitePlaneProjectionGraph
open NativeABCOriginalLossBudget NativeQuarterBalancedMesh NativeQuarterScaleParameters
/-- The actual original-data constructor, original power-loss budget, and
 proved quarter mesh supply ONE standard native ABC input. All point sets
 and graph edges are retained exactly, and the upper C exponent is fixed
 in zeta. The strip width has a factor-two allowance for Euclidean normals. -/
theorem exists_uniform_ABC_input (J : ℕ) {delta rho a s u zeta KP KB beta lambda angularK angleRatio exponent error : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (ha : 0 ≤ a) (hs : 0 ≤ s) (hu : 0 ≤ u)
    (hz : 0 < zeta) (hbranch : zeta < exponent) (hExponent : exponent ≤ 2)
    (hMeshLow : delta^(1/2:ℝ) ≤ rho/8) (hMeshHigh : rho/8 ≤ quarterScale delta)
    (hSmallWidth : delta^(4*s) ≤ (1/8:ℝ)) (hFractionGap : 10*a ≤ u/8)
    (hBudget : 6168 ≤ delta^(-a))
    (hKP0 : 0 < KP) (hKB0 : 0 < KB) (hb : 0 < beta) (hlambda : 0 < lambda)
    (hKP : KP ≤ delta^(-a)) (hKB : KB ≤ delta^(-a))
    (hScales : ((dyadicScales J rho).card:ℝ) ≤ delta^(-a))
    (hbInv : beta⁻¹ ≤ delta^(-a)) (hlambdaInv : lambda⁻¹ ≤ delta^(-a))
    (hAng0 : 0 ≤ angularK) (hAng : angularK ≤ delta^(-a))
    (hRatio1 : 1 ≤ angleRatio) (hRatio : angleRatio ≤ delta^(-a))
    (hError0 : 0 ≤ error) (hError : error/rho ≤ delta^(-a))
    (data : Data (rho/8) exponent
      (400*graphLoss J rho KB beta*graphMassLoss J rho KP KB beta/(beta*lambda))
      ((2:ℝ)^exponent*((2:ℝ)^exponent*angularK^2*angleRatio^exponent))
      (beta/graphMassLoss J rho KP KB beta) (delta^(4*s)/4)
      (graphMassLoss J rho KP KB beta/beta*delta^(u/4))
      ((graphMassLoss J rho KP KB beta/beta)*(4*error/rho+8)^2)) :
    ∃ uniform : Data (rho/8) (zeta/2) ((rho/8)^(-64*a)) ((rho/8)^(-64*a))
      ((rho/8)^(64*a)) (2*(rho/8)^(32*s)) ((rho/8)^(u/4)) ((rho/8)^(-64*a)),
      uniform.A=data.A ∧ uniform.B=data.B ∧ uniform.C=data.C ∧ uniform.G=data.G := by
  let T := delta^(-a)
  let L := graphMassLoss J rho KP KB beta
  have hT : 0 < T := Real.rpow_pos_of_pos hd _
  have hT1 : 1 ≤ T := by dsimp [T]; linarith only [hBudget]
  have hm : 0 < rho/8 := (Real.rpow_pos_of_pos hd (1/2:ℝ)).trans_le hMeshLow
  have hrho : 0 < rho := by linarith only [hm]
  have hm1 : rho/8 ≤ 1 := hMeshHigh.trans (Real.rpow_le_one hd.le hd1 (by norm_num))
  have hL : 0 < L := graphMassLoss_pos J rho hKP0 hKB0 hb
  obtain ⟨hRate,hDensity,hBCost,hCCost,hCoverCost⟩ := actual_constructor_loss_budget J rho
    hBudget hKP0 hKB0 hb hlambda hKP hKB hScales hbInv hlambdaInv hAng0 hAng hRatio1 hRatio hExponent
    (div_nonneg hError0 hrho.le) hError
  have hPower := native_sixteenth_budget hd hm hMeshHigh ha
  have hP5 : T^5 ≤ T^16 := pow_le_pow_right₀ hT1 (by norm_num)
  have hP10 : T^10 ≤ T^16 := pow_le_pow_right₀ hT1 (by norm_num)
  have hP14 : T^14 ≤ T^16 := pow_le_pow_right₀ hT1 (by norm_num)
  have hDensityNative : (rho/8)^(64*a) ≤ beta/L :=
    hPower.2.trans (((inv_le_inv₀ (by positivity : (0:ℝ)<T^16) (by positivity : (0:ℝ)<T^10)).mpr hP10).trans hDensity)
  have hBNative : 400*graphLoss J rho KB beta*L/(beta*lambda) ≤ (rho/8)^(-64*a) := hBCost.trans hPower.1
  have hCNative : (2:ℝ)^exponent*((2:ℝ)^exponent*angularK^2*angleRatio^exponent) ≤ (rho/8)^(-64*a) :=
    hCCost.trans (hP5.trans hPower.1)
  have hMNative : (L/beta)*(4*error/rho+8)^2 ≤ (rho/8)^(-64*a) := by
    have hh := hCoverCost.trans (hP14.trans hPower.1)
    simpa only [← mul_div_assoc] using hh
  have hT10 : T^10=delta^(-(10*a)) := by
    dsimp [T]
    rw [← Real.rpow_natCast,← Real.rpow_mul hd.le]
    congr 1
    norm_num
    ring
  have hRatePower : L/beta ≤ delta^(-(10*a)) := by simpa only [← hT10] using hRate
  have hFraction : (L/beta)*delta^(u/4) ≤ (rho/8)^(u/4) := by
    apply native_line_fraction hd hMeshLow hu
    exact absorb_original_fraction_loss hd hd1 (div_nonneg hL.le hb.le) hRatePower le_rfl
      (show 10*a+u/8 ≤ u/4 by linarith only [hFractionGap])
  have hWidth : 2*(rho/8)^(32*s) ≤ delta^(4*s)/4 := by
    have hh := native_strip_width hd hm.le hMeshHigh hs hSmallWidth
    linarith only [hh]
  obtain ⟨fixed,hA,hB,hC,hG⟩ := NativePlanarABCFixedExponent.exists_zeta_exponent_data data hm hm1 hz hbranch
  let uniform : Data (rho/8) (zeta/2) ((rho/8)^(-64*a)) ((rho/8)^(-64*a))
      ((rho/8)^(64*a)) (2*(rho/8)^(32*s)) ((rho/8)^(u/4)) ((rho/8)^(-64*a)) := {
    A := fixed.A, B := fixed.B, C := fixed.C, G := fixed.G,
    nonemptyA := fixed.nonemptyA, nonemptyB := fixed.nonemptyB, nonemptyC := fixed.nonemptyC,
    graph_subset := fixed.graph_subset, boxA := fixed.boxA, boxB := fixed.boxB, boxC := fixed.boxC,
    separatedA := fixed.separatedA, separatedB := fixed.separatedB, separatedC := fixed.separatedC,
    ballB := by
      intro center R hR
      exact (fixed.ballB center R hR).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hBNative (hm.le.trans hR)) (Nat.cast_nonneg _)),
    lineB := by
      intro aa dd cc hnorm
      have hsub : fixed.B.filter (fun b => |aa*b.1+dd*b.2-cc| ≤ 2*(rho/8)^(32*s)) ⊆
          fixed.B.filter (fun b => |aa*b.1+dd*b.2-cc| ≤ delta^(4*s)/4) := by
        intro b hbB
        obtain ⟨hbB,hh⟩ := Finset.mem_filter.mp hbB
        exact Finset.mem_filter.mpr ⟨hbB,hh.trans hWidth⟩
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        ((fixed.lineB aa dd cc hnorm).trans (mul_le_mul_of_nonneg_right hFraction (Nat.cast_nonneg _))),
    frostmanC := by
      intro center R hR
      exact (fixed.frostmanC center R hR).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCNative (Real.rpow_nonneg (hm.le.trans hR) _)) (Nat.cast_nonneg _)),
    graph_density := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDensityNative (Nat.cast_nonneg fixed.A.card))
          (Nat.cast_nonneg fixed.B.card)) (Nat.cast_nonneg fixed.C.card)
      exact hh.trans fixed.graph_density,
    output_cover := fixed.output_cover.trans (mul_le_mul_of_nonneg_right hMNative (Nat.cast_nonneg _)) }
  exact ⟨uniform,hA,hB,hC,hG⟩
end NativeUniformABCInput
