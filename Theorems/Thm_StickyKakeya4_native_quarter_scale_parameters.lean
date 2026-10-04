import Theorems.Thm_StickyKakeya4_finite_plane_projection_allscale
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeQuarterScaleParameters
open Classical FinitePlaneProjectionGrid
def quarterScale (delta : ℝ) : ℝ := delta^(1/4:ℝ)
/-- An actual positive cutoff for a positive power, rather than an assumed
 eventual smallness certificate. -/
theorem exists_small_power_cutoff {a C : ℝ} (ha : 0 < a) (hC : 0 < C) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧ ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ → delta^a ≤ C := by
  refine ⟨min 1 (C^(1/a)),lt_min (by norm_num) (Real.rpow_pos_of_pos hC _),min_le_left _ _,?_⟩
  intro delta hd hsmall
  have hh := Real.rpow_le_rpow hd.le (hsmall.trans (min_le_right _ _)) ha.le
  have hid : (C^(1/a))^a=C := by
    rw [← Real.rpow_mul hC.le,one_div_mul_cancel ha.ne',Real.rpow_one]
  simpa only [hid] using hh
/-- At the quarter scale, a scheduled-bin factor delta^-g is harmless only
 when the explicit gap 1/4-g-2s is positive and made small. -/
theorem quarter_representative_buffer {delta sigma g s : ℝ} (hd : 0 < delta)
    (hwidth : sigma ≤ delta^(-g)*(quarterScale delta)^2)
    (hsmall : delta^((1/4:ℝ)-g-2*s) ≤ (1/8:ℝ)) :
    sigma/quarterScale delta ≤ (1/8:ℝ)*delta^(2*s) := by
  have hr : 0 < quarterScale delta := Real.rpow_pos_of_pos hd _
  calc
    _ ≤ (delta^(-g)*(quarterScale delta)^2)/quarterScale delta := div_le_div_of_nonneg_right hwidth hr.le
    _ = delta^(-g)*quarterScale delta := by field_simp
    _ = delta^((1/4:ℝ)-g) := by
      unfold quarterScale
      rw [← Real.rpow_add hd]
      congr 1
      ring
    _ = delta^((1/4:ℝ)-g-2*s)*delta^(2*s) := by
      rw [← Real.rpow_add hd]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (Real.rpow_pos_of_pos hd _).le
/-- Working-scale rounding can first be included in the proved error
 envelope. The actual normalized representative error need not use an
 exactly quarter-sized physical interval. -/
theorem quarter_error_buffer {delta g s e : ℝ} (hd : 0 < delta)
    (he : e ≤ delta^(-g)*quarterScale delta)
    (hsmall : delta^((1/4:ℝ)-g-2*s) ≤ (1/8:ℝ)) : e ≤ (1/8:ℝ)*delta^(2*s) := by
  have hr : 0 < quarterScale delta := Real.rpow_pos_of_pos hd _
  have hs : e*quarterScale delta ≤ delta^(-g)*(quarterScale delta)^2 := by
    have hh := mul_le_mul_of_nonneg_right he hr.le
    nlinarith only [hh]
  have hh := quarter_representative_buffer hd hs hsmall
  have hid : e*quarterScale delta/quarterScale delta=e := by field_simp
  simpa only [hid] using hh
/-- The widened ORIGINAL cross tube satisfies the strict affine source167
 threshold with concrete quarter-scale exponents and an explicit Lip loss. -/
theorem quarter_affine_source_buffer {delta Lip ell s e : ℝ} (hd : 0 < delta)
    (hLip0 : 0 ≤ Lip) (hLip : Lip ≤ delta^(-ell))
    (he : e ≤ (1/8:ℝ)*delta^(2*s))
    (hsmall : delta^(3*s/4-ell) ≤ (1/4:ℝ)) :
    Lip*quarterScale delta*((delta^(2*s)+2*e)/delta^s) < (quarterScale delta)^(1+s) := by
  have hp (a : ℝ) : 0 < delta^a := Real.rpow_pos_of_pos hd a
  have hr : 0 < quarterScale delta := hp _
  have ht : (quarterScale delta)^(1+s)=delta^((1/4:ℝ)+s/4) := by
    unfold quarterScale
    rw [← Real.rpow_mul hd.le]
    congr 1
    ring
  calc
    _ ≤ Lip*quarterScale delta*((2*delta^(2*s))/delta^s) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by nlinarith only [he,hp (2*s)]) (hp s).le)
        (mul_nonneg hLip0 hr.le)
    _ ≤ delta^(-ell)*quarterScale delta*((2*delta^(2*s))/delta^s) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLip hr.le) (by positivity)
    _ = 2*(delta^(-ell)*delta^(1/4:ℝ)*(delta^(2*s)/delta^s)) := by unfold quarterScale; ring
    _ = 2*delta^((1/4:ℝ)+s-ell) := by
      rw [← Real.rpow_sub hd,← Real.rpow_add hd,← Real.rpow_add hd]
      congr 1
      congr 1
      ring
    _ = 2*(delta^(3*s/4-ell)*delta^((1/4:ℝ)+s/4)) := by
      rw [← Real.rpow_add hd]
      congr 1
      congr 1
      ring
    _ ≤ (1/2:ℝ)*delta^((1/4:ℝ)+s/4) := by
      have hh := mul_le_mul_of_nonneg_right hsmall (hp ((1/4:ℝ)+s/4)).le
      nlinarith only [hh]
    _ < delta^((1/4:ℝ)+s/4) := by nlinarith only [hp ((1/4:ℝ)+s/4)]
    _ = _ := ht.symm
/-- Explicit projection widths: r0=delta^s, w0=delta^(2s), w=delta^(4s),
 theta=delta^(u/4), with 0 < u ≤ s. Original close/line fractions are charged before using
 this budget; the projection's reciprocal-area cost is not suppressed. -/
theorem projection_scalar_budget {delta s u close line parameterMesh : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (_hu : 0 < u) (hus : u ≤ s)
    (hclose : close ≤ delta^u) (hline : line ≤ delta^u)
    (hmesh : parameterMesh ≤ delta^s) (hsmall : delta^(u/4) ≤ (1/396:ℝ)) :
    3*(close+line+128*delta^(4*s)/(delta^s*delta^(2*s))+2*parameterMesh) ≤ (delta^(u/4))^3 := by
  have hratio : delta^(4*s)/(delta^s*delta^(2*s))=delta^s := by
    rw [← Real.rpow_add hd,← Real.rpow_sub hd]
    congr 1
    ring
  have hpow : delta^s ≤ delta^u := Real.rpow_le_rpow_of_exponent_ge hd hd1 hus
  have htheta : (delta^(u/4))^3=delta^(3*u/4) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hd.le]
    congr 1
    norm_num
    ring
  have hsplit : delta^u=delta^(u/4)*delta^(3*u/4) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_right hsmall (Real.rpow_pos_of_pos hd (3*u/4)).le
  rw [← hsplit] at hh
  have hratio128 : 128*delta^(4*s)/(delta^s*delta^(2*s))=128*delta^s := by
    rw [mul_div_assoc,hratio]
  rw [hratio128,htheta]
  nlinarith only [hclose,hline,hmesh,hpow,hh]
/-- Actual finite parameter resolution and logarithmic scale menu. The
 projection parameter mesh is selected; it is not taken as an unexplained
 fine-grid hypothesis. -/
theorem exists_projection_resolution_and_scales {rho tolerance : ℝ}
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (htol : 0 < tolerance) :
    ∃ n J : ℕ, mesh n ≤ rho ∧ mesh n ≤ tolerance ∧
      2 ≤ 2^(J+1)*rho ∧
      ((dyadicScales J rho).card : ℝ) ≤ Real.log (2/rho)/Real.log 2+2 := by
  let q := min rho tolerance
  have hq : 0 < q := lt_min hrho htol
  obtain ⟨n,hn⟩ := exists_nat_gt (1/q)
  have hm : mesh n ≤ q := by
    unfold mesh
    apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
    have hh := (div_lt_iff₀ hq).mp hn
    nlinarith only [hh,hq]
  have hx : (1:ℝ) ≤ 2/rho := (le_div_iff₀ hrho).mpr (by linarith)
  obtain ⟨J,hlo,hhi⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<2)
  have hJ : 2 ≤ 2^(J+1)*rho := ((div_lt_iff₀ hrho).mp hhi).le
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<2^J) hlo
  rw [Real.log_pow] at hlog
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hJlog : (J:ℝ) ≤ Real.log (2/rho)/Real.log 2 := (le_div_iff₀ hlog2).mpr hlog
  have hcard : ((dyadicScales J rho).card : ℝ) ≤ (J:ℝ)+2 := by
    exact_mod_cast dyadicScales_card_bound J rho
  exact ⟨n,J,hm.trans (min_le_left _ _),hm.trans (min_le_right _ _),hJ,by linarith⟩
/-- A nonempty explicit quarter-scale parameter region and one common
 small-delta cutoff for the representative, affine, and projection budgets.
 In particular s<1/8 is substantive, not an automatic consequence of eta. -/
theorem exists_quarter_parameter_cutoff {s g ell u : ℝ}
    (_hs : 0 < s) (hu : 0 < u) (hrepresentative : g+2*s < (1/4:ℝ)) (haffine : ell < 3*s/4) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧ ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      delta^((1/4:ℝ)-g-2*s) ≤ (1/8:ℝ) ∧
      delta^(3*s/4-ell) ≤ (1/4:ℝ) ∧ delta^(u/4) ≤ (1/396:ℝ) := by
  obtain ⟨d₁,hd₁,hd₁1,h₁⟩ := exists_small_power_cutoff
    (show 0 < (1/4:ℝ)-g-2*s by linarith) (by norm_num : (0:ℝ)<1/8)
  obtain ⟨d₂,hd₂,_hd₂1,h₂⟩ := exists_small_power_cutoff
    (show 0 < 3*s/4-ell by linarith) (by norm_num : (0:ℝ)<1/4)
  obtain ⟨d₃,hd₃,_hd₃1,h₃⟩ := exists_small_power_cutoff
    (show 0 < u/4 by positivity) (by norm_num : (0:ℝ)<1/396)
  refine ⟨min d₁ (min d₂ d₃),lt_min hd₁ (lt_min hd₂ hd₃),(min_le_left _ _).trans hd₁1,?_⟩
  intro delta hd hd0
  exact ⟨h₁ delta hd (hd0.trans (min_le_left _ _)),
    h₂ delta hd (hd0.trans ((min_le_right _ _).trans (min_le_left _ _))),
    h₃ delta hd (hd0.trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
/-- Choose the fraction exponent using BOTH original avoidance exponents.
 The projected tube-width exponent remains controlled by s; no lower bound
 on the independent source epsilon is silently imposed. -/
theorem fraction_exponent_choice {s epsilon : ℝ} (hs : 0 < s) (he : 0 < epsilon) :
    let u := min (s/4) (epsilon/16)
    0 < u ∧ 4*u ≤ s ∧ 4*u ≤ epsilon/4 := by
  refine ⟨lt_min (by positivity) (by positivity),?_,?_⟩
  · have hh := min_le_left (s/4) (epsilon/16)
    linarith
  · have hh := min_le_right (s/4) (epsilon/16)
    linarith
/-- Every fixed original loss coefficient admits a nonempty eta interval
 preserving the quarter-scale gaps and the fraction-exponent budget. -/
theorem exists_original_eta_region {s u Cgrain Clip Ccost : ℝ}
    (hs : 0 < s) (hsQuarter : s < (1/8:ℝ)) (hu : 0 < u)
    (hCg : 0 < Cgrain) (hCl : 0 < Clip) (hCc : 0 < Ccost) :
    ∃ eta₀ : ℝ, 0 < eta₀ ∧ eta₀ ≤ 1 ∧ ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta₀ →
      Cgrain*eta+2*s < (1/4:ℝ) ∧ Clip*eta < 3*s/4 ∧ Ccost*eta ≤ u/2 := by
  let a := ((1/4:ℝ)-2*s)/(2*Cgrain)
  let b := (3*s)/(8*Clip)
  let c := u/(2*Ccost)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (by linarith only [hsQuarter]) (by positivity)
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨min 1 (min a (min b c)),lt_min (by norm_num) (lt_min ha (lt_min hb hc)),min_le_left _ _,?_⟩
  intro eta _heta hsmall
  have heA : eta ≤ a := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heB : eta ≤ b := hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heC : eta ≤ c := hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hA := (le_div_iff₀ (by positivity : 0 < 2*Cgrain)).mp heA
  have hB := (le_div_iff₀ (by positivity : 0 < 8*Clip)).mp heB
  have hC := (le_div_iff₀ (by positivity : 0 < 2*Ccost)).mp heC
  exact ⟨by nlinarith only [hA,hsQuarter],by nlinarith only [hB,hs],by nlinarith only [hC]⟩
/-- Original inverse-density/fiber losses can be charged to a power budget
 BEFORE the finite projection scalar theorem is invoked. -/
theorem absorb_original_fraction_loss {delta loss fraction a b u : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hLoss : 0 ≤ loss)
    (hLossCap : loss ≤ delta^(-a)) (hFractionCap : fraction ≤ delta^b)
    (hExponent : a+u ≤ b) : loss*fraction ≤ delta^u := by
  calc
    _ ≤ loss*delta^b := mul_le_mul_of_nonneg_left hFractionCap hLoss
    _ ≤ delta^(-a)*delta^b := mul_le_mul_of_nonneg_right hLossCap (Real.rpow_pos_of_pos hd b).le
    _ = delta^(b-a) := by rw [← Real.rpow_add hd]; congr 1; ring
    _ ≤ delta^u := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
/-- On the nontrivial branch the ABC upper exponent may be fixed in zeta,
 while the ORIGINAL cardinality exponent kappa remains available. -/
theorem fixed_upper_exponent {zeta kappa : ℝ} (hz : 0 < zeta) (hbranch : zeta < kappa) :
    0 < zeta/2 ∧ zeta/2 ≤ kappa ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → r^kappa ≤ r^(zeta/2) := by
  refine ⟨by positivity,by linarith,?_⟩
  intro r hr hr1
  exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
end NativeQuarterScaleParameters
