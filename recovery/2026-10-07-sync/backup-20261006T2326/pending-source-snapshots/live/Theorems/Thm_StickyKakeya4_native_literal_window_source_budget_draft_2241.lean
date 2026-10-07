import Theorems.Thm_StickyKakeya4_native_literal_packed_window_caps_draft_2230
import Theorems.Thm_StickyKakeya4_native_retention_output_power

/- UNVERIFIED payment using the ACTUAL base chooser and rank-stop radius.
The parent-input thickness is never substituted for the rank radius.
The chain is eps^2<=rho(m), rho(m)^2<=6144*rStop, and sigma<=eps^(chi/2).
Thus no c^3 window occurs in the weak-Lipschitz cost and no requirement
epsilonGeom<<c^3*chi is introduced.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeLiteralWindowSourceBudgetDraft2241
open StickyKakeya4 NativeLiteralPackedWindowCapsDraft2230 NativeRetentionOutputPower

/-- The checked actual chooser transports rank-radius losses to the real
remembered native mesh with coefficient16/chi, retaining the fixed6144. -/
theorem rank_loss_at_native_mesh {rho eps rStop sigma chi epsilonGeom : ℝ}
    (hRho : 0<rho) (hRho1 : rho≤1) (hEps : 0<eps) (hSigma : 0<sigma)
    (hChi : 0<chi) (hGeom : 0≤epsilonGeom) (hGeom4 : epsilonGeom≤1/4)
    (hShape : 64*eps≤2*max ((5/4:ℝ)*rho^(1-2*epsilonGeom)) rho)
    (hStop : rho^2≤6144*rStop) (hOutput : sigma≤eps^(chi/2)) :
    rStop^(-2*epsilonGeom)≤6144*sigma^(-(16*epsilonGeom/chi)) := by
  have hSquare := configured_square_le_reference hRho hRho1 hEps.le hGeom hGeom4 hShape
  have hFourth := output_fourth_le_stop hRho.le hSquare hStop
  have hFirst := stop_loss_to_output hEps (by positivity : (0:ℝ)≤2*epsilonGeom)
    (by linarith only [hGeom4] : 2*epsilonGeom≤1) hFourth
  have hPower := Real.rpow_le_rpow_of_nonpos hSigma hOutput
    (show -(16*epsilonGeom/chi)≤0 by positivity)
  have hIdentity : (eps^(chi/2))^(-(16*epsilonGeom/chi))=eps^(-(8*epsilonGeom)) := by
    rw [←Real.rpow_mul hEps.le]
    congr 1
    field_simp [hChi.ne']
    ring
  rw [hIdentity] at hPower
  have hFirst' : rStop^(-2*epsilonGeom)≤6144*eps^(-(8*epsilonGeom)) := by
    convert hFirst using 1 <;> ring
  exact hFirst'.trans (mul_le_mul_of_nonneg_left hPower (by norm_num))

/-- The literal window-cap constant, including the real two512 time
contractions, costs64epsilonGeom/chi at native sigma. The constant2^176
is independent of all source scales and is paid only by a final cutoff. -/
theorem actual_window_cap_power {rho eps rStop sigma chi epsilonGeom Lold : ℝ}
    (hRho : 0<rho) (hRho1 : rho≤1) (hEps : 0<eps) (hSigma : 0<sigma) (hSigma1 : sigma≤1)
    (hChi : 0<chi) (hGeom : 0≤epsilonGeom) (hGeom4 : epsilonGeom≤1/4)
    (hShape : 64*eps≤2*max ((5/4:ℝ)*rho^(1-2*epsilonGeom)) rho)
    (hStop : rho^2≤6144*rStop) (hOutput : sigma≤eps^(chi/2))
    (hLold : 0≤Lold) (hWeak : Lold≤3*rStop^(-2*epsilonGeom)) :
    (((2*menuRadius ((2:ℝ)^23*Lold)+1)^4:ℕ):ℝ)≤
      (2:ℝ)^176*sigma^(-(64*epsilonGeom/chi)) := by
  let u := sigma^(-(16*epsilonGeom/chi))
  let L := (2:ℝ)^23*Lold
  have hu : 1≤u := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hSigma hSigma1
    (by dsimp only [u]; positivity)
  have hL : 0≤L := by dsimp only [L]; positivity
  have hRank := rank_loss_at_native_mesh hRho hRho1 hEps hSigma hChi hGeom hGeom4 hShape hStop hOutput
  have hLbound : L≤((2:ℝ)^23*3*6144)*u := by
    have hh := mul_le_mul_of_nonneg_left
      (hWeak.trans (mul_le_mul_of_nonneg_left hRank (by norm_num))) (by positivity : (0:ℝ)≤(2:ℝ)^23)
    simpa only [L,u,mul_assoc] using hh
  have hCeil : (menuRadius L:ℝ)≤9+28*L := by
    have hh := Nat.ceil_lt_add_one (show 0≤(8:ℝ)+28*L by positivity)
    change (menuRadius L:ℝ)<8+28*L+1 at hh
    linarith only [hh]
  have hMenu : (2*(menuRadius L:ℝ)+1)≤(2:ℝ)^44*u := by
    nlinarith only [hCeil,hLbound,hu]
  have hUfour : u^4=sigma^(-(64*epsilonGeom/chi)) := by
    dsimp only [u]
    rw [←Real.rpow_natCast,←Real.rpow_mul hSigma.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  calc
    _ = (2*(menuRadius L:ℝ)+1)^4 := by dsimp only [L]; push_cast; rfl
    _ ≤ ((2:ℝ)^44*u)^4 := pow_le_pow_left₀ (by positivity) hMenu 4
    _ = (2:ℝ)^176*sigma^(-(64*epsilonGeom/chi)) := by rw [mul_pow,←pow_mul,hUfour]

/-- A single small-sigma cutoff precedes the source and pays the fixed
constant. epsilonGeom is compared with chi times the OUTPUT tolerance;
the independent rank parameter may still satisfy c<=epsilonGeom/24. -/
theorem exists_actual_window_cap_cutoff (tolerance : ℝ) (hTol : 0<tolerance) :
    ∃sigma0 : ℝ,0<sigma0 ∧ sigma0≤1 ∧
      ∀{rho eps rStop sigma chi epsilonGeom Lold : ℝ},
        0<rho → rho≤1 → 0<eps → 0<sigma → sigma≤sigma0 → 0<chi →
        0≤epsilonGeom → epsilonGeom≤1/4 → epsilonGeom≤chi*tolerance/128 →
        64*eps≤2*max ((5/4:ℝ)*rho^(1-2*epsilonGeom)) rho →
        rho^2≤6144*rStop → sigma≤eps^(chi/2) →
        0≤Lold → Lold≤3*rStop^(-2*epsilonGeom) →
        (((2*menuRadius ((2:ℝ)^23*Lold)+1)^4:ℕ):ℝ)≤sigma^(-tolerance) := by
  obtain ⟨sigma0,hS0,hS1,Hpay⟩ := exists_positive_rpow_absorption_threshold
    (half_pos hTol) (by positivity : (0:ℝ)≤(2:ℝ)^176) (by norm_num : (0:ℝ)<1)
  refine ⟨sigma0,hS0,hS1,?_⟩
  intro rho eps rStop sigma chi epsilonGeom Lold hRho hRho1 hEps hSigma hSmall hChi
    hGeom hGeom4 hBudget hShape hStop hOutput hLold hWeak
  have hSigma1 : sigma≤1 := hSmall.trans hS1
  have hCost := actual_window_cap_power hRho hRho1 hEps hSigma hSigma1 hChi hGeom hGeom4
    hShape hStop hOutput hLold hWeak
  have hExp : 64*epsilonGeom/chi≤tolerance/2 := by
    apply (div_le_iff₀ hChi).mpr
    nlinarith only [hBudget]
  have hPower : sigma^(-(64*epsilonGeom/chi))≤sigma^(-(tolerance/2)) :=
    Real.rpow_le_rpow_of_exponent_ge hSigma hSigma1 (by linarith only [hExp])
  have hConstant : (2:ℝ)^176≤sigma^(-(tolerance/2)) := by
    rw [Real.rpow_neg hSigma.le,←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hSigma _)).mpr (Hpay sigma hSigma hSmall)
  calc
    _ ≤ (2:ℝ)^176*sigma^(-(64*epsilonGeom/chi)) := hCost
    _ ≤ sigma^(-(tolerance/2))*sigma^(-(tolerance/2)) :=
      mul_le_mul hConstant hPower (by positivity) (by positivity)
    _ = sigma^(-tolerance) := by rw [←Real.rpow_add hSigma]; congr 1; ring

end NativeLiteralWindowSourceBudgetDraft2241
