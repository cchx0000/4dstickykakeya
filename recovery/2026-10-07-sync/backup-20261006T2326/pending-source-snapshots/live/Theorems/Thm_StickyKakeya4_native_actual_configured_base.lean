import Theorems.Thm_StickyKakeya4_native_angular_test_scale
import Theorems.Thm_StickyKakeya4_native_configured_dyadic_matching
import Theorems.Thm_StickyKakeya4_native_single_height_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeActualConfiguredBase
open NativeAngularTestScale NativeConfiguredDyadicMatching
open NativeQuarterScaleParameters NativeSingleHeightBudget

/- These are the literal scalar definitions of NativeReferenceXYGridPoints.rho
and .mu. The local notation expands in every theorem statement, so later
source callers see definitionally identical scales without importing the
unrelated point/quotient geometry. No new scale or coordinate map is chosen. -/
local notation "rho" => (fun m : ℕ => (64:ℝ)/((2^m:ℕ):ℝ))
local notation "mu" => (fun m : ℕ => ((64:ℝ)/((2^m:ℕ):ℝ))/64)

/-- This cutoff precedes the native source. The actual middle-scale square
bound then gives any requested positive upper bound on rho, uniformly over
all rank exponents above the fixed amin. -/
theorem exists_source_rho_cutoff (amin cap : ℝ) (ha : 0< amin) (hcap : 0< cap) :
    ∃delta0 : ℝ,0< delta0 ∧ delta0≤ 1 ∧
      ∀delta r power : ℝ,0< delta → delta≤ delta0 → amin≤ power → r≤ delta^power →
        ∀m : ℕ,(rho m)^2≤ 6144*r → rho m≤ cap := by
  obtain ⟨delta0,hd0,hd01,H⟩:=exists_small_power_cutoff ha
    (show 0< cap^2/6144 by positivity)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta r power hd hsmall hpower hr m hroot
  have hd1:=hsmall.trans hd01
  have hp : delta^power≤ delta^amin := Real.rpow_le_rpow_of_exponent_ge hd hd1 hpower
  have hc:=H delta hd hsmall
  have hbound : (rho m)^2≤ cap^2 := by nlinarith only [hroot,hr,hp,hc]
  have hpos:=(by positivity : 0< rho m)
  nlinarith only [hbound,hpos,hcap]

/-- The configured base is actually chosen above the affine-error envelope.
It has a genuine dyadic depth, an integer recoding factor and the paid old
height count; none of those quantities is an unconstructed output premise. -/
theorem exists_actual_base (m : ℕ) (epsilon : ℝ) (he : 0≤ epsilon) (he4 : epsilon≤ 1/4)
    (hsmall : rho m≤ 1/16) :
    ∃u : ℕ,u+6≤ m ∧
      let R0 : ℕ := 2^(m-u)
      0< R0 ∧ mu m*(R0:ℝ)=(2:ℝ)⁻¹^u ∧
      rho m≤ mu m*(R0:ℝ) ∧ (5/4:ℝ)*(rho m)^(1-2*epsilon)≤ mu m*(R0:ℝ) ∧
      mu m*(R0:ℝ)≤ 2*max ((5/4:ℝ)*(rho m)^(1-2*epsilon)) (rho m) ∧
      mu m*(R0:ℝ)≤ 1 ∧
      ((8*R0:ℕ):ℝ)≤ 1280*(mu m)^(-2*epsilon) := by
  have hr:=(by positivity : 0< rho m)
  have hr1 : rho m≤ 1 := hsmall.trans (by norm_num)
  have hhalf : (rho m)^(1/2:ℝ)≤ (1/4:ℝ) := by
    rw [←Real.sqrt_eq_rpow]
    exact Real.sqrt_le_iff.mpr ⟨by norm_num,by nlinarith only [hsmall]⟩
  have hp : (rho m)^(1-2*epsilon)≤ (rho m)^(1/2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith only [he4])
  have hrp : rho m≤ (rho m)^(1-2*epsilon) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hr hr1
      (show 1-2*epsilon≤ 1 by linarith only [he])
  have herr : rho m≤ (5/4:ℝ)*(rho m)^(1-2*epsilon) := by
    have hpp:=Real.rpow_pos_of_pos hr (1-2*epsilon)
    nlinarith only [hrp,hpp]
  let target:=max ((5/4:ℝ)*(rho m)^(1-2*epsilon)) (rho m)
  have ht : 0< target := hr.trans_le (le_max_right _ _)
  have htHalf : target≤ 1/2 := max_le (by nlinarith only [hp,hhalf]) (hsmall.trans (by norm_num))
  obtain ⟨s,hs,hlo,hhi⟩:=exists_dyadic_angular_scale ht (htHalf.trans (by norm_num))
  let u:=s-6
  have hsu : s=u+6 := by dsimp [u]; omega
  have hscale : 64/((2^s:ℕ):ℝ)=(2:ℝ)⁻¹^u := by
    rw [hsu,Nat.cast_pow,Nat.cast_ofNat,pow_add,inv_pow]
    norm_num
    field_simp
  have hdepth : u+6≤ m := configured_depth_le m u ((le_max_right _ _).trans (hlo.trans_eq hscale))
  let R0 : ℕ := 2^(m-u)
  have hR0 : 0< R0 := by dsimp [R0]; positivity
  have hpow : (2:ℝ)^(m-u)*(2:ℝ)^u=(2:ℝ)^m := by
    rw [←pow_add,Nat.sub_add_cancel (by omega)]
  have hbase : mu m*(R0:ℝ)=(2:ℝ)⁻¹^u := by
    dsimp [R0]
    push_cast
    rw [inv_pow]
    field_simp
    nlinarith only [hpow]
  have hlow : target≤ mu m*(R0:ℝ) := by rw [hbase]; exact hlo.trans_eq hscale
  have hhigh : mu m*(R0:ℝ)≤ 2*target := by rw [hbase,←hscale]; exact hhi
  have hmu:=(by positivity : 0< mu m)
  have hmuRho : 64*mu m=rho m := by dsimp; ring
  have hmu1 : mu m≤ 1 := by nlinarith only [hmuRho,hr1]
  have hEnvelope : mu m*(R0:ℝ)≤ 2*max ((5/4:ℝ)*(64*mu m)^(1-2*epsilon)) (mu m) := by
    rw [hmuRho]
    apply hhigh.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤ 2)
    exact max_le (le_max_left _ _) (herr.trans (le_max_left _ _))
  have hHeight:=height_cost_from_error_envelope R0 hmu hmu1 he (by norm_num : (0:ℝ)≤ 5/4) hEnvelope
  norm_num at hHeight
  have hHeightNat : ((8*R0:ℕ):ℝ) ≤ 1280*(mu m)^(-2*epsilon) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,neg_mul] using hHeight
  refine ⟨u,hdepth,hR0,hbase,(le_max_right _ _).trans hlow,(le_max_left _ _).trans hlow,
    hhigh,?_,hHeightNat⟩
  exact hhigh.trans (by nlinarith only [htHalf])

/-- A caller's FINAL configured tube-scale bound is paid before choosing
the original source, uniformly over the allowed geometry tolerance. -/
theorem exists_source_base (amin finalBound : ℝ) (ha : 0< amin) (hB : 0< finalBound) :
    ∃delta0 : ℝ,0< delta0 ∧ delta0≤ 1 ∧
      ∀delta r power : ℝ,0< delta → delta≤ delta0 → amin≤ power → r≤ delta^power →
      ∀m : ℕ,(rho m)^2≤ 6144*r → ∀epsilon : ℝ,0≤ epsilon → epsilon≤ 1/4 →
      ∃u : ℕ,6≤ u ∧ u+6≤ m ∧
        let R0 : ℕ := 2^(m-u)
        0< R0 ∧ mu m*(R0:ℝ)=(2:ℝ)⁻¹^u ∧
        rho m≤ mu m*(R0:ℝ) ∧ (5/4:ℝ)*(rho m)^(1-2*epsilon)≤ mu m*(R0:ℝ) ∧
        mu m*(R0:ℝ)≤ 2*max ((5/4:ℝ)*(rho m)^(1-2*epsilon)) (rho m) ∧
        mu m*(R0:ℝ)≤ 1 ∧ ((8*R0:ℕ):ℝ)≤ 1280*(mu m)^(-2*epsilon) ∧
        (mu m*(R0:ℝ))/64< finalBound := by
  let bound:=min finalBound (1/4096:ℝ)
  have hBound : 0< bound := lt_min hB (by norm_num)
  let cap:=min (1/16:ℝ) (((64/5:ℝ)*bound)^2)
  have hcap : 0< cap := lt_min (by norm_num) (by positivity)
  obtain ⟨delta0,hd0,hd01,H⟩:=exists_source_rho_cutoff amin cap ha hcap
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta r power hd hsmall hpower hr m hroot epsilon he he4
  have hrhoCap:=H delta r power hd hsmall hpower hr m hroot
  have hrhoSmall : rho m≤ 1/16 := hrhoCap.trans (min_le_left _ _)
  obtain ⟨u,hdepth,hR0,hbase,hrho,herror,hhigh,hbase1,hheight⟩:=
    exists_actual_base m epsilon he he4 hrhoSmall
  have hrho1 : rho m≤ 1 := hrhoSmall.trans (by norm_num)
  have hp : (rho m)^(1-2*epsilon)≤ Real.sqrt (rho m) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge ((by positivity : 0< rho m)) hrho1 (by linarith only [he4])
  have hrootCap : Real.sqrt (rho m)≤ (64/5:ℝ)*bound :=
    Real.sqrt_le_iff.mpr ⟨by positivity,hrhoCap.trans (min_le_right _ _)⟩
  have hlow : rho m≤ Real.sqrt (rho m) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ((by positivity : 0< rho m)) hrho1
      (show (1/2:ℝ)≤ 1 by norm_num)
  have htarget : max ((5/4:ℝ)*(rho m)^(1-2*epsilon)) (rho m)≤
      (5/4:ℝ)*Real.sqrt (rho m) := by
    refine max_le (mul_le_mul_of_nonneg_left hp (by norm_num)) ?_
    have hnonneg:=Real.sqrt_nonneg (rho m)
    nlinarith only [hlow,hnonneg]
  have hFinal : (mu m*((2^(m-u):ℕ):ℝ))/64< bound := by
    nlinarith only [hhigh,htarget,hrootCap,hBound]
  have hTiny : (mu m*((2^(m-u):ℕ):ℝ))/64< (1/4096:ℝ) :=
    hFinal.trans_le (min_le_right _ _)
  have hu6 : 6≤ u := by
    by_contra hu
    have hu5 : u≤ 5 := by omega
    have hPow : (2:ℝ)^u≤ (2:ℝ)^5 := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0< (2:ℕ)) hu5
    norm_num at hPow
    have hProd : (2:ℝ)^u*((2:ℝ)⁻¹^u)=1 := by
      rw [inv_pow,mul_inv_cancel₀ (by positivity)]
    have hPos : 0< (2:ℝ)⁻¹^u := by positivity
    have hMul:=mul_le_mul_of_nonneg_right hPow hPos.le
    rw [hProd] at hMul
    rw [hbase] at hTiny
    nlinarith only [hTiny,hMul]
  exact ⟨u,hu6,hdepth,hR0,hbase,hrho,herror,hhigh,hbase1,hheight,
    hFinal.trans_le (min_le_left _ _)⟩

/-- Every prepared depth above the chosen base has the exact natural
multiple used by the final time-floor reader. -/
lemma prepared_multiple (u depth : ℕ) (hdepth : depth≤ u+6) :
    64/((2^depth:ℕ):ℝ)=(2:ℝ)⁻¹^u*((2^(u+6-depth):ℕ):ℝ) := by
  have hp : (2:ℝ)^(u+6-depth)*(2:ℝ)^depth=(2:ℝ)^(u+6) := by
    rw [←pow_add,Nat.sub_add_cancel hdepth]
  rw [pow_add] at hp
  norm_num only [show (2:ℝ)^6=64 by norm_num] at hp
  push_cast
  rw [inv_pow]
  field_simp
  nlinarith only [hp]

/-- The actual source caller ALWAYS includes its exact configured base.
K is the number of additional prepared scales; the pre-D total is K+1. -/
def preparedDepths {K : ℕ} (u : ℕ) (depths : Fin K → ℕ) : Fin (K+1) → ℕ :=
  Fin.cases (u+6) depths

lemma preparedDepths_zero {K : ℕ} (u : ℕ) (depths : Fin K → ℕ) :
    preparedDepths u depths 0=u+6 := rfl

lemma preparedDepths_succ {K : ℕ} (u : ℕ) (depths : Fin K → ℕ) (j : Fin K) :
    preparedDepths u depths j.succ=depths j := rfl

lemma preparedDepths_bounds {K : ℕ} (m u : ℕ) (depths : Fin K → ℕ)
    (hu : u+6≤ m) (H : ∀j,6≤ depths j ∧ depths j≤ u+6) :
    ∀j,6≤ preparedDepths u depths j ∧ preparedDepths u depths j≤ m := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [preparedDepths_zero] using
      (show 6 ≤ u+6 ∧ u+6 ≤ m from ⟨by omega,hu⟩)
  · simpa only [preparedDepths_succ] using
      (show 6 ≤ depths i ∧ depths i ≤ m from ⟨(H i).1,(H i).2.trans hu⟩)

lemma preparedDepths_base_scale {K : ℕ} (u : ℕ) (depths : Fin K → ℕ) :
    64/((2^(preparedDepths u depths 0):ℕ):ℝ)=(2:ℝ)⁻¹^u := by
  change 64/((2^(u+6):ℕ):ℝ)=(2:ℝ)⁻¹^u
  simpa only [Nat.sub_self,pow_zero,Nat.cast_one,mul_one] using prepared_multiple u (u+6) le_rfl

lemma preparedDepths_multiples {K : ℕ} (u : ℕ) (depths : Fin K → ℕ)
    (H : ∀j,depths j≤ u+6) :
    ∀j,64/((2^(preparedDepths u depths j):ℕ):ℝ)=
      (2:ℝ)⁻¹^u*((2^(u+6-preparedDepths u depths j):ℕ):ℝ) := by
  intro j
  apply prepared_multiple
  exact Fin.cases le_rfl (fun i => H i) j

end NativeActualConfiguredBase
