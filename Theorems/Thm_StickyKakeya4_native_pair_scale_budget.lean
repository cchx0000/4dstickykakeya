import Theorems.Thm_StickyKakeya4_native_same_source_balance_absorption
import Theorems.Thm_StickyKakeya4_native_near_target_loss

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativePairScaleBudget
open Classical Finset StickyKakeya4 NativeIncidenceMultiplicityTower
open NativeSameSourceMultiplicityBalance NativeSameSourceBalanceAbsorption NativeNearTargetLoss

/-- The returned source transfer budget pays the whole geometric Q-fourth
constant; no additional subpower premise on the retained radix is needed. -/
theorem radix_four_cost {delta eta gamma : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1)
    (heta : 0 ≤ eta) (F Q : ℕ) (hF : 0 < F)
    (hcost : localCost*(F:ℝ)*(Q:ℝ)^2*delta^(-eta)  ≤  delta^(-gamma)) :
    (41472:ℝ)*(Q:ℝ)^4  ≤  delta^(-(2*gamma)) ∧
      (125:ℝ)*(Q:ℝ)^4  ≤  delta^(-(2*gamma)) := by
  have hF1 : (1:ℝ) ≤ F := by exact_mod_cast hF
  have hp : 1 ≤ delta^(-eta) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (neg_nonpos.mpr heta)
  have hC : 0 ≤ localCost := by norm_num [localCost]
  have hbase : localCost*(Q:ℝ)^2  ≤  delta^(-gamma) := by
    calc
      _  ≤  localCost*(F:ℝ)*(Q:ℝ)^2  := by
        simpa only [mul_one,mul_assoc,mul_left_comm,mul_comm] using
          mul_le_mul_of_nonneg_left hF1 (mul_nonneg hC (sq_nonneg (Q:ℝ)))
      _  ≤  localCost*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) :=
        le_mul_of_one_le_right (by positivity) hp
      _  ≤  _ := hcost
  have hs := pow_le_pow_left₀ (mul_nonneg hC (sq_nonneg (Q:ℝ))) hbase 2
  have hmain : (41472:ℝ)*(Q:ℝ)^4  ≤  delta^(-(2*gamma)) := by
    calc
      _  ≤  (localCost*(Q:ℝ)^2)^2 := by
        have hc : (41472:ℝ) ≤ localCost^2 := by norm_num [localCost]
        nlinarith [mul_le_mul_of_nonneg_right hc (pow_nonneg (Nat.cast_nonneg Q) 4)]
      _  ≤  (delta^(-gamma))^2 := hs
      _ = _ := by rw [←Real.rpow_mul_natCast hd.le]; congr 1; norm_num; ring
  refine ⟨hmain,?_⟩
  exact (mul_le_mul_of_nonneg_right (by norm_num : (125:ℝ) ≤ 41472)
    (pow_nonneg (Nat.cast_nonneg Q) 4)).trans hmain

lemma dyadic_scale_product {m f : ℕ} (hmf : m ≤ f) :
    ((2^m:ℕ):ℝ)*((2^(f-m+6):ℕ):ℝ)=64*((2^f:ℕ):ℝ) := by
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [←pow_add,show m+(f-m+6)=f+6 by omega,pow_add]
  norm_num [mul_comm]

lemma relative_scale_eq {m f : ℕ} (hmf : m ≤ f) :
    64/((2^(f-m+6):ℕ):ℝ)=((2^m:ℕ):ℝ)/((2^f:ℕ):ℝ) ∧
    64/((2^(f-m+6):ℕ):ℝ)=(64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)) := by
  have hp := dyadic_scale_product hmf
  have h1 : 64/((2^(f-m+6):ℕ):ℝ)=((2^m:ℕ):ℝ)/((2^f:ℕ):ℝ) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith only [hp]
  refine ⟨h1,?_⟩
  rw [h1]
  field_simp

lemma relative_local_product {delta : ℝ} {m f : ℕ} (hmf : m ≤ f) :
    (64/((2^(f-m+6):ℕ):ℝ))*(((2^f:ℕ):ℝ)*delta/64)=((2^m:ℕ):ℝ)*delta/64 := by
  rw [(relative_scale_eq hmf).1]
  field_simp

/-- Original depth separation and the two original scale windows imply the
relative coarse window inside the literal local source, without resampling. -/
theorem relative_power_window {delta w : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1) (hw : 0 < w)
    {m f : ℕ} (hmf : m ≤ f)
    (hlocal : delta ≤ ((2^m:ℕ):ℝ)*delta/64)
    (hf : ((2^f:ℕ):ℝ)*delta ≤ delta^w)
    (hgap : ((2^m:ℕ):ℝ)/((2^f:ℕ):ℝ) ≤ delta^w) :
    1/((2^(f-m+6):ℕ):ℝ) ≤ (((2^m:ℕ):ℝ)*delta/64)^(w/2) ∧
      ((((2^m:ℕ):ℝ)*delta/64)/(1/((2^(f-m+6):ℕ):ℝ))) ≤ 
        (((2^m:ℕ):ℝ)*delta/64)^(w/2) := by
  have hpower : delta^w  ≤  (((2^m:ℕ):ℝ)*delta/64)^(w/2) :=
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)).trans
      (Real.rpow_le_rpow hd.le hlocal (half_pos hw).le)
  have hcoarse : 1/((2^(f-m+6):ℕ):ℝ)  ≤  delta^w := by
    have hh := (relative_scale_eq hmf).1.trans_le hgap
    have hc : 1/((2^(f-m+6):ℕ):ℝ)  ≤  64/((2^(f-m+6):ℕ):ℝ) := by
      apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
    exact hc.trans hh
  refine ⟨hcoarse.trans hpower,?_⟩
  have he : ((((2^m:ℕ):ℝ)*delta/64)/(1/((2^(f-m+6):ℕ):ℝ)))=((2^f:ℕ):ℝ)*delta := by
    have hp := dyadic_scale_product hmf
    calc
      _ = (((2^m:ℕ):ℝ)*((2^(f-m+6):ℕ):ℝ))*delta/64 := by
        rw [div_div_eq_mul_div,div_one]
        ring
      _ = (64*((2^f:ℕ):ℝ))*delta/64 := by rw [hp]
      _ = _ := by ring
  rw [he]
  exact hf.trans hpower

/-- Fixed scalar choices leave room for local admission, relative original
population transfer, and both final conditional multiplicity errors. -/
theorem parameter_margins {tau w eC seed eLocal zeta : ℝ}
    (htau : 0 < tau) (hw : 0 < w) (heC : 0 < eC)
    (heSmall : eC ≤ tau/(128*w)) (hsTau : seed ≤ tau/64)
    (hsScale : seed ≤ w^2*eC/256) (hzEq : zeta=w*eLocal/32) (hzSmall : zeta ≤ seed/256) :
    eLocal ≤ (w/2)*eC/512 ∧ zeta<w*((w/2)*eC/32) ∧
      2*seed+seed/4 ≤ tau ∧ seed/4+7*((w/2)*eC/32)+tau/16 ≤ tau := by
  have heScale := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<128) hw)).mp heSmall
  have hwE : 0 < w^2*eC := mul_pos (sq_pos_of_pos hw) heC
  refine ⟨?_,?_,?_,?_⟩
  · rw [hzEq] at hzSmall
    apply (mul_le_mul_iff_right₀ hw).mp
    nlinarith
  · nlinarith
  · linarith
  · nlinarith

/-- OLD parent/child bounds and the exact conditional incidence tower force
the original conditional physical coarse lower after its proved bridge. -/
theorem conditional_lower {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (E : Finset (T × X)) (f : T → P)
    {delta epsParent epsChild relative kappa seed gamma C : ℝ}
    (hd : 0 < delta) (_hep : 0 < epsParent) (hec : 0 < epsChild) (hr : 0 < relative)
    (hscale : relative*epsChild=epsParent) (Q : ℕ) (hC : 0 ≤ C)
    (hparent : delta^seed*epsParent^(-kappa) ≤ multiplicity E)
    (hchildren : ∀q∈E.image (fun z => f z.1),multiplicity (parent E f q) ≤ 
      delta^(-seed)*epsChild^(-kappa))
    (hbridge : multiplicity (coarse E f) ≤ 125*(Q:ℝ)^4*C)
    (hcost : (125:ℝ)*(Q:ℝ)^4 ≤ delta^(-(2*gamma))) :
    delta^(2*seed+2*gamma)*relative^(-kappa) ≤ C := by
  have hupper := fine_le_coarse_from_parent_upper E f
    (by positivity : 0 ≤ delta^(-seed)*epsChild^(-kappa)) hchildren hbridge
  have hpow : epsParent^(-kappa)=relative^(-kappa)*epsChild^(-kappa) := by
    rw [←hscale,Real.mul_rpow hr.le hec.le]
  have hcancel : delta^seed*relative^(-kappa) ≤ (125*(Q:ℝ)^4)*delta^(-seed)*C := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hec (-kappa))).mp
    calc
      _ = delta^seed*epsParent^(-kappa) := by rw [hpow]; ring
      _  ≤  _ := hparent.trans hupper
      _ = _ := by ring
  have hm := move_density_loss hd hcancel
  have ha := absorb_balance_cost (power:=seed+seed) (loss:=2*gamma)
    (X:=relative^(-kappa)) hd hC hm hcost
  simpa only [show seed+seed=2*seed by ring] using ha

end NativePairScaleBudget
