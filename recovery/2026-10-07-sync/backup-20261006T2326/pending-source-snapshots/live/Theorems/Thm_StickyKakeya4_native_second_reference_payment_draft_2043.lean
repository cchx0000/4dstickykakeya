/- UNVERIFIED scalar payment at the actual final native sigma.
The second Reference's eta0 precedes first-stage E, zeta53, chi and D.
The final admission is weakened to eta0/2; no intermediate z2 is substituted.
This pays the actual U,L inequalities when their source readers are composed
on one S. It does not assert those source inequalities or native admission.
-/
import Theorems.Thm_StickyKakeya4_wz_carrier_pruning
import Theorems.Thm_StickyKakeya4_native_finite_kakeya_counts

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeSecondReferencePaymentDraft2043
open StickyKakeya4

/-- A fixed quarter-eta0 gap pays the concrete shading denominator and
union numerator, uniformly over the later allowed E,chi,etaUnion. -/
theorem exists_volume_payment_cutoff (eta0 Cnum Cden : ℝ)
    (hEta : 0<eta0) (hNum : 0<Cnum) (hDen : 0<Cden) :
    ∃sigma0 : ℝ,0<sigma0 ∧ sigma0≤1 ∧
      ∀(E chi etaUnion sigma L U : ℝ),
        0≤E → E≤eta0/4 → 0<chi → 0≤etaUnion → etaUnion≤chi*eta0/32 →
        0<sigma → sigma≤sigma0 →
        sigma^(5*E/4096)/Cden≤L → U≤Cnum*sigma^(-(2*etaUnion/chi)) →
        U*sigma^(eta0/2)≤L := by
  obtain ⟨sigma0,hs0,hs01,Hcut⟩ := exists_positive_rpow_absorption_threshold
    (show 0<eta0/4 by positivity) (show 0≤Cnum*Cden by positivity) (by norm_num : (0:ℝ)<1)
  refine ⟨sigma0,hs0,hs01,?_⟩
  intro E chi etaUnion sigma L U _hE hEtop hChi _hUnion hUnionTop hSigma hSmall hL hU
  have hs1 : sigma≤1 := hSmall.trans hs01
  have hUnionLoss : 2*etaUnion/chi≤eta0/16 := by
    apply (div_le_iff₀ hChi).mpr
    nlinarith only [hUnionTop]
  have hMargin : 5*E/4096+eta0/4≤eta0/2-2*etaUnion/chi := by
    linarith only [hUnionLoss,hEtop,hEta]
  have hPow : sigma^(eta0/2-2*etaUnion/chi)≤sigma^(5*E/4096+eta0/4) :=
    Real.rpow_le_rpow_of_exponent_ge hSigma hs1 hMargin
  have hAbsorb := Hcut sigma hSigma hSmall
  calc
    U*sigma^(eta0/2)≤(Cnum*sigma^(-(2*etaUnion/chi)))*sigma^(eta0/2) :=
      mul_le_mul_of_nonneg_right hU (Real.rpow_nonneg hSigma.le _)
    _ = Cnum*sigma^(eta0/2-2*etaUnion/chi) := by
      rw [mul_assoc,←Real.rpow_add hSigma]
      congr 2
      ring
    _ ≤ Cnum*sigma^(5*E/4096+eta0/4) := mul_le_mul_of_nonneg_left hPow hNum.le
    _ = Cnum*sigma^(eta0/4)*sigma^(5*E/4096) := by
      rw [Real.rpow_add hSigma]
      ring
    _ ≤ sigma^(5*E/4096)/Cden := by
      apply (le_div_iff₀ hDen).mpr
      calc
        _ = (Cnum*Cden*sigma^(eta0/4))*sigma^(5*E/4096) := by ring
        _ ≤ 1*sigma^(5*E/4096) :=
          mul_le_mul_of_nonneg_right hAbsorb (Real.rpow_nonneg hSigma.le _)
        _ = _ := one_mul _
    _ ≤ L := hL

/-- The actual stronger source admission may be used with eta0/2 in the
fixed Reference. This does not require a lower bound for its old exponent. -/
theorem native_input_at_half_eta0 {n : ℕ} {S : FiniteScaleSource n} {E eta0 : ℝ}
    (hS : IsWangZakharovNativeFiniteInput S E) (hE : E≤eta0/4) (hEta : 0≤eta0) :
    IsWangZakharovNativeFiniteInput S (eta0/2) :=
  NativeFiniteKakeyaCounts.input_mono hS (by linarith only [hE,hEta])

/-- Any proved positive source power window pulls the two final cutoffs
back to one ORIGINAL-datum cutoff chosen before the original datum. -/
theorem exists_original_cutoff (power sigma0 deltaRef : ℝ)
    (hPower : 0<power) (hSigma : 0<sigma0) (hRef : 0<deltaRef) :
    ∃delta0 : ℝ,0<delta0 ∧ delta0≤1 ∧
      ∀delta sigma : ℝ,0<delta → delta≤delta0 → sigma≤delta^power →
        sigma≤sigma0 ∧ sigma≤deltaRef := by
  obtain ⟨delta0,hd0,hd01,H⟩ := exists_positive_rpow_absorption_threshold
    hPower (by norm_num : (0:ℝ)≤1) (lt_min hSigma hRef)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta sigma hd hsmall hwindow
  have hh : delta^power≤min sigma0 deltaRef := by simpa only [one_mul] using H delta hd hsmall
  exact ⟨hwindow.trans (hh.trans (min_le_left _ _)),hwindow.trans (hh.trans (min_le_right _ _))⟩

end NativeSecondReferencePaymentDraft2043
