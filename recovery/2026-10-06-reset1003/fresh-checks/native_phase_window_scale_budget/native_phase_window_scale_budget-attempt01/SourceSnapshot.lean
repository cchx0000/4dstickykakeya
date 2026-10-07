import Theorems.Thm_StickyKakeya4_native_angular_test_scale

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativePhaseWindowScaleBudget
open NativeAngularTestScale NativeMiddleGrainParentBudget NativeQuarterScaleParameters

/-- The factor1728 is the actual frozen configured-time metric conversion.
The exponent b remains free for the later analytic mesoscopic choice. -/
def physicalLip (r epsilon : ℝ) : ℝ := 1728*r^(-2*epsilon)
def phaseRho (r b : ℝ) : ℝ := r^b
def phaseMesh (r b : ℝ) : ℝ := 4099*phaseRho r b
def tangentMesh (r b : ℝ) : ℝ := 4099*(phaseRho r b)^2
def offsetMesh (r b epsilon : ℝ) : ℝ := 4099*physicalLip r epsilon*(phaseRho r b)^2
def grainWidth (r b epsilon : ℝ) : ℝ := (9*physicalLip r epsilon+8193)*(phaseRho r b)^2
def target (r b epsilon : ℝ) : ℝ := (36*physicalLip r epsilon+40970)*(phaseRho r b)^2

lemma physical_lip_power {r b epsilon : ℝ} (hr : 0<r) (hr1 : r≤1)
    (he : epsilon≤b/2) : physicalLip r epsilon*(phaseRho r b)^2≤1728*r^b := by
  have hid : physicalLip r epsilon*(phaseRho r b)^2=1728*r^(2*b-2*epsilon) := by
    unfold physicalLip phaseRho
    rw [←Real.rpow_mul_natCast hr.le, mul_assoc, ←Real.rpow_add hr]
    congr 1
    congr 1
    norm_num
    ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith only [he])) (by norm_num)

lemma target_power {r b epsilon : ℝ} (hr : 0<r) (hr1 : r≤1)
    (hb : 0<b) (he : epsilon≤b/2) : target r b epsilon≤104000*r^b := by
  have hl:=physical_lip_power hr hr1 he
  have hp : 0≤r^b := Real.rpow_nonneg hr.le _
  have hp1 : r^b≤1 := Real.rpow_le_one hr.le hr1 hb.le
  have hs : (phaseRho r b)^2≤r^b := by unfold phaseRho; nlinarith only [hp,hp1]
  calc
    _=36*(physicalLip r epsilon*(phaseRho r b)^2)+40970*(phaseRho r b)^2 := by unfold target; ring
    _≤36*(1728*r^b)+40970*r^b := add_le_add
      (mul_le_mul_of_nonneg_left hl (by norm_num))
      (mul_le_mul_of_nonneg_left hs (by norm_num))
    _≤_ := by nlinarith only [hp]

/-- The source stopping identity, rather than a reversed delta/radius
comparison, supplies the exact80 square-root bound used by the base envelope. -/
lemma actual_base_analytic_bound {r b epsilon base : ℝ}
    (hr : 0<r) (stop : ℕ) (hs : 6≤stop)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1)
    (hb : b≤1/8) (he0 : 0≤epsilon) (he : epsilon≤b/2)
    (hbase : base≤2*max ((5/4:ℝ)*
      ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))^(1-2*epsilon))
      ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))) :
    base/8≤25*r^((1/2:ℝ)-epsilon) := by
  let Rho : ℝ := 64/((2^(middleDepth stop):ℕ):ℝ)
  obtain ⟨hRho,hRho1,_hsq,_hlo,_hhi⟩:=middle_scale_bounds stop hs r hidentity
  have hroot : Rho≤80*r^(1/2:ℝ) := middle_scale_root_bound hr stop hs hidentity
  have hexp : 0≤1-2*epsilon := by linarith only [hb,he]
  have hpow := Real.rpow_le_rpow hRho.le hroot hexp
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤80) (Real.rpow_nonneg hr.le _),
    ←Real.rpow_mul hr.le] at hpow
  have h80 : (80:ℝ)^(1-2*epsilon)≤80 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ)≤80) (by linarith only [he0] : 1-2*epsilon≤1)
  have hp : Rho^(1-2*epsilon)≤80*r^((1/2:ℝ)-epsilon) := by
    apply hpow.trans
    rw [show (1/2:ℝ)*(1-2*epsilon)=(1/2:ℝ)-epsilon by ring]
    exact mul_le_mul_of_nonneg_right h80 (Real.rpow_nonneg hr.le _)
  have hlo : Rho≤Rho^(1-2*epsilon) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hRho hRho1
      (by linarith only [he0] : 1-2*epsilon≤1)
  have hRpow := Real.rpow_nonneg hRho.le (1-2*epsilon)
  have hmax : max ((5/4:ℝ)*Rho^(1-2*epsilon)) Rho=(5/4:ℝ)*Rho^(1-2*epsilon) :=
    max_eq_left (by nlinarith only [hlo,hRpow])
  change base≤2*max ((5/4:ℝ)*Rho^(1-2*epsilon)) Rho at hbase
  rw [hmax] at hbase
  nlinarith only [hbase,hp]

lemma analytic_le_phase_square {r b epsilon base : ℝ}
    (hr : 0<r) (hr1 : r≤1) (stop : ℕ) (hs : 6≤stop)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1)
    (_hb : 0<b) (hb8 : b≤1/8) (he0 : 0≤epsilon) (he : epsilon≤b/2)
    (hsmall : r^b≤1/25)
    (hbase : base≤2*max ((5/4:ℝ)*
      ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))^(1-2*epsilon))
      ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))) :
    base/8≤(phaseRho r b)^2 := by
  have hbnd:=actual_base_analytic_bound hr stop hs hidentity hb8 he0 he hbase
  have hexp : 3*b≤(1/2:ℝ)-epsilon := by linarith only [hb8,he]
  have hp:=Real.rpow_le_rpow_of_exponent_ge hr hr1 hexp
  have hid : (25*r^b)*(phaseRho r b)^2=25*r^(3*b) := by
    unfold phaseRho
    rw [←Real.rpow_mul_natCast hr.le, mul_assoc, ←Real.rpow_add hr]
    congr 1
    congr 1
    norm_num
    ring
  calc
    base/8≤25*r^((1/2:ℝ)-epsilon) := hbnd
    _≤25*r^(3*b) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _=(25*r^b)*(phaseRho r b)^2 := hid.symm
    _≤(phaseRho r b)^2 := mul_le_of_le_one_left (sq_nonneg _) (by linarith only [hsmall])

/-- Round the required FINAL physical width. The old source width is64
times this width, so the configured base and affine-error guard are preserved. -/
theorem exists_prepared_depth (u : ℕ) {required : ℝ} (ht : 0<required)
    (htop : required≤1/128) (hbase : (2:ℝ)⁻¹^u/64≤required) :
    ∃d : ℕ,6≤d ∧ d≤u+6 ∧ required≤1/((2^d:ℕ):ℝ) ∧
      1/((2^d:ℕ):ℝ)≤2*required ∧ (2:ℝ)⁻¹^u≤64/((2^d:ℕ):ℝ) := by
  obtain ⟨d,hd,hlo,hhi⟩:=exists_dyadic_angular_scale
    (show 0<(64:ℝ)*required by positivity) (show (64:ℝ)*required≤1 by linarith only [htop])
  have hlo' : required≤1/((2^d:ℕ):ℝ) := by nlinarith only [hlo]
  have hhi' : 1/((2^d:ℕ):ℝ)≤2*required := by nlinarith only [hhi]
  have hBase : (2:ℝ)⁻¹^u≤64/((2^d:ℕ):ℝ) := by nlinarith only [hbase,hlo]
  have hid : (2:ℝ)⁻¹^u=64/((2^(u+6):ℕ):ℝ) := by
    rw [Nat.cast_pow,Nat.cast_ofNat,pow_add,inv_pow]
    norm_num
    field_simp
  have hpow : ((2^d:ℕ):ℝ)≤((2^(u+6):ℕ):ℝ) := by
    rw [hid] at hBase
    have hh:=(div_le_div_iff₀ (by positivity : (0:ℝ)<((2^(u+6):ℕ):ℝ))
      (by positivity : (0:ℝ)<((2^d:ℕ):ℝ))).mp hBase
    linarith only [hh]
  have hdepth : d≤u+6 := (Nat.pow_le_pow_iff_right (by norm_num : 1<(2:ℕ))).mp
    (by exact_mod_cast hpow)
  exact ⟨d,hd,hdepth,hlo',hhi',hBase⟩

lemma physicalLip_ge_one {r epsilon : ℝ} (hr : 0<r) (hr1 : r≤1)
    (he : 0≤epsilon) : 1≤physicalLip r epsilon := by
  have hp : (1:ℝ)≤r^(-2*epsilon) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hr hr1
      (show -2*epsilon≤0 by linarith only [he])
  unfold physicalLip
  linarith only [hp]

/-- These are exactly the two physical meshes in the rounded phase-edge
theorem: tangent mesh=normalized mesh*rho, offset mesh=normalized mesh*Lip*rho. -/
lemma phase_mesh_readbacks (r b epsilon : ℝ) :
    tangentMesh r b=phaseMesh r b*phaseRho r b ∧
      offsetMesh r b epsilon=phaseMesh r b*physicalLip r epsilon*phaseRho r b := by
  constructor
  · unfold tangentMesh phaseMesh
    ring
  · unfold offsetMesh phaseMesh
    ring

lemma dyadic_width_le_offset_mesh {r b epsilon Delta : ℝ}
    (hr : 0<r) (hr1 : r≤1) (he : 0≤epsilon)
    (hDelta : Delta≤2*target r b epsilon) : Delta≤21*offsetMesh r b epsilon := by
  have hL:=physicalLip_ge_one hr hr1 he
  have hcoeff : 2*(36*physicalLip r epsilon+40970)≤21*(4099*physicalLip r epsilon) := by
    linarith only [hL]
  apply hDelta.trans
  calc
    2*target r b epsilon=(2*(36*physicalLip r epsilon+40970))*(phaseRho r b)^2 := by
      unfold target
      ring
    _≤(21*(4099*physicalLip r epsilon))*(phaseRho r b)^2 :=
      mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
    _=21*offsetMesh r b epsilon := by unfold offsetMesh; ring

/-- The native2064 offset-coherence constant gives a fixed phase population
factor, with the genuine offset-bin width retained in the denominator. -/
lemma offset_population_factor {Delta tau : ℝ} (hD : 0≤Delta) (ht : 0<tau)
    (hDt : Delta≤21*tau) :
    27*(2*(2064:ℝ)*Delta/tau+2)^2≤27*(86690:ℝ)^2 := by
  have hratio : Delta/tau≤21 := (div_le_iff₀ ht).mpr hDt
  have hupper : 2*(2064:ℝ)*Delta/tau+2≤86690 := by nlinarith only [hratio]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hupper 2) (by norm_num)

/-- A pre-source cutoff produces the actual analytic scale and prepared
coherence depth from the source's base envelope and stopping identity.
There is no extra physical-window or affine-error budget premise. -/
theorem exists_source_window_cutoff (amin b rhoBound : ℝ)
    (ha : 0<amin) (hb : 0<b) (hb8 : b≤1/8) (hBound : 0<rhoBound) :
    ∃delta0 : ℝ,0<delta0 ∧ delta0≤1 ∧
      ∀delta r power : ℝ,0<delta → delta≤delta0 → 0<r → amin≤power → r≤delta^power →
      ∀epsilon : ℝ,0≤epsilon → epsilon≤b/2 →
      ∀stop u : ℕ,6≤stop → 48*((2^stop:ℕ):ℝ)*r=1 →
      (2:ℝ)⁻¹^u≤2*max ((5/4:ℝ)*
        ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))^(1-2*epsilon))
        ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ)) →
      0<phaseRho r b ∧ phaseRho r b≤rhoBound ∧
      (2:ℝ)⁻¹^u/8≤(phaseRho r b)^2 ∧
      ∃d : ℕ,6≤d ∧ d≤u+6 ∧
        tangentMesh r b≤1/((2^d:ℕ):ℝ) ∧
        4*grainWidth r b epsilon+tangentMesh r b≤1/((2^d:ℕ):ℝ) ∧
        1/((2^d:ℕ):ℝ)≤2*target r b epsilon ∧
        (2:ℝ)⁻¹^u≤64/((2^d:ℕ):ℝ) := by
  obtain ⟨delta0,hd0,hd01,H⟩:=exists_small_power_cutoff
    (mul_pos ha hb) (lt_min (show (0:ℝ)<1/(128*104000) by norm_num) hBound)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta r power hd hsmall hr hpower hrdelta epsilon he0 he stop u hs hidentity hbase
  have hd1:=hsmall.trans hd01
  have hr1 : r≤1 := hrdelta.trans (Real.rpow_le_one hd.le hd1 (ha.le.trans hpower))
  have hrpow : r^b≤delta^(amin*b) := by
    calc
      r^b≤(delta^power)^b := Real.rpow_le_rpow hr.le hrdelta hb.le
      _=delta^(power*b) := (Real.rpow_mul hd.le power b).symm
      _≤delta^(amin*b) := Real.rpow_le_rpow_of_exponent_ge hd hd1
        (mul_le_mul_of_nonneg_right hpower hb.le)
  have hbudget:=hrpow.trans (H delta hd hsmall)
  have htiny : r^b≤1/(128*104000) := hbudget.trans (min_le_left _ _)
  have hrho : 0<phaseRho r b := Real.rpow_pos_of_pos hr _
  have hanalytic:=analytic_le_phase_square hr hr1 stop hs hidentity hb hb8 he0 he
    (htiny.trans (by norm_num : (1:ℝ)/(128*104000)≤1/25)) hbase
  have htargetPos : 0<target r b epsilon := by unfold target physicalLip phaseRho; positivity
  have htargetSmall : target r b epsilon≤1/128 := by
    have hh:=target_power hr hr1 hb he
    nlinarith only [hh,htiny]
  have hbaseTarget : (2:ℝ)⁻¹^u/64≤target r b epsilon := by
    have hlip : 0≤physicalLip r epsilon := by unfold physicalLip; positivity
    have hsq : 0≤(phaseRho r b)^2 := sq_nonneg _
    have htarget : (phaseRho r b)^2≤target r b epsilon := by unfold target; nlinarith only [hlip,hsq]
    have hBasePos : 0≤(2:ℝ)⁻¹^u := by positivity
    exact (show (2:ℝ)⁻¹^u/64≤(2:ℝ)⁻¹^u/8 by linarith only [hBasePos]).trans
      (hanalytic.trans htarget)
  obtain ⟨d,hd6,hdu,hlo,hhi,hguard⟩:=exists_prepared_depth u htargetPos htargetSmall hbaseTarget
  refine ⟨hrho,hbudget.trans (min_le_right _ _),hanalytic,d,hd6,hdu,?_,?_,hhi,hguard⟩
  · apply le_trans _ hlo
    have hlip : 0≤physicalLip r epsilon := by unfold physicalLip; positivity
    have hsq : 0≤(phaseRho r b)^2 := sq_nonneg _
    unfold tangentMesh target
    nlinarith only [hlip,hsq]
  · apply le_trans _ hlo
    have hsq : 0≤(phaseRho r b)^2 := sq_nonneg _
    unfold grainWidth tangentMesh target
    nlinarith only [hsq]

end NativePhaseWindowScaleBudget
