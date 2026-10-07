import Theorems.Thm_StickyKakeya4_native_parent_average_uniformity
import Theorems.Thm_StickyKakeya4_native_same_source_balance_absorption

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

noncomputable section
namespace NativeAllParentNearBalance
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeIncidenceMultiplicityTower NativeSameSourceMultiplicityBalance
open NativeSameSourceBalanceAbsorption NativeLocalAdmissionBudget
open scoped BigOperators ENNReal

/-- Formal parent-point uniformity promotes the tower witness to EVERY active
parent, without another incidence selection. Each physical local source pays
one extra radix-square factor through the actual parent/source comparison. -/
theorem all_actual_parent_near_lower {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (E : Finset (T × X)) (f : T → P) (hne : E.Nonempty)
    {delta rho eps kappa theta gamma eta loss C : ℝ}
    (hd : 0<delta) (hr : 0<rho) (he : 0<eps) (hscale : rho*eps=delta)
    (F rad : ℕ) (S : P → ℝ)
    (hnear : delta^(-kappa+theta) ≤ (F:ℝ)*multiplicity E)
    (hphysical : multiplicity (coarse E f) ≤ 125*(rad:ℝ)^4*C)
    (hupper : C ≤ delta^(-gamma)*rho^(-kappa-loss))
    (hformal : ∀x∈E,∀y∈E,
      (E.filter (fun z => (f z.1,z.2)=(f x.1,x.2))).card ≤
        rad^2*(E.filter (fun z => (f z.1,z.2)=(f y.1,y.2))).card)
    (htransfer : ∀p,(parent E f p).Nonempty → multiplicity (parent E f p) ≤
      localCost*(F:ℝ)*(rad:ℝ)^2*delta^(-eta)*S p)
    (q : P) (hq : (parent E f q).Nonempty) :
    delta^(theta+gamma+eta)*rho^loss*eps^(-kappa) ≤
      balanceCost*(F:ℝ)^2*(rad:ℝ)^8*S q := by
  obtain ⟨p,_hp,hpne,hlo⟩ := exists_parent_near_lower E f hne hd hr he hscale F rad hnear hphysical hupper
  have hcomp := NativeParentAverageUniformity.parent_multiplicity_le E f rad hformal p hpne q hq
  have hc := hlo.trans (mul_le_mul_of_nonneg_left
    (hcomp.trans (mul_le_mul_of_nonneg_left (htransfer q hq) (by positivity)))
      (show (0:ℝ)≤125*(F:ℝ)*(rad:ℝ)^4 by positivity))
  have hh : delta^(theta+gamma)*(rho^loss*eps^(-kappa)) ≤
      (balanceCost*(F:ℝ)^2*(rad:ℝ)^8)*delta^(-eta)*S q := by
    calc
      _ = delta^(theta+gamma)*rho^loss*eps^(-kappa) := by ring
      _ ≤ _ := hc
      _ = _ := by dsimp [balanceCost]; ring
  simpa only [mul_assoc] using move_density_loss hd hh

/-- The complete all-parent coefficient is bounded from original native
source geometry and the same radix chosen before incidence uniformization. -/
theorem exists_all_parent_balance_cutoff {zeta : ℝ} (hz : 0<zeta) (F L : ℕ) (hL : 0<L)
    (hlarge : 16/zeta < (L:ℝ)) :
    ∃delta0 : ℝ,0<delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
      (_h : IsWangZakharovNativeFiniteInput D eta), D.thickness ≤ delta0 →
      ∀ original : Fin n → Finset Index,
        (∀i,D.shading i=wzCellShading (mesh D) original i) →
        ∀ A : Finset (Fin n × Index),A⊆incidences original → A.Nonempty →
          balanceCost*(F:ℝ)^2*(NativeSourceSizeBounds.radix A.card L:ℝ)^8 ≤
            D.thickness^(-(3*zeta)) := by
  have hLp : (0:ℝ)<L := by exact_mod_cast hL
  let C := balanceCost*(F:ℝ)^2*(16*incidenceConstant^(2/(L:ℝ)))^4
  have hC : 0≤C := by
    have hp := incidenceConstant_pos
    dsimp [C,balanceCost,localCost]
    positivity
  obtain ⟨delta0,hd0,hd01,habsorb⟩ := exists_positive_rpow_absorption_threshold
    hz hC (by norm_num : (0:ℝ)<1)
  refine ⟨delta0,hd0,?_⟩
  intro n D eta h hsmall original horiginal A hA hAne
  have hd := h.1.2.1
  have hd1 := hsmall.trans hd01
  have hradix := retained_radix_sq_upper h original horiginal A hA hAne L hL
  have hradix8 : (NativeSourceSizeBounds.radix A.card L:ℝ)^8 ≤
      (16*incidenceConstant^(2/(L:ℝ)))^4*D.thickness^(-32/(L:ℝ)) := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(NativeSourceSizeBounds.radix A.card L:ℝ)^2) hradix 4
    rw [←pow_mul,mul_pow,←Real.rpow_mul_natCast hd.le] at hh
    norm_num only [Nat.cast_ofNat] at hh
    simpa only [show (2:ℕ)*4=8 by norm_num,show (-8/(L:ℝ))*4 = -32/(L:ℝ) by ring] using hh
  have hExp : 32/(L:ℝ) ≤ 2*zeta := by
    have hh := (div_lt_iff₀ hz).mp hlarge
    apply (div_le_iff₀ hLp).mpr
    nlinarith
  have hpay := pay_power hd hd1 (habsorb D.thickness hd hsmall)
    (show -(3*zeta)+zeta ≤ -32/(L:ℝ) by rw [neg_div]; linarith)
  exact (mul_le_mul_of_nonneg_left hradix8
    (show 0≤balanceCost*(F:ℝ)^2 by dsimp [balanceCost,localCost]; positivity)).trans
    (by simpa only [C,mul_assoc] using hpay)

end NativeAllParentNearBalance
