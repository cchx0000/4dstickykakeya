import Theorems.Thm_StickyKakeya4_native_same_source_multiplicity_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

noncomputable section
namespace NativeSameSourceBalanceAbsorption
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection
open NativeIncidenceMultiplicityTower NativeSameSourceMultiplicityBalance NativeLocalAdmissionBudget
open scoped BigOperators ENNReal

/-- The actual source cardinal bound pays the entire F-squared/radix-six
balance cost before D or the selected incidence set is chosen. -/
theorem exists_balance_cutoff {zeta : ℝ} (hz : 0<zeta) (F L : ℕ) (hL : 0<L)
    (hlarge : 16/zeta < (L:ℝ)) :
    ∃delta0 : ℝ,0<delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
      (_h : IsWangZakharovNativeFiniteInput D eta), D.thickness ≤ delta0 →
      ∀ original : Fin n → Finset Index,
        (∀i,D.shading i=wzCellShading (mesh D) original i) →
        ∀ A : Finset (Fin n × Index),A⊆incidences original → A.Nonempty →
          balanceCost*(F:ℝ)^2*(NativeSourceSizeBounds.radix A.card L:ℝ)^6 ≤
            D.thickness^(-(2*zeta)) := by
  have hLp : (0:ℝ)<L := by exact_mod_cast hL
  let C := balanceCost*(F:ℝ)^2*(16*incidenceConstant^(2/(L:ℝ)))^3
  have hC : 0≤C := by
    have hp := incidenceConstant_pos
    dsimp [C,balanceCost,localCost]
    positivity
  obtain ⟨delta0,hd0,hd01,habsorb⟩ := exists_positive_rpow_absorption_threshold
    (half_pos hz) hC (by norm_num : (0:ℝ)<1)
  refine ⟨delta0,hd0,?_⟩
  intro n D eta h hsmall original horiginal A hA hAne
  have hd := h.1.2.1
  have hd1 := hsmall.trans hd01
  have hradix := retained_radix_sq_upper h original horiginal A hA hAne L hL
  have hradix6 : (NativeSourceSizeBounds.radix A.card L:ℝ)^6 ≤
      (16*incidenceConstant^(2/(L:ℝ)))^3*D.thickness^(-24/(L:ℝ)) := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(NativeSourceSizeBounds.radix A.card L:ℝ)^2) hradix 3
    rw [←pow_mul,mul_pow,←Real.rpow_mul_natCast hd.le] at hh
    norm_num only [Nat.cast_ofNat] at hh
    simpa only [show (2:ℕ)*3=6 by norm_num,show (-8/(L:ℝ))*3 = -24/(L:ℝ) by ring] using hh
  have hExp : 24/(L:ℝ) ≤ 3*zeta/2 := by
    have hh := (div_lt_iff₀ hz).mp hlarge
    apply (div_le_iff₀ hLp).mpr
    nlinarith
  have hpay := pay_power hd hd1 (habsorb D.thickness hd hsmall)
    (show -(2*zeta)+zeta/2 ≤ -24/(L:ℝ) by rw [neg_div]; linarith)
  exact (mul_le_mul_of_nonneg_left hradix6
    (show 0≤balanceCost*(F:ℝ)^2 by dsimp [balanceCost,localCost]; positivity)).trans
    (by simpa only [C,mul_assoc] using hpay)

/-- Absorb an explicit source-derived balance coefficient into its stated
original-delta exponent; no smallness assertion is made about an output. -/
lemma absorb_balance_cost {delta power loss X C M : ℝ}
    (hd : 0<delta) (hM : 0≤M)
    (hbound : delta^power*X ≤ C*M) (hcost : C ≤ delta^(-loss)) :
    delta^(power+loss)*X ≤ M := by
  have hh : delta^power*X ≤ (1:ℝ)*delta^(-loss)*M := by
    simpa only [one_mul] using hbound.trans (mul_le_mul_of_nonneg_right hcost hM)
  simpa only [one_mul] using move_density_loss hd hh

/-- The physical local source of the parent picked by the exact tower also
has the complementary near lower bound, with the true geometric transfer cost. -/
theorem exists_actual_parent_near_lower {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (E : Finset (T × X)) (f : T → P) (hne : E.Nonempty)
    {delta rho eps kappa theta gamma eta loss C : ℝ}
    (hd : 0<delta) (hr : 0<rho) (he : 0<eps) (hscale : rho*eps=delta)
    (F rad : ℕ) (S : P → ℝ)
    (hnear : delta^(-kappa+theta) ≤ (F:ℝ)*multiplicity E)
    (hphysical : multiplicity (coarse E f) ≤ 125*(rad:ℝ)^4*C)
    (hupper : C ≤ delta^(-gamma)*rho^(-kappa-loss))
    (htransfer : ∀p∈E.image (fun z => f z.1),multiplicity (parent E f p) ≤
      localCost*(F:ℝ)*(rad:ℝ)^2*delta^(-eta)*S p) :
    ∃p∈E.image (fun z => f z.1),(parent E f p).Nonempty ∧
      delta^(theta+gamma+eta)*rho^loss*eps^(-kappa) ≤
        balanceCost*(F:ℝ)^2*(rad:ℝ)^6*S p := by
  obtain ⟨p,hp,hpne,hlo⟩ := exists_parent_near_lower E f hne hd hr he hscale F rad hnear hphysical hupper
  refine ⟨p,hp,hpne,?_⟩
  have hh : delta^(theta+gamma)*(rho^loss*eps^(-kappa)) ≤
      (balanceCost*(F:ℝ)^2*(rad:ℝ)^6)*delta^(-eta)*S p := by
    have hc := hlo.trans (mul_le_mul_of_nonneg_left (htransfer p hp)
      (show (0:ℝ)≤125*(F:ℝ)*(rad:ℝ)^4 by positivity))
    calc
      _ = delta^(theta+gamma)*rho^loss*eps^(-kappa) := by ring
      _ ≤ _ := hc
      _ = _ := by dsimp [balanceCost]; ring
  simpa only [mul_assoc] using move_density_loss hd hh

end NativeSameSourceBalanceAbsorption
