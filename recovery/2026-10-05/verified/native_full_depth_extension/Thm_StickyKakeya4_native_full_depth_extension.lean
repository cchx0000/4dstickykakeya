import Theorems.Thm_StickyKakeya4_native_endpoint_power_budgets
import Theorems.Thm_StickyKakeya4_native_boundary_depths
import Theorems.Thm_StickyKakeya4_native_coarse_upper_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeFullDepthExtension
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentDensityCore NativeLocalMenuInterpolation
open NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance NativeBoundaryDepths
open NativeEndpointParentBounds NativeEndpointPowerBudgets NativeScaleMenuSuccessor NativeNearTargetLoss

lemma upper_with_loss {delta rho exponent target kappa M : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hr : 0 < rho) (hmargin : exponent ≤ target)
    (H : M ≤ delta^(-exponent)*rho^(-kappa)) : M ≤ delta^(-target)*rho^(-kappa) := by
  exact H.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)) (Real.rpow_pos_of_pos hr _).le)

lemma weaken_scale {n : ℕ} {D : FiniteScaleSource n} {eta a b target : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (level m : ℕ) (hbt : b ≤ target)
    (H : HasMiddleScale h R E a level m b) : HasMiddleScale h R E a level m target := by
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hr : (0:ℝ) < 64/((2^m:ℕ):ℝ) := by positivity
  refine ⟨lower_with_target_loss hd hd1 hr hbt H.1,
    upper_with_loss hd hd1 hr hbt H.2.1,?_⟩
  intro p hp
  exact ⟨lower_with_target_loss hd hd1 (localScale_pos hd m) hbt (H.2.2 p hp).1,
    upper_with_loss hd hd1 (localScale_pos hd m) hbt (H.2.2 p hp).2⟩

lemma dyadic_ratio_one_le (gap : ℕ) : (1:ℝ) ≤ ((2^gap:ℕ):ℝ) := by
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using (one_le_pow₀ (by norm_num : (1:ℝ)≤2) : (1:ℝ)≤(2:ℝ)^gap)

lemma coarse_thickness_ratio (c m : ℕ) (hcm : c ≤ m) :
    64/((2^c:ℕ):ℝ)=((2^(m-c):ℕ):ℝ)*(64/((2^m:ℕ):ℝ)) := by
  have hh := NativeCoarseScaleInterpolation.coarse_mesh_ratio c m hcm
  calc
    _ = 2*(32/((2^c:ℕ):ℝ)) := by ring
    _ = 2*(((2^(m-c):ℕ):ℝ)*(32/((2^m:ℕ):ℝ))) := by rw [hh]
    _ = _ := by ring

/-- The middle configuration extends to EVERY original dyadic depth on
the same R and E. All boundary losses come from proved finite geometry and
nonempty incidence counts; no additional refinement or shading law is used. -/
theorem full_from_middle {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (hR : ∀z∈E,z.1∈R) (hne : E.Nonempty) (level : ℕ)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (v b target : ℝ)
    (hv : 0 < v) (hvquarter : v ≤ 1/4) (hb : 0 ≤ b)
    (hlarge : 4 ≤ v*(level:ℝ)) (hbudget : 2*b+20*v ≤ target)
    (hconstant : (64:ℝ)^3 ≤ D.thickness^(-b))
    (HM : ∀ m : ℕ,v*(level:ℝ) ≤ m → (m:ℝ) ≤ (1-v)*(level:ℝ) →
      HasMiddleScale h R E a level m b) :
    ∀ m : ℕ,m ≤ level → HasMiddleScale h R E a level m target := by
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have h729 : (729:ℝ) ≤ D.thickness^(-b) := (by norm_num : (729:ℝ)≤(64:ℝ)^3).trans hconstant
  obtain ⟨hlu,huL,hlWindow,huWindow,_hlgap,_hugap⟩ := anchor_bounds v hv hvquarter level hlarge
  let l := lowerAnchor v level
  let u := upperAnchor v level
  have hlL : l ≤ level := hlu.trans huL
  have HL := HM l hlWindow.1 hlWindow.2
  have HU := HM u huWindow.1 huWindow.2
  have hk : (2*v)*extremalExponent ≤ 6*v := by
    have hh := mul_le_mul_of_nonneg_left extremalExponent_le_three (show 0≤2*v by positivity)
    nlinarith only [hh]
  have hmarginC : 2*b+(2*v)*(4+extremalExponent) ≤ target := by nlinarith only [hbudget,hk,hv]
  have hmarginLow : b+(2*v)*extremalExponent ≤ target := by nlinarith only [hbudget,hk,hv,hb]
  have hmarginSix : b+6*(2*v) ≤ target := by nlinarith only [hbudget,hv,hb]
  have hmarginFine : b+3*(2*v) ≤ target := by nlinarith only [hbudget,hv,hb]
  have hmarginInitial : 3*(2*v) ≤ target := by nlinarith only [hbudget,hv,hb]
  have hbt : b ≤ target := by nlinarith only [hbudget,hv,hb]
  intro m hm
  have hrm : (0:ℝ) < 64/((2^m:ℕ):ℝ) := by positivity
  by_cases hlow : m < l
  · have hml : m ≤ l := hlow.le
    have hgap := lower_gap v hv hvquarter level m hlarge
    have hratio := NativeLocalMenuInterpolation.dyadic_gap_power hdy hgap
    have htransfer := NativeCoarseScaleInterpolation.full_source_multiplicity_le
      h original horiginal ha R E hE hR level m l hdy hml hlL
    have hupper := NativeCoarseUpperInterpolation.forward_upper hd
      (by positivity : (0:ℝ) < 64/((2^l:ℕ):ℝ)) (dyadic_ratio_one_le (l-m))
      (coarse_thickness_ratio m l hml) hratio (by norm_num : (0:ℝ)≤729) h729
      extremalExponent_nonneg htransfer HL.2.1
    refine ⟨initial_coarse_lower h R E hR hne a level m hdy (2*v) target
      (initial_gap v hv hvquarter level m hlarge hml) hmarginInitial,
      upper_with_loss hd hd1 hrm hmarginC hupper,?_⟩
    intro p hp
    have hlower := off_menu_parent_power_lower D hd a E level hdy hml (2*v) b
      extremalExponent hgap extremalExponent_nonneg (fun q hq => (HL.2.2 q hq).1) p hp
    have hupperOld := old_parent_power_upper_from_children D hd a E level hdy hml
      (2*v) b extremalExponent hgap extremalExponent_nonneg (fun q hq => (HL.2.2 q hq).2) p
    exact ⟨lower_with_target_loss hd hd1 (localScale_pos hd m) hmarginLow hlower,
      upper_with_loss hd hd1 (localScale_pos hd m) hmarginSix hupperOld⟩
  · by_cases hhigh : u < m
    · have hum : u ≤ m := hhigh.le
      have hgap := upper_gap v hv hvquarter level m hlarge hm
      have hratio := NativeLocalMenuInterpolation.dyadic_gap_power hdy hgap
      have hforward := NativeCoarseScaleInterpolation.full_source_multiplicity_le
        h original horiginal ha R E hE hR level u m hdy hum hm
      have hreverse := NativeCoarseScaleReverse.full_source_multiplicity_le
        h original horiginal ha R E hE hR level u m hdy hum hm
      have hscale := coarse_thickness_ratio u m hum
      have hlower := NativeCoarsePowerInterpolation.middle_lower_of_forward_bound hd hrm
        (by positivity : (0:ℝ)<((2^(m-u):ℕ):ℝ)) extremalExponent_nonneg
        hscale hratio h729 HU.1 hforward ENNReal.toReal_nonneg
      have hupper := NativeCoarseUpperInterpolation.reverse_upper hd hrm (dyadic_ratio_one_le (m-u))
        hscale hratio (by norm_num : (0:ℝ)≤729) h729 extremalExponent_nonneg hreverse HU.2.1
      refine ⟨lower_with_target_loss hd hd1 hrm hmarginC hlower,
        upper_with_loss hd hd1 hrm (by nlinarith only [hbudget]) hupper,?_⟩
      intro p hp
      exact terminal_old_parent_bounds h R E hR a level m hdy hm (2*v) b target
        (remaining_gap v hv hvquarter level m hlarge hum) hconstant hmarginFine p hp
    · have hlm : l ≤ m := by omega
      have hmu : m ≤ u := by omega
      have hmlower : v*(level:ℝ) ≤ m := hlWindow.1.trans (by exact_mod_cast hlm)
      have hmupper : (m:ℝ) ≤ (1-v)*(level:ℝ) := (show (m:ℝ)≤u by exact_mod_cast hmu).trans huWindow.2
      exact weaken_scale h R E level m hbt (HM m hmlower hmupper)

end NativeFullDepthExtension
