/- UNVERIFIED source draft. No strict Lean check has run on this file. -/
import Theorems.Thm_StickyKakeya4_native_common_Y_total_budget
import Theorems.Thm_StickyKakeya4_native_rank_exponent_hierarchy

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeYTotalEpsilonBudget
open NativeCommonYTotalBudget NativeQuarterScaleParameters NativeOutputAlignmentMenuBudget

/-- Keep the baseline power at eps. Using eps<=r^window converts only the
independent raw third allowance, not eB, to this scale. -/
lemma radix_cost_at_epsilon {r eps window c3 : ℝ} (Q3 : ℕ)
    (hr : 0 < r) (heps : 0 < eps) (hw : 0 < window) (hc3 : 0 ≤ c3)
    (hwindow : eps ≤ r^window) (hQ : (Q3:ℝ)^4 ≤ r^(-(2*c3))) :
    (Q3:ℝ)^4 ≤ eps^(-(2*c3/window)) := by
  have hh := Real.rpow_le_rpow_of_nonpos heps hwindow
    (show -(2*c3/window) ≤ 0 by positivity)
  have he : (r^window)^(-(2*c3/window))=r^(-(2*c3)) := by
    rw [←Real.rpow_mul hr.le]
    congr 1
    field_simp [hw.ne']
  rw [he] at hh
  exact hQ.trans hh

/-- All constants and the actual polynomial common-scale menu are paid
at eps, before the native source. No rank window is spent on eB. -/
theorem exists_epsilon_cutoff (E zeta53 chi menuTax : ℝ)
    (hE : 0 < E) (hchi : 0 < chi) (hmenuTax : 0 < menuTax) (bins : ℕ) :
    ∃eps0 : ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧
      ∀eps : ℝ,0 < eps → eps ≤ eps0 →
        32768*eps^(chi/2) ≤ 1 ∧
        ((5:ℝ)^4*(32768:ℝ)^zeta53/16)*eps^((chi/2)*(E/8192)) ≤ 1 ∧
        ∀u : ℕ,eps=(2:ℝ)⁻¹^(u+6) →
          2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ) ≤ eps^(-menuTax) := by
  let B : ℝ := (5:ℝ)^4*(32768:ℝ)^zeta53/16
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨dm,hdm,hdm1,Hmenu⟩ := exists_menu_cutoff menuTax hmenuTax bins
  obtain ⟨dg,hdg,_hdg1,Hgap⟩ := exists_small_power_cutoff
    (show 0 < chi/2 by positivity) (by norm_num : (0:ℝ)<1/32768)
  obtain ⟨dc,hdc,_hdc1,Hconstant⟩ := exists_small_power_cutoff
    (show 0 < (chi/2)*(E/8192) by positivity) (div_pos (by norm_num : (0:ℝ)<1) hB)
  refine ⟨min dm (min dg dc),lt_min hdm (lt_min hdg hdc),(min_le_left _ _).trans hdm1,?_⟩
  intro eps heps hsmall
  have hg := Hgap eps heps (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc := Hconstant eps heps (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨by linarith only [hg],?_,?_⟩
  · have hh := (le_div_iff₀ hB).mp hc
    simpa only [mul_comm] using hh
  · intro u heq
    subst eps
    exact Hmenu u (hsmall.trans (min_le_left _ _))

/-- The actual common graph lower pays htotal using only eps exponents.
This removes the artificial requirement eB << c^3 that would result from
first weakening eps^(5eB/16) to r^(5eB/16). -/
theorem pay_actual_graph_mass_at_epsilon
    {eps sigma E zeta53 eB c3 window menuTax N total : ℝ}
    (Q3 : ℕ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hs : 0 < sigma) (hE : 0 < E) (hzeta : zeta53 ≤ E/16384)
    (heB : 0 ≤ eB) (hchi : ℝ) (hchiPos : 0 < hchi)
    (htax : 5*eB/16+2*c3/window+menuTax ≤ (hchi/2)*(E/16384))
    (hMenu : N ≤ eps^(-menuTax)) (hQ : (Q3:ℝ)^4 ≤ eps^(-(2*c3/window)))
    (hSigma : sigma ≤ eps^(hchi/2))
    (hfixed : ((5:ℝ)^4*(32768:ℝ)^zeta53/16)*eps^((hchi/2)*(E/8192)) ≤ 1)
    (htotal : 0 ≤ total)
    (Hsource : (16/(5:ℝ)^4)*(sigma/32768)^zeta53*eps^(5*eB/16) ≤
      N*(Q3:ℝ)^4*eps^4*total) :
    sigma^(E/4096) ≤ eps^4*total := by
  have htax' : 5*eB/16+2*(c3/window)+menuTax ≤ (hchi/2)*(E/16384) := by
    convert htax using 1 <;> ring
  have hQ' : (Q3:ℝ)^4 ≤ eps^(-(2*(c3/window))) := by
    convert hQ using 1 <;> ring
  exact pay_actual_graph_mass Q3 heps heps1 le_rfl hs hE hzeta heB
    (by positivity : 0 < hchi/2) htax' hMenu hQ' hSigma hfixed htotal Hsource

/-- For the actual hierarchy, the only divided third tax is independent
of c. The baseline window here is the conservative amin/8=c^3/64. -/
lemma actual_third_tax (eta0 c : ℝ) (hc : 0 < c) :
    2*(NativeRankExponentHierarchy.commonBudget eta0 c/4)/(c^3/64)=4*eta0 := by
  unfold NativeRankExponentHierarchy.commonBudget
  field_simp [hc.ne']
  ring

end NativeYTotalEpsilonBudget
