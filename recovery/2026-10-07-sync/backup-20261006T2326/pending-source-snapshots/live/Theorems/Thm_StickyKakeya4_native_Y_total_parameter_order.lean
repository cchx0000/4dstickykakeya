/- UNVERIFIED source draft. No strict Lean check has run on this file. -/
import Theorems.Thm_StickyKakeya4_native_common_Y_total_budget

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace NativeYTotalParameterOrder

/-- The planar retention loss is chosen before the planar gap exponent,
the baseline window, or any native source. -/
theorem exists_planar_loss (E : ℝ) (hE : 0 < E) :
    ∃zeta53 : ℝ,0 < zeta53 ∧ zeta53 ≤ E/16384 := by
  refine ⟨E/32768,by positivity,?_⟩
  linarith only [hE]

/-- Once the actual planar gap chi and baseline window have been chosen,
all three additional taxes can be selected below arbitrary positive source
ceilings. Thus the source budget introduces no circular exponent order. -/
theorem exists_source_taxes (E chi window eCeiling cCeiling menuCeiling : ℝ)
    (hE : 0 < E) (hchi : 0 < chi) (hw : 0 < window)
    (he : 0 < eCeiling) (hc : 0 < cCeiling) (hm : 0 < menuCeiling) :
    ∃eB c3 menuTax : ℝ,
      0 < eB ∧ eB ≤ eCeiling ∧ 0 < c3 ∧ c3 ≤ cCeiling ∧
      0 < menuTax ∧ menuTax ≤ menuCeiling ∧
      5*eB/16+2*c3+menuTax ≤ (window*chi/2)*(E/16384) := by
  let A : ℝ := (window*chi/2)*(E/16384)
  let budget : ℝ := min A (min (4*eCeiling) (min (8*cCeiling) (4*menuCeiling)))
  have hA : 0 < A := by dsimp [A]; positivity
  have hbudget : 0 < budget := by dsimp [budget]; positivity
  have hbA : budget ≤ A := min_le_left _ _
  have hbe : budget ≤ 4*eCeiling :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hbc : budget ≤ 8*cCeiling :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbm : budget ≤ 4*menuCeiling :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨budget/4,budget/8,budget/4,by positivity,?_,by positivity,?_,by positivity,?_,?_⟩
  · linarith only [hbe]
  · linarith only [hbc]
  · linarith only [hbm]
  · change 5*(budget/4)/16+2*(budget/8)+budget/4 ≤ A
    linarith only [hbA,hbudget]

end NativeYTotalParameterOrder
