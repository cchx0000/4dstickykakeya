import Theorems.Thm_StickyKakeya4_original_weighted_line_color_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace OriginalThickeningColorBudget

def thickeningModulus (rho w : ℝ) : ℕ := ⌈36*w/rho⌉₊+2

/-- Explicit finite residue modulus for any requested coarse thickening.
The number of colors is at most 4(37w/rho)^3, before any small-scale
absorption. The source weight loss therefore stays quantitative. -/
theorem original_thickening_color_budget (rho w : ℝ)
    (hrho : 0<rho) (hwidth : 3*rho≤w) :
    0<thickeningModulus rho w ∧
    36*w<((thickeningModulus rho w:ℝ)-1)*rho ∧
    (thickeningModulus rho w:ℝ)≤37*w/rho := by
  have hw : 0≤w := by linarith only [hrho,hwidth]
  have hc := Nat.le_ceil (36*w/rho)
  have hu := Nat.ceil_lt_add_one (show 0≤36*w/rho by positivity)
  have hratio : 3≤w/rho := (le_div_iff₀ hrho).mpr hwidth
  have hmul := (div_le_iff₀ hrho).mp hc
  have he : (thickeningModulus rho w:ℝ)=(⌈36*w/rho⌉₊:ℝ)+2 := by
    simp only [thickeningModulus,Nat.cast_add,Nat.cast_ofNat]
  refine ⟨by unfold thickeningModulus; omega,?_,?_⟩
  · rw [he]
    nlinarith only [hmul,hrho]
  · rw [he]
    have he' : 37*w/rho=36*w/rho+w/rho := by ring
    rw [he']
    linarith only [hu,hratio]

end OriginalThickeningColorBudget
