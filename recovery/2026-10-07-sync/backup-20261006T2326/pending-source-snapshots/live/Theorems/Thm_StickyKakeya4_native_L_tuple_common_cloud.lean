import Theorems.Thm_StickyKakeya4_native_V_L_contact_identity

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace NativeLTupleCommonCloud
open NativeVLContactIdentity
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The source condition in Lemma20.1 bounds both actual first directions;
linearity gives the bound for their genuine difference. -/
theorem difference_action_bound (f g : X →L[ℝ] Y) (a₁ a₂ : X) (v : ℝ)
    (h₁ : ‖(f-g) a₁‖ ≤ v) (h₂ : ‖(f-g) a₂‖ ≤ v) :
    ‖(f-g) (a₁-a₂)‖ ≤ 2*v := by
  rw [map_sub]
  exact (norm_sub_le _ _).trans (by linarith)

/-- Two genuine arms with the same root and same intermediate height have
close intermediate quotient coordinates, before moving within their grains. -/
theorem quotient_cloud (f g : X →L[ℝ] Y) (x x₁ x₂ a₁ a₂ : X)
    (y y₁ y₂ xi : Y) (t dx dy rho v : ℝ)
    (ht : |t| ≤ rho)
    (hx₁ : ‖x₁-x-t • a₁‖ ≤ dx) (hx₂ : ‖x₂-x-t • a₂‖ ≤ dx)
    (hy₁ : ‖y₁+g x₁-(y+f x)-t • (xi+f a₁)‖ ≤ dy)
    (hy₂ : ‖y₂+g x₂-(y+f x)-t • (xi+f a₂)‖ ≤ dy)
    (hv₁ : ‖(f-g) a₁‖ ≤ v) (hv₂ : ‖(f-g) a₂‖ ≤ v) :
    ‖y₁-y₂‖ ≤ 2*rho*v+2*dy+2*‖g‖*dx := by
  have hv : 0 ≤ v := (norm_nonneg _).trans hv₁
  have hlin := difference_action_bound f g a₁ a₂ v hv₁ hv₂
  have hterm : ‖t • ((f-g) (a₁-a₂))‖ ≤ rho*(2*v) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul ht hlin (norm_nonneg _) ((abs_nonneg t).trans ht)
  have hres := v_residual f g x x₁ x₂ a₁ a₂ y y₁ y₂ xi t dx dy hx₁ hx₂ hy₁ hy₂
  have he : y₁-y₂=(y₁-y₂-t • ((f-g) (a₁-a₂)))+t • ((f-g) (a₁-a₂)) := by abel
  calc
    ‖y₁-y₂‖ = ‖(y₁-y₂-t • ((f-g) (a₁-a₂)))+t • ((f-g) (a₁-a₂))‖ := congrArg norm he
    _ ≤ ‖y₁-y₂-t • ((f-g) (a₁-a₂))‖+‖t • ((f-g) (a₁-a₂))‖ := norm_add_le _ _
    _ ≤ (2*dy+2*‖g‖*dx)+rho*(2*v) := add_le_add hres hterm
    _ = _ := by ring

/-- Moving to actual points in the same two grains keeps each quotient
coordinate. The spatial-cell gap then puts both moved points in one cloud. -/
theorem same_grain_move_cloud (g : X →L[ℝ] Y) (u₁ u₂ : X) (y₁ y₂ : Y)
    (gap quotientGap : ℝ) (hx : ‖u₁-u₂‖ ≤ gap) (hy : ‖y₁-y₂‖ ≤ quotientGap) :
    dist (u₁,y₁+g u₁) (u₂,y₂+g u₂) ≤ max gap (quotientGap+‖g‖*gap) := by
  have hv : ‖(y₁+g u₁)-(y₂+g u₂)‖ ≤ quotientGap+‖g‖*gap := by
    have he : (y₁+g u₁)-(y₂+g u₂)=(y₁-y₂)+g (u₁-u₂) := by rw [map_sub]; abel
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hy (g.le_opNorm_of_le hx))
  rw [dist_eq_norm]
  change max ‖u₁-u₂‖ ‖(y₁+g u₁)-(y₂+g u₂)‖ ≤ _
  exact max_le_max hx hv

/-- The common physical cloud required for L-tuple key counting is derived
from the same-root contact equations and actual grain moves. No pairwise
intersection or density of distinct direction clouds is assumed. -/
theorem actual_two_arm_common_cloud (f g : X →L[ℝ] Y)
    (x x₁ x₂ u₁ u₂ a₁ a₂ : X) (y y₁ y₂ xi : Y)
    (t delta tau rho v : ℝ)
    (hdelta : 0 ≤ delta) (hg : ‖g‖ ≤ 1) (ht : |t| ≤ rho)
    (hscale : 8*delta ≤ tau) (hvariation : 2*rho*v ≤ tau/2)
    (hx₁ : ‖x₁-x-t • a₁‖ ≤ delta) (hx₂ : ‖x₂-x-t • a₂‖ ≤ delta)
    (hy₁ : ‖y₁+g x₁-(y+f x)-t • (xi+f a₁)‖ ≤ delta)
    (hy₂ : ‖y₂+g x₂-(y+f x)-t • (xi+f a₂)‖ ≤ delta)
    (hv₁ : ‖(f-g) a₁‖ ≤ v) (hv₂ : ‖(f-g) a₂‖ ≤ v)
    (hmove : ‖u₁-u₂‖ ≤ tau) :
    dist (u₁,y₁+g u₁) (u₂,y₂+g u₂) ≤ 2*tau := by
  have htau : 0 ≤ tau := (norm_nonneg _).trans hmove
  have hquot := quotient_cloud f g x x₁ x₂ a₁ a₂ y y₁ y₂ xi t delta delta rho v
    ht hx₁ hx₂ hy₁ hy₂ hv₁ hv₂
  have hgd : ‖g‖*delta ≤ delta := by nlinarith only [hg,hdelta]
  have hgt : ‖g‖*tau ≤ tau := by nlinarith only [hg,htau]
  have hy : ‖y₁-y₂‖ ≤ tau := hquot.trans (by linarith)
  exact (same_grain_move_cloud g u₁ u₂ y₁ y₂ tau tau hmove hy).trans
    (max_le (by linarith) (by linarith))

end NativeLTupleCommonCloud
