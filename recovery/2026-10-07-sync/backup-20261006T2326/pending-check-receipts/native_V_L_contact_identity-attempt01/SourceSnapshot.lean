import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace NativeVLContactIdentity
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Exact V-tuple cancellation with the same physical root and offset.
The right side contains only the four genuine contact errors. -/
theorem v_identity (f g : X →L[ℝ] Y) (x x₁ x₂ a₁ a₂ : X)
    (y y₁ y₂ xi : Y) (t : ℝ) :
    y₁-y₂-t • ((f-g) (a₁-a₂)) =
      (y₁+g x₁-(y+f x)-t • (xi+f a₁))-
      (y₂+g x₂-(y+f x)-t • (xi+f a₂))-
      g ((x₁-x-t • a₁)-(x₂-x-t • a₂)) := by
  simp only [ContinuousLinearMap.sub_apply,map_sub,map_smul,smul_sub,smul_add]
  abel

/-- Equation157 with an explicit residual; no old collision error is
replaced by the diameter of a newly chosen label. -/
theorem v_residual (f g : X →L[ℝ] Y) (x x₁ x₂ a₁ a₂ : X)
    (y y₁ y₂ xi : Y) (t dx dy : ℝ)
    (hx₁ : ‖x₁-x-t • a₁‖ ≤ dx) (hx₂ : ‖x₂-x-t • a₂‖ ≤ dx)
    (hy₁ : ‖y₁+g x₁-(y+f x)-t • (xi+f a₁)‖ ≤ dy)
    (hy₂ : ‖y₂+g x₂-(y+f x)-t • (xi+f a₂)‖ ≤ dy) :
    ‖y₁-y₂-t • ((f-g) (a₁-a₂))‖ ≤ 2*dy+2*‖g‖*dx := by
  rw [v_identity f g x x₁ x₂ a₁ a₂ y y₁ y₂ xi t]
  have hx : ‖(x₁-x-t • a₁)-(x₂-x-t • a₂)‖ ≤ 2*dx :=
    (norm_sub_le _ _).trans (by linarith)
  have hy : ‖(y₁+g x₁-(y+f x)-t • (xi+f a₁))-
      (y₂+g x₂-(y+f x)-t • (xi+f a₂))‖ ≤ 2*dy :=
    (norm_sub_le _ _).trans (by linarith)
  calc
    _ ≤ ‖(y₁+g x₁-(y+f x)-t • (xi+f a₁))-
      (y₂+g x₂-(y+f x)-t • (xi+f a₂))‖+
      ‖g ((x₁-x-t • a₁)-(x₂-x-t • a₂))‖ := norm_sub_le _ _
    _ ≤ 2*dy+‖g‖*(2*dx) := add_le_add hy (g.le_opNorm_of_le hx)
    _ = _ := by ring

/-- Exact two-arm terminal quotient identity. The moved points retain the
same old grain coordinates y₁,y₂. -/
theorem terminal_identity (g h : X →L[ℝ] Y) (x₁ x₂ u₁ u₂ a₁ a₂ : X)
    (y₁ y₂ z₁ z₂ b₁ b₂ : Y) (t : ℝ) :
    (z₁-z₂)-(y₁-y₂) = (g-h) (u₁-u₂)+t • (b₁-b₂-h (a₁-a₂))+
      ((z₁+h x₁-(y₁+g u₁)-t • b₁)-
       (z₂+h x₂-(y₂+g u₂)-t • b₂))-
      h ((x₁-u₁-t • a₁)-(x₂-u₂-t • a₂)) := by
  simp only [ContinuousLinearMap.sub_apply,map_sub,map_smul,smul_sub]
  abel

/-- The actual terminal-direction and moved-point gaps yield the explicit
error in161, before any time-Lipschitz simplification. -/
theorem terminal_residual (g h : X →L[ℝ] Y) (x₁ x₂ u₁ u₂ a₁ a₂ : X)
    (y₁ y₂ z₁ z₂ b₁ b₂ : Y) (t dx dy gap slopeGap : ℝ)
    (hx₁ : ‖x₁-u₁-t • a₁‖ ≤ dx) (hx₂ : ‖x₂-u₂-t • a₂‖ ≤ dx)
    (hy₁ : ‖z₁+h x₁-(y₁+g u₁)-t • b₁‖ ≤ dy)
    (hy₂ : ‖z₂+h x₂-(y₂+g u₂)-t • b₂‖ ≤ dy)
    (hmove : ‖u₁-u₂‖ ≤ gap)
    (ha : ‖a₁-a₂‖ ≤ slopeGap) (hb : ‖b₁-b₂‖ ≤ slopeGap) :
    ‖(z₁-z₂)-(y₁-y₂)‖ ≤
      ‖g-h‖*gap+|t|*((1+‖h‖)*slopeGap)+2*dy+2*‖h‖*dx := by
  rw [terminal_identity g h x₁ x₂ u₁ u₂ a₁ a₂ y₁ y₂ z₁ z₂ b₁ b₂ t]
  have ha' := h.le_opNorm_of_le ha
  have hs : ‖b₁-b₂-h (a₁-a₂)‖ ≤ (1+‖h‖)*slopeGap :=
    (norm_sub_le _ _).trans (by nlinarith only [hb,ha'])
  have ht : ‖t • (b₁-b₂-h (a₁-a₂))‖ ≤ |t|*((1+‖h‖)*slopeGap) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  have hx : ‖(x₁-u₁-t • a₁)-(x₂-u₂-t • a₂)‖ ≤ 2*dx :=
    (norm_sub_le _ _).trans (by linarith)
  have hy : ‖(z₁+h x₁-(y₁+g u₁)-t • b₁)-
      (z₂+h x₂-(y₂+g u₂)-t • b₂)‖ ≤ 2*dy :=
    (norm_sub_le _ _).trans (by linarith)
  calc
    _ ≤ ‖(g-h) (u₁-u₂)+t • (b₁-b₂-h (a₁-a₂))+
      ((z₁+h x₁-(y₁+g u₁)-t • b₁)-(z₂+h x₂-(y₂+g u₂)-t • b₂))‖+
      ‖h ((x₁-u₁-t • a₁)-(x₂-u₂-t • a₂))‖ := norm_sub_le _ _
    _ ≤ (‖(g-h) (u₁-u₂)‖+‖t • (b₁-b₂-h (a₁-a₂))‖)+
      ‖(z₁+h x₁-(y₁+g u₁)-t • b₁)-(z₂+h x₂-(y₂+g u₂)-t • b₂)‖+
      ‖h ((x₁-u₁-t • a₁)-(x₂-u₂-t • a₂))‖ := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ (‖g-h‖*gap+|t|*((1+‖h‖)*slopeGap))+2*dy+‖h‖*(2*dx) := by
      exact add_le_add (add_le_add (add_le_add ((g-h).le_opNorm_of_le hmove) ht) hy)
        (h.le_opNorm_of_le hx)
    _ = _ := by ring

/-- The V residual and the genuine terminal residual combine directly.
All source labels, direction labels and inherited contact errors remain. -/
theorem l_residual_of_v {w z₁ z₂ y₁ y₂ : Y} {vError terminalError : ℝ}
    (hv : ‖y₁-y₂-w‖ ≤ vError)
    (ht : ‖(z₁-z₂)-(y₁-y₂)‖ ≤ terminalError) :
    ‖z₁-z₂-w‖ ≤ vError+terminalError := by
  have he : z₁-z₂-w=(y₁-y₂-w)+((z₁-z₂)-(y₁-y₂)) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hv ht)

end NativeVLContactIdentity
