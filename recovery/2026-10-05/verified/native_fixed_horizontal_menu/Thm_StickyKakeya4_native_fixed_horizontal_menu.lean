import Theorems.Thm_StickyKakeya4_native_squared_grain_queries
import Theorems.Thm_StickyKakeya4_native_fixed_size_scale_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
namespace NativeFixedHorizontalMenu
open NativeSquaredGrainQueries NativeFixedSizeScaleMenu

/-- J+1 requested horizontal widths, with J fixed before the source.
The source only determines their locations between m and2m-6. -/
def depths (J m : ℕ) (j : Fin (J+1)) : ℕ :=
  m+(schedule J (phaseDepth m-m) j).val

lemma depths_zero (J m : ℕ) : depths J m 0=m := by simp [depths,schedule_zero]

lemma depths_last (J m : ℕ) (hJ : 0 < J) (hm6 : 6 ≤ m) :
    depths J m (Fin.last J)=phaseDepth m := by
  rw [depths,schedule_last J _ hJ]
  have hm : m ≤ phaseDepth m := by unfold phaseDepth; omega
  omega

lemma depths_bounds (J m : ℕ) (hm6 : 6 ≤ m) (j : Fin (J+1)) :
    m ≤ depths J m j ∧ depths J m j ≤ phaseDepth m := by
  have hj := (schedule J (phaseDepth m-m) j).isLt
  have hm : m ≤ phaseDepth m := by unfold phaseDepth; omega
  unfold depths
  omega

lemma depths_monotone (J m : ℕ) : Monotone (depths J m) := by
  intro i j hij
  unfold depths schedule
  exact Nat.add_le_add_left (Nat.div_le_div_right (Nat.mul_le_mul_right _ hij)) _

lemma depths_gap (J m : ℕ) (hJ : 0 < J) (i : Fin J) :
    depths J m i.succ-depths J m i.castSucc ≤ (phaseDepth m-m)/J+1 := by
  let L := phaseDepth m-m
  let a := i.val*L/J
  let b := (i.val+1)*L/J
  have hab : a ≤ b := Nat.div_le_div_right (Nat.mul_le_mul_right L (Nat.le_succ i.val))
  have ha : i.val*L < J*(a+1) := Nat.lt_mul_div_succ (i.val*L) hJ
  have hb : b*J ≤ (i.val+1)*L := Nat.div_mul_le_self ((i.val+1)*L) J
  have hL : L < J*(L/J+1) := Nat.lt_mul_div_succ L hJ
  have hsub : b-a+a=b := Nat.sub_add_cancel hab
  have hgap : b-a ≤ L/J+1 := by nlinarith only [ha,hb,hL,hsub,hJ]
  change (m+b)-(m+a) ≤ L/J+1
  omega

end NativeFixedHorizontalMenu
