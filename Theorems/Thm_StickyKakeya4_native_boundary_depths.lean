import Theorems.Thm_StickyKakeya4_native_fixed_size_scale_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

noncomputable section
namespace NativeBoundaryDepths

def lowerAnchor (v : ℝ) (level : ℕ) : ℕ := ⌈v*(level:ℝ)⌉₊
def upperAnchor (v : ℝ) (level : ℕ) : ℕ := ⌊(1-v)*(level:ℝ)⌋₊

/-- The two integer anchors lie inside the middle window. Rounding costs
at most twice its width once v*level is at least four. -/
theorem anchor_bounds (v : ℝ) (hv : 0 < v) (hvquarter : v ≤ 1/4)
    (level : ℕ) (hlarge : 4 ≤ v*(level:ℝ)) :
    lowerAnchor v level ≤ upperAnchor v level ∧ upperAnchor v level ≤ level ∧
    (v*(level:ℝ) ≤ lowerAnchor v level ∧ (lowerAnchor v level:ℝ) ≤ (1-v)*(level:ℝ)) ∧
    (v*(level:ℝ) ≤ upperAnchor v level ∧ (upperAnchor v level:ℝ) ≤ (1-v)*(level:ℝ)) ∧
    (lowerAnchor v level:ℝ) ≤ (2*v)*(level:ℝ) ∧
    ((level-upperAnchor v level:ℕ):ℝ) ≤ (2*v)*(level:ℝ) := by
  have hln : (0:ℝ) ≤ level := Nat.cast_nonneg _
  have hvl : 0 ≤ v*(level:ℝ) := mul_nonneg hv.le hln
  have hvL := mul_le_mul_of_nonneg_right hvquarter hln
  have hclo : v*(level:ℝ) ≤ lowerAnchor v level := Nat.le_ceil _
  have hchi : (lowerAnchor v level:ℝ) < v*(level:ℝ)+1 := Nat.ceil_lt_add_one hvl
  have hnon : 0 ≤ (1-v)*(level:ℝ) := mul_nonneg (by linarith) hln
  have hflo : (upperAnchor v level:ℝ) ≤ (1-v)*(level:ℝ) := Nat.floor_le hnon
  have hfhi : (1-v)*(level:ℝ) < (upperAnchor v level:ℝ)+1 := Nat.lt_floor_add_one _
  have hclast : (lowerAnchor v level:ℝ) ≤ (1-v)*(level:ℝ) := by nlinarith
  have hcu : lowerAnchor v level ≤ upperAnchor v level := Nat.le_floor hclast
  have hul : upperAnchor v level ≤ level := Nat.floor_le_of_le (by nlinarith)
  have hcuR : (lowerAnchor v level:ℝ) ≤ upperAnchor v level := by exact_mod_cast hcu
  refine ⟨hcu,hul,⟨hclo,hclast⟩,⟨hclo.trans hcuR,hflo⟩,by nlinarith,?_⟩
  rw [Nat.cast_sub hul]
  nlinarith

lemma lower_gap (v : ℝ) (hv : 0 < v) (hvquarter : v ≤ 1/4)
    (level m : ℕ) (hlarge : 4 ≤ v*(level:ℝ)) :
    ((lowerAnchor v level-m:ℕ):ℝ) ≤ (2*v)*(level:ℝ) := by
  have hg := (anchor_bounds v hv hvquarter level hlarge).2.2.2.2.1
  exact (show ((lowerAnchor v level-m:ℕ):ℝ) ≤ lowerAnchor v level by
    exact_mod_cast Nat.sub_le (lowerAnchor v level) m).trans hg

lemma upper_gap (v : ℝ) (hv : 0 < v) (hvquarter : v ≤ 1/4)
    (level m : ℕ) (hlarge : 4 ≤ v*(level:ℝ)) (hm : m ≤ level) :
    ((m-upperAnchor v level:ℕ):ℝ) ≤ (2*v)*(level:ℝ) := by
  have hg := (anchor_bounds v hv hvquarter level hlarge).2.2.2.2.2
  have hh : m-upperAnchor v level ≤ level-upperAnchor v level := by omega
  exact (show ((m-upperAnchor v level:ℕ):ℝ) ≤ (level-upperAnchor v level:ℕ) by
    exact_mod_cast hh).trans hg

lemma remaining_gap (v : ℝ) (hv : 0 < v) (hvquarter : v ≤ 1/4)
    (level m : ℕ) (hlarge : 4 ≤ v*(level:ℝ)) (hm : upperAnchor v level ≤ m) :
    ((level-m:ℕ):ℝ) ≤ (2*v)*(level:ℝ) := by
  have hg := (anchor_bounds v hv hvquarter level hlarge).2.2.2.2.2
  have hh : level-m ≤ level-upperAnchor v level := by omega
  exact (show ((level-m:ℕ):ℝ) ≤ (level-upperAnchor v level:ℕ) by exact_mod_cast hh).trans hg

lemma initial_gap (v : ℝ) (hv : 0 < v) (hvquarter : v ≤ 1/4)
    (level m : ℕ) (hlarge : 4 ≤ v*(level:ℝ)) (hm : m ≤ lowerAnchor v level) :
    (m:ℝ) ≤ (2*v)*(level:ℝ) := by
  exact (show (m:ℝ) ≤ lowerAnchor v level by exact_mod_cast hm).trans
    (anchor_bounds v hv hvquarter level hlarge).2.2.2.2.1

def boundaryWindow (tau : ℝ) : ℝ := min (1/4) (tau/1000)

lemma boundaryWindow_pos {tau : ℝ} (htau : 0 < tau) : 0 < boundaryWindow tau :=
  lt_min (by norm_num) (by positivity)

lemma boundaryWindow_le_quarter (tau : ℝ) : boundaryWindow tau ≤ 1/4 := min_le_left _ _

lemma boundaryWindow_le_loss (tau : ℝ) : boundaryWindow tau ≤ tau/1000 := min_le_right _ _

end NativeBoundaryDepths
