import Theorems.Thm_StickyKakeya4_native_conditional_grid_coverage

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeTrimGridSuccessor
open NativeConditionalReferenceMenu

/-- The trim uses a successor depth, hence a smaller angular cell inside
the requested radius. Its finite grid and every label are fixed before the
pointwise trim; this is not a posthoc rich-class assumption at new scales. -/
theorem exists_grid_successor (m K d : ℕ) (hK : 0< K) (hd : 6≤ d) (hdm : d≤ m) :
    ∃j : Fin (K+1),d≤ gridDepth m K j ∧ gridDepth m K j≤ m ∧
      ((gridDepth m K j-d:ℕ):ℝ)≤ ((m-6:ℕ):ℝ)/K+1 := by
  have hex : ∃j : ℕ,j≤ K ∧ d≤ 6+(m-6)*j/K := by
    refine ⟨K,le_rfl,?_⟩
    rw [Nat.mul_div_cancel _ hK,Nat.add_sub_of_le (hd.trans hdm)]
    exact hdm
  let j := Nat.find hex
  have hjK : j≤ K := (Nat.find_spec hex).1
  have hjd : d≤ 6+(m-6)*j/K := (Nat.find_spec hex).2
  let jf : Fin (K+1) := ⟨j,by omega⟩
  have hBound := gridDepth_bounds m K hK (hd.trans hdm) jf
  refine ⟨jf,hjd,hBound.2,?_⟩
  by_cases hj0 : j=0
  · have hd6 : d=6 := by simp only [hj0,Nat.mul_zero,Nat.zero_div,Nat.add_zero] at hjd; omega
    have he : gridDepth m K jf=6 := by simp only [gridDepth,jf,hj0,Nat.mul_zero,Nat.zero_div,Nat.add_zero]
    rw [he,hd6]
    simp only [Nat.sub_self,Nat.cast_zero]
    positivity
  · have hjpos : 0< j := by omega
    have hPrev : ¬(j-1≤ K ∧ d≤ 6+(m-6)*(j-1)/K) := Nat.find_min hex (by dsimp [j]; omega)
    have hPrevLt : 6+(m-6)*(j-1)/K<d := by omega
    let q := (m-6)*j/K
    let p := (m-6)*(j-1)/K
    have hqLow : d-6≤ q := by dsimp [q]; omega
    have hp : p+1≤ d-6 := by dsimp [p]; omega
    have hqMul : q*K≤ (m-6)*j := Nat.div_mul_le_self _ _
    have hpMul : (m-6)*(j-1)< K*(p+1) := Nat.lt_mul_div_succ _ hK
    have hj : j-1+1=j := by omega
    have hprod : (m-6)*j=(m-6)*(j-1)+(m-6) := by
      calc
        _ = (m-6)*(j-1+1) := congrArg (fun x => (m-6)*x) hj.symm
        _ = _ := by rw [Nat.mul_add,Nat.mul_one]
    have hsub : q-(d-6)+(d-6)=q := Nat.sub_add_cancel hqLow
    have hgap : (q-(d-6))*K< m-6 := by nlinarith only [hqMul,hpMul,hprod,hsub,Nat.mul_le_mul_left K hp]
    have hGapEq : gridDepth m K jf-d=q-(d-6) := by dsimp [gridDepth,jf,q]; omega
    have hKR : (0:ℝ)<K := by exact_mod_cast hK
    have hgapR : ((q-(d-6):ℕ):ℝ)*(K:ℝ)<(m-6:ℕ) := by exact_mod_cast hgap
    rw [hGapEq]
    have hh := (lt_div_iff₀ hKR).mpr hgapR
    linarith only [hh]

end NativeTrimGridSuccessor
