import Theorems.Thm_StickyKakeya4_original_polynomial_coefficient_grid
import Theorems.Thm_StickyKakeya4_original_separated_packing

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalTensorCoefficientCollision
open OriginalPolynomialCoefficientGrid OriginalTensorFrostman

def tail {n : ℕ} (v : Fin (n+1) → ℝ) : Fin n → ℝ := fun i => v i.succ

lemma original_first_coordinate_interval {n : ℕ}
    (v d : Fin (n+1) → ℝ) (w : Fin n → ℝ) {r : ℝ}
    (hd : d 0≠0) (htail : tail v=w) (hnear : |∑ i, v i*d i| ≤ r) :
    |v 0-(-(∑ i : Fin n, w i*d i.succ)/d 0)| ≤ r/|d 0| := by
  let S : ℝ := ∑ i : Fin n, w i*d i.succ
  have ht (i : Fin n) : v i.succ=w i := congrFun htail i
  have hp : |v 0*d 0+S| ≤ r := by
    simpa only [Fin.sum_univ_succ,ht] using hnear
  have he : d 0*(v 0-(-S/d 0))=v 0*d 0+S := by field_simp; ring
  have ha : |d 0| * |v 0-(-S/d 0)| ≤ r := by
    rw [← abs_mul,he]
    exact hp
  apply (le_div_iff₀ (abs_pos.mpr hd)).mpr
  nlinarith only [ha]

/-- Condition on all but one actual coefficient. The remaining literal
grid interval count bounds the COMPLETE original coefficient tensor fiber. -/
theorem original_tensor_first_collision (n M : ℕ) (d : Fin (n+1) → ℝ)
    {r : ℝ} (hr : 0 ≤ r) (hd : d 0≠0) :
    (((tensor (grid M) (n+1)).filter (fun v => |∑ i, v i*d i| ≤ r)).card:ℝ) ≤
      (4*r/|d 0|+2*FinitePlaneProjectionGrid.mesh M)*(tensor (grid M) (n+1)).card := by
  let P := (tensor (grid M) (n+1)).filter (fun v => |∑ i, v i*d i| ≤ r)
  let E : ℝ := 4*(r/|d 0|)+2*FinitePlaneProjectionGrid.mesh M
  have hmesh := (FinitePlaneProjectionGrid.mesh_pos M).le
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hfiber (w : Fin n → ℝ) :
      ((P.filter (fun v => tail v=w)).card:ℝ) ≤ E*(grid M).card := by
    let c : ℝ := -(∑ i : Fin n, w i*d i.succ)/d 0
    have hcN : (P.filter (fun v => tail v=w)).card ≤
        ((grid M).filter (fun u => |u-c| ≤ r/|d 0|)).card := by
      apply Finset.card_le_card_of_injOn (fun v : Fin (n+1) → ℝ => v 0)
      · intro v hv
        obtain ⟨hv,hvw⟩ := Finset.mem_filter.mp hv
        obtain ⟨hvT,hvnear⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hvT 0,
          original_first_coordinate_interval v d w hd hvw hvnear⟩
      · intro v hv u hu he
        change v 0=u 0 at he
        have htail : tail v=tail u :=
          (Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hu).2.symm
        funext i
        exact Fin.cases he (fun k => congrFun htail k) i
    have hc : ((P.filter (fun v => tail v=w)).card:ℝ) ≤
        ((grid M).filter (fun u => |u-c| ≤ r/|d 0|)).card := Nat.cast_le.mpr hcN
    exact hc.trans (original_coefficient_interval_count M c (div_nonneg hr (abs_nonneg _)))
  have hsub : P.image tail ⊆ tensor (grid M) n := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    have hvT := (Finset.mem_filter.mp hv).1
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Fintype.mem_piFinset.mp hvT i.succ
  have hi : ((P.image tail).card:ℝ) ≤ (tensor (grid M) n).card :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  have hc := OriginalSeparatedPacking.card_le_real_mul_image P tail (fun w _hw => hfiber w)
  have hh := hc.trans (mul_le_mul_of_nonneg_left hi
    (show 0 ≤ E*(grid M).card by positivity))
  have hcard : (tensor (grid M) (n+1)).card=(grid M).card*(tensor (grid M) n).card := by
    simp only [tensor_card,pow_succ,mul_comm]
  rw [hcard,Nat.cast_mul]
  change (P.card:ℝ) ≤ _
  dsimp [E] at hh
  have he : 4*r/|d 0|=4*(r/|d 0|) := by ring
  rw [he]
  simpa only [mul_assoc] using hh

end OriginalTensorCoefficientCollision
