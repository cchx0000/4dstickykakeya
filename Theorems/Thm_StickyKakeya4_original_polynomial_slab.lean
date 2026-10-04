import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalPolynomialSlab

/-- A literal lattice translation with bounded projection. The last n
coordinates are the original integer box coordinates. -/
def slabVector {n R : ℕ} (v : Fin (n+1) → ℝ) (a : Fin n → Fin (R+1)) : Fin (n+1) → ℤ :=
  Fin.cons (-⌊(∑ i : Fin n, v i.succ*(a i:ℕ))/v 0⌋) (fun i => (a i:ℕ))

def slabVectors (n R : ℕ) (v : Fin (n+1) → ℝ) : Finset (Fin (n+1) → ℤ) :=
  Finset.univ.image (slabVector (R:=R) v)

lemma slabVector_injective {n R : ℕ} (v : Fin (n+1) → ℝ) :
    Function.Injective (slabVector (R:=R) v) := by
  intro a b he
  funext i
  apply Fin.ext
  have hi := congrFun he i.succ
  change ((a i:ℕ):ℤ)=((b i:ℕ):ℤ) at hi
  exact_mod_cast hi

/-- The slab contains an actual (R+1)^n-member family of lattice translations. -/
theorem slabVectors_card (n R : ℕ) (v : Fin (n+1) → ℝ) :
    (slabVectors n R v).card=(R+1)^n := by
  unfold slabVectors
  rw [Finset.card_image_of_injective _ (slabVector_injective v)]
  simp

/-- All these many distinct original lattice translations have projections
in one fixed interval, independently of the box radius. -/
theorem slabVector_projection {n R : ℕ} {v : Fin (n+1) → ℝ}
    (hv : 0 < v 0) (a : Fin n → Fin (R+1)) :
    0 ≤ ∑ i, v i*(slabVector v a i:ℝ) ∧
      ∑ i, v i*(slabVector v a i:ℝ) < v 0 := by
  let S : ℝ := ∑ i : Fin n, v i.succ*(a i:ℕ)
  have hlo := Int.floor_le (S/v 0)
  have hhi := Int.lt_floor_add_one (S/v 0)
  have hid : (∑ i, v i*(slabVector v a i:ℝ))=
      v 0*(S/v 0-(⌊S/v 0⌋:ℝ)) := by
    rw [Fin.sum_univ_succ]
    simp only [slabVector,Fin.cons_zero,Fin.cons_succ,Int.cast_neg,Int.cast_natCast]
    change v 0*(-(⌊S/v 0⌋:ℝ))+S=v 0*(S/v 0-(⌊S/v 0⌋:ℝ))
    have hcancel : v 0*(S/v 0)=S := by field_simp
    rw [mul_sub,hcancel]
    ring
  rw [hid]
  constructor
  · exact mul_nonneg hv.le (sub_nonneg.mpr hlo)
  · have hh := mul_lt_mul_of_pos_left hhi hv
    have hid' : v 0*(S/v 0-(⌊S/v 0⌋:ℝ)) < v 0 := by
      nlinarith only [hh]
    exact hid'

/-- The integer coefficients used by the slab construction have a fixed
polynomial-size bound in n and R. -/
theorem slabVector_coordinate_bound {n R : ℕ} {v : Fin (n+1) → ℝ}
    (hv : ∀ i, (1/2:ℝ) ≤ v i ∧ v i ≤ 1) (a : Fin n → Fin (R+1)) :
    ∀ i, |(slabVector v a i:ℝ)| ≤ (2*(n:ℝ)+1)*R := by
  have hv0 : 0 < v 0 := lt_of_lt_of_le (by norm_num) (hv 0).1
  let S : ℝ := ∑ i : Fin n, v i.succ*(a i:ℕ)
  have ha (i : Fin n) : ((a i:ℕ):ℝ) ≤ R := by
    exact_mod_cast Nat.le_of_lt_succ (a i).isLt
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ =>
    mul_nonneg ((by norm_num : (0:ℝ) ≤ 1/2).trans (hv i.succ).1) (Nat.cast_nonneg _))
  have hS : S ≤ (n:ℝ)*R := by
    calc
      _ ≤ ∑ _i : Fin n, (R:ℝ) := by
        apply Finset.sum_le_sum
        intro i _hi
        calc
          _ ≤ 1*((a i:ℕ):ℝ) := mul_le_mul_of_nonneg_right (hv i.succ).2 (Nat.cast_nonneg _)
          _ ≤ R := by simpa only [one_mul] using ha i
      _ = _ := by simp
  have hratio0 : 0 ≤ S/v 0 := div_nonneg hS0 hv0.le
  have hratio : S/v 0 ≤ 2*(n:ℝ)*R := by
    apply (div_le_iff₀ hv0).mpr
    have hh := mul_le_mul_of_nonneg_left (hv 0).1 (show 0 ≤ 2*(n:ℝ)*R by positivity)
    nlinarith only [hS,hh]
  have hfloor0 : (0:ℝ) ≤ (⌊S/v 0⌋:ℝ) := by
    exact_mod_cast Int.floor_nonneg.mpr hratio0
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change |((-(⌊S/v 0⌋):ℤ):ℝ)| ≤ _
    rw [Int.cast_neg,abs_neg,abs_of_nonneg hfloor0]
    have hf := Int.floor_le (S/v 0)
    nlinarith only [hf,hratio,show (0:ℝ) ≤ R from Nat.cast_nonneg _]
  · change |((a j:ℕ):ℝ)| ≤ _
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    have hextra : 0 ≤ 2*(n:ℝ)*R := by positivity
    nlinarith only [ha j,hextra]

end OriginalPolynomialSlab
