import Theorems.Thm_StickyKakeya4_original_polynomial_dimension_drop
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalQuadraticWords
open OriginalPolynomialDimensionDrop

def quadraticDifferences (A : Finset ℝ) : Finset ℝ := (A*A)-(A*A)

lemma original_product_difference_mem (A : Finset ℝ) {a b c d : ℝ}
    (ha : a∈A) (hb : b∈A) (hc : c∈A) (hd : d∈A) :
    a*b-c*d∈quadraticDifferences A :=
  Finset.mem_sub.mpr ⟨a*b,Finset.mul_mem_mul ha hb,c*d,Finset.mul_mem_mul hc hd,rfl⟩

lemma quadratic_zero_mem (A : Finset ℝ) (hA : A.Nonempty) : 0∈quadraticDifferences A := by
  obtain ⟨a,ha⟩ := hA
  simpa only [sub_self] using original_product_difference_mem A ha ha ha ha

lemma quadratic_neg_mem (A : Finset ℝ) {z : ℝ} (hz : z∈quadraticDifferences A) :
    -z∈quadraticDifferences A := by
  obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_sub.mp hz
  exact Finset.mem_sub.mpr ⟨y,hy,x,hx,by ring⟩

/-- A signed original integer coefficient is represented by a bounded
number of original summands, with padding by the actual zero element. -/
theorem integer_multiple_mem_padded (W : Finset ℝ) {z : ℝ} (hz : z∈W)
    (hzero : 0∈W) (hneg : ∀ x∈W, -x∈W) (m : ℤ) (N : ℕ)
    (hm : |(m:ℝ)| ≤ N) : (m:ℝ)*z∈N • W := by
  have habs : (m.natAbs:ℝ)=|(m:ℝ)| := by
    have he := congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs m)
    simpa only [Int.cast_natCast,Int.cast_abs] using he
  let w : ℝ := if 0 ≤ m then z else -z
  have hw : w∈W := by
    dsimp [w]
    split_ifs
    · exact hz
    · exact hneg z hz
  have he : (m:ℝ)*z=(m.natAbs:ℝ)*w := by
    rw [habs]
    dsimp [w]
    split_ifs with hnon
    · have hnonR : (0:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnon
      rw [abs_of_nonneg hnonR]
    · have hnegR : (m:ℝ) < 0 := by exact_mod_cast lt_of_not_ge hnon
      rw [abs_of_neg hnegR]
      ring
  have hN : m.natAbs ≤ N := by
    have hh : (m.natAbs:ℝ) ≤ N := by rw [habs]; exact hm
    exact_mod_cast hh
  have hbase : (m.natAbs:ℝ)*w∈m.natAbs • W := by
    simpa only [nsmul_eq_mul] using Finset.nsmul_mem_nsmul hw (n:=m.natAbs)
  rw [he]
  exact Finset.nsmul_subset_nsmul_right hzero hN hbase

/-- Each new reduced scalar value is a bounded sum of ORIGINAL quadratic
differences when the interval endpoints are themselves original points. -/
theorem original_reduced_alphabet_quadratic {n : ℕ}
    (A : Finset ℝ) (x y : Fin (n+1) → ℝ) (m : Fin (n+1) → ℤ)
    (j : Fin (n+1)) (N : ℕ) {lo d : ℝ}
    (hlo : lo∈A) (hhi : lo+d∈A)
    (hx : ∀ i, x i∈A) (hy : ∀ i, y i∈A)
    (hm : ∀ i, |(m i:ℝ)| ≤ N) :
    reducedAlphabet A (fun i => x i-y i+d*(m i:ℝ)) j ⊆
      (2+N+N) • quadraticDifferences A := by
  let W := quadraticDifferences A
  have hzero : 0∈W := quadratic_zero_mem A ⟨lo,hlo⟩
  have hneg : ∀ z∈W, -z∈W := fun z hz => quadratic_neg_mem A hz
  intro z hz
  obtain ⟨i,_hi,hz⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
  let k := j.succAbove i
  let u := x j*p.1-y j*p.1
  let w := y k*p.2-x k*p.2
  let r := (lo+d)*p.1-lo*p.1
  let s := (lo+d)*p.2-lo*p.2
  have hu : u∈W := original_product_difference_mem A (hx j) ha (hy j) ha
  have hw : w∈W := original_product_difference_mem A (hy k) hb (hx k) hb
  have hr : r∈W := original_product_difference_mem A hhi ha hlo ha
  have hs : s∈W := original_product_difference_mem A hhi hb hlo hb
  have hmj : (m j:ℝ)*r∈N • W := integer_multiple_mem_padded W hr hzero hneg (m j) N (hm j)
  have hmk : ((-m k:ℤ):ℝ)*s∈N • W := integer_multiple_mem_padded W hs hzero hneg (-m k) N
    (by simpa only [Int.cast_neg,abs_neg] using hm k)
  have huw : u+w∈(2:ℕ) • W := by
    rw [two_nsmul]
    exact Finset.add_mem_add hu hw
  have hsum := Finset.add_mem_add (Finset.add_mem_add huw hmj) hmk
  rw [← add_nsmul,← add_nsmul] at hsum
  have he : (x j-y j+d*(m j:ℝ))*p.1-
      (x (j.succAbove i)-y (j.succAbove i)+d*(m (j.succAbove i):ℝ))*p.2=
        (u+w+(m j:ℝ)*r)+((-m k:ℤ):ℝ)*s := by
    dsimp [u,w,r,s,k]
    push_cast
    ring
  rw [he]
  exact hsum

end OriginalQuadraticWords
