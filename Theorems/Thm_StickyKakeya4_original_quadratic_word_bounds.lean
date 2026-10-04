import Theorems.Thm_StickyKakeya4_original_quadratic_words
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalQuadraticWordBounds
open OriginalQuadraticWords

lemma original_quadratic_abs_bound (A : Finset ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ a∈A, |a| ≤ B) {z : ℝ} (hz : z∈quadraticDifferences A) :
    |z| ≤ 2*B^2 := by
  obtain ⟨p,hp,q,hq,rfl⟩ := Finset.mem_sub.mp hz
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp hp
  obtain ⟨c,hc,d,hd,rfl⟩ := Finset.mem_mul.mp hq
  have hp := mul_le_mul (hA a ha) (hA b hb) (abs_nonneg _) hB
  have hq := mul_le_mul (hA c hc) (hA d hd) (abs_nonneg _) hB
  have ht := abs_sub_le (a*b) 0 (c*d)
  simp only [sub_zero,zero_sub,abs_neg,abs_mul] at ht
  nlinarith only [hp,hq,ht]

/-- Every actual bounded-length sum retains its full pointwise norm bound. -/
theorem original_word_abs_bound (W : Finset ℝ) (N : ℕ) {B : ℝ}
    (hW : ∀ w∈W, |w| ≤ B) : ∀ z∈N • W, |z| ≤ (N:ℝ)*B := by
  induction N with
  | zero =>
    intro z hz
    have he : z=0 := by
      rw [zero_nsmul] at hz
      exact Finset.mem_singleton.mp hz
    subst z
    simp
  | succ N ih =>
    intro z hz
    rw [succ_nsmul] at hz
    obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_add.mp hz
    have ht := abs_add_le x y
    have hbound := ih x hx
    have hybound := hW y hy
    push_cast
    nlinarith only [ht,hbound,hybound]

/-- An actual original diameter gives a genuine nonzero quadratic value;
its negative is represented with the same number of original summands. -/
theorem original_diameter_square_mem (A : Finset ℝ) {lo d : ℝ}
    (hlo : lo∈A) (hhi : lo+d∈A) (N : ℕ) (hN : 2 ≤ N) :
    d^2∈N • quadraticDifferences A ∧ -(d^2)∈N • quadraticDifferences A := by
  let W := quadraticDifferences A
  have hzero : 0∈W := quadratic_zero_mem A ⟨lo,hlo⟩
  have h1 := original_product_difference_mem A hhi hhi hlo hhi
  have h2 := original_product_difference_mem A hlo hlo hlo hhi
  have hp : d^2∈(2:ℕ) • W := by
    rw [two_nsmul]
    apply Finset.mem_add.mpr
    exact ⟨(lo+d)*(lo+d)-lo*(lo+d),h1,lo*lo-lo*(lo+d),h2,by ring⟩
  have hm : -(d^2)∈(2:ℕ) • W := by
    rw [two_nsmul]
    apply Finset.mem_add.mpr
    exact ⟨-((lo+d)*(lo+d)-lo*(lo+d)),quadratic_neg_mem A h1,
      -(lo*lo-lo*(lo+d)),quadratic_neg_mem A h2,by ring⟩
  exact ⟨Finset.nsmul_subset_nsmul_right hzero hN hp,
    Finset.nsmul_subset_nsmul_right hzero hN hm⟩

/-- The next polynomial carrier has actual endpoints, a uniformly bounded
range, and a diameter bounded below by the square of the original diameter. -/
theorem exists_original_word_endpoints (A : Finset ℝ) (N : ℕ)
    {lo d B : ℝ} (hlo : lo∈A) (hhi : lo+d∈A) (hN : 2 ≤ N)
    (hB : 0 ≤ B) (hA : ∀ a∈A, |a| ≤ B) :
    ∃ lo' d' : ℝ, lo'∈N • quadraticDifferences A ∧
      lo'+d'∈N • quadraticDifferences A ∧
      (∀ a∈N • quadraticDifferences A, lo' ≤ a ∧ a ≤ lo'+d') ∧
      2*d^2 ≤ d' ∧ d' ≤ 4*(N:ℝ)*B^2 ∧ |lo'| ≤ 2*(N:ℝ)*B^2 := by
  let S := N • quadraticDifferences A
  obtain ⟨hplus,hminus⟩ := original_diameter_square_mem A hlo hhi N hN
  have hS : S.Nonempty := ⟨d^2,hplus⟩
  let a := S.min' hS
  let b := S.max' hS
  have ha : a∈S := Finset.min'_mem S hS
  have hb : b∈S := Finset.max'_mem S hS
  have hbounds : ∀ z∈S, |z| ≤ 2*(N:ℝ)*B^2 := by
    intro z hz
    have hh := original_word_abs_bound (quadraticDifferences A) N
      (fun w hw => original_quadratic_abs_bound A hB hA hw) z hz
    nlinarith only [hh]
  have haB := abs_le.mp (hbounds a ha)
  have hbB := abs_le.mp (hbounds b hb)
  have ha0 : a ≤ -(d^2) := Finset.min'_le S _ hminus
  have hb0 : d^2 ≤ b := Finset.le_max' S _ hplus
  have hab : a+(b-a)=b := by ring
  refine ⟨a,b-a,ha,?_,?_,?_,?_,hbounds a ha⟩
  · simpa only [hab] using hb
  · intro z hz
    have hzlo : a ≤ z := Finset.min'_le S _ hz
    have hzhi : z ≤ b := Finset.le_max' S _ hz
    exact ⟨hzlo,by simpa only [hab] using hzhi⟩
  · linarith only [ha0,hb0]
  · linarith only [haB.1,hbB.2]

end OriginalQuadraticWordBounds
