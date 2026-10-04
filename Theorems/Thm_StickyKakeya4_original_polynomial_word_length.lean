import Theorems.Thm_StickyKakeya4_original_quadratic_words
import Mathlib.Algebra.Ring.Pointwise.Finset

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open Classical
open scoped Pointwise BigOperators
namespace OriginalPolynomialWordLength
open OriginalQuadraticWords

/-- A signed degree-D original monomial, including the zero polynomial. -/
def signedMonomials (A : Finset ℝ) (D : ℕ) : Finset ℝ :=
  insert 0 ((A^D) ∪ -(A^D))

/-- Literal sums of at most T signed original degree-D monomials, padded
by zero. The total expanded term count and degree are separate parameters. -/
def polynomialWords (A : Finset ℝ) (T D : ℕ) : Finset ℝ := T • signedMonomials A D

lemma signed_monomial_zero (A : Finset ℝ) (D : ℕ) : 0∈signedMonomials A D :=
  Finset.mem_insert_self _ _

lemma original_atom_mem (A : Finset ℝ) {a : ℝ} (ha : a∈A) :
    a∈polynomialWords A 1 1 := by
  simpa only [polynomialWords,one_nsmul,signedMonomials,pow_one] using
    Finset.mem_insert_of_mem (Finset.mem_union_left (-A) ha)

lemma signed_monomial_neg (A : Finset ℝ) (D : ℕ) {x : ℝ}
    (hx : x∈signedMonomials A D) : -x∈signedMonomials A D := by
  obtain hx|hx := Finset.mem_insert.mp hx
  · subst x
    simpa only [neg_zero] using signed_monomial_zero A D
  · rcases Finset.mem_union.mp hx with hx|hx
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.neg_mem_neg hx))
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_neg.mp hx
      simpa only [neg_neg,signedMonomials] using Finset.mem_insert_of_mem
        (Finset.mem_union_left (-(A^D)) hy)

lemma signed_monomial_mul (A : Finset ℝ) (D E : ℕ) {x y : ℝ}
    (hx : x∈signedMonomials A D) (hy : y∈signedMonomials A E) :
    x*y∈signedMonomials A (D+E) := by
  obtain rfl|hx := Finset.mem_insert.mp hx
  · simpa only [zero_mul] using signed_monomial_zero A (D+E)
  obtain rfl|hy := Finset.mem_insert.mp hy
  · simpa only [mul_zero] using signed_monomial_zero A (D+E)
  have hp {a b : ℝ} (ha : a∈A^D) (hb : b∈A^E) : a*b∈signedMonomials A (D+E) := by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_left
    rw [pow_add]
    exact Finset.mul_mem_mul ha hb
  rcases Finset.mem_union.mp hx with hx|hx <;> rcases Finset.mem_union.mp hy with hy|hy
  · exact hp hx hy
  · obtain ⟨b,hb,rfl⟩ := Finset.mem_neg.mp hy
    simpa only [mul_neg] using signed_monomial_neg A (D+E) (hp hx hb)
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_neg.mp hx
    simpa only [neg_mul] using signed_monomial_neg A (D+E) (hp ha hy)
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_neg.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_neg.mp hy
    simpa only [neg_mul_neg] using hp ha hb

lemma finite_mul_word_subset (S T : Finset ℝ) (n : ℕ) :
    S*(n • T)⊆n • (S*T) := by
  induction n with
  | zero =>
    intro x hx
    obtain ⟨a,_ha,b,hb,rfl⟩ := Finset.mem_mul.mp hx
    have hb0 : b=0 := by simpa only [zero_nsmul,Finset.mem_zero] using hb
    simp [hb0]
  | succ n ih =>
    rw [succ_nsmul,succ_nsmul]
    exact (Finset.mul_add_subset _ _ _).trans (Finset.add_subset_add ih (Finset.Subset.refl _))

lemma finite_word_mul_word_subset (S T : Finset ℝ) (m n : ℕ) :
    (m • S)*(n • T)⊆(m*n) • (S*T) := by
  induction m with
  | zero =>
    intro x hx
    obtain ⟨a,ha,b,_hb,rfl⟩ := Finset.mem_mul.mp hx
    have ha0 : a=0 := by simpa only [zero_nsmul,Finset.mem_zero] using ha
    simp [ha0]
  | succ m ih =>
    rw [succ_nsmul,Nat.succ_mul,add_nsmul]
    exact (Finset.add_mul_subset _ _ _).trans
      (Finset.add_subset_add ih (finite_mul_word_subset S T n))

lemma polynomial_word_neg (A : Finset ℝ) (T D : ℕ) {x : ℝ}
    (hx : x∈polynomialWords A T D) : -x∈polynomialWords A T D := by
  induction T generalizing x with
  | zero =>
    have hx0 : x=0 := by simpa only [polynomialWords,zero_nsmul,Finset.mem_zero] using hx
    subst x
    simp [polynomialWords]
  | succ T ih =>
    change x∈(T+1) • signedMonomials A D at hx
    rw [succ_nsmul] at hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
    change -(a+b)∈(T+1) • signedMonomials A D
    rw [succ_nsmul,neg_add]
    exact Finset.add_mem_add (ih ha) (signed_monomial_neg A D hb)

lemma polynomial_word_product (A : Finset ℝ) (T U D E : ℕ) {x y : ℝ}
    (hx : x∈polynomialWords A T D) (hy : y∈polynomialWords A U E) :
    x*y∈polynomialWords A (T*U) (D+E) := by
  have hm := finite_word_mul_word_subset (signedMonomials A D) (signedMonomials A E) T U
    (Finset.mul_mem_mul hx hy)
  apply Finset.nsmul_subset_nsmul_left (t := signedMonomials A (D+E)) ?_ hm
  intro z hz
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp hz
  exact signed_monomial_mul A D E ha hb

/-- Each quadratic step doubles polynomial degree and updates the FULL
expanded monomial count to 2*N*T^2; no variable-length word is hidden. -/
theorem original_quadratic_word_complexity (A B : Finset ℝ) (N T D : ℕ)
    (hB : B⊆polynomialWords A T D) :
    N • quadraticDifferences B⊆polynomialWords A (2*N*T^2) (2*D) := by
  have hquad : quadraticDifferences B⊆polynomialWords A (2*T^2) (2*D) := by
    intro z hz
    obtain ⟨p,hp,q,hq,rfl⟩ := Finset.mem_sub.mp hz
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp hp
    obtain ⟨c,hc,d,hd,rfl⟩ := Finset.mem_mul.mp hq
    have hp' := polynomial_word_product A T T D D (hB ha) (hB hb)
    have hq' := polynomial_word_neg A (T*T) (D+D)
      (polynomial_word_product A T T D D (hB hc) (hB hd))
    have hs := Finset.add_mem_add hp' hq'
    change a*b+ -(c*d)∈(T*T) • signedMonomials A (D+D)+(T*T) • signedMonomials A (D+D) at hs
    rw [← add_nsmul] at hs
    convert hs using 1 <;> congr 1 <;> ring
  have hn := Finset.nsmul_subset_nsmul_left (n := N) hquad
  unfold polynomialWords at hn ⊢
  rw [← mul_nsmul] at hn
  convert hn using 1
  congr 1
  ring

/-- A single signed monomial has literal original factor witnesses. -/
theorem exists_signed_monomial_witness (A : Finset ℝ) (D : ℕ) (hA : A.Nonempty)
    (x : ℝ) (hx : x∈signedMonomials A D) :
    ∃ eps : ℝ,∃ a : Fin D → ℝ,(eps=0 ∨ eps=1 ∨ eps= -1) ∧
      (∀ i,a i∈A) ∧ x=eps*(∏ i,a i) := by
  obtain rfl|hx := Finset.mem_insert.mp hx
  · obtain ⟨a0,ha0⟩ := hA
    exact ⟨0,fun _ => a0,Or.inl rfl,fun _ => ha0,by simp⟩
  · rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨a,ha⟩ := Finset.mem_pow.mp hx
      refine ⟨1,fun i => (a i:ℝ),Or.inr (Or.inl rfl),fun i => (a i).2,?_⟩
      simpa only [one_mul,List.prod_ofFn] using ha.symm
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_neg.mp hx
      obtain ⟨a,ha⟩ := Finset.mem_pow.mp hy
      refine ⟨-1,fun i => (a i:ℝ),Or.inr (Or.inr rfl),fun i => (a i).2,?_⟩
      have he : (∏ i,(a i:ℝ))=y := by simpa only [List.prod_ofFn] using ha
      rw [he,neg_one_mul]

/-- A selected value uses only its own at-most-T signed monomials. This
explicit witness list does not take a union over all possible monomials. -/
theorem exists_polynomial_word_witnesses (A : Finset ℝ) (T D : ℕ) (hA : A.Nonempty)
    (x : ℝ) (hx : x∈polynomialWords A T D) :
    ∃ eps : Fin T → ℝ,∃ a : Fin T → Fin D → ℝ,
      (∀ j,eps j=0 ∨ eps j=1 ∨ eps j= -1) ∧
      (∀ j i,a j i∈A) ∧ x=∑ j,eps j*(∏ i,a j i) := by
  obtain ⟨f,hf⟩ := Finset.mem_nsmul.mp hx
  have hw (j : Fin T) := exists_signed_monomial_witness A D hA (f j) (f j).2
  choose eps a hs ha he using hw
  refine ⟨eps,a,hs,ha,?_⟩
  calc
    x = ∑ j,(f j:ℝ) := by simpa only [List.sum_ofFn] using hf.symm
    _ = ∑ j,eps j*(∏ i,a j i) := Finset.sum_congr rfl (fun j _ => he j)

end OriginalPolynomialWordLength
