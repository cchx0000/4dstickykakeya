import Theorems.Thm_StickyKakeya4_original_polynomial_word_length
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open Classical
open scoped Pointwise
namespace OriginalPolynomialWordHomogeneity
open OriginalPolynomialWordLength

def normalizedCarrier (S : Finset ℝ) (c R : ℝ) : Finset ℝ :=
  S.image (fun x => (x-c)/R)

lemma polynomial_word_zero (A : Finset ℝ) (T D : ℕ) : 0∈polynomialWords A T D := by
  simpa only [nsmul_zero,polynomialWords] using Finset.nsmul_mem_nsmul (signed_monomial_zero A D) (n := T)

lemma centered_original_atom_word (A : Finset ℝ) {x c : ℝ} (hx : x∈A) (hc : c∈A) :
    x-c∈polynomialWords A 2 1 := by
  have hx' : x∈signedMonomials A 1 := by
    simpa only [polynomialWords,one_nsmul] using original_atom_mem A hx
  have hc' : -c∈signedMonomials A 1 := signed_monomial_neg A 1 (by
    simpa only [polynomialWords,one_nsmul] using original_atom_mem A hc)
  change x-c∈(2:ℕ) • signedMonomials A 1
  rw [two_nsmul,sub_eq_add_neg]
  exact Finset.add_mem_add hx' hc'

/-- Clearing the homogeneous denominator expands each centered factor
into two actual original atoms; no arbitrary coefficient is introduced. -/
theorem normalized_monomial_homogeneity (S A : Finset ℝ) (c R : ℝ)
    (hSA : S⊆A) (hc : c∈A) (hR : 0 < R) (D : ℕ)
    {y : ℝ} (hy : y∈(normalizedCarrier S c R)^D) :
    R^D*y∈polynomialWords A (2^D) D := by
  induction D generalizing y with
  | zero =>
    have hy1 : y=1 := by simpa only [pow_zero,Finset.mem_one] using hy
    subst y
    have hb : (1:ℝ)∈signedMonomials A 0 := by
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (by simp))
    simpa only [pow_zero,mul_one,polynomialWords,one_nsmul] using hb
  | succ D ih =>
    rw [pow_succ] at hy
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb
    have hcenter : R*((x-c)/R)=x-c := by field_simp [hR.ne']
    have hb' : R*((x-c)/R)∈polynomialWords A 2 1 := by
      rw [hcenter]
      exact centered_original_atom_word A (hSA hx) hc
    have hp := polynomial_word_product A (2^D) 2 D 1 (ih ha) hb'
    have he : R^(D+1)*(a*((x-c)/R))=(R^D*a)*(R*((x-c)/R)) := by
      rw [pow_succ]
      ring
    rw [he]
    simpa only [pow_succ] using hp

lemma normalized_signed_monomial_homogeneity (S A : Finset ℝ) (c R : ℝ)
    (hSA : S⊆A) (hc : c∈A) (hR : 0 < R) (D : ℕ)
    {y : ℝ} (hy : y∈signedMonomials (normalizedCarrier S c R) D) :
    R^D*y∈polynomialWords A (2^D) D := by
  obtain rfl|hy := Finset.mem_insert.mp hy
  · simpa only [mul_zero] using polynomial_word_zero A (2^D) D
  · rcases Finset.mem_union.mp hy with hy|hy
    · exact normalized_monomial_homogeneity S A c R hSA hc hR D hy
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_neg.mp hy
      simpa only [mul_neg] using polynomial_word_neg A (2^D) D
        (normalized_monomial_homogeneity S A c R hSA hc hR D hx)

/-- Exact source-preserving homogeneity. The full expanded signed-term
count grows by 2^D, while polynomial degree remains D. -/
theorem original_polynomial_word_homogeneity (S A : Finset ℝ) (c R : ℝ)
    (hSA : S⊆A) (hc : c∈A) (hR : 0 < R) (T D : ℕ) :
    (polynomialWords (normalizedCarrier S c R) T D).image (fun y => R^D*y)⊆
      polynomialWords A (T*2^D) D := by
  have hmem : ∀ y∈polynomialWords (normalizedCarrier S c R) T D,
      R^D*y∈polynomialWords A (T*2^D) D := by
    induction T with
    | zero =>
      intro y hy
      have hy0 : y=0 := by simpa only [polynomialWords,zero_nsmul,Finset.mem_zero] using hy
      subst y
      simpa only [mul_zero] using polynomial_word_zero A (0*2^D) D
    | succ T ih =>
      intro y hy
      change y∈(T+1) • signedMonomials (normalizedCarrier S c R) D at hy
      rw [succ_nsmul] at hy
      obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hy
      have h1 := ih a ha
      have h2 := normalized_signed_monomial_homogeneity S A c R hSA hc hR D hb
      have hs := Finset.add_mem_add h1 h2
      change R^D*a+R^D*b∈(T*2^D) • signedMonomials A D+(2^D) • signedMonomials A D at hs
      rw [← add_nsmul] at hs
      simpa only [polynomialWords,Nat.succ_mul,mul_add] using hs
  intro z hz
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
  exact hmem y hy

end OriginalPolynomialWordHomogeneity
