import Theorems.Thm_StickyKakeya4_original_pure_quadratic_dimension_drop
import Theorems.Thm_StickyKakeya4_original_quadratic_word_bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
noncomputable section
open Classical
open scoped Pointwise BigOperators
namespace OriginalUniformQuadraticStep
open ActualRoundedAdditiveEnergy OriginalTensorFrostman OriginalSlabCollision
open OriginalFiniteDimensionReduction OriginalPureQuadraticDimensionDrop
open OriginalQuadraticWords OriginalQuadraticWordBounds

def uniformWordCount (n : ℕ) (B L : ℝ) : ℕ := wordCount n (2*B) L

def nextAlphabet (n : ℕ) (B L : ℝ) (A : Finset ℝ) : Finset ℝ :=
  uniformWordCount n B L • quadraticDifferences A

def nextBound (n : ℕ) (B L : ℝ) : ℝ := 2*(uniformWordCount n B L : ℝ)*B^2

def nextDiameter (d : ℝ) : ℝ := 2*d^2

def stepFactor (n : ℕ) (B L : ℝ) : ℝ :=
  (2+2*coefficientBound n (2*B) L)*(6*B+4)

def nextCover (n : ℕ) (B d L : ℝ) : ℝ := d*L/stepFactor n B L

lemma uniform_word_count_two_le (n : ℕ) (B L : ℝ) : 2 ≤ uniformWordCount n B L := by
  unfold uniformWordCount wordCount
  omega

lemma uniform_step_positive (n : ℕ) (B d L : ℝ) (hB : 0 < B) (hd : 0 < d) (hL : 0 < L) :
    0 < nextBound n B L ∧ 0 < nextDiameter d ∧ 0 < stepFactor n B L ∧
      0 < nextCover n B d L := by
  have hN : (0:ℝ) < uniformWordCount n B L := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) (uniform_word_count_two_le n B L))
  have hF : 0 < stepFactor n B L := by
    unfold stepFactor coefficientBound
    positivity
  refine ⟨?_,?_,hF,?_⟩
  · unfold nextBound
    positivity
  · unfold nextDiameter
    positivity
  · exact div_pos (mul_pos hd hL) hF

lemma uniform_slab_radius_bound (n : ℕ) (d B L : ℝ) (hL : 0 < L) (hd : d ≤ 2*B) :
    slabRadius n d L ≤ slabRadius n (2*B) L := by
  unfold slabRadius
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ hL.le
  have hn : (0:ℝ) ≤ (n:ℝ)+3 := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left hd hn]

lemma uniform_word_count_bound (n : ℕ) (d B L : ℝ) (hL : 0 < L) (hd : d ≤ 2*B) :
    wordCount n d L ≤ uniformWordCount n B L := by
  have hR := uniform_slab_radius_bound n d B L hL hd
  unfold wordCount uniformWordCount
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left (2*n+1) hR)) 2

lemma uniform_coefficient_bound (n : ℕ) (d B L : ℝ) (hB : 0 ≤ B)
    (hL : 0 < L) (hdB : d ≤ 2*B) :
    coefficientBound n d L ≤ coefficientBound n (2*B) L := by
  have hR : (slabRadius n d L : ℝ) ≤ slabRadius n (2*B) L := by
    exact_mod_cast uniform_slab_radius_bound n d B L hL hdB
  have hn : (0:ℝ) ≤ 2*(n:ℝ)+1 := by positivity
  have hinner : 1+4*((2*(n:ℝ)+1)*(slabRadius n d L:ℝ)) ≤
      1+4*((2*(n:ℝ)+1)*(slabRadius n (2*B) L:ℝ)) := by
    nlinarith only [mul_le_mul_of_nonneg_left hR hn]
  unfold coefficientBound
  exact mul_le_mul hdB hinner (by positivity) (by positivity)

/-- One actual drop with every word count and loss fixed by numerical
bounds before the mesh, carrier or projection coefficients are supplied. -/
theorem exists_uniform_original_quadratic_step (n : ℕ) (B d0 L : ℝ)
    (hn : 1 ≤ n) (hB : 0 < B) (hd0 : 0 < d0) (hL : 0 < L)
    (delta : ℝ) (A : Finset ℝ) (v : Fin (n+1) → ℝ) (lo d : ℝ)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hv : ∀ i,(1/2:ℝ) ≤ v i ∧ v i ≤ 1)
    (hlo : lo∈A) (hhi : lo+d∈A) (hdiam : d0 ≤ d)
    (hbox : ∀ a∈A,lo ≤ a ∧ a ≤ lo+d) (habs : ∀ a∈A,|a| ≤ B)
    (himage : L ≤ delta*((tensor A (n+1)).image
      (fun a => rounded delta (∑ i,v i*a i))).card) :
    ∃ j : Fin (n+1),∃ lo' d' : ℝ,
      lo'∈nextAlphabet n B L A ∧ lo'+d'∈nextAlphabet n B L A ∧
      (∀ a∈nextAlphabet n B L A,lo' ≤ a ∧ a ≤ lo'+d') ∧
      nextDiameter d0 ≤ d' ∧ (∀ a∈nextAlphabet n B L A,|a| ≤ nextBound n B L) ∧
      nextCover n B d0 L ≤ delta*((tensor (nextAlphabet n B L A) n).image
        (fun a => rounded delta (∑ i,v (j.succAbove i)*a i))).card := by
  have hd : 0 < d := hd0.trans_le hdiam
  have hdB : d ≤ 2*B := by
    have h0 := abs_le.mp (habs lo hlo)
    have h1 := abs_le.mp (habs (lo+d) hhi)
    linarith only [h0.1,h1.2]
  obtain ⟨j,hdrop⟩ := exists_original_quadratic_dimension_drop n A v hdelta hdelta1 hd hL hn hv hlo hhi hbox himage
  have hsub : wordCount n d L • quadraticDifferences A⊆nextAlphabet n B L A :=
    Finset.nsmul_subset_nsmul_right (quadratic_zero_mem A ⟨lo,hlo⟩)
      (uniform_word_count_bound n d B L hL hdB)
  have hcard : (((tensor (wordCount n d L • quadraticDifferences A) n).image
      (fun a => rounded delta (∑ i,v (j.succAbove i)*a i))).card : ℝ) ≤
      ((tensor (nextAlphabet n B L A) n).image
        (fun a => rounded delta (∑ i,v (j.succAbove i)*a i))).card :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image
      (Fintype.piFinset_subset _ _ (fun _ => hsub))))
  have hcoef := uniform_coefficient_bound n d B L hB.le hL hdB
  have hfac : (2+2*coefficientBound n d L)*(2*(|lo|+d)+4) ≤ stepFactor n B L := by
    unfold stepFactor
    apply mul_le_mul
    · linarith only [hcoef]
    · nlinarith only [habs lo hlo,hdB]
    · positivity
    · unfold coefficientBound
      positivity
  have hfac0 : 0 ≤ stepFactor n B L := (uniform_step_positive n B d0 L hB hd0 hL).2.2.1.le
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_right hfac hdelta.le) hcard
    (Nat.cast_nonneg _) (mul_nonneg hfac0 hdelta.le)
  have hlow := mul_le_mul_of_nonneg_right hdiam hL.le
  have hnewcover : nextCover n B d0 L ≤ delta*((tensor (nextAlphabet n B L A) n).image
      (fun a => rounded delta (∑ i,v (j.succAbove i)*a i))).card := by
    apply (div_le_iff₀ (uniform_step_positive n B d0 L hB hd0 hL).2.2.1).mpr
    nlinarith only [hlow,hdrop,hprod]
  obtain ⟨lo',d',hlo',hhi',hbox',hlower,_hupper,_hloabs⟩ :=
    exists_original_word_endpoints A (uniformWordCount n B L) hlo hhi
      (uniform_word_count_two_le n B L) hB.le habs
  have habs' : ∀ a∈nextAlphabet n B L A,|a| ≤ nextBound n B L := by
    intro a ha
    have h := original_word_abs_bound (quadraticDifferences A) (uniformWordCount n B L)
      (fun w hw => original_quadratic_abs_bound A hB.le habs hw) a ha
    dsimp [nextBound]
    nlinarith only [h]
  refine ⟨j,lo',d',hlo',hhi',hbox',?_,habs',hnewcover⟩
  unfold nextDiameter
  have hs := pow_le_pow_left₀ hd0.le hdiam 2
  nlinarith only [hlower,hs]

end OriginalUniformQuadraticStep
