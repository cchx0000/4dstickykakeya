import Theorems.Thm_StickyKakeya4_original_uniform_quadratic_step
import Theorems.Thm_StickyKakeya4_original_polynomial_word_length
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000
noncomputable section
open Classical
open scoped Pointwise BigOperators
namespace OriginalUniformPolynomialIteration
open ActualRoundedAdditiveEnergy OriginalTensorFrostman OriginalUniformQuadraticStep
open OriginalPolynomialWordLength GKZGridCodePerturbation

def iterationAlphabet : ℕ → ℝ → ℝ → ℝ → Finset ℝ → Finset ℝ
  | 0,_,_,_,A => A
  | n+1,B,d,L,A => iterationAlphabet n (nextBound (n+1) B L) (nextDiameter d)
      (nextCover (n+1) B d L) (nextAlphabet (n+1) B L A)

def coverConstant : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0,_,_,L => L/4
  | n+1,B,d,L => coverConstant n (nextBound (n+1) B L) (nextDiameter d)
      (nextCover (n+1) B d L)

def monomialCount : ℕ → ℝ → ℝ → ℝ → ℕ → ℕ
  | 0,_,_,_,T => T
  | n+1,B,d,L,T => monomialCount n (nextBound (n+1) B L) (nextDiameter d)
      (nextCover (n+1) B d L) (2*uniformWordCount (n+1) B L*T^2)

lemma uniform_cover_constant_pos (n : ℕ) (B d L : ℝ)
    (hB : 0 < B) (hd : 0 < d) (hL : 0 < L) : 0 < coverConstant n B d L := by
  induction n generalizing B d L with
  | zero => exact div_pos hL (by norm_num)
  | succ n ih =>
    have hp := uniform_step_positive (n+1) B d L hB hd hL
    exact ih _ _ _ hp.1 hp.2.1 hp.2.2.2

lemma uniform_monomial_count_pos (n : ℕ) (B d L : ℝ) (T : ℕ) (hT : 0 < T) :
    0 < monomialCount n B d L T := by
  induction n generalizing B d L T with
  | zero => exact hT
  | succ n ih =>
    have hN : 0 < uniformWordCount (n+1) B L :=
      lt_of_lt_of_le (by norm_num) (uniform_word_count_two_le (n+1) B L)
    exact ih _ _ _ _ (by positivity)

/-- Literal expansion of the full iterated alphabet: the count records
all monomials after distributive expansion, while degree is exactly doubled
at each dimension drop. Both bounds are numerical functions of the initial
fixed parameters, independent of the mesh and source data. -/
theorem original_iteration_word_complexity (n : ℕ) (B d L : ℝ)
    (A0 A : Finset ℝ) (T D : ℕ) (hA : A⊆polynomialWords A0 T D) :
    iterationAlphabet n B d L A⊆polynomialWords A0 (monomialCount n B d L T) (2^n*D) := by
  induction n generalizing B d L A T D with
  | zero => simpa only [iterationAlphabet,monomialCount,pow_zero,one_mul] using hA
  | succ n ih =>
    have hs := original_quadratic_word_complexity A0 A (uniformWordCount (n+1) B L) T D hA
    have ht := ih (nextBound (n+1) B L) (nextDiameter d) (nextCover (n+1) B d L)
      (nextAlphabet (n+1) B L A) (2*uniformWordCount (n+1) B L*T^2) (2*D) hs
    have hdeg : 2^n*(2*D)=2^(n+1)*D := by rw [pow_succ]; ring
    simpa only [iterationAlphabet,monomialCount,hdeg] using ht

lemma original_tensor_one_cover (A : Finset ℝ) (v : Fin 1 → ℝ) (delta : ℝ) :
    (tensor A 1).image (fun a => rounded delta (∑ i,v i*a i))=
      A.image (fun x => rounded delta (v 0*x)) := by
  ext z
  constructor
  · intro hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr ⟨a 0,Fintype.mem_piFinset.mp ha 0,?_⟩
    simp only [Fin.sum_univ_one]
  · intro hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr ⟨fun _ => x,Fintype.mem_piFinset.mpr (fun _ => hx),?_⟩
    simp only [Fin.sum_univ_one]

/-- A complete finite dimension iteration from an actual original tensor
image to an actual scalar word alphabet, at the same literal mesh. -/
theorem original_uniform_iteration_cover (n : ℕ) :
    ∀ (B d0 L : ℝ),0 < B → 0 < d0 → 0 < L →
    ∀ (delta : ℝ) (A : Finset ℝ) (v : Fin (n+1) → ℝ) (lo d : ℝ),
      0 < delta → delta ≤ 1 →
      (∀ i,(1/2:ℝ) ≤ v i ∧ v i ≤ 1) →
      lo∈A → lo+d∈A → d0 ≤ d →
      (∀ a∈A,lo ≤ a ∧ a ≤ lo+d) → (∀ a∈A,|a| ≤ B) →
      L ≤ delta*((tensor A (n+1)).image
        (fun a => rounded delta (∑ i,v i*a i))).card →
      coverConstant n B d0 L ≤ delta*((iterationAlphabet n B d0 L A).image (rounded delta)).card := by
  induction n with
  | zero =>
    intro B d0 L _hB _hd0 _hL delta A v _lo _d hdelta _hdelta1 hv _hlo _hhi _hdiam _hbox _habs himage
    rw [original_tensor_one_cover] at himage
    have hv0 : |v 0| ≤ 1 := by
      rw [abs_of_nonneg (by linarith only [(hv 0).1])]
      exact (hv 0).2
    have hcount := bounded_dilation_floor_image A (fun x => x) hdelta (by norm_num : (0:ℝ) ≤ 1) hv0
    norm_num at hcount
    have hh := mul_le_mul_of_nonneg_left hcount hdelta.le
    change L/4 ≤ delta*((A.image (rounded delta)).card : ℝ)
    nlinarith only [himage,hh]
  | succ n ih =>
    intro B d0 L hB hd0 hL delta A v lo d hdelta hdelta1 hv hlo hhi hdiam hbox habs himage
    obtain ⟨j,lo',d',hlo',hhi',hbox',hdiam',habs',himage'⟩ :=
      exists_uniform_original_quadratic_step (n+1) B d0 L (by omega) hB hd0 hL
        delta A v lo d hdelta hdelta1 hv hlo hhi hdiam hbox habs himage
    have hp := uniform_step_positive (n+1) B d0 L hB hd0 hL
    exact ih (nextBound (n+1) B L) (nextDiameter d0) (nextCover (n+1) B d0 L)
      hp.1 hp.2.1 hp.2.2.2 delta (nextAlphabet (n+1) B L A)
      (fun i => v (j.succAbove i)) lo' d' hdelta hdelta1 (fun i => hv (j.succAbove i))
      hlo' hhi' hdiam' hbox' habs' himage'

/-- Both total expanded monomial length and degree are fixed BEFORE the
mesh, source carrier, original endpoints and projection coefficients. The
conclusion is interval-scale covering by a literal original polynomial word
set, with no variable-length Plunnecke loss substituted for a fixed power. -/
theorem exists_fixed_original_polynomial_word_cover (n : ℕ) (B d0 L : ℝ)
    (hB : 0 < B) (hd0 : 0 < d0) (hL : 0 < L) :
    ∃ T : ℕ,0 < T ∧ ∃ C : ℝ,0 < C ∧
      ∀ (delta : ℝ) (A : Finset ℝ) (v : Fin (n+1) → ℝ) (lo d : ℝ),
        0 < delta → delta ≤ 1 →
        (∀ i,(1/2:ℝ) ≤ v i ∧ v i ≤ 1) →
        lo∈A → lo+d∈A → d0 ≤ d →
        (∀ a∈A,lo ≤ a ∧ a ≤ lo+d) → (∀ a∈A,|a| ≤ B) →
        L ≤ delta*((tensor A (n+1)).image
          (fun a => rounded delta (∑ i,v i*a i))).card →
        C ≤ delta*((polynomialWords A T (2^n)).image (rounded delta)).card := by
  refine ⟨monomialCount n B d0 L 1,uniform_monomial_count_pos n B d0 L 1 (by norm_num),
    coverConstant n B d0 L,uniform_cover_constant_pos n B d0 L hB hd0 hL,?_⟩
  intro delta A v lo d hdelta hdelta1 hv hlo hhi hdiam hbox habs himage
  have hc := original_uniform_iteration_cover n B d0 L hB hd0 hL
    delta A v lo d hdelta hdelta1 hv hlo hhi hdiam hbox habs himage
  have hsub := original_iteration_word_complexity n B d0 L A A 1 1 (fun _ hx => original_atom_mem A hx)
  simp only [mul_one] at hsub
  have hm : (((iterationAlphabet n B d0 L A).image (rounded delta)).card : ℝ) ≤
      ((polynomialWords A (monomialCount n B d0 L 1) (2^n)).image (rounded delta)).card :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hsub))
  exact hc.trans (mul_le_mul_of_nonneg_left hm hdelta.le)

end OriginalUniformPolynomialIteration
