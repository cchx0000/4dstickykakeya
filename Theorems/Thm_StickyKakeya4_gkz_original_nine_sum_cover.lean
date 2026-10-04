import Theorems.Thm_StickyKakeya4_gkz_original_mixed_dilate_bounds
import Theorems.Thm_StickyKakeya4_gkz_real_dilation_union
import Theorems.Thm_StickyKakeya4_gkz_original_ratio_dichotomy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped Pointwise

namespace GKZOriginalNineSumCover
open ActualRoundedAdditiveEnergy GKZOriginalProductOverlap GKZDilateRoundedSums
open GKZOriginalMixedDilateBounds GKZRealDilationUnion GKZOriginalRatioDichotomy

def OriginalExpansionCoefficients (A : Finset ℝ) (e1 e2 : ℝ) : Prop :=
  ∃ x∈A, ∃ x'∈A, ∃ y∈A, ∃ y'∈A,
    (e2=y-y' ∧ e1=x-x') ∨
      (e2=2*(y-y') ∧ (e1=x-x' ∨ e1=(x-x')+(y-y')))

lemma gap_coefficients_are_expansion_coefficients (A : Finset ℝ) {e1 e2 : ℝ}
    (h : OriginalCoefficients A e1 e2) : OriginalExpansionCoefficients A e1 e2 := by
  obtain ⟨x,hx,x',hx',y,hy,y',hy',he2,he1⟩ := h
  exact ⟨x,hx,x',hx',y,hy,y',hy',Or.inr ⟨he2,he1⟩⟩

lemma dense_coefficients_are_expansion_coefficients (A : Finset ℝ)
    {x x' y y' : ℝ} (hx : x∈A) (hx' : x'∈A) (hy : y∈A) (hy' : y'∈A) :
    OriginalExpansionCoefficients A (x-x') (y-y') :=
  ⟨x,hx,x',hx',y,hy,y',hy',Or.inl ⟨rfl,rfl⟩⟩

/-- Actual small original sum/product covers produce one original popular
carrier whose every gap coefficient expression has a polynomial full-anchor
cover bound. The nine-fold union and all rounding losses are derived. -/
theorem exists_original_nine_sum_cover (A : Finset ℝ) {delta K : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta) (hK : 0 < K)
    (hbox : ∀ a∈A, 1 ≤ a ∧ a ≤ 2)
    (hsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|)
    (hproduct : ((productCells delta A).card : ℝ) ≤ K*A.card)
    (hsum : (((A.product A).image (fun p => rounded delta (p.1+p.2))).card : ℝ) ≤ K*A.card) :
    ∃ b∈A, ∃ V : Finset ℝ, V ⊆ A ∧
      ((1/K)^2/2)*(A.card : ℝ) ≤ V.card ∧
      ∀ (A1 : Finset ℝ) (e1 e2 : ℝ), A1 ⊆ V → OriginalExpansionCoefficients V e1 e2 →
        (((A.product ((A1.product A1).image (fun p => e2*p.1+e1*p.2))).image
          (fun p => rounded delta (b*p.1+p.2))).card : ℝ) ≤
            21*(110592:ℝ)^9*K^36*A.card := by
  obtain ⟨b, hb, V, hVA, hVmass, hmixed⟩ := exists_original_mixed_dilate_family
    A hA hd hK hbox hsep hproduct hsum
  have hN : 0 < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hK1 : 1 ≤ K := by
    have hc := (original_product_incidence_mass A hA hd
      (fun a ha => (hbox a ha).1) hsep).2.2
    have hcR : (A.card : ℝ) ≤ (productCells delta A).card := Nat.cast_le.mpr hc
    nlinarith only [hN,hcR,hproduct]
  have hK4 : 1 ≤ K^4 := one_le_pow₀ hK1
  have hKpow : K ≤ K^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK1 (show (1:ℕ) ≤ 4 by norm_num)
  refine ⟨b, hb, V, hVA, hVmass, ?_⟩
  intro A1 e1 e2 hA1 hcoeff
  obtain ⟨x, hx, x', hx', y, hy, y', hy', hpattern⟩ := hcoeff
  let f : Fin 6 → ℝ := ![0,b,x,-x',y,-y']
  let J : Finset ℝ := Finset.univ.image f
  let U := dilateUnion A J
  let X := dilateCells delta A b
  let M : ℝ := 18432*K^4
  have hXcard : X.card=A.card := Finset.card_image_of_injOn
    (product_code_injective A hd (hbox b hb).1 hsep)
  have hX : X.Nonempty := Finset.card_pos.mp (by rw [hXcard]; exact hA.card_pos)
  have hJcard : J.card ≤ 6 := by
    have hc := Finset.card_image_le (s := (Finset.univ : Finset (Fin 6))) (f := f)
    simpa using hc
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hsmall : ∀ a∈J, ((X+dilateCells delta A a).card : ℝ) ≤ M*X.card := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    rw [hXcard]
    fin_cases i
    · change ((X+dilateCells delta A 0).card : ℝ) ≤ M*A.card
      have hz : dilateCells delta A 0=(0 : Finset ℤ) := by
        change A.image (fun a => rounded delta (0*a))=({0} : Finset ℤ)
        simp only [zero_mul,rounded,zero_div,Int.floor_zero]
        exact Finset.image_const hA 0
      rw [hz, add_zero, hXcard]
      have hm1 : 1 ≤ M := by dsimp [M]; nlinarith only [hK4]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm1 (Nat.cast_nonneg A.card)
    · change ((X+X).card : ℝ) ≤ M*A.card
      have habs : |b| ≤ 2 := abs_le.mpr ⟨by linarith [(hbox b hb).1], (hbox b hb).2⟩
      have hs := original_dilate_selfsum_cover A hd habs
      have hm := mul_le_mul_of_nonneg_left hsum (show (0:ℝ) ≤ 48 by norm_num)
      have hp := mul_le_mul_of_nonneg_right hKpow (Nat.cast_nonneg A.card)
      change ((X+X).card : ℝ) ≤ _ at hs
      dsimp [M]
      nlinarith only [hs,hm,hp,show 0 ≤ K^4*(A.card : ℝ) by positivity]
    · change ((X+dilateCells delta A x).card : ℝ) ≤ M*A.card
      have hp := (hmixed x hx).1
      change ((X+dilateCells delta A x).card : ℝ) ≤ _ at hp
      dsimp [M]
      nlinarith only [hp,show 0 ≤ K^4*(A.card : ℝ) by positivity]
    · change ((X+dilateCells delta A (-x')).card : ℝ) ≤ M*A.card
      exact (hmixed x' hx').2.2
    · change ((X+dilateCells delta A y).card : ℝ) ≤ M*A.card
      have hp := (hmixed y hy).1
      change ((X+dilateCells delta A y).card : ℝ) ≤ _ at hp
      dsimp [M]
      nlinarith only [hp,show 0 ≤ K^4*(A.card : ℝ) by positivity]
    · change ((X+dilateCells delta A (-y')).card : ℝ) ≤ M*A.card
      exact (hmixed y' hy').2.2
  have hmem (i : Fin 6) (a : ℝ) (ha : a∈A) : f i*a∈U :=
    Finset.mem_biUnion.mpr ⟨f i, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      Finset.mem_image_of_mem _ ha⟩
  obtain ⟨a0, ha0⟩ := hA
  have hzero : 0∈U := by simpa [f] using hmem 0 a0 ha0
  have hanchor : ∀ a∈A, b*a∈U := fun a ha => by simpa [f] using hmem 1 a ha
  have hxp : ∀ a∈A, x*a∈U := fun a ha => by simpa [f] using hmem 2 a ha
  have hxn : ∀ a∈A, (-x')*a∈U := fun a ha => by simpa [f] using hmem 3 a ha
  have hyp : ∀ a∈A, y*a∈U := fun a ha => by simpa [f] using hmem 4 a ha
  have hyn : ∀ a∈A, (-y')*a∈U := fun a ha => by simpa [f] using hmem 5 a ha
  have htarget : (A.product ((A1.product A1).image (fun p => e2*p.1+e1*p.2))).image
      (fun p => b*p.1+p.2) ⊆ 9 • U := by
    rcases hpattern with ⟨he2,he1⟩ | ⟨he2,he1⟩
    · rw [he2,he1]
      exact original_dense_target_subset_nine A A1 U (hA1.trans hVA) hzero hanchor hxp hxn hyp hyn
    · exact original_gap_target_subset_nine A A1 U (hA1.trans hVA) hzero hanchor hxp hxn hyp hyn he2 he1
  have himage := Finset.image_subset_image (f := rounded delta) htarget
  have htargetcard : (((A.product ((A1.product A1).image (fun p => e2*p.1+e1*p.2))).image
      (fun p => rounded delta (b*p.1+p.2))).card : ℝ) ≤
      (((9 • U).image (rounded delta)).card : ℝ) := by
    have hc := Finset.card_le_card himage
    simp only [Finset.image_image] at hc
    exact_mod_cast hc
  have hiter := original_dilate_union_iterated_cover A J X hd hX hsmall 9
  rw [hXcard] at hiter
  norm_num only at hiter
  have hJcardR : (J.card : ℝ) ≤ 6 := by exact_mod_cast hJcard
  have hbase : (J.card : ℝ)*M ≤ 110592*K^4 := by
    have hm := mul_le_mul_of_nonneg_right hJcardR hM0
    dsimp [M] at hm ⊢
    nlinarith only [hm]
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg J.card) hM0) hbase 9
  calc
    _ ≤ (((9 • U).image (rounded delta)).card : ℝ) := htargetcard
    _ ≤ 21*((J.card : ℝ)*M)^9*A.card := hiter
    _ ≤ 21*(110592*K^4)^9*A.card := by
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (show (0:ℝ) ≤ 21 by norm_num)) (Nat.cast_nonneg A.card)
      exact hm
    _ = _ := by ring

end GKZOriginalNineSumCover
