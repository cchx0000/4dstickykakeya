import Theorems.Thm_StickyKakeya4_dyadic_height_boundary_padding

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

namespace DyadicHeightCutoffSelection

open DyadicHeightBoundaryPadding

noncomputable section

/-- Select the first ACTUAL working scale above the threshold. Its preceding
working scale gives the upper range; neither endpoint is a certificate. -/
theorem exists_working_cutoff (E : Finset ℕ) (M : ℕ) (G T : ℝ)
    (hzero : 0 ∈ E) (hroot : M ∈ E) (hG : 1 ≤ G) (hT : 1 ≤ T)
    (htop : T ≤ (2 ^ M : ℕ))
    (hgap : ∀ a ∈ E, ∀ b ∈ E, a < b →
      (∀ e ∈ E, a < e → e < b → False) → (2 ^ b : ℕ) ≤ G * (2 ^ a : ℕ)) :
    ∃ e ∈ E, e ≤ M ∧ T ≤ (2 ^ e : ℕ) ∧ (2 ^ e : ℕ) ≤ G * T := by
  classical
  let A := E.filter (fun e => T ≤ (2 ^ e : ℕ))
  have hA : A.Nonempty := ⟨M, Finset.mem_filter.mpr ⟨hroot, htop⟩⟩
  let e := A.min' hA
  have heA : e ∈ A := Finset.min'_mem A hA
  obtain ⟨heE, hTe⟩ := Finset.mem_filter.mp heA
  have heM : e ≤ M := Finset.min'_le A M (Finset.mem_filter.mpr ⟨hroot, htop⟩)
  refine ⟨e, heE, heM, hTe, ?_⟩
  by_cases hezero : e = 0
  · have hprod : (1 : ℝ) ≤ G * T := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ G * T := mul_le_mul hG hT (by norm_num) (by linarith only [hG])
    simpa [hezero] using hprod
  · let D := E.filter (fun a => a < e)
    have hD : D.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨hzero, Nat.pos_of_ne_zero hezero⟩⟩
    let a := D.max' hD
    have haD : a ∈ D := Finset.max'_mem D hD
    obtain ⟨haE, hae⟩ := Finset.mem_filter.mp haD
    have hbelow : (2 ^ a : ℕ) < T := by
      by_contra h
      have haA : a ∈ A := Finset.mem_filter.mpr ⟨haE, le_of_not_gt h⟩
      have hh : e ≤ a := Finset.min'_le A a haA
      omega
    have hadj : ∀ f ∈ E, a < f → f < e → False := by
      intro f hf haf hfe
      have hfD : f ∈ D := Finset.mem_filter.mpr ⟨hf, hfe⟩
      have hh : f ≤ a := Finset.le_max' D f hfD
      omega
    exact (hgap a haE e heE hae hadj).trans
      (mul_le_mul_of_nonneg_left hbelow.le (by linarith only [hG]))

/-- The full original working grid constructs its cutoff and retained levels
before applying the proved original-height padding theorem. -/
theorem padded_lipschitz_of_feasible_cutoff {X : Type*} [PseudoMetricSpace X]
    (B E : Finset ℕ) (M : ℕ) (K G q lam : ℝ) (F : ℕ → X)
    (hB : B ⊆ Finset.range (2 ^ M)) (hE : ∀ e ∈ E, e ≤ M)
    (hzero : 0 ∈ E) (hroot : M ∈ E)
    (hK : 0 ≤ K) (hG : 1 ≤ G) (hq : 0 < q) (hqone : q < 1) (hlam : 0 < lam)
    (hdensity : lam * (2 ^ M : ℕ) ≤ (B.card : ℝ))
    (hfeasible : 8 ≤ q * lam * (2 ^ M : ℕ))
    (hgap : ∀ a ∈ E, ∀ b ∈ E, a < b →
      (∀ e ∈ E, a < e → e < b → False) → (2 ^ b : ℕ) ≤ G * (2 ^ a : ℕ))
    (hosc : ∀ e ∈ E, ∀ n ∈ B, ∀ m ∈ B, n / 2 ^ e = m / 2 ^ e →
      dist (F n) (F m) ≤ K * (((2 ^ e : ℕ) : ℝ) / ((2 ^ M : ℕ) : ℝ))) :
    ∃ S ⊆ B, S.Nonempty ∧ (1 - q) * (B.card : ℝ) ≤ (S.card : ℝ) ∧
      ∀ n ∈ S, ∀ m ∈ S,
        dist (F n) (F m) ≤ lipschitzConstant E K G q lam * |height M n - height M m| := by
  classical
  have hN : (0 : ℝ) < (2 ^ M : ℕ) := by positivity
  have hqlam : 0 < q * lam := mul_pos hq hlam
  have hcard : (B.card : ℝ) ≤ (2 ^ M : ℕ) := by
    exact_mod_cast (Finset.card_le_card hB).trans_eq (Finset.card_range _)
  have hlamone : lam ≤ 1 := by
    apply (mul_le_mul_iff_left₀ hN).mp
    simpa only [one_mul] using hdensity.trans hcard
  have hqlamone : q * lam ≤ 1 := by
    calc
      q * lam ≤ 1 * lam := mul_le_mul_of_nonneg_right hqone.le hlam.le
      _ ≤ 1 := by simpa only [one_mul] using hlamone
  have hT : (1 : ℝ) ≤ 8 / (q * lam) := (le_div_iff₀ hqlam).mpr (by linarith only [hqlamone])
  have htop : 8 / (q * lam) ≤ (2 ^ M : ℕ) := (div_le_iff₀ hqlam).mpr (by nlinarith only [hfeasible])
  obtain ⟨e₀, he₀, heM, hlo, hhi⟩ := exists_working_cutoff E M G (8 / (q * lam)) hzero hroot hG hT htop hgap
  let E' := E.filter (fun e => e₀ ≤ e)
  have hE'sub : E' ⊆ E := Finset.filter_subset _ _
  have hE' : ∀ e ∈ E', e₀ ≤ e ∧ e ≤ M := by
    intro e he
    obtain ⟨heE, hloe⟩ := Finset.mem_filter.mp he
    exact ⟨hloe, hE e heE⟩
  have hroot' : M ∈ E' := Finset.mem_filter.mpr ⟨hroot, heM⟩
  have hmin' : e₀ ∈ E' := Finset.mem_filter.mpr ⟨he₀, le_rfl⟩
  have hgap' : ∀ a ∈ E', ∀ b ∈ E', a < b →
      (∀ e ∈ E', a < e → e < b → False) → (2 ^ b : ℕ) ≤ G * (2 ^ a : ℕ) := by
    intro a ha b hb hab hadj
    apply hgap a (hE'sub ha) b (hE'sub hb) hab
    intro e he hae heb
    have hea : e₀ ≤ e := (hE' a ha).1.trans hae.le
    exact hadj e (Finset.mem_filter.mpr ⟨he, hea⟩) hae heb
  have hcutoff : 8 ≤ q * lam * (2 ^ e₀ : ℕ) := by
    have hh := (div_le_iff₀ hqlam).mp hlo
    nlinarith only [hh]
  have hupper : q * lam * (2 ^ e₀ : ℕ) ≤ 8 * G := by
    have heq : G * (8 / (q * lam)) = 8 * G / (q * lam) := by ring
    rw [heq] at hhi
    have hh := (le_div_iff₀ hqlam).mp hhi
    nlinarith only [hh]
  obtain ⟨S, hSB, hSne, hret, _, hlip⟩ :=
    DyadicHeightBoundaryPadding.exists_padded_lipschitz B E' M e₀ K G q lam F hB hE'
      hroot' hmin' hK hG hq hqone hlam hdensity hcutoff hupper hgap'
      (fun e he => hosc e (hE'sub he))
  have hC : lipschitzConstant E' K G q lam ≤ lipschitzConstant E K G q lam := by
    unfold lipschitzConstant
    apply div_le_div_of_nonneg_right _ hqlam.le
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hE'sub)) (by positivity)
  refine ⟨S, hSB, hSne, hret, ?_⟩
  intro n hn m hm
  exact (hlip n hn m hm).trans (mul_le_mul_of_nonneg_right hC (abs_nonneg _))

/-- Complete root-scale endpoint: when the cutoff is above the root, keeping
all original heights already has the claimed Lipschitz constant. Otherwise
the actual working-cutoff and boundary-deletion construction is used. -/
theorem exists_padded_lipschitz_from_full_grid {X : Type*} [PseudoMetricSpace X]
    (B E : Finset ℕ) (M : ℕ) (K G q lam : ℝ) (F : ℕ → X)
    (hB : B ⊆ Finset.range (2 ^ M)) (hE : ∀ e ∈ E, e ≤ M)
    (hzero : 0 ∈ E) (hroot : M ∈ E)
    (hK : 0 ≤ K) (hG : 1 ≤ G) (hq : 0 < q) (hqone : q < 1) (hlam : 0 < lam)
    (hdensity : lam * (2 ^ M : ℕ) ≤ (B.card : ℝ))
    (hgap : ∀ a ∈ E, ∀ b ∈ E, a < b →
      (∀ e ∈ E, a < e → e < b → False) → (2 ^ b : ℕ) ≤ G * (2 ^ a : ℕ))
    (hosc : ∀ e ∈ E, ∀ n ∈ B, ∀ m ∈ B, n / 2 ^ e = m / 2 ^ e →
      dist (F n) (F m) ≤ K * (((2 ^ e : ℕ) : ℝ) / ((2 ^ M : ℕ) : ℝ))) :
    ∃ S ⊆ B, S.Nonempty ∧ (1 - q) * (B.card : ℝ) ≤ (S.card : ℝ) ∧
      ∀ n ∈ S, ∀ m ∈ S,
        dist (F n) (F m) ≤ lipschitzConstant E K G q lam * |height M n - height M m| := by
  by_cases hfeasible : 8 ≤ q * lam * (2 ^ M : ℕ)
  · exact padded_lipschitz_of_feasible_cutoff B E M K G q lam F hB hE hzero hroot
      hK hG hq hqone hlam hdensity hfeasible hgap hosc
  · have hN : (0 : ℝ) < (2 ^ M : ℕ) := by positivity
    have hqlam : 0 < q * lam := mul_pos hq hlam
    have hneE : E.Nonempty := ⟨M, hroot⟩
    have hLone : (1 : ℝ) ≤ E.card := by exact_mod_cast Finset.card_pos.mpr hneE
    have hG0 : 0 ≤ G := by linarith only [hG]
    have hBpos : (0 : ℝ) < B.card := (mul_pos hlam hN).trans_le hdensity
    have hBne : B.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hBpos)
    have hC0 : 0 ≤ lipschitzConstant E K G q lam := by unfold lipschitzConstant; positivity
    have hC : K * (2 ^ M : ℕ) ≤ lipschitzConstant E K G q lam := by
      unfold lipschitzConstant
      apply (le_div_iff₀ hqlam).mpr
      have hsmall : q * lam * (2 ^ M : ℕ) ≤ 8 := (lt_of_not_ge hfeasible).le
      have hsmallK := mul_le_mul_of_nonneg_left hsmall hK
      have hGL : 1 ≤ G * (E.card : ℝ) := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ G * (E.card : ℝ) := mul_le_mul hG hLone (by norm_num) hG0
      have hbound := mul_le_mul_of_nonneg_left hGL (show 0 ≤ 8 * K by positivity)
      nlinarith only [hsmallK, hbound]
    refine ⟨B, Finset.Subset.refl _, hBne, ?_, ?_⟩
    · have hnonneg : 0 ≤ q * (B.card : ℝ) := by positivity
      nlinarith only [hnonneg]
    · intro n hn m hm
      by_cases hnm : n = m
      · subst m
        simp
      have hsame : n / 2 ^ M = m / 2 ^ M := by
        rw [Nat.div_eq_of_lt (Finset.mem_range.mp (hB hn)), Nat.div_eq_of_lt (Finset.mem_range.mp (hB hm))]
      have hrootosc : dist (F n) (F m) ≤ K := by
        simpa only [div_self hN.ne', mul_one] using hosc M hroot n hn m hm hsame
      have hsep := integer_height_separation hnm
      have hcross : (2 ^ M : ℕ) * dist (F n) (F m) ≤
          lipschitzConstant E K G q lam * |(n : ℝ) - (m : ℝ)| := by
        calc
          _ ≤ K * (2 ^ M : ℕ) := by nlinarith only [mul_le_mul_of_nonneg_right hrootosc hN.le]
          _ ≤ lipschitzConstant E K G q lam := hC
          _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsep hC0
      rw [height_difference, ← mul_div_assoc]
      apply (le_div_iff₀ hN).mpr
      nlinarith only [hcross]

end
end DyadicHeightCutoffSelection
