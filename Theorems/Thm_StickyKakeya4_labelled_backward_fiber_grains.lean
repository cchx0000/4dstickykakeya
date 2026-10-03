import Theorems.Thm_StickyKakeya4_backward_fiber_grains

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace BackwardFiberGrains

variable {E α : Type*} [AddCommGroup E] [Module ℝ E]

/-- Original occurrence labels in an affine plane. Distinct labels may share a point. -/
def labelledAffineFiber (B : Finset α) (x : α → E) (P : Submodule ℝ E) (y : E) : Finset α :=
  B.filter fun a => x a - y ∈ P

/-- The quotient class does not identify occurrence labels inside the finite sum. -/
theorem labelled_classMass_eq (B : Finset α) (x : α → E) (P : Submodule ℝ E)
    (w : α → ℝ) (a : α) :
    classMass B (P.mkQ ∘ x) w ((P.mkQ ∘ x) a) =
      ∑ b ∈ labelledAffineFiber B x P (x a), w b := by
  unfold classMass labelledAffineFiber
  congr 1
  ext b
  simp [Function.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]

/-- Count geometric grain planes using the geometric image of the labelled configuration. -/
theorem labelled_grain_count_mul_le (A : Finset E) (B : Finset α) (x : α → E)
    (P : Submodule ℝ E) (q : ℕ)
    (hgrain : ∀ a ∈ B, q ≤ (affineFiber A P (x a)).card) :
    (B.image (P.mkQ ∘ x)).card * q ≤ A.card := by
  have h := affine_grain_count_mul_le A (B.image x) P q ?_
  · simpa only [affineGrains, Finset.image_image, Function.comp_def] using h
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact hgrain a ha

/-- Dense grain retention on the original occurrence space, with repeated geometric points.
Every selected plane retains exactly its entire original labelled weight. -/
theorem labelled_dense_affine_grains (A : Finset E) (B : Finset α) (x : α → E)
    (P : Submodule ℝ E) (q : ℕ) (hq : 0 < q)
    (hgrain : ∀ a ∈ B, q ≤ (affineFiber A P (x a)).card)
    (w : α → ℝ) (hw : ∀ a ∈ B, 0 ≤ w a) (hM : 0 < ∑ a ∈ B, w a) :
    let f := P.mkQ ∘ x
    let M := ∑ a ∈ B, w a
    let t := M * q / (2 * A.card)
    let R := denseClassRestriction B f w t
    (B.image f).card ≤ A.card / q ∧ R ⊆ B ∧ M / 2 ≤ ∑ a ∈ R, w a ∧
      ∀ a ∈ R,
        t ≤ ∑ b ∈ labelledAffineFiber B x P (x a), w b ∧
        (∑ b ∈ labelledAffineFiber R x P (x a), w b) =
          ∑ b ∈ labelledAffineFiber B x P (x a), w b := by
  dsimp only
  have hB : B.Nonempty := by
    by_contra h
    have hempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hempty, Finset.sum_empty, lt_self_iff_false] at hM
  obtain ⟨a, ha⟩ := hB
  have hA : 0 < A.card := lt_of_lt_of_le hq
    ((hgrain a ha).trans (Finset.card_filter_le A (fun b => b - x a ∈ P)))
  have hcount := labelled_grain_count_mul_le A B x P q hgrain
  have hret := dense_class_retains_half B (P.mkQ ∘ x) w A.card q hA hw hM hcount
  refine ⟨(Nat.le_div_iff_mul_le hq).mpr hcount, Finset.filter_subset _ _, hret.1, ?_⟩
  intro a ha
  have heq := retained_classMass_eq B (P.mkQ ∘ x) w _ a ha
  rw [labelled_classMass_eq, labelled_classMass_eq] at heq
  refine ⟨?_, heq⟩
  have hdense := hret.2 a ha
  rw [labelled_classMass_eq, heq] at hdense
  exact hdense

/-- The independent predecessor geometry yields dense grains directly on arbitrary original
occurrence labels. No injectivity of the geometry map and no aggregation hypothesis is needed. -/
theorem labelled_independent_dense_grains {n : ℕ} (v : Fin n → E)
    (hv : LinearIndependent ℝ v) (A : ℕ → Finset E) (L : ℕ → ℕ)
    (hpred : ∀ i : Fin n, ∀ y ∈ A (i.val + 1),
      L i.val ≤ (affineFiber (A i.val) (Submodule.span ℝ {v i}) y).card)
    (hq : 0 < ∏ i ∈ Finset.range n, L i)
    (B : Finset α) (x : α → E) (hx : ∀ a ∈ B, x a ∈ A n)
    (w : α → ℝ) (hw : ∀ a ∈ B, 0 ≤ w a) (hM : 0 < ∑ a ∈ B, w a) :
    let P := Submodule.span ℝ (Set.range v)
    let q := ∏ i ∈ Finset.range n, L i
    let f := P.mkQ ∘ x
    let M := ∑ a ∈ B, w a
    let t := M * q / (2 * (A 0).card)
    let R := denseClassRestriction B f w t
    (B.image f).card ≤ (A 0).card / q ∧ R ⊆ B ∧ M / 2 ≤ ∑ a ∈ R, w a ∧
      ∀ a ∈ R,
        t ≤ ∑ b ∈ labelledAffineFiber B x P (x a), w b ∧
        (∑ b ∈ labelledAffineFiber R x P (x a), w b) =
          ∑ b ∈ labelledAffineFiber B x P (x a), w b := by
  exact labelled_dense_affine_grains (A 0) B x (Submodule.span ℝ (Set.range v)) _ hq
    (fun a ha => independent_backward_fiber_bound v hv A L hpred (x a) (hx a ha)) w hw hM

end BackwardFiberGrains
