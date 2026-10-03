import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace BackwardFiberGrains

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The original finite points lying in the affine plane `x + P`. -/
def affineFiber (A : Finset E) (P : Submodule ℝ E) (x : E) : Finset E := by
  classical
  exact A.filter fun a => a - x ∈ P

@[simp] theorem mem_affineFiber (A : Finset E) (P : Submodule ℝ E) (x a : E) :
    a ∈ affineFiber A P x ↔ a ∈ A ∧ a - x ∈ P := by
  classical
  simp [affineFiber]

/-- Independent predecessor directions give disjoint translates of the previous span. -/
theorem predecessor_fibers_disjoint (A B : Finset E) (P Q : Submodule ℝ E) (x : E)
    (hPQ : Disjoint P Q) (hB : ∀ y ∈ B, y - x ∈ Q) :
    (B : Set E).PairwiseDisjoint (affineFiber A P) := by
  classical
  intro y hy z hz hyz
  apply Finset.disjoint_left.mpr
  intro a hay haz
  have hayP := (mem_affineFiber A P y a).mp hay |>.2
  have hazP := (mem_affineFiber A P z a).mp haz |>.2
  have hzyP : z - y ∈ P := by
    convert P.sub_mem hayP hazP using 1; abel
  have hzyQ : z - y ∈ Q := by
    convert Q.sub_mem (hB z hz) (hB y hy) using 1; abel
  exact hyz (sub_eq_zero.mp (Submodule.disjoint_def.mp hPQ _ hzyP hzyQ)).symm

/-- One genuine geometric multiplication step; no final fiber bound is assumed. -/
theorem backward_fiber_step (A B : Finset E) (P Q : Submodule ℝ E) (x : E) (q : ℕ)
    (hPQ : Disjoint P Q) (hB : ∀ y ∈ B, y - x ∈ Q)
    (hq : ∀ y ∈ B, q ≤ (affineFiber A P y).card) :
    B.card * q ≤ (affineFiber A (P ⊔ Q) x).card := by
  classical
  have hsub : B.biUnion (affineFiber A P) ⊆ affineFiber A (P ⊔ Q) x := by
    intro a ha
    obtain ⟨y, hy, hay⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨haA, hayP⟩ := (mem_affineFiber A P y a).mp hay
    apply (mem_affineFiber A (P ⊔ Q) x a).mpr
    refine ⟨haA, ?_⟩
    have h := (P ⊔ Q).add_mem
      ((show P ≤ P ⊔ Q from le_sup_left) hayP)
      ((show Q ≤ P ⊔ Q from le_sup_right) (hB y hy))
    convert h using 1; abel
  calc
    B.card * q = ∑ y ∈ B, q := by simp
    _ ≤ ∑ y ∈ B, (affineFiber A P y).card := Finset.sum_le_sum hq
    _ = (B.biUnion (affineFiber A P)).card :=
      (Finset.card_biUnion (predecessor_fibers_disjoint A B P Q x hPQ hB)).symm
    _ ≤ (affineFiber A (P ⊔ Q) x).card := Finset.card_le_card hsub

/-- Layered exact-coordinate backward fibers. The layers need not be nested. -/
theorem layered_backward_fiber_bound (A : ℕ → Finset E) (P Q : ℕ → Submodule ℝ E)
    (L : ℕ → ℕ) (n : ℕ) (hP0 : P 0 = ⊥)
    (hPQ : ∀ i < n, Disjoint (P i) (Q i))
    (hPs : ∀ i < n, P (i + 1) = P i ⊔ Q i)
    (hpred : ∀ i < n, ∀ x ∈ A (i + 1), L i ≤ (affineFiber (A i) (Q i) x).card) :
    ∀ x ∈ A n, (∏ i ∈ Finset.range n, L i) ≤ (affineFiber (A 0) (P n) x).card := by
  classical
  induction n with
  | zero =>
      intro x hx
      simp only [Finset.range_zero, Finset.prod_empty]
      apply Finset.one_le_card.mpr
      refine ⟨x, ?_⟩
      simp [hx, hP0]
  | succ n ih =>
      intro x hx
      have hi := ih (fun i hi => hPQ i (by omega)) (fun i hi => hPs i (by omega))
        (fun i hi => hpred i (by omega))
      rw [Finset.prod_range_succ, hPs n (by omega)]
      calc
        (∏ i ∈ Finset.range n, L i) * L n
          ≤ (affineFiber (A n) (Q n) x).card * (∏ i ∈ Finset.range n, L i) := by
            rw [Nat.mul_comm]
            exact Nat.mul_le_mul_right _ (hpred n (by omega) x hx)
        _ ≤ (affineFiber (A 0) (P n ⊔ Q n) x).card := by
          apply backward_fiber_step (A 0) (affineFiber (A n) (Q n) x)
            (P n) (Q n) x _ (hPQ n (by omega))
          · intro y hy
            exact (mem_affineFiber _ _ _ _).mp hy |>.2
          · intro y hy
            exact hi y ((mem_affineFiber _ _ _ _).mp hy |>.1)

/-- Span of the first `i` members of a finite vector family. -/
def prefixSpan {n : ℕ} (v : Fin n → E) (i : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (v '' {j | j.val < i})

/-- The individual direction at index `i`, empty outside the finite index range. -/
def directionSpan {n : ℕ} (v : Fin n → E) (i : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (v '' {j | j.val = i})

@[simp] theorem prefixSpan_zero {n : ℕ} (v : Fin n → E) : prefixSpan v 0 = ⊥ := by
  simp [prefixSpan]

theorem prefixSpan_succ {n : ℕ} (v : Fin n → E) (i : ℕ) :
    prefixSpan v (i + 1) = prefixSpan v i ⊔ directionSpan v i := by
  have hs : {j : Fin n | j.val < i + 1} =
      {j : Fin n | j.val < i} ∪ {j : Fin n | j.val = i} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    omega
  simp only [prefixSpan, directionSpan, hs, Set.image_union, Submodule.span_union]

theorem directionSpan_eq {n : ℕ} (v : Fin n → E) (i : Fin n) :
    directionSpan v i.val = Submodule.span ℝ {v i} := by
  have hs : {j : Fin n | j.val = i.val} = {i} := by
    ext j
    simp [Fin.ext_iff]
  simp [directionSpan, hs]

@[simp] theorem prefixSpan_full {n : ℕ} (v : Fin n → E) :
    prefixSpan v n = Submodule.span ℝ (Set.range v) := by
  simp [prefixSpan]

theorem independent_prefix_direction_disjoint {n : ℕ} (v : Fin n → E)
    (hv : LinearIndependent ℝ v) (i : ℕ) :
    Disjoint (prefixSpan v i) (directionSpan v i) := by
  apply hv.disjoint_span_image
  apply Set.disjoint_left.mpr
  intro j hj hj'
  simp only [Set.mem_ofPred_eq] at hj hj'
  omega

/-- The backward-fiber grain theorem for a genuinely linearly independent finite family.
Every predecessor lies on the exact affine line in the indicated direction. -/
theorem independent_backward_fiber_bound {n : ℕ} (v : Fin n → E)
    (hv : LinearIndependent ℝ v) (A : ℕ → Finset E) (L : ℕ → ℕ)
    (hpred : ∀ i : Fin n, ∀ x ∈ A (i.val + 1),
      L i.val ≤ (affineFiber (A i.val) (Submodule.span ℝ {v i}) x).card) :
    ∀ x ∈ A n, (∏ i ∈ Finset.range n, L i) ≤
      (affineFiber (A 0) (Submodule.span ℝ (Set.range v)) x).card := by
  have h := layered_backward_fiber_bound A (prefixSpan v) (directionSpan v) L n
    (prefixSpan_zero v) (fun i _ => independent_prefix_direction_disjoint v hv i)
    (fun i _ => prefixSpan_succ v i) ?_
  · simpa only [prefixSpan_full] using h
  · intro i hi x hx
    simpa only [directionSpan_eq v ⟨i, hi⟩] using hpred ⟨i, hi⟩ x hx

/-- Distinct affine `P`-planes meeting the final layer, represented canonically by the quotient. -/
def affineGrains (B : Finset E) (P : Submodule ℝ E) : Finset (E ⧸ P) := by
  classical
  exact B.image P.mkQ

theorem affineFiber_eq_quotient_filter (A : Finset E) (P : Submodule ℝ E) (x : E) :
    affineFiber A P x = A.filter (fun a => P.mkQ a = P.mkQ x) := by
  classical
  ext a
  simp [affineFiber, Submodule.mkQ_apply, Submodule.Quotient.eq]

/-- The backward fibers bound the number of distinct affine grain planes. -/
theorem affine_grain_count_mul_le (A B : Finset E) (P : Submodule ℝ E) (q : ℕ)
    (hgrain : ∀ x ∈ B, q ≤ (affineFiber A P x).card) :
    (affineGrains B P).card * q ≤ A.card := by
  classical
  calc
    (affineGrains B P).card * q = ∑ c ∈ affineGrains B P, q := by simp
    _ ≤ ∑ c ∈ affineGrains B P, (A.filter (fun a => P.mkQ a = c)).card := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
      simpa only [affineFiber_eq_quotient_filter] using hgrain x hx
    _ = (A.filter (fun a => P.mkQ a ∈ affineGrains B P)).card :=
      Finset.sum_card_fiberwise_eq_card_filter A (affineGrains B P) P.mkQ
    _ ≤ A.card := Finset.card_filter_le _ _

/-- Integer-division form of the bound on the number of planes meeting the final layer. -/
theorem affine_grain_count_le_div (A B : Finset E) (P : Submodule ℝ E) (q : ℕ)
    (hq : 0 < q) (hgrain : ∀ x ∈ B, q ≤ (affineFiber A P x).card) :
    (affineGrains B P).card ≤ A.card / q := by
  exact (Nat.le_div_iff_mul_le hq).mpr (affine_grain_count_mul_le A B P q hgrain)

section Weighted

variable {α β : Type*}

/-- Original mass of one class, with no relabeling or reweighting. -/
def classMass (B : Finset α) (f : α → β) (w : α → ℝ) (c : β) : ℝ :=
  ∑ a ∈ B.filter (fun a => f a = c), w a

/-- Keep precisely the original labels whose entire original class is dense. -/
def denseClassRestriction (B : Finset α) (f : α → β) (w : α → ℝ) (t : ℝ) : Finset α :=
  B.filter fun a => t ≤ classMass B f w (f a)

theorem sum_classMass (B : Finset α) (f : α → β) (w : α → ℝ) :
    ∑ c ∈ B.image f, classMass B f w c = ∑ a ∈ B, w a := by
  exact Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) w

theorem sum_denseClassRestriction (B : Finset α) (f : α → β) (w : α → ℝ) (t : ℝ) :
    ∑ a ∈ denseClassRestriction B f w t, w a =
      ∑ c ∈ (B.image f).filter (fun c => t ≤ classMass B f w c), classMass B f w c := by
  symm
  calc
    _ = ∑ a ∈ B.filter (fun a => f a ∈ (B.image f).filter
        (fun c => t ≤ classMass B f w c)), w a :=
      Finset.sum_fiberwise_eq_sum_filter B
        ((B.image f).filter (fun c => t ≤ classMass B f w c)) f w
    _ = _ := by
      congr 1
      ext a
      simp only [denseClassRestriction, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨ha, _, ht⟩
        exact ⟨ha, ht⟩
      · rintro ⟨ha, ht⟩
        exact ⟨ha, ⟨⟨a, ha, rfl⟩, ht⟩⟩

/-- Restricting by whole classes retains their original mass exactly. -/
theorem retained_classMass_eq (B : Finset α) (f : α → β) (w : α → ℝ) (t : ℝ)
    (a : α) (ha : a ∈ denseClassRestriction B f w t) :
    classMass (denseClassRestriction B f w t) f w (f a) = classMass B f w (f a) := by
  have ht : t ≤ classMass B f w (f a) := (Finset.mem_filter.mp ha).2
  unfold classMass
  congr 1
  ext b
  simp only [denseClassRestriction, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hb, _⟩, hba⟩
    exact ⟨hb, hba⟩
  · rintro ⟨hb, hba⟩
    exact ⟨⟨hb, by simpa only [hba] using ht⟩, hba⟩

/-- Safe dense-class retention from an actual class-count bound.
The selected finset consists of original labels, and every sum uses the original weight. -/
theorem dense_class_retains_half (B : Finset α) (f : α → β) (w : α → ℝ)
    (N q : ℕ) (hN : 0 < N) (hw : ∀ a ∈ B, 0 ≤ w a)
    (hM : 0 < ∑ a ∈ B, w a) (hcount : (B.image f).card * q ≤ N) :
    let M := ∑ a ∈ B, w a
    let t := M * q / (2 * N)
    let R := denseClassRestriction B f w t
    M / 2 ≤ ∑ a ∈ R, w a ∧ ∀ a ∈ R, t ≤ classMass R f w (f a) := by
  dsimp only
  let M := ∑ a ∈ B, w a
  let t := M * q / (2 * N)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have ht : 0 ≤ t :=
    div_nonneg (mul_nonneg (Finset.sum_nonneg hw) (Nat.cast_nonneg q)) (by positivity)
  have hcr : ((B.image f).card : ℝ) * q ≤ N := by exact_mod_cast hcount
  have hsmall : ((B.image f).card : ℝ) * t ≤ M / 2 := by
    dsimp only [t]
    calc
      _ = (M * (((B.image f).card : ℝ) * q)) / (2 * N) := by ring
      _ ≤ (M * N) / (2 * N) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcr (le_of_lt hM)) (by positivity)
      _ = M / 2 := mul_div_mul_right M 2 (ne_of_gt hNr)
  have hdiscard :
      ∑ c ∈ (B.image f).filter (fun c => ¬t ≤ classMass B f w c), classMass B f w c
        ≤ M / 2 := by
    calc
      _ ≤ ∑ c ∈ (B.image f).filter (fun c => ¬t ≤ classMass B f w c), t := by
        apply Finset.sum_le_sum
        intro c hc
        exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hc).2)
      _ = (((B.image f).filter (fun c => ¬t ≤ classMass B f w c)).card : ℝ) * t := by simp
      _ ≤ ((B.image f).card : ℝ) * t := by
        apply mul_le_mul_of_nonneg_right _ ht
        exact_mod_cast Finset.card_filter_le (B.image f) (fun c => ¬t ≤ classMass B f w c)
      _ ≤ M / 2 := hsmall
  have hpartition := Finset.sum_filter_add_sum_filter_not (B.image f)
    (fun c => t ≤ classMass B f w c) (classMass B f w)
  rw [sum_classMass, ← sum_denseClassRestriction] at hpartition
  constructor
  · change M / 2 ≤ ∑ a ∈ denseClassRestriction B f w t, w a
    change _ + _ = M at hpartition
    linarith
  · intro a ha
    rw [retained_classMass_eq B f w _ a ha]
    exact (Finset.mem_filter.mp ha).2

end Weighted

/-- Dense exact affine grains, retaining at least half the original final-layer mass.
The retained set is a subset of the original labels, and `w` is never modified. -/
theorem dense_affine_grains (A B : Finset E) (P : Submodule ℝ E) (q : ℕ)
    (hq : 0 < q) (hgrain : ∀ x ∈ B, q ≤ (affineFiber A P x).card)
    (w : E → ℝ) (hw : ∀ x ∈ B, 0 ≤ w x) (hM : 0 < ∑ x ∈ B, w x) :
    let M := ∑ x ∈ B, w x
    let t := M * q / (2 * A.card)
    let R := denseClassRestriction B P.mkQ w t
    (affineGrains B P).card ≤ A.card / q ∧ R ⊆ B ∧
      M / 2 ≤ ∑ x ∈ R, w x ∧ ∀ x ∈ R, t ≤ ∑ a ∈ affineFiber R P x, w a := by
  dsimp only
  have hB : B.Nonempty := by
    by_contra h
    have hempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hempty, Finset.sum_empty, lt_self_iff_false] at hM
  obtain ⟨x, hx⟩ := hB
  have hA : 0 < A.card := lt_of_lt_of_le hq
    ((hgrain x hx).trans (Finset.card_filter_le A (fun a => a - x ∈ P)))
  have hret := dense_class_retains_half B P.mkQ w A.card q hA hw hM
    (affine_grain_count_mul_le A B P q hgrain)
  refine ⟨affine_grain_count_le_div A B P q hq hgrain, Finset.filter_subset _ _, hret.1, ?_⟩
  intro y hy
  rw [affineFiber_eq_quotient_filter]
  exact hret.2 y hy

/-- Full exact-coordinate Step-5 grain conclusion from independent predecessor directions.
This does not assert any adapter from approximate tubes or construct the rich layers. -/
theorem independent_dense_grains {n : ℕ} (v : Fin n → E)
    (hv : LinearIndependent ℝ v) (A : ℕ → Finset E) (L : ℕ → ℕ)
    (hpred : ∀ i : Fin n, ∀ x ∈ A (i.val + 1),
      L i.val ≤ (affineFiber (A i.val) (Submodule.span ℝ {v i}) x).card)
    (hq : 0 < ∏ i ∈ Finset.range n, L i)
    (w : E → ℝ) (hw : ∀ x ∈ A n, 0 ≤ w x) (hM : 0 < ∑ x ∈ A n, w x) :
    let P := Submodule.span ℝ (Set.range v)
    let q := ∏ i ∈ Finset.range n, L i
    let M := ∑ x ∈ A n, w x
    let t := M * q / (2 * (A 0).card)
    let R := denseClassRestriction (A n) P.mkQ w t
    (affineGrains (A n) P).card ≤ (A 0).card / q ∧ R ⊆ A n ∧
      M / 2 ≤ ∑ x ∈ R, w x ∧ ∀ x ∈ R, t ≤ ∑ a ∈ affineFiber R P x, w a := by
  exact dense_affine_grains (A 0) (A n) (Submodule.span ℝ (Set.range v)) _ hq
    (independent_backward_fiber_bound v hv A L hpred) w hw hM

end BackwardFiberGrains
