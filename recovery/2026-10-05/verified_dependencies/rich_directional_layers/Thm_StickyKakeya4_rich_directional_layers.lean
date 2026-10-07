import Theorems.Thm_StickyKakeya4_backward_fiber_grains

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace RichDirectionalLayers

variable {α β : Type*}

/-- The current points in a fixed exact partition class. -/
def classFiber (B : Finset α) (f : α → β) (c : β) : Finset α :=
  B.filter fun a => f a = c

/-- Remove all current classes having fewer than `K` current points. -/
def richRestriction (B : Finset α) (f : α → β) (K : ℕ) : Finset α :=
  B.filter fun a => K ≤ (classFiber B f (f a)).card

theorem richRestriction_subset (B : Finset α) (f : α → β) (K : ℕ) :
    richRestriction B f K ⊆ B := Finset.filter_subset _ _

theorem richRestriction_predecessors (B : Finset α) (f : α → β) (K : ℕ)
    (a : α) (ha : a ∈ richRestriction B f K) :
    K ≤ (classFiber B f (f a)).card := (Finset.mem_filter.mp ha).2

/-- A discarded class costs at most `K - 1` points, counted over occupied ambient classes. -/
theorem richRestriction_card_loss (A B : Finset α) (f : α → β) (K : ℕ) (hBA : B ⊆ A) :
    B.card ≤ (richRestriction B f K).card + (A.image f).card * (K - 1) := by
  let D := B.filter fun a => ¬K ≤ (classFiber B f (f a)).card
  have hD : D ⊆ B := Finset.filter_subset _ _
  have hc : ∀ c ∈ A.image f, (classFiber D f c).card ≤ K - 1 := by
    intro c _
    by_cases hne : (classFiber D f c).Nonempty
    · obtain ⟨a, ha⟩ := hne
      obtain ⟨haD, hac⟩ := Finset.mem_filter.mp ha
      have hlow := (Finset.mem_filter.mp haD).2
      have hsub : classFiber D f c ⊆ classFiber B f (f a) := by
        intro b hb
        obtain ⟨hbD, hbc⟩ := Finset.mem_filter.mp hb
        exact Finset.mem_filter.mpr ⟨hD hbD, hbc.trans hac.symm⟩
      have hcard := Finset.card_le_card hsub
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  have hloss : D.card ≤ (A.image f).card * (K - 1) := by
    calc
      D.card = ∑ c ∈ A.image f, (classFiber D f c).card :=
        Finset.card_eq_sum_card_fiberwise (fun a ha => Finset.mem_image_of_mem f (hBA (hD ha)))
      _ ≤ ∑ c ∈ A.image f, (K - 1) := Finset.sum_le_sum hc
      _ = (A.image f).card * (K - 1) := by simp
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := B) (fun a => K ≤ (classFiber B f (f a)).card)
  change (richRestriction B f K).card + D.card = B.card at hpartition
  omega

section Layers

variable {γ : ℕ → Type*}

/-- Explicit sequential pruning, starting from the actual common-tuple point set. -/
def richLayers (E : Finset α) (f : (i : ℕ) → α → γ i) (K : ℕ → ℕ) : ℕ → Finset α
  | 0 => E
  | i + 1 => richRestriction (richLayers E f K i) (f i) (K i)

@[simp] theorem richLayers_zero (E : Finset α) (f : (i : ℕ) → α → γ i) (K : ℕ → ℕ) :
    richLayers E f K 0 = E := rfl

@[simp] theorem richLayers_succ (E : Finset α) (f : (i : ℕ) → α → γ i) (K : ℕ → ℕ) (i : ℕ) :
    richLayers E f K (i + 1) = richRestriction (richLayers E f K i) (f i) (K i) := rfl

theorem richLayers_step_subset (E : Finset α) (f : (i : ℕ) → α → γ i) (K : ℕ → ℕ) (i : ℕ) :
    richLayers E f K (i + 1) ⊆ richLayers E f K i := richRestriction_subset _ _ _

theorem richLayers_subset_start (E : Finset α) (f : (i : ℕ) → α → γ i) (K : ℕ → ℕ) (i : ℕ) :
    richLayers E f K i ⊆ E := by
  induction i with
  | zero => exact Finset.Subset.refl _
  | succ i ih => exact (richLayers_step_subset E f K i).trans ih

theorem richLayers_predecessors (E : Finset α) (f : (i : ℕ) → α → γ i) (K : ℕ → ℕ)
    (i : ℕ) (a : α) (ha : a ∈ richLayers E f K (i + 1)) :
    K i ≤ (classFiber (richLayers E f K i) (f i) (f i a)).card :=
  richRestriction_predecessors _ _ _ a ha

/-- The full deletion cost of the constructed layers, with no assumed rich-core certificate. -/
theorem richLayers_card_loss (A E : Finset α) (hEA : E ⊆ A)
    (f : (i : ℕ) → α → γ i) (K : ℕ → ℕ) (n : ℕ) :
    E.card ≤ (richLayers E f K n).card +
      ∑ i ∈ Finset.range n, (A.image (f i)).card * (K i - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := richRestriction_card_loss A (richLayers E f K n) (f n) (K n)
        ((richLayers_subset_start E f K n).trans hEA)
      rw [Finset.sum_range_succ]
      change E.card ≤ (richRestriction (richLayers E f K n) (f n) (K n)).card + _
      omega

/-- A verified total deletion budget leaves at least half of the starting points. -/
theorem richLayers_half_of_budget (A E : Finset α) (hEA : E ⊆ A)
    (f : (i : ℕ) → α → γ i) (K : ℕ → ℕ) (n : ℕ)
    (hbudget : 2 * (∑ i ∈ Finset.range n, (A.image (f i)).card * (K i - 1)) ≤ E.card) :
    E.card ≤ 2 * (richLayers E f K n).card := by
  have h := richLayers_card_loss A E hEA f K n
  omega

end Layers

/-- An explicit integer threshold strictly above the desired rational density threshold.
Using floor plus one makes all deletion budgets exact natural-number inequalities. -/
def richThreshold (m N n L : ℕ) : ℕ := m * L / (2 * n * N) + 1

theorem richThreshold_positive (m N n L : ℕ) : 0 < richThreshold m N n L := by
  exact Nat.zero_lt_succ _

/-- The product required by the grain counting and retention callers is always positive. -/
theorem richThreshold_product_positive (m N n : ℕ) (L : ℕ → ℕ) :
    0 < ∏ i ∈ Finset.range n, richThreshold m N n (L i) := by
  exact Finset.prod_pos (fun i _ => richThreshold_positive m N n (L i))

/-- The actual class-count hypothesis supplies the full half-retention budget. -/
theorem richThreshold_budget (m N n : ℕ) (C L : ℕ → ℕ) (hN : 0 < N)
    (hcount : ∀ i < n, C i * L i ≤ N) :
    2 * (∑ i ∈ Finset.range n, C i * (richThreshold m N n (L i) - 1)) ≤ m := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := by omega
  have hstep : ∀ i < n, (2 * n) * (C i * (richThreshold m N n (L i) - 1)) ≤ m := by
    intro i hi
    unfold richThreshold
    simp only [Nat.add_sub_cancel]
    apply Nat.le_of_mul_le_mul_right (c := N) _ hN
    calc
      (2 * n) * (C i * (m * L i / (2 * n * N))) * N
          = C i * ((2 * n * N) * (m * L i / (2 * n * N))) := by ring
      _ ≤ C i * (m * L i) := Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)
      _ = m * (C i * L i) := by ring
      _ ≤ m * N := Nat.mul_le_mul_left _ (hcount i hi)
  have hs := Finset.sum_le_sum (fun i (hi : i ∈ Finset.range n) => hstep i (Finset.mem_range.mp hi))
  rw [← Finset.mul_sum] at hs
  have hs' : (2 * (∑ i ∈ Finset.range n, C i * (richThreshold m N n (L i) - 1))) * n ≤ m * n := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hs
  exact Nat.le_of_mul_le_mul_right hs' hnpos

/-- Lower ambient occupancy, rather than upper occupancy, bounds the number of classes. -/
theorem class_count_mul_le (A : Finset α) (f : α → β) (L : ℕ)
    (hlower : ∀ c ∈ A.image f, L ≤ (classFiber A f c).card) :
    (A.image f).card * L ≤ A.card := by
  calc
    (A.image f).card * L = ∑ c ∈ A.image f, L := by simp
    _ ≤ ∑ c ∈ A.image f, (classFiber A f c).card := Finset.sum_le_sum hlower
    _ = A.card := (Finset.card_eq_sum_card_fiberwise
      (fun a ha => Finset.mem_image_of_mem f ha)).symm

/-- Construct the rich layers from a bounded number of occupied ambient classes per direction. -/
theorem construct_richLayers {γ : ℕ → Type*} (A E : Finset α) (hEA : E ⊆ A)
    (hE : E.Nonempty) (f : (i : ℕ) → α → γ i) (L : ℕ → ℕ) (n : ℕ)
    (hcount : ∀ i < n, (E.image (f i)).card * L i ≤ A.card) :
    let K := fun i => richThreshold E.card A.card n (L i)
    let B := richLayers E f K
    B 0 = E ∧ (∀ i, B (i + 1) ⊆ B i) ∧ E.card ≤ 2 * (B n).card ∧
      (B n).Nonempty ∧ ∀ i < n, ∀ a ∈ B (i + 1),
        K i ≤ (classFiber (B i) (f i) (f i a)).card := by
  dsimp only
  have hA : 0 < A.card := Finset.card_pos.mpr (hE.mono hEA)
  have hbudget := richThreshold_budget E.card A.card n (fun i => (E.image (f i)).card) L hA hcount
  have hhalf := richLayers_half_of_budget E E (Finset.Subset.refl E) f
    (fun i => richThreshold E.card A.card n (L i)) n hbudget
  refine ⟨rfl, richLayers_step_subset _ _ _, hhalf, ?_, ?_⟩
  · apply Finset.card_pos.mp
    have hp := Finset.card_pos.mpr hE
    omega
  · intro i _ a ha
    exact richLayers_predecessors _ _ _ i a ha

/-- The chosen integer richness strictly exceeds the intended rational threshold. -/
theorem richThreshold_crossmul (m N n L : ℕ) (hN : 0 < N) (hn : 0 < n) :
    m * L < (2 * n * N) * richThreshold m N n L := by
  have hden : 0 < 2 * n * N := by positivity
  have h := (Nat.div_lt_iff_lt_mul hden).mp (Nat.lt_succ_self (m * L / (2 * n * N)))
  simpa only [richThreshold, Nat.mul_comm] using h

/-- If the initial set has density at least `β` in the reference set, the constructed
integer predecessor threshold is stronger than `β L / (2n)`. -/
theorem richThreshold_density (m N n L : ℕ) (hN : 0 < N) (hn : 0 < n)
    (β : ℝ) (hβ : β * N ≤ m) :
    β * L / (2 * n) < (richThreshold m N n L : ℝ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcross : (m : ℝ) * L < (2 * n * N) * richThreshold m N n L := by
    exact_mod_cast richThreshold_crossmul m N n L hN hn
  have hb := mul_le_mul_of_nonneg_right hβ (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
  by_contra h
  have hbad := mul_le_mul_of_nonneg_right (le_of_not_gt h) hNr.le
  nlinarith

section Geometry

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
open BackwardFiberGrains

/-- Quotient classes are exactly affine subspace fibers. -/
theorem classFiber_eq_affineFiber (B : Finset V) (P : Submodule ℝ V) (x : V) :
    classFiber B P.mkQ (P.mkQ x) = affineFiber B P x := by
  simp only [classFiber, affineFiber_eq_quotient_filter]

/-- Construct the rich layers and the resulting independent-direction grain bound directly.
Only classes meeting the original common-tuple set need the lower ambient occupancy bound. -/
theorem construct_independent_rich_layers {n : ℕ} (v : Fin n → V)
    (hv : LinearIndependent ℝ v) (A E : Finset V) (hEA : E ⊆ A) (hE : E.Nonempty)
    (L : ℕ → ℕ)
    (hlower : ∀ i : Fin n, ∀ x ∈ E,
      L i.val ≤ (affineFiber A (Submodule.span ℝ {v i}) x).card) :
    let f := fun (i : ℕ) (x : V) => (directionSpan v i).mkQ x
    let K := fun i => richThreshold E.card A.card n (L i)
    let B := richLayers E f K
    B 0 = E ∧ (∀ i, B (i + 1) ⊆ B i) ∧ E.card ≤ 2 * (B n).card ∧
      (B n).Nonempty ∧
      (∀ i : Fin n, ∀ x ∈ B (i.val + 1),
        K i.val ≤ (affineFiber (B i.val) (Submodule.span ℝ {v i}) x).card) ∧
      ∀ x ∈ B n, (∏ i ∈ Finset.range n, K i) ≤
        (affineFiber E (Submodule.span ℝ (Set.range v)) x).card := by
  let f := fun (i : ℕ) (x : V) => (directionSpan v i).mkQ x
  let K := fun i => richThreshold E.card A.card n (L i)
  let B := richLayers E f K
  have hcount : ∀ i < n, (E.image (f i)).card * L i ≤ A.card := by
    intro i hi
    apply affine_grain_count_mul_le A E (directionSpan v i) (L i)
    intro x hx
    simpa only [directionSpan_eq v ⟨i, hi⟩] using hlower ⟨i, hi⟩ x hx
  have hc := construct_richLayers A E hEA hE f L n hcount
  have hpred : ∀ i : Fin n, ∀ x ∈ B (i.val + 1),
      K i.val ≤ (affineFiber (B i.val) (Submodule.span ℝ {v i}) x).card := by
    intro i x hx
    have h := richLayers_predecessors E f K i.val x hx
    change K i.val ≤ (classFiber (B i.val) (directionSpan v i.val).mkQ
      ((directionSpan v i.val).mkQ x)).card at h
    simpa only [classFiber_eq_affineFiber, directionSpan_eq] using h
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hpred, ?_⟩
  exact independent_backward_fiber_bound v hv B K hpred

end Geometry

end RichDirectionalLayers
