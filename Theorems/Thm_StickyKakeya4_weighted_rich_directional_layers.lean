import Theorems.Thm_StickyKakeya4_rich_directional_layers

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace WeightedRichDirectionalLayers

open RichDirectionalLayers
variable {α β : Type*}

/-- Total original integer weight of a finite set of occurrence labels. -/
def mass (B : Finset α) (w : α → ℕ) : ℕ := ∑ a ∈ B, w a

theorem mass_mono (A B : Finset α) (w : α → ℕ) (hAB : A ⊆ B) : mass A w ≤ mass B w :=
  Finset.sum_le_sum_of_subset hAB

theorem mass_partition (B : Finset α) (f : α → β) (w : α → ℕ) :
    ∑ c ∈ B.image f, mass (classFiber B f c) w = mass B w :=
  Finset.sum_fiberwise_of_maps_to (fun _ ha => Finset.mem_image_of_mem f ha) w

/-- Whole current columns are kept according to their original weight. -/
def weightedRestriction (B : Finset α) (f : α → β) (w : α → ℕ) (k : ℕ) : Finset α :=
  B.filter fun a => k ≤ mass (classFiber B f (f a)) w

theorem weightedRestriction_subset (B : Finset α) (f : α → β) (w : α → ℕ) (k : ℕ) :
    weightedRestriction B f w k ⊆ B := Finset.filter_subset _ _

theorem weightedRestriction_predecessors (B : Finset α) (f : α → β) (w : α → ℕ) (k : ℕ)
    (a : α) (ha : a ∈ weightedRestriction B f w k) :
    k ≤ mass (classFiber B f (f a)) w := (Finset.mem_filter.mp ha).2

/-- The deletion charge is against original weight, not the number of labels. -/
theorem weightedRestriction_mass_loss (A B : Finset α) (f : α → β) (w : α → ℕ)
    (k : ℕ) (hBA : B ⊆ A) :
    mass B w ≤ mass (weightedRestriction B f w k) w + (A.image f).card * (k - 1) := by
  let D := B.filter fun a => ¬k ≤ mass (classFiber B f (f a)) w
  have hD : D ⊆ B := Finset.filter_subset _ _
  have hc : ∀ c ∈ A.image f, mass (classFiber D f c) w ≤ k - 1 := by
    intro c _
    by_cases hne : (classFiber D f c).Nonempty
    · obtain ⟨a, ha⟩ := hne
      obtain ⟨haD, hac⟩ := Finset.mem_filter.mp ha
      have hlow := (Finset.mem_filter.mp haD).2
      have hsub : classFiber D f c ⊆ classFiber B f (f a) := by
        intro b hb
        obtain ⟨hbD, hbc⟩ := Finset.mem_filter.mp hb
        exact Finset.mem_filter.mpr ⟨hD hbD, hbc.trans hac.symm⟩
      have hm := mass_mono _ _ w hsub
      omega
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [mass, hempty]
  have hloss : mass D w ≤ (A.image f).card * (k - 1) := by
    calc
      mass D w = ∑ c ∈ A.image f, mass (classFiber D f c) w :=
        (Finset.sum_fiberwise_of_maps_to
          (fun a ha => Finset.mem_image_of_mem f (hBA (hD ha))) w).symm
      _ ≤ ∑ c ∈ A.image f, (k - 1) := Finset.sum_le_sum hc
      _ = (A.image f).card * (k - 1) := by simp
  have hpartition := Finset.sum_filter_add_sum_filter_not B
    (fun a => k ≤ mass (classFiber B f (f a)) w) w
  change mass (weightedRestriction B f w k) w + mass D w = mass B w at hpartition
  omega

section Layers
variable {γ : ℕ → Type*}

/-- Explicit weighted deletion on the original occurrence space. -/
def weightedLayers (E : Finset α) (f : (i : ℕ) → α → γ i) (w : α → ℕ)
    (k : ℕ → ℕ) : ℕ → Finset α
  | 0 => E
  | i + 1 => weightedRestriction (weightedLayers E f w k i) (f i) w (k i)

@[simp] theorem weightedLayers_zero (E : Finset α) (f : (i : ℕ) → α → γ i)
    (w : α → ℕ) (k : ℕ → ℕ) : weightedLayers E f w k 0 = E := rfl

@[simp] theorem weightedLayers_succ (E : Finset α) (f : (i : ℕ) → α → γ i)
    (w : α → ℕ) (k : ℕ → ℕ) (i : ℕ) :
    weightedLayers E f w k (i + 1) = weightedRestriction (weightedLayers E f w k i) (f i) w (k i) := rfl

theorem weightedLayers_step_subset (E : Finset α) (f : (i : ℕ) → α → γ i)
    (w : α → ℕ) (k : ℕ → ℕ) (i : ℕ) :
    weightedLayers E f w k (i + 1) ⊆ weightedLayers E f w k i := weightedRestriction_subset _ _ _ _

theorem weightedLayers_subset_start (E : Finset α) (f : (i : ℕ) → α → γ i)
    (w : α → ℕ) (k : ℕ → ℕ) (i : ℕ) : weightedLayers E f w k i ⊆ E := by
  induction i with
  | zero => exact Finset.Subset.refl _
  | succ i ih => exact (weightedLayers_step_subset E f w k i).trans ih

theorem weightedLayers_predecessors (E : Finset α) (f : (i : ℕ) → α → γ i)
    (w : α → ℕ) (k : ℕ → ℕ) (i : ℕ) (a : α) (ha : a ∈ weightedLayers E f w k (i + 1)) :
    k i ≤ mass (classFiber (weightedLayers E f w k i) (f i) (f i a)) w :=
  weightedRestriction_predecessors _ _ _ _ a ha

/-- Sum of all deletion losses, still evaluated using the unchanged original weights. -/
theorem weightedLayers_mass_loss (E : Finset α) (f : (i : ℕ) → α → γ i)
    (w : α → ℕ) (k : ℕ → ℕ) (n : ℕ) :
    mass E w ≤ mass (weightedLayers E f w k n) w +
      ∑ i ∈ Finset.range n, (E.image (f i)).card * (k i - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := weightedRestriction_mass_loss E (weightedLayers E f w k n) (f n) w (k n)
        (weightedLayers_subset_start E f w k n)
      rw [Finset.sum_range_succ]
      change mass E w ≤ mass (weightedRestriction (weightedLayers E f w k n) (f n) w (k n)) w + _
      omega

/-- Active reference columns carry a lower reference weight, giving the needed count bound. -/
theorem active_column_count (A E : Finset α) (hEA : E ⊆ A) (f : α → β)
    (w : α → ℕ) (b : ℕ) (hlower : ∀ c ∈ E.image f, b ≤ mass (classFiber A f c) w) :
    (E.image f).card * b ≤ mass A w := by
  calc
    (E.image f).card * b = ∑ c ∈ E.image f, b := by simp
    _ ≤ ∑ c ∈ E.image f, mass (classFiber A f c) w := Finset.sum_le_sum hlower
    _ ≤ ∑ c ∈ A.image f, mass (classFiber A f c) w :=
      Finset.sum_le_sum_of_subset (Finset.image_subset_image hEA)
    _ = mass A w := mass_partition A f w

/-- Construct a half-original-weight core from lower reference weight on active columns. -/
theorem construct_weightedLayers (A E : Finset α) (hEA : E ⊆ A)
    (f : (i : ℕ) → α → γ i) (w : α → ℕ) (b : ℕ → ℕ) (n : ℕ)
    (hW : 0 < mass E w)
    (hlower : ∀ i < n, ∀ c ∈ E.image (f i), b i ≤ mass (classFiber A (f i) c) w) :
    let k := fun i => richThreshold (mass E w) (mass A w) n (b i)
    let Ω := weightedLayers E f w k
    Ω 0 = E ∧ (∀ i, Ω (i + 1) ⊆ Ω i) ∧ mass E w ≤ 2 * mass (Ω n) w ∧
      0 < mass (Ω n) w ∧ ∀ i < n, ∀ a ∈ Ω (i + 1),
        k i ≤ mass (classFiber (Ω i) (f i) (f i a)) w := by
  dsimp only
  have hWA : 0 < mass A w := hW.trans_le (mass_mono E A w hEA)
  have hcount : ∀ i < n, (E.image (f i)).card * b i ≤ mass A w := by
    intro i hi
    exact active_column_count A E hEA (f i) w (b i) (hlower i hi)
  have hbudget := richThreshold_budget (mass E w) (mass A w) n
    (fun i => (E.image (f i)).card) b hWA hcount
  have hloss := weightedLayers_mass_loss E f w
    (fun i => richThreshold (mass E w) (mass A w) n (b i)) n
  have hhalf : mass E w ≤ 2 * mass (weightedLayers E f w
      (fun i => richThreshold (mass E w) (mass A w) n (b i)) n) w := by omega
  refine ⟨rfl, weightedLayers_step_subset _ _ _ _, hhalf, ?_, ?_⟩
  · omega
  · intro i _ a ha
    exact weightedLayers_predecessors _ _ _ _ i a ha

end Layers

section Geometry

variable {V : Type*}
open BackwardFiberGrains

/-- Every subset inherits the original reference upper weight per geometric vertex. -/
theorem mass_le_image_card_mul (A B : Finset α) (hBA : B ⊆ A) (x : α → V)
    (w : α → ℕ) (M : ℕ) (hvertex : ∀ y, mass (classFiber A x y) w ≤ M) :
    mass B w ≤ (B.image x).card * M := by
  calc
    mass B w = ∑ y ∈ B.image x, mass (classFiber B x y) w := (mass_partition B x w).symm
    _ ≤ ∑ y ∈ B.image x, M := by
      apply Finset.sum_le_sum
      intro y _
      apply (mass_mono _ _ w ?_).trans (hvertex y)
      intro a ha
      obtain ⟨haB, hax⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨hBA haB, hax⟩
    _ = (B.image x).card * M := by simp

variable [AddCommGroup V] [Module ℝ V]

/-- A label column defined by the geometric quotient is exactly the corresponding affine condition. -/
theorem geometric_classFiber_eq (B : Finset α) (x : α → V) (P : Submodule ℝ V) (a : α) :
    classFiber B (fun b => P.mkQ (x b)) (P.mkQ (x a)) =
      B.filter (fun b => x b - x a ∈ P) := by
  ext b
  simp [classFiber, Submodule.mkQ_apply, Submodule.Quotient.eq]

/-- Passing to the geometric image counts distinct vertices, even with repeated labels. -/
theorem image_geometric_classFiber (B : Finset α) (x : α → V) (P : Submodule ℝ V) (a : α) :
    (classFiber B (fun b => P.mkQ (x b)) (P.mkQ (x a))).image x =
      affineFiber (B.image x) P (x a) := by
  rw [geometric_classFiber_eq]
  ext y
  simp only [Finset.mem_image, Finset.mem_filter, mem_affineFiber]
  constructor
  · rintro ⟨b, ⟨hb, hline⟩, rfl⟩
    exact ⟨⟨b, hb, rfl⟩, hline⟩
  · rintro ⟨⟨b, hb, rfl⟩, hline⟩
    exact ⟨b, ⟨hb, hline⟩, rfl⟩

/-- Original predecessor weight gives a ceiling lower bound on distinct predecessor vertices. -/
theorem weighted_predecessor_vertices (A B : Finset α) (hBA : B ⊆ A) (x : α → V)
    (P : Submodule ℝ V) (w : α → ℕ) (M : ℕ) (hM : 0 < M)
    (hvertex : ∀ y, mass (classFiber A x y) w ≤ M) (k : ℕ) (a : α)
    (hpred : k ≤ mass (classFiber B (fun b => P.mkQ (x b)) (P.mkQ (x a))) w) :
    k ⌈/⌉ M ≤ (affineFiber (B.image x) P (x a)).card := by
  have hsub : classFiber B (fun b => P.mkQ (x b)) (P.mkQ (x a)) ⊆ A :=
    (Finset.filter_subset _ _).trans hBA
  have hcap := mass_le_image_card_mul A _ hsub x w M hvertex
  rw [image_geometric_classFiber] at hcap
  apply (ceilDiv_le_iff_le_mul hM).mpr
  simpa only [Nat.mul_comm] using hpred.trans hcap

/-- A nonzero predecessor threshold gives a nonzero ceiling lower bound. -/
theorem positive_predecessor_ceiling (k M : ℕ) (hk : 0 < k) (hM : 0 < M) :
    0 < k ⌈/⌉ M := by
  have h := (ceilDiv_le_iff_le_mul hM).mp (le_refl (k ⌈/⌉ M))
  by_contra hn
  have hz : k ⌈/⌉ M = 0 := by omega
  simp only [hz, Nat.mul_zero] at h
  omega

/-- Construct half-original-weight rich layers and derive their geometric backward-fiber grains.
The reference vertex cap converts weighted columns to distinct vertices without changing labels. -/
theorem construct_weighted_independent_grains {n : ℕ} (v : Fin n → V)
    (hv : LinearIndependent ℝ v) (A E : Finset α) (hEA : E ⊆ A)
    (x : α → V) (w : α → ℕ) (hW : 0 < mass E w) (b : ℕ → ℕ)
    (hlower : ∀ i : Fin n, ∀ a ∈ E,
      b i.val ≤ mass (A.filter (fun c => x c - x a ∈ Submodule.span ℝ {v i})) w)
    (M : ℕ) (hvertex : ∀ y, mass (classFiber A x y) w ≤ M) :
    let f := fun (i : ℕ) (a : α) => (directionSpan v i).mkQ (x a)
    let k := fun i => richThreshold (mass E w) (mass A w) n (b i)
    let Ω := weightedLayers E f w k
    let B := fun i => (Ω i).image x
    let L := fun i => k i ⌈/⌉ M
    Ω 0 = E ∧ (∀ i, Ω (i + 1) ⊆ Ω i) ∧ mass E w ≤ 2 * mass (Ω n) w ∧
      0 < mass (Ω n) w ∧
      (∀ i : Fin n, ∀ a ∈ Ω (i.val + 1),
        k i.val ≤ mass (classFiber (Ω i.val) (f i.val) (f i.val a)) w) ∧
      (∀ i : Fin n, ∀ y ∈ B (i.val + 1),
        L i.val ≤ (affineFiber (B i.val) (Submodule.span ℝ {v i}) y).card) ∧
      0 < (∏ i ∈ Finset.range n, L i) ∧
      ∀ y ∈ B n, (∏ i ∈ Finset.range n, L i) ≤
        (affineFiber (E.image x) (Submodule.span ℝ (Set.range v)) y).card := by
  let f := fun (i : ℕ) (a : α) => (directionSpan v i).mkQ (x a)
  let k := fun i => richThreshold (mass E w) (mass A w) n (b i)
  let Ω := weightedLayers E f w k
  let B := fun i => (Ω i).image x
  let L := fun i => k i ⌈/⌉ M
  have hWA : 0 < mass A w := hW.trans_le (mass_mono E A w hEA)
  have hM : 0 < M := by
    have hcap := mass_le_image_card_mul A A (Finset.Subset.refl A) x w M hvertex
    by_contra hn
    have hz : M = 0 := by omega
    simp only [hz, Nat.mul_zero] at hcap
    omega
  have href : ∀ i < n, ∀ c ∈ E.image (f i), b i ≤ mass (classFiber A (f i) c) w := by
    intro i hi c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    change b i ≤ mass (classFiber A (fun a => (directionSpan v i).mkQ (x a))
      ((directionSpan v i).mkQ (x a))) w
    rw [geometric_classFiber_eq, directionSpan_eq v ⟨i, hi⟩]
    exact hlower ⟨i, hi⟩ a ha
  have hc := construct_weightedLayers A E hEA f w b n hW href
  have hpred : ∀ i : Fin n, ∀ y ∈ B (i.val + 1),
      L i.val ≤ (affineFiber (B i.val) (Submodule.span ℝ {v i}) y).card := by
    intro i y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    have hweight := weightedLayers_predecessors E f w k i.val a ha
    have hsub : Ω i.val ⊆ A := (weightedLayers_subset_start E f w k i.val).trans hEA
    have h := weighted_predecessor_vertices A (Ω i.val) hsub x (directionSpan v i.val)
      w M hM hvertex (k i.val) a hweight
    simpa only [directionSpan_eq] using h
  have hproduct : 0 < ∏ i ∈ Finset.range n, L i := by
    apply Finset.prod_pos
    intro i _
    exact positive_predecessor_ceiling _ _ (richThreshold_positive _ _ _ _) hM
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, ?_, hpred, hproduct, ?_⟩
  · intro i a ha
    exact weightedLayers_predecessors E f w k i.val a ha
  · exact independent_backward_fiber_bound v hv B L hpred

end Geometry

end WeightedRichDirectionalLayers
