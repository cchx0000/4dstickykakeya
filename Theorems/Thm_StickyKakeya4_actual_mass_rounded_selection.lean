import Theorems.Thm_StickyKakeya4_cumulative_mass_rounding

set_option autoImplicit false
set_option warningAsError true

namespace ActualMassRoundedSelection
open scoped BigOperators
open CumulativeMassRounding
noncomputable section
variable {P : Type*} [DecidableEq P]

def binMass (A : Finset P) (label : P → ℕ) (i : ℕ) : ℝ :=
  ((A.filter (fun p => label p = i)).card : ℝ)

omit [DecidableEq P] in
lemma binMass_nonneg (A : Finset P) (label : P → ℕ) (i : ℕ) :
    0 ≤ binMass A label i := Nat.cast_nonneg _

omit [DecidableEq P] in
lemma total_mass (A : Finset P) (label : P → ℕ) (n : ℕ)
    (hlabel : ∀ p ∈ A, label p < n) : massPrefix (binMass A label) n = (A.card : ℝ) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := A) (t := Finset.range n)
    (f := label) (fun p hp => Finset.mem_range.mpr (hlabel p hp))
  unfold massPrefix binMass
  exact_mod_cast h.symm

/-- Choose one actual original point for each requested occupied bin. -/
theorem exists_original_representatives (A : Finset P) (label : P → ℕ)
    (S : Finset ℕ) (hS : S ⊆ A.image label) :
    ∃ B ⊆ A, B.image label = S ∧ Set.InjOn label B ∧ B.card = S.card := by
  classical
  have hex (i : S) : ∃ p, p ∈ A ∧ label p = i.val := Finset.mem_image.mp (hS i.property)
  let f : S → P := fun i => Classical.choose (hex i)
  have hf (i : S) : f i ∈ A ∧ label (f i) = i.val := Classical.choose_spec (hex i)
  let B := S.attach.image f
  have hBA : B ⊆ A := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact (hf i).1
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact (hf i).2.symm.trans ((congrArg label hij).trans (hf j).2)
  have himage : B.image label = S := by
    ext k
    constructor
    · intro hk
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      rw [(hf i).2]
      exact i.property
    · intro hk
      exact Finset.mem_image.mpr ⟨f ⟨k, hk⟩,
        Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_attach _ _, rfl⟩, (hf ⟨k, hk⟩).2⟩
  have hinj : Set.InjOn label B := by
    intro p hp q hq heq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    have hij : i = j := Subtype.ext ((hf i).2.symm.trans (heq.trans (hf j).2))
    exact congrArg f hij
  refine ⟨B, hBA, himage, hinj, ?_⟩
  exact (Finset.card_image_of_injective _ hfinj).trans Finset.card_attach

omit [DecidableEq P] in
lemma selected_occupied (A : Finset P) (label : P → ℕ) (M : ℝ) (n : ℕ) :
    selected (binMass A label) M n ⊆ A.image label := by
  intro i hi
  have hpos := selected_positive_weight (binMass A label) n i
    (fun j _ => binMass_nonneg A label j) hi
  change (0 : ℝ) < ((A.filter (fun p => label p = i)).card : ℝ) at hpos
  have hcard : 0 < (A.filter (fun p => label p = i)).card := by exact_mod_cast hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  obtain ⟨hpA, hpi⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_image.mpr ⟨p, hpA, hpi⟩

omit [DecidableEq P] in
/-- The selected ORIGINAL points and cumulative bins have exactly equal interval counts. -/
lemma rounded_interval_card (B : Finset P) (label : P → ℕ) (w : ℕ → ℝ)
    (M : ℝ) (n a b : ℕ) (hbn : b ≤ n)
    (himage : B.image label = selected w M n) (hinj : Set.InjOn label B) :
    (B.filter (fun p => a ≤ label p ∧ label p < b)).card = (window w M a b).card := by
  classical
  let C := B.filter (fun p => a ≤ label p ∧ label p < b)
  have heq : C.image label = window w M a b := by
    ext k
    constructor
    · intro hk
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hpB, ha, hb⟩ := Finset.mem_filter.mp hp
      have hsel : label p ∈ selected w M n := by
        rw [← himage]
        exact Finset.mem_image_of_mem label hpB
      exact (mem_window w M a b (label p)).mpr ⟨ha, hb, (Finset.mem_filter.mp hsel).2⟩
    · intro hk
      obtain ⟨ha, hb, hinc⟩ := (mem_window w M a b k).mp hk
      have hsel : k ∈ selected w M n :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le hb hbn), hinc⟩
      rw [← himage] at hsel
      obtain ⟨p, hp, hpk⟩ := Finset.mem_image.mp hsel
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, by simpa only [hpk] using ha,
        by simpa only [hpk] using hb⟩, hpk⟩
  have hC : Set.InjOn label C := fun p hp q hq he =>
    hinj (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 he
  exact (Finset.card_image_of_injOn hC).symm.trans (congrArg Finset.card heq)

/-- Cumulative selection constructs a genuine source subset. Every selected
point lies in its original bin; all interval bounds refer to original masses. -/
theorem exists_mass_rounded_source (A : Finset P) (label : P → ℕ) (n : ℕ)
    {M : ℝ} (hM : 0 < M) (hlabel : ∀ p ∈ A, label p < n)
    (hcap : ∀ i < n, binMass A label i ≤ M) :
    ∃ B ⊆ A, B.image label = selected (binMass A label) M n ∧
      Set.InjOn label B ∧
      M * (B.card : ℝ) ≤ (A.card : ℝ) ∧ (A.card : ℝ) < M * ((B.card : ℝ)+1) ∧
      (∀ a b : ℕ, a ≤ b → b ≤ n →
        massPrefix (binMass A label) b - massPrefix (binMass A label) a - M ≤
          M * ((B.filter (fun p => a ≤ label p ∧ label p < b)).card : ℝ) ∧
        M * ((B.filter (fun p => a ≤ label p ∧ label p < b)).card : ℝ) ≤
          massPrefix (binMass A label) b - massPrefix (binMass A label) a + M) := by
  obtain ⟨B, hBA, himage, hinj, hcard⟩ := exists_original_representatives A label
    (selected (binMass A label) M n) (selected_occupied A label M n)
  have hw : ∀ i < n, 0 ≤ binMass A label i ∧ binMass A label i ≤ M :=
    fun i hi => ⟨binMass_nonneg A label i, hcap i hi⟩
  have hb := selected_mass_bounds (binMass A label) hM n hw
  rw [total_mass A label n hlabel, ← hcard] at hb
  refine ⟨B, hBA, himage, hinj, hb.1, hb.2, ?_⟩
  intro a b hab hbn
  rw [rounded_interval_card B label (binMass A label) M n a b hbn himage hinj]
  exact window_mass_bounds (binMass A label) hM hab (fun i hi => hw i (lt_of_lt_of_le hi hbn))
end
end ActualMassRoundedSelection
