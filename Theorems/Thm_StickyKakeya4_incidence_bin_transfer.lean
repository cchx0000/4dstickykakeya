import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Heavy-bin transfer for a genuine finite incidence set

An incidence is an actual pair `(tube, oldCell)`.  The bin map is one global
function on old spatial cells. No injectivity of that map is assumed.
All incidences in a heavy tube/bin fiber are retained, with their original
labels and any prescribed weights. The spatial support estimate uses that a
fixed-tube fiber has distinct old-cell labels.
-/

namespace IncidenceBinTransfer

open Finset
open scoped BigOperators

variable {T C D : Type*} [DecidableEq T] [DecidableEq D]

/-- A global spatial bin assignment, leaving the tube label unchanged. -/
def binLabel (f : C → D) (p : T × C) : T × D := (p.1, f p.2)

/-- The original incidences in one tube/bin fiber. -/
def binFiber (I : Finset (T × C)) (f : C → D) (b : T × D) : Finset (T × C) :=
  I.filter (fun p => binLabel f p = b)

/-- All nonempty tube/bin fibers. -/
def bins (I : Finset (T × C)) (f : C → D) : Finset (T × D) := I.image (binLabel f)

/-- Precisely those tube/bin fibers containing at least `m` original incidences. -/
def heavyBins (I : Finset (T × C)) (f : C → D) (m : ℕ) : Finset (T × D) :=
  (bins I f).filter (fun b => m ≤ (binFiber I f b).card)

/-- Retain every original incidence in every heavy tube/bin fiber. -/
def kept (I : Finset (T × C)) (f : C → D) (m : ℕ) : Finset (T × C) :=
  I.filter (fun p => binLabel f p ∈ heavyBins I f m)

/-- Tube labels actually used by the original incidence set. -/
def usedTubes (I : Finset (T × C)) : Finset T := I.image Prod.fst

/-- Original spatial-cell labels, with no multiplicity across tubes. -/
def oldCells [DecidableEq C] (I : Finset (T × C)) : Finset C := I.image Prod.snd

/-- New spatial-bin labels used by the retained incidences. -/
def newCells (I : Finset (T × C)) (f : C → D) (m : ℕ) : Finset D :=
  (heavyBins I f m).image Prod.snd

/-- The nonempty new bins met by one original tube. -/
def tubeBins (I : Finset (T × C)) (f : C → D) (t : T) : Finset (T × D) :=
  (bins I f).filter (fun b => b.1 = t)

@[simp] theorem mem_binFiber {I : Finset (T × C)} {f : C → D} {b : T × D}
    {p : T × C} : p ∈ binFiber I f b ↔ p ∈ I ∧ binLabel f p = b := by
  simp [binFiber]

@[simp] theorem mem_heavyBins {I : Finset (T × C)} {f : C → D} {m : ℕ}
    {b : T × D} : b ∈ heavyBins I f m ↔ b ∈ bins I f ∧ m ≤ (binFiber I f b).card := by
  simp [heavyBins]

/-- Exact old-label retention criterion: no incidences are added or relabelled. -/
@[simp] theorem mem_kept {I : Finset (T × C)} {f : C → D} {m : ℕ} {p : T × C} :
    p ∈ kept I f m ↔ p ∈ I ∧ m ≤ (binFiber I f (binLabel f p)).card := by
  simp only [kept, mem_filter, mem_heavyBins]
  constructor
  · rintro ⟨hp, _, hm⟩
    exact ⟨hp, hm⟩
  · rintro ⟨hp, hm⟩
    exact ⟨hp, mem_image_of_mem _ hp, hm⟩

theorem kept_subset (I : Finset (T × C)) (f : C → D) (m : ℕ) : kept I f m ⊆ I :=
  filter_subset _ _

/-- A retained tube/bin fiber equals its entire original fiber, including labels. -/
theorem kept_fiber_eq {I : Finset (T × C)} {f : C → D} {m : ℕ} {b : T × D}
    (hb : b ∈ heavyBins I f m) : binFiber (kept I f m) f b = binFiber I f b := by
  ext p
  simp only [mem_binFiber, mem_kept]
  constructor
  · exact fun ⟨⟨hp, _⟩, he⟩ => ⟨hp, he⟩
  · rintro ⟨hp, he⟩
    exact ⟨⟨hp, he ▸ (mem_heavyBins.mp hb).2⟩, he⟩

/-- Every heavy bin, and only a heavy bin, occurs among retained incidences. -/
theorem bins_kept_eq (I : Finset (T × C)) (f : C → D) (m : ℕ) :
    bins (kept I f m) f = heavyBins I f m := by
  ext b
  constructor
  · rintro hb
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hb
    exact (mem_filter.mp hp).2
  · intro hb
    obtain ⟨p, hp, he⟩ := mem_image.mp (mem_heavyBins.mp hb).1
    exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, he ▸ hb⟩, he⟩

/-- Any additive weight is exactly the sum of the original weights in the kept bins. -/
theorem sum_kept_eq_sum_heavy_fibers {A : Type*} [AddCommMonoid A]
    (I : Finset (T × C)) (f : C → D) (m : ℕ) (w : T × C → A) :
    ∑ p ∈ kept I f m, w p =
      ∑ b ∈ heavyBins I f m, ∑ p ∈ binFiber I f b, w p := by
  have h := Finset.sum_fiberwise_of_maps_to (M := A) (g := binLabel f)
    (s := kept I f m) (t := heavyBins I f m) (fun p hp => (mem_filter.mp hp).2) w
  rw [← h]
  apply sum_congr rfl
  intro b hb
  rw [← kept_fiber_eq hb]
  rfl

/-- The number of nonempty tube/bin fibers is bounded using the actual used tubes. -/
theorem card_bins_le (I : Finset (T × C)) (f : C → D) (M : ℕ)
    (hM : ∀ t ∈ usedTubes I, (tubeBins I f t).card ≤ M) :
    (bins I f).card ≤ M * (usedTubes I).card := by
  have hmap : (↑(bins I f) : Set (T × D)).MapsTo Prod.fst (usedTubes I) := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hb
    exact mem_image_of_mem _ hp
  rw [card_eq_sum_card_fiberwise hmap]
  calc
    ∑ t ∈ usedTubes I, ((bins I f).filter (fun b => b.1 = t)).card
        ≤ ∑ _t ∈ usedTubes I, M := sum_le_sum (fun t ht => hM t ht)
    _ = M * (usedTubes I).card := by simp [Nat.mul_comm]

/-- Only light fibers are discarded; each loses at most `m−1` incidences. -/
theorem card_discarded_le [DecidableEq C] (I : Finset (T × C)) (f : C → D) (m M : ℕ)
    (hM : ∀ t ∈ usedTubes I, (tubeBins I f t).card ≤ M) :
    (I \ kept I f m).card ≤ (m - 1) * M * (usedTubes I).card := by
  have hmap : (↑(I \ kept I f m) : Set (T × C)).MapsTo (binLabel f) (bins I f) := by
    intro p hp
    exact mem_image_of_mem _ (mem_sdiff.mp hp).1
  have hfiber : ∀ b ∈ bins I f,
      ((I \ kept I f m).filter (fun p => binLabel f p = b)).card ≤ m - 1 := by
    intro b hb
    by_cases hh : b ∈ heavyBins I f m
    · have hz : (I \ kept I f m).filter (fun p => binLabel f p = b) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨hp, he⟩ := mem_filter.mp hp
        obtain ⟨hpI, hpk⟩ := mem_sdiff.mp hp
        exact hpk (mem_filter.mpr ⟨hpI, he ▸ hh⟩)
      simp [hz]
    · have hlt : (binFiber I f b).card < m := by
        exact Nat.lt_of_not_ge (fun h => hh (mem_heavyBins.mpr ⟨hb, h⟩))
      have hsub : (I \ kept I f m).filter (fun p => binLabel f p = b) ⊆
          binFiber I f b := by
        intro p hp
        obtain ⟨hp, he⟩ := mem_filter.mp hp
        exact mem_binFiber.mpr ⟨(mem_sdiff.mp hp).1, he⟩
      exact (card_le_card hsub).trans (by omega)
  calc
    (I \ kept I f m).card = ∑ b ∈ bins I f,
        ((I \ kept I f m).filter (fun p => binLabel f p = b)).card :=
      card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _b ∈ bins I f, (m - 1) := sum_le_sum hfiber
    _ = (m - 1) * (bins I f).card := by simp [Nat.mul_comm]
    _ ≤ (m - 1) * (M * (usedTubes I).card) :=
      Nat.mul_le_mul_left _ (card_bins_le I f M hM)
    _ = (m - 1) * M * (usedTubes I).card := by ring

/-- The sharp loss hypothesis keeps at least half the original incidences. -/
theorem card_le_twice_kept [DecidableEq C] (I : Finset (T × C)) (f : C → D) (m M : ℕ)
    (hM : ∀ t ∈ usedTubes I, (tubeBins I f t).card ≤ M)
    (hhalf : 2 * (m - 1) * M * (usedTubes I).card ≤ I.card) :
    I.card ≤ 2 * (kept I f m).card := by
  have hloss := card_discarded_le I f m M hM
  have hsplit := card_sdiff_add_card_eq_card (kept_subset I f m)
  have hhalf' : 2 * ((m - 1) * M * (usedTubes I).card) ≤ I.card := by
    convert hhalf using 1
    ring
  omega

/-- Fiber capacity bounds retained incidences by the number of actual heavy bins. -/
theorem card_kept_le (I : Finset (T × C)) (f : C → D) (m L : ℕ)
    (hL : ∀ b ∈ bins I f, (binFiber I f b).card ≤ L) :
    (kept I f m).card ≤ L * (heavyBins I f m).card := by
  have hmap : (↑(kept I f m) : Set (T × C)).MapsTo (binLabel f) (heavyBins I f m) := by
    exact fun p hp => (mem_filter.mp hp).2
  calc
    (kept I f m).card = ∑ b ∈ heavyBins I f m, (binFiber (kept I f m) f b).card :=
      card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _b ∈ heavyBins I f m, L := by
      apply sum_le_sum
      intro b hb
      rw [kept_fiber_eq hb]
      exact hL b (mem_heavyBins.mp hb).1
    _ = L * (heavyBins I f m).card := by simp [Nat.mul_comm]

/-- Projection to old-cell labels is injective inside a fixed-tube bin fiber. -/
theorem snd_injective_on_binFiber (I : Finset (T × C)) (f : C → D) (b : T × D) :
    Set.InjOn Prod.snd (↑(binFiber I f b) : Set (T × C)) := by
  intro p hp q hq he
  apply Prod.ext
  · have hpfirst := congrArg Prod.fst (mem_binFiber.mp hp).2
    have hqfirst := congrArg Prod.fst (mem_binFiber.mp hq).2
    exact hpfirst.trans hqfirst.symm
  · exact he

/-- A tube/bin fiber counts distinct old cells in the corresponding global bin. -/
theorem card_binFiber_le_oldCells_fiber [DecidableEq C] (I : Finset (T × C)) (f : C → D) (b : T × D) :
    (binFiber I f b).card ≤ ((oldCells I).filter (fun c => f c = b.2)).card := by
  rw [← card_image_of_injOn (snd_injective_on_binFiber I f b)]
  apply card_le_card
  intro c hc
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hc
  obtain ⟨hpI, he⟩ := mem_binFiber.mp hp
  exact mem_filter.mpr ⟨mem_image_of_mem _ hpI, congrArg Prod.snd he⟩

/-- Each used new spatial bin contains at least `m` distinct original spatial cells. -/
theorem heavy_new_cell_fiber_lower [DecidableEq C] (I : Finset (T × C)) (f : C → D) (m : ℕ)
    {d : D} (hd : d ∈ newCells I f m) :
    m ≤ ((oldCells I).filter (fun c => f c = d)).card := by
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hd
  exact (mem_heavyBins.mp hb).2.trans (card_binFiber_le_oldCells_fiber I f b)

/-- Spatial bin fibers are disjoint because the bin map is global. -/
theorem mul_card_newCells_le [DecidableEq C] (I : Finset (T × C)) (f : C → D) (m : ℕ) :
    m * (newCells I f m).card ≤ (oldCells I).card := by
  calc
    m * (newCells I f m).card = ∑ _d ∈ newCells I f m, m := by simp [Nat.mul_comm]
    _ ≤ ∑ d ∈ newCells I f m, ((oldCells I).filter (fun c => f c = d)).card :=
      sum_le_sum (fun d hd => heavy_new_cell_fiber_lower I f m hd)
    _ = ((oldCells I).filter (fun c => f c ∈ newCells I f m)).card :=
      sum_card_fiberwise_eq_card_filter (oldCells I) (newCells I f m) f
    _ ≤ (oldCells I).card := card_filter_le _ _

/-- New spatial support is exactly the image of the retained original support. -/
theorem newCells_eq_image_oldCells_kept [DecidableEq C]
    (I : Finset (T × C)) (f : C → D) (m : ℕ) :
    newCells I f m = (oldCells (kept I f m)).image f := by
  unfold newCells
  rw [← bins_kept_eq I f m]
  simp only [bins, oldCells, image_image]
  rfl

/-- The spatial gain holds even for the smaller retained old spatial support. -/
theorem mul_card_newCells_le_kept [DecidableEq C]
    (I : Finset (T × C)) (f : C → D) (m : ℕ) :
    m * (newCells I f m).card ≤ (oldCells (kept I f m)).card := by
  have hlower : ∀ d ∈ newCells I f m,
      m ≤ ((oldCells (kept I f m)).filter (fun c => f c = d)).card := by
    intro d hd
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hd
    have hcount := (mem_heavyBins.mp hb).2
    rw [← kept_fiber_eq hb] at hcount
    exact hcount.trans (card_binFiber_le_oldCells_fiber (kept I f m) f b)
  calc
    m * (newCells I f m).card = ∑ _d ∈ newCells I f m, m := by simp [Nat.mul_comm]
    _ ≤ ∑ d ∈ newCells I f m,
        ((oldCells (kept I f m)).filter (fun c => f c = d)).card := sum_le_sum hlower
    _ = ((oldCells (kept I f m)).filter (fun c => f c ∈ newCells I f m)).card :=
      sum_card_fiberwise_eq_card_filter (oldCells (kept I f m)) (newCells I f m) f
    _ ≤ (oldCells (kept I f m)).card := card_filter_le _ _

/-- No mass is lost when the heavy-bin threshold is one. -/
theorem kept_one_eq (I : Finset (T × C)) (f : C → D) : kept I f 1 = I := by
  apply Subset.antisymm (kept_subset I f 1)
  intro p hp
  apply mem_kept.mpr
  refine ⟨hp, ?_⟩
  exact card_pos.mpr ⟨p, mem_binFiber.mpr ⟨hp, rfl⟩⟩

/-- Multiplicity transfer comes from honest incidence and spatial fiber counts. -/
theorem multiplicity_transfer [DecidableEq C] (I : Finset (T × C)) (f : C → D) (m M L : ℕ)
    (hM : ∀ t ∈ usedTubes I, (tubeBins I f t).card ≤ M)
    (hL : ∀ b ∈ bins I f, (binFiber I f b).card ≤ L)
    (hhalf : 2 * (m - 1) * M * (usedTubes I).card ≤ I.card) :
    m * I.card * (newCells I f m).card ≤
      2 * L * (heavyBins I f m).card * (oldCells I).card := by
  calc
    m * I.card * (newCells I f m).card = I.card * (m * (newCells I f m).card) := by ring
    _ ≤ (2 * (kept I f m).card) * (oldCells I).card :=
      Nat.mul_le_mul (card_le_twice_kept I f m M hM hhalf) (mul_card_newCells_le I f m)
    _ ≤ (2 * (L * (heavyBins I f m).card)) * (oldCells I).card :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (card_kept_le I f m L hL))
    _ = 2 * L * (heavyBins I f m).card * (oldCells I).card := by ring

/-- Stronger transfer measured against the retained original spatial support. -/
theorem multiplicity_transfer_kept_support [DecidableEq C]
    (I : Finset (T × C)) (f : C → D) (m M L : ℕ)
    (hM : ∀ t ∈ usedTubes I, (tubeBins I f t).card ≤ M)
    (hL : ∀ b ∈ bins I f, (binFiber I f b).card ≤ L)
    (hhalf : 2 * (m - 1) * M * (usedTubes I).card ≤ I.card) :
    m * I.card * (newCells I f m).card ≤
      2 * L * (heavyBins I f m).card * (oldCells (kept I f m)).card := by
  calc
    m * I.card * (newCells I f m).card = I.card * (m * (newCells I f m).card) := by ring
    _ ≤ (2 * (kept I f m).card) * (oldCells (kept I f m)).card :=
      Nat.mul_le_mul (card_le_twice_kept I f m M hM hhalf) (mul_card_newCells_le_kept I f m)
    _ ≤ (2 * (L * (heavyBins I f m).card)) * (oldCells (kept I f m)).card :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (card_kept_le I f m L hL))
    _ = 2 * L * (heavyBins I f m).card * (oldCells (kept I f m)).card := by ring

/-- The real-valued multiplicity inequality when both spatial supports are nonempty. -/
theorem multiplicity_transfer_ratio [DecidableEq C]
    (I : Finset (T × C)) (f : C → D) (m M L : ℕ)
    (hM : ∀ t ∈ usedTubes I, (tubeBins I f t).card ≤ M)
    (hL : ∀ b ∈ bins I f, (binFiber I f b).card ≤ L)
    (hhalf : 2 * (m - 1) * M * (usedTubes I).card ≤ I.card)
    (hold : 0 < (oldCells I).card) (hnew : 0 < (newCells I f m).card) :
    (m : ℝ) * ((I.card : ℝ) / (oldCells I).card) ≤
      2 * (L : ℝ) * ((heavyBins I f m).card / (newCells I f m).card) := by
  have holdR : (0 : ℝ) < (oldCells I).card := by exact_mod_cast hold
  have hnewR : (0 : ℝ) < (newCells I f m).card := by exact_mod_cast hnew
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply (div_le_div_iff₀ holdR hnewR).mpr
  exact_mod_cast multiplicity_transfer I f m M L hM hL hhalf

end IncidenceBinTransfer
