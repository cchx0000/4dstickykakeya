import Mathlib.Tactic
import Mathlib.Combinatorics.Pigeonhole

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 3000000

noncomputable section

open scoped BigOperators

namespace TwoStepMenuPaths

variable {M L A : Type*}

/-- All actual depth-two paths through a root menu and its successor menus. -/
def paths [DecidableEq M] (S : Finset M) (T : M → Finset M) : Finset (M × M) :=
  S.biUnion fun m => {m} ×ˢ T m

@[simp]
theorem mem_paths [DecidableEq M] (S : Finset M) (T : M → Finset M) (p : M × M) :
    p ∈ paths S T ↔ p.1 ∈ S ∧ p.2 ∈ T p.1 := by
  rcases p with ⟨m, n⟩
  simp [paths]

/-- Different first menus give disjoint path families, so there is no loss. -/
theorem card_paths [DecidableEq M] (S : Finset M) (T : M → Finset M) :
    (paths S T).card = ∑ m ∈ S, (T m).card := by
  rw [paths, Finset.card_biUnion]
  · simp
  · intro m hm n hn hmn
    exact Finset.disjoint_product.mpr (Or.inl (by simpa using hmn))

/-- A lower bound on each branching number yields a squared path bound. -/
theorem card_paths_lower [DecidableEq M] (S : Finset M) (T : M → Finset M)
    (B : ℝ) (hB : 0 ≤ B) (hS : B ≤ (S.card : ℝ))
    (hT : ∀ m ∈ S, B ≤ ((T m).card : ℝ)) :
    B ^ 2 ≤ ((paths S T).card : ℝ) := by
  rw [card_paths, Nat.cast_sum]
  calc
    B ^ 2 = B * B := by ring
    _ ≤ (S.card : ℝ) * B := mul_le_mul_of_nonneg_right hS hB
    _ = ∑ _m ∈ S, B := by simp
    _ ≤ ∑ m ∈ S, ((T m).card : ℝ) := Finset.sum_le_sum hT

/-- The two ordered labels of a path. -/
def pathLabel (label : M → L) (p : M × M) : L × L :=
  (label p.1, label p.2)

/-- An actual label fiber of an arbitrary finite path family. -/
def frozen [DecidableEq L] (P : Finset (M × M)) (label : M → L) (l : L × L) :
    Finset (M × M) := P.filter fun p => pathLabel label p = l

@[simp]
theorem mem_frozen [DecidableEq L] (P : Finset (M × M)) (label : M → L)
    (l : L × L) (p : M × M) :
    p ∈ frozen P label l ↔ p ∈ P ∧ pathLabel label p = l := by
  simp [frozen]

@[simp]
theorem mem_frozen_paths [DecidableEq M] [DecidableEq L]
    (S : Finset M) (T : M → Finset M) (label : M → L) (l : L × L) (p : M × M) :
    p ∈ frozen (paths S T) label l ↔
      p.1 ∈ S ∧ p.2 ∈ T p.1 ∧ pathLabel label p = l := by
  simp only [mem_frozen, mem_paths, and_assoc]

theorem frozen_subset [DecidableEq L] (P : Finset (M × M)) (label : M → L)
    (l : L × L) : frozen P label l ⊆ P := Finset.filter_subset _ _

theorem frozen_label [DecidableEq L] (P : Finset (M × M)) (label : M → L)
    (l : L × L) {p : M × M} (hp : p ∈ frozen P label l) :
    pathLabel label p = l := (mem_frozen P label l p).mp hp |>.2

/-- Real-valued pigeonhole freezing, including nonintegral lower bounds. -/
theorem exists_frozen [DecidableEq L] (P : Finset (M × M)) (K : Finset L)
    (label : M → L) (hK : K.Nonempty)
    (hlabel : ∀ p ∈ P, label p.1 ∈ K ∧ label p.2 ∈ K)
    (b : ℝ) (hcard : b * (K.card : ℝ) ^ 2 ≤ (P.card : ℝ)) :
    ∃ l ∈ K ×ˢ K, b ≤ ((frozen P label l).card : ℝ) := by
  have hmap : ∀ p ∈ P, pathLabel label p ∈ K ×ˢ K := by
    intro p hp
    exact Finset.mem_product.mpr (hlabel p hp)
  have hnonempty : (K ×ˢ K).Nonempty := Finset.nonempty_product.mpr ⟨hK, hK⟩
  have hmul : (K ×ˢ K).card • b ≤ (P.card : ℝ) := by
    simpa only [nsmul_eq_mul, Finset.card_product, Nat.cast_mul, pow_two,
      mul_assoc, mul_comm, mul_left_comm] using hcard
  simpa only [frozen] using
    (Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmap hnonempty hmul)

/-- Freeze an actual pair of labels on constructed paths. The hypotheses are
only menu cardinalities and label containment; path cardinality is derived. -/
theorem exists_frozen_paths [DecidableEq M] [DecidableEq L]
    (S : Finset M) (T : M → Finset M) (K : Finset L) (label : M → L)
    (hK : K.Nonempty)
    (hroot : ∀ m ∈ S, label m ∈ K)
    (hsecond : ∀ m ∈ S, ∀ n ∈ T m, label n ∈ K)
    (B b : ℝ) (hB : 0 ≤ B) (hS : B ≤ (S.card : ℝ))
    (hT : ∀ m ∈ S, B ≤ ((T m).card : ℝ))
    (hb : b * (K.card : ℝ) ^ 2 ≤ B ^ 2) :
    ∃ l ∈ K ×ˢ K,
      frozen (paths S T) label l ⊆ paths S T ∧
      (∀ p ∈ frozen (paths S T) label l, pathLabel label p = l) ∧
      b ≤ ((frozen (paths S T) label l).card : ℝ) := by
  have hlabel : ∀ p ∈ paths S T, label p.1 ∈ K ∧ label p.2 ∈ K := by
    intro p hp
    obtain ⟨hm, hn⟩ := (mem_paths S T p).mp hp
    exact ⟨hroot p.1 hm, hsecond p.1 hm p.2 hn⟩
  obtain ⟨l, hl, hcard⟩ := exists_frozen (paths S T) K label hK hlabel b
    (hb.trans (card_paths_lower S T B hB hS hT))
  exact ⟨l, hl, frozen_subset _ _ _, fun _ hp => frozen_label _ _ _ hp, hcard⟩

/-- A concrete menu contains an ordered pair of times and an angular pair. -/
abbrev Menu (A : Type*) := (ℝ × ℝ) × (A × A)

/-- Retain both ordered time pairs of a depth-two menu path. -/
def orderedTimes (p : Menu A × Menu A) : (ℝ × ℝ) × (ℝ × ℝ) :=
  (p.1.1, p.2.1)

/-- Once both angular pairs are fixed, the time-pair sequence determines the
entire menu path; projection therefore incurs no multiplicity denominator. -/
theorem orderedTimes_injOn_of_fixed_angles
    (F : Finset (Menu A × Menu A)) (l : (A × A) × (A × A))
    (hfixed : ∀ p ∈ F, pathLabel Prod.snd p = l) :
    Set.InjOn orderedTimes (F : Set (Menu A × Menu A)) := by
  intro p hp q hq htime
  have hp' := hfixed p hp
  have hq' := hfixed q hq
  have hangle : pathLabel Prod.snd p = pathLabel Prod.snd q := hp'.trans hq'.symm
  have htime₁ : p.1.1 = q.1.1 := congrArg (fun r : (ℝ × ℝ) × (ℝ × ℝ) => r.1) htime
  have htime₂ : p.2.1 = q.2.1 := congrArg (fun r : (ℝ × ℝ) × (ℝ × ℝ) => r.2) htime
  have hangle₁ : p.1.2 = q.1.2 := congrArg (fun r : (A × A) × (A × A) => r.1) hangle
  have hangle₂ : p.2.2 = q.2.2 := congrArg (fun r : (A × A) × (A × A) => r.2) hangle
  exact Prod.ext (Prod.ext htime₁ hangle₁) (Prod.ext htime₂ hangle₂)

/-- Cardinality is preserved by the time projection on a fixed angular fiber. -/
theorem card_orderedTimes_image_of_fixed_angles
    (F : Finset (Menu A × Menu A)) (l : (A × A) × (A × A))
    (hfixed : ∀ p ∈ F, pathLabel Prod.snd p = l) :
    (F.image orderedTimes).card = F.card := by
  classical
  exact Finset.card_image_of_injOn (orderedTimes_injOn_of_fixed_angles F l hfixed)

/-- Specialized injectivity for the actual frozen angular-label family. -/
theorem orderedTimes_injOn_frozen [DecidableEq A]
    (P : Finset (Menu A × Menu A)) (l : (A × A) × (A × A)) :
    Set.InjOn orderedTimes (frozen P Prod.snd l : Set (Menu A × Menu A)) :=
  orderedTimes_injOn_of_fixed_angles _ l (fun _ hp => frozen_label _ _ _ hp)

/-- The frozen path family and its ordered time sequences have equal size. -/
theorem card_orderedTimes_image_frozen [DecidableEq A]
    (P : Finset (Menu A × Menu A)) (l : (A × A) × (A × A)) :
    ((frozen P Prod.snd l).image orderedTimes).card = (frozen P Prod.snd l).card := by
  classical
  exact Finset.card_image_of_injOn (orderedTimes_injOn_frozen P l)

/-- A real lower bound on the frozen menu paths transfers without loss to
ordered time-pair sequences. -/
theorem orderedTimes_image_lower_frozen [DecidableEq A]
    (P : Finset (Menu A × Menu A)) (l : (A × A) × (A × A))
    (b : ℝ) (hb : b ≤ ((frozen P Prod.snd l).card : ℝ)) :
    b ≤ (((frozen P Prod.snd l).image orderedTimes).card : ℝ) := by
  simpa only [card_orderedTimes_image_frozen] using hb

end TwoStepMenuPaths
