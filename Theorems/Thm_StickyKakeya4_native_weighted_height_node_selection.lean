import Theorems.Thm_StickyKakeya4_compatible_tuple_selection

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1600000

namespace NativeWeightedHeightNodeSelection

open SelfUniform

variable {α β γ : Type*}

/-- Select whole source atoms using their original weights. At each of the
`J` stages, independently select a maximum-weight node class in each occupied
height class. The finite menu bound is on the original source. -/
theorem weighted_height_node_selection [DecidableEq β] [DecidableEq γ]
    {J : ℕ} (w : α → ℕ) (A : Finset α)
    (f : Fin J → α → β) (h : Fin J → α → γ) (C : ℕ)
    (Hcap : ∀ j t, ((A.filter (fun x => h j x = t)).image (f j)).card ≤ C) :
    ∃ B ⊆ A, (∑ x ∈ A, w x) ≤ C ^ J * (∑ x ∈ B, w x) ∧
      ∀ j x y, x ∈ B → y ∈ B → h j x = h j y → f j x = f j y := by
  classical
  induction J generalizing A with
  | zero =>
    refine ⟨A, Finset.Subset.refl _, ?_, ?_⟩
    · simp
    · intro j
      exact Fin.elim0 j
  | succ J ih =>
    obtain ⟨E, hEA, hEmass, hEalign⟩ :=
      CompatibleTupleSelection.weighted_spatial_selection w A (h 0) (f 0) C
        (Hcap 0)
    have htail : ∀ (j : Fin J) t,
        ((E.filter (fun x => h j.succ x = t)).image (f j.succ)).card ≤ C := by
      intro j t
      apply (Finset.card_le_card (Finset.image_subset_image
        (show E.filter (fun x => h j.succ x = t) ⊆
          A.filter (fun x => h j.succ x = t) from ?_))).trans (Hcap j.succ t)
      intro x hx
      exact Finset.mem_filter.mpr
        ⟨hEA (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    obtain ⟨B, hBE, hBmass, hBalign⟩ :=
      ih E (fun j => f j.succ) (fun j => h j.succ) htail
    refine ⟨B, hBE.trans hEA, ?_, ?_⟩
    · calc
        (∑ x ∈ A, w x) ≤ C * (∑ x ∈ E, w x) := hEmass
        _ ≤ C * (C ^ J * (∑ x ∈ B, w x)) := Nat.mul_le_mul_left C hBmass
        _ = C ^ (J + 1) * (∑ x ∈ B, w x) := by rw [pow_succ]; ring
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · intro x y hx hy hxy
        exact hEalign x y (hBE hx) (hBE hy) hxy
      · exact hBalign k

/-- Positive original total weight ensures that the selected set is nonempty;
zero individual weights and a zero menu bound need no special assumptions. -/
theorem weighted_height_node_selection_nonempty [DecidableEq β] [DecidableEq γ]
    {J : ℕ} (w : α → ℕ) (A : Finset α)
    (f : Fin J → α → β) (h : Fin J → α → γ) (C : ℕ)
    (Hcap : ∀ j t, ((A.filter (fun x => h j x = t)).image (f j)).card ≤ C)
    (Hpos : 0 < ∑ x ∈ A, w x) :
    ∃ B ⊆ A, B.Nonempty ∧
      (∑ x ∈ A, w x) ≤ C ^ J * (∑ x ∈ B, w x) ∧
      ∀ j x y, x ∈ B → y ∈ B → h j x = h j y → f j x = f j y := by
  classical
  obtain ⟨B, hBA, hmass, halign⟩ := weighted_height_node_selection w A f h C Hcap
  refine ⟨B, hBA, ?_, hmass, halign⟩
  by_contra hB
  have hzero : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
  rw [hzero] at hmass
  simp only [Finset.sum_empty, Nat.mul_zero] at hmass
  omega

/-- Cut a finite original source by selected whole node labels. -/
def cutByNodes {ι ν : Type*} [DecidableEq ν]
    (A : Finset ι) (node : ι → ν) (B : Finset ν) : Finset ι :=
  A.filter (fun x => node x ∈ B)

@[simp] lemma mem_cutByNodes {ι ν : Type*} [DecidableEq ν]
    (A : Finset ι) (node : ι → ν) (B : Finset ν) (x : ι) :
    x ∈ cutByNodes A node B ↔ x ∈ A ∧ node x ∈ B := by
  simp [cutByNodes]

/-- If the original grain label determines the node, retaining one point of a
grain by a whole-node cut retains every original point in that grain. -/
theorem surviving_grain_fiber_eq {ι κ ν : Type*}
    [DecidableEq κ] [DecidableEq ν]
    (A : Finset ι) (grain : ι → κ) (node : ι → ν) (B : Finset ν)
    (Hnode : ∀ x y, x ∈ A → y ∈ A → grain x = grain y → node x = node y)
    {x : ι} (Hx : x ∈ cutByNodes A node B) :
    (cutByNodes A node B).filter (fun y => grain y = grain x) =
      A.filter (fun y => grain y = grain x) := by
  classical
  obtain ⟨hxA, hxB⟩ := (mem_cutByNodes A node B x).mp Hx
  ext y
  constructor
  · intro hy
    obtain ⟨hycut, hygrain⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr
      ⟨((mem_cutByNodes A node B y).mp hycut).1, hygrain⟩
  · intro hy
    obtain ⟨hyA, hygrain⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_filter.mpr ⟨?_, hygrain⟩
    apply (mem_cutByNodes A node B y).mpr
    refine ⟨hyA, ?_⟩
    rw [Hnode y x hyA hxA hygrain]
    exact hxB

/-- The fiber equality also applies to any occupied surviving grain label. -/
theorem surviving_grain_label_fiber_eq {ι κ ν : Type*}
    [DecidableEq κ] [DecidableEq ν]
    (A : Finset ι) (grain : ι → κ) (node : ι → ν) (B : Finset ν)
    (Hnode : ∀ x y, x ∈ A → y ∈ A → grain x = grain y → node x = node y)
    {t : κ} (Ht : t ∈ (cutByNodes A node B).image grain) :
    (cutByNodes A node B).filter (fun y => grain y = t) =
      A.filter (fun y => grain y = t) := by
  classical
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp Ht
  exact surviving_grain_fiber_eq A grain node B Hnode hx

/-- Arbitrary original incidence weights are unchanged on every surviving
grain: this is equality of the original fibers, with no new weights. -/
theorem surviving_grain_weight_eq {ι κ ν : Type*}
    [DecidableEq κ] [DecidableEq ν]
    (A : Finset ι) (grain : ι → κ) (node : ι → ν) (B : Finset ν)
    (w : ι → ℕ)
    (Hnode : ∀ x y, x ∈ A → y ∈ A → grain x = grain y → node x = node y)
    {t : κ} (Ht : t ∈ (cutByNodes A node B).image grain) :
    (∑ y ∈ (cutByNodes A node B).filter (fun y => grain y = t), w y) =
      ∑ y ∈ A.filter (fun y => grain y = t), w y := by
  rw [surviving_grain_label_fiber_eq A grain node B Hnode Ht]

end NativeWeightedHeightNodeSelection
