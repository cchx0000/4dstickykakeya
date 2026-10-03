import Theorems.Thm_StickyKakeya4_self_uniform_incidence_refinement

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

namespace SelfUniform

variable {α : Type*}

/-- Self-uniformity for a partition forces every occupied final grain to carry
at least a `1 / (Q^2 * #(A.image label))` fraction of the retained mass. The
statement uses natural-number cross multiplication and arbitrary label types;
only the labels occurring in the finite original set are counted. -/
theorem partition_richness_of_self_uniform {β : Type*} [DecidableEq β]
    (w : α → ℕ) (label : α → β) (Q : ℕ) {A B : Finset α}
    (hBA : B ⊆ A)
    (huniform : ∀ x y, x ∈ B → y ∈ B →
      degree w (fun a b => label a = label b) B x ≤
        Q ^ 2 * degree w (fun a b => label a = label b) B y)
    {x : α} (hx : x ∈ B) :
    mass w B ≤ Q ^ 2 * (A.image label).card *
      degree w (fun a b => label a = label b) B x := by
  classical
  let D : β → ℕ := fun t => ∑ y ∈ B, if label y = t then w y else 0
  have hsum : mass w B = ∑ t ∈ A.image label, D t := by
    simpa only [mass, D, Finset.sum_filter] using
      (Finset.sum_fiberwise_of_maps_to (s := B) (t := A.image label) (g := label)
        (fun y hy => Finset.mem_image_of_mem label (hBA hy)) w).symm
  have hD : ∀ t ∈ A.image label,
      D t ≤ Q ^ 2 * degree w (fun a b => label a = label b) B x := by
    intro t _ht
    by_cases ht : ∃ y ∈ B, label y = t
    · obtain ⟨y, hy, hyt⟩ := ht
      calc
        D t = degree w (fun a b => label a = label b) B y := by
          simp only [D, degree, hyt, eq_comm]
        _ ≤ Q ^ 2 * degree w (fun a b => label a = label b) B x :=
          huniform y x hy hx
    · have hzero : D t = 0 := by
        apply Finset.sum_eq_zero
        intro y hy
        exact if_neg (fun h => ht ⟨y, hy, h⟩)
      rw [hzero]
      exact Nat.zero_le _
  calc
    mass w B = ∑ t ∈ A.image label, D t := hsum
    _ ≤ ∑ _t ∈ A.image label,
        Q ^ 2 * degree w (fun a b => label a = label b) B x :=
      Finset.sum_le_sum hD
    _ = Q ^ 2 * (A.image label).card *
        degree w (fun a b => label a = label b) B x := by
      simp only [Finset.sum_const, smul_eq_mul]
      ring

/-- A single simultaneous refinement for existing incidence relations and
fixed grain partitions. Appending the grain equivalence relations to the
original relations and applying `weighted_self_uniform_refinement` once
constructs a nonempty retained set. The same set is self-uniform for every
original relation and quantitatively rich in every one of its occupied grains,
with the original construction's mass loss at dimension `d + g`.

The label type may depend on the grain level, and no global finiteness of any
label type is required. Neither a final core nor a richness certificate is an
input. -/
theorem weighted_self_uniform_grain_refinement {d g Q L : ℕ}
    {β : Fin g → Type*} [∀ j, DecidableEq (β j)]
    (hdg : 0 < d + g) (hQ : 4 ≤ Q) (w : α → ℕ)
    (R : Fin d → α → α → Prop) (hrefl : ∀ i x, R i x x)
    (hsym : ∀ i x y, R i x y → R i y x)
    (label : ∀ j, α → β j)
    (A : Finset α) (hne : A.Nonempty) (hw : ∀ x ∈ A, 0 < w x)
    (hheight : mass w A ≤ Q ^ L) :
    ∃ B ⊆ A, B.Nonempty ∧
      mass w A ≤ 2 * (4 * (d + g)) ^ ((d + g) * L) * mass w B ∧
      (∀ i x y, x ∈ B → y ∈ B →
        degree w (R i) B x ≤ Q ^ 2 * degree w (R i) B y) ∧
      (∀ j x, x ∈ B →
        mass w B ≤ Q ^ 2 * (A.image (label j)).card *
          degree w (fun a b => label j a = label j b) B x) := by
  classical
  let T : Fin (d + g) → α → α → Prop :=
    Fin.addCases R (fun j x y => label j x = label j y)
  have hTrefl : ∀ i x, T i x x := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro k x
      simpa only [T, Fin.addCases_left] using hrefl k x
    · intro j x
      simp only [T, Fin.addCases_right]
  have hTsym : ∀ i x y, T i x y → T i y x := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro k x y
      simpa only [T, Fin.addCases_left] using hsym k x y
    · intro j x y
      simpa only [T, Fin.addCases_right] using
        (fun h : label j x = label j y => h.symm)
  obtain ⟨B, hBA, hBne, hBmass, hBuniform⟩ :=
    weighted_self_uniform_refinement hdg hQ w T hTrefl hTsym A hne hw hheight
  refine ⟨B, hBA, hBne, hBmass, ?_, ?_⟩
  · intro i x y hx hy
    simpa only [T, Fin.addCases_left] using
      hBuniform (Fin.castAdd g i) x y hx hy
  · intro j x hx
    apply partition_richness_of_self_uniform w (label j) Q hBA ?_ hx
    intro y z hy hz
    simpa only [T, Fin.addCases_right] using
      hBuniform (Fin.natAdd d j) y z hy hz

end SelfUniform
