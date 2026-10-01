import Theorems.Thm_StickyKakeya4_dense_bipartite_genuine_four_cycle
import Theorems.Thm_StickyKakeya4_four_cycle_contact_frame

open Set

noncomputable section

namespace StickyKakeya4

/-- Read a bipartite `K_{2,2}` on marked lines in the cyclic order
`left₀, right₀, left₁, right₁`. -/
def GenuineBipartiteFourCycle.toMarkedCycle
    {X Y : Finset MarkedLine} {E : Finset (MarkedLine × MarkedLine)}
    (cycle : GenuineBipartiteFourCycle X Y E) : Fin 4 → MarkedLine :=
  ![cycle.left₀, cycle.right₀, cycle.left₁, cycle.right₁]

@[simp] theorem GenuineBipartiteFourCycle.toMarkedCycle_zero
    {X Y : Finset MarkedLine} {E : Finset (MarkedLine × MarkedLine)}
    (cycle : GenuineBipartiteFourCycle X Y E) :
    cycle.toMarkedCycle 0 = cycle.left₀ := rfl

@[simp] theorem GenuineBipartiteFourCycle.toMarkedCycle_one
    {X Y : Finset MarkedLine} {E : Finset (MarkedLine × MarkedLine)}
    (cycle : GenuineBipartiteFourCycle X Y E) :
    cycle.toMarkedCycle 1 = cycle.right₀ := rfl

@[simp] theorem GenuineBipartiteFourCycle.toMarkedCycle_two
    {X Y : Finset MarkedLine} {E : Finset (MarkedLine × MarkedLine)}
    (cycle : GenuineBipartiteFourCycle X Y E) :
    cycle.toMarkedCycle 2 = cycle.left₁ := rfl

@[simp] theorem GenuineBipartiteFourCycle.toMarkedCycle_three
    {X Y : Finset MarkedLine} {E : Finset (MarkedLine × MarkedLine)}
    (cycle : GenuineBipartiteFourCycle X Y E) :
    cycle.toMarkedCycle 3 = cycle.right₁ := rfl

/-- Disjoint left and right parts turn the two within-part inequalities of a
genuine bipartite cycle into four pairwise distinct marked lines. -/
theorem GenuineBipartiteFourCycle.toMarkedCycle_injective
    {X Y : Finset MarkedLine} {E : Finset (MarkedLine × MarkedLine)}
    (cycle : GenuineBipartiteFourCycle X Y E)
    (hXY : Disjoint X Y) : Function.Injective cycle.toMarkedCycle := by
  have hcross : ∀ x ∈ X, ∀ y ∈ Y, x ≠ y := by
    intro x hx y hy hxy
    subst y
    exact (Finset.disjoint_left.mp hXY hx hy)
  have h00 : cycle.left₀ ≠ cycle.right₀ :=
    hcross cycle.left₀ cycle.left₀_mem cycle.right₀ cycle.right₀_mem
  have h01 : cycle.left₀ ≠ cycle.right₁ :=
    hcross cycle.left₀ cycle.left₀_mem cycle.right₁ cycle.right₁_mem
  have h10 : cycle.left₁ ≠ cycle.right₀ :=
    hcross cycle.left₁ cycle.left₁_mem cycle.right₀ cycle.right₀_mem
  have h11 : cycle.left₁ ≠ cycle.right₁ :=
    hcross cycle.left₁ cycle.left₁_mem cycle.right₁ cycle.right₁_mem
  have hleft : cycle.left₀ ≠ cycle.left₁ := cycle.left_ne
  have hright : cycle.right₀ ≠ cycle.right₁ := cycle.right_ne
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [toMarkedCycle, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.isValue] at hij ⊢ <;>
    simp_all

/-- Disjoint ambient parts are unnecessary when every relation edge is
off-diagonal: the four `K_{2,2}` edges themselves rule out all cross-side
identifications, while genuine-cycle data already separates each side. -/
theorem GenuineBipartiteFourCycle.toMarkedCycle_injective_of_irrefl
    {X Y : Finset MarkedLine} {E : Finset (MarkedLine × MarkedLine)}
    (cycle : GenuineBipartiteFourCycle X Y E)
    (hirrefl : ∀ line, (line, line) ∉ E) :
    Function.Injective cycle.toMarkedCycle := by
  have h00 : cycle.left₀ ≠ cycle.right₀ := by
    intro h
    exact hirrefl cycle.left₀ (h ▸ cycle.edge₀₀)
  have h01 : cycle.left₀ ≠ cycle.right₁ := by
    intro h
    exact hirrefl cycle.left₀ (h ▸ cycle.edge₀₁)
  have h10 : cycle.left₁ ≠ cycle.right₀ := by
    intro h
    exact hirrefl cycle.left₁ (h ▸ cycle.edge₁₀)
  have h11 : cycle.left₁ ≠ cycle.right₁ := by
    intro h
    exact hirrefl cycle.left₁ (h ▸ cycle.edge₁₁)
  have hleft : cycle.left₀ ≠ cycle.left₁ := cycle.left_ne
  have hright : cycle.right₀ ≠ cycle.right₁ := cycle.right_ne
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [toMarkedCycle, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.isValue] at hij ⊢ <;>
    simp_all

theorem GenuineBipartiteFourCycle.toMarkedCycle_mem_selector
    {selector : Set MarkedLine}
    {X Y : Finset MarkedLine} {E : Finset (MarkedLine × MarkedLine)}
    (cycle : GenuineBipartiteFourCycle X Y E)
    (hXselector : ∀ line ∈ X, line ∈ selector)
    (hYselector : ∀ line ∈ Y, line ∈ selector) :
    ∀ i, cycle.toMarkedCycle i ∈ selector := by
  intro i
  fin_cases i <;>
    simp [toMarkedCycle,
      hXselector cycle.left₀ cycle.left₀_mem,
      hXselector cycle.left₁ cycle.left₁_mem,
      hYselector cycle.right₀ cycle.right₀_mem,
      hYselector cycle.right₁ cycle.right₁_mem]

theorem GenuineBipartiteFourCycle.toMarkedCycle_edges
    {X Y : Finset MarkedLine} {E : Finset (MarkedLine × MarkedLine)}
    (cycle : GenuineBipartiteFourCycle X Y E) :
    (cycle.toMarkedCycle 0, cycle.toMarkedCycle 1) ∈ E ∧
    (cycle.toMarkedCycle 2, cycle.toMarkedCycle 1) ∈ E ∧
    (cycle.toMarkedCycle 2, cycle.toMarkedCycle 3) ∈ E ∧
    (cycle.toMarkedCycle 0, cycle.toMarkedCycle 3) ∈ E := by
  simpa using ⟨cycle.edge₀₀, cycle.edge₁₀, cycle.edge₁₁, cycle.edge₀₁⟩

/-- A dense collision relation between two disjoint finite families of
actual selector lines produces four pairwise distinct selector lines in
cyclic order, together with the four physical relation edges. -/
theorem dense_bipartite_has_marked_four_cycle
    (selector : Set MarkedLine)
    (X Y : Finset MarkedLine) (hXY : Disjoint X Y)
    (hX : X.Nonempty) (hY : Y.Nonempty)
    (hXselector : ∀ line ∈ X, line ∈ selector)
    (hYselector : ∀ line ∈ Y, line ∈ selector)
    (E : Finset (MarkedLine × MarkedLine)) (hE_sub : E ⊆ X ×ˢ Y)
    (c : ℝ) (hc_pos : 0 < c) (hc_le : c ≤ 1)
    (hE_dense : c * (X.card : ℝ) * (Y.card : ℝ) ≤ (E.card : ℝ))
    (hX_large : 4 ≤ c * (X.card : ℝ))
    (hY_large : 8 < c ^ 2 * (Y.card : ℝ)) :
    ∃ line : Fin 4 → MarkedLine,
      Function.Injective line ∧
      (∀ i, line i ∈ selector) ∧
      (line 0, line 1) ∈ E ∧
      (line 2, line 1) ∈ E ∧
      (line 2, line 3) ∈ E ∧
      (line 0, line 3) ∈ E := by
  let cycle := Classical.choice
    (dense_bipartite_has_genuine_four_cycle X Y hX hY E hE_sub
      c hc_pos hc_le hE_dense hX_large hY_large)
  refine ⟨cycle.toMarkedCycle,
    cycle.toMarkedCycle_injective hXY,
    cycle.toMarkedCycle_mem_selector hXselector hYselector, ?_⟩
  exact cycle.toMarkedCycle_edges

/-- Looplessness is the intrinsic hypothesis needed for a marked four-cycle.
This form applies directly to a collision graph on one finite family, with the
same family used on the two sides of the bipartite DRC argument. -/
theorem dense_bipartite_has_marked_four_cycle_of_irrefl
    (selector : Set MarkedLine)
    (X Y : Finset MarkedLine)
    (hX : X.Nonempty) (hY : Y.Nonempty)
    (hXselector : ∀ line ∈ X, line ∈ selector)
    (hYselector : ∀ line ∈ Y, line ∈ selector)
    (E : Finset (MarkedLine × MarkedLine)) (hE_sub : E ⊆ X ×ˢ Y)
    (hE_irrefl : ∀ line, (line, line) ∉ E)
    (c : ℝ) (hc_pos : 0 < c) (hc_le : c ≤ 1)
    (hE_dense : c * (X.card : ℝ) * (Y.card : ℝ) ≤ (E.card : ℝ))
    (hX_large : 4 ≤ c * (X.card : ℝ))
    (hY_large : 8 < c ^ 2 * (Y.card : ℝ)) :
    ∃ line : Fin 4 → MarkedLine,
      Function.Injective line ∧
      (∀ i, line i ∈ selector) ∧
      (line 0, line 1) ∈ E ∧
      (line 2, line 1) ∈ E ∧
      (line 2, line 3) ∈ E ∧
      (line 0, line 3) ∈ E := by
  let cycle := Classical.choice
    (dense_bipartite_has_genuine_four_cycle X Y hX hY E hE_sub
      c hc_pos hc_le hE_dense hX_large hY_large)
  refine ⟨cycle.toMarkedCycle,
    cycle.toMarkedCycle_injective_of_irrefl hE_irrefl,
    cycle.toMarkedCycle_mem_selector hXselector hYselector, ?_⟩
  exact cycle.toMarkedCycle_edges

end StickyKakeya4
