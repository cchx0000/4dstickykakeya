import Theorems.Thm_StickyKakeya4_grid_quotient_ad

set_option autoImplicit false
set_option warningAsError true

namespace NativeSliceGridGeometry

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Three spatial integer coordinates and one height coordinate. -/
abbrev Cell := (Fin 3 → ℤ) × ℤ

/-- The floor quotient defining a spatial cube of side length `R`. -/
def coarseSpatial (R : ℕ) (c : Cell) : Fin 3 → ℤ :=
  fun i => c.1 i / (R : ℤ)

/-- A cylinder retains the exact height and coarsens only the spatial coordinates. -/
def cylinderLabel (R : ℕ) (c : Cell) : ℤ × (Fin 3 → ℤ) :=
  (c.2, coarseSpatial R c)

def cylinder (P : Finset Cell) (R : ℕ) (c : Cell) : Finset Cell :=
  P.filter fun q => cylinderLabel R q = cylinderLabel R c

/-- A closed spatial sup-norm ball within a single height slice. -/
def gridBall (P : Finset Cell) (R : ℕ) (c : Cell) : Finset Cell :=
  P.filter fun q => q.2 = c.2 ∧ ∀ i, |q.1 i - c.1 i| ≤ (R : ℤ)

theorem mem_cylinder_iff (P : Finset Cell) (R : ℕ) (c q : Cell) :
    q ∈ cylinder P R c ↔ q ∈ P ∧ cylinderLabel R q = cylinderLabel R c := by
  exact Finset.mem_filter

theorem mem_gridBall_iff (P : Finset Cell) (R : ℕ) (c q : Cell) :
    q ∈ gridBall P R c ↔ q ∈ P ∧ q.2 = c.2 ∧
      ∀ i, |q.1 i - c.1 i| ≤ (R : ℤ) := by
  exact Finset.mem_filter

/-- Points in one floor cube are within distance `R` in every spatial coordinate. -/
theorem cylinder_subset_gridBall (P : Finset Cell) (R : ℕ) (c : Cell)
    (hR : 0 < R) : cylinder P R c ⊆ gridBall P R c := by
  intro q hq
  obtain ⟨hqP, hlabel⟩ := (mem_cylinder_iff P R c q).mp hq
  have hheight : q.2 = c.2 := congrArg Prod.fst hlabel
  have hspatial : coarseSpatial R q = coarseSpatial R c := congrArg Prod.snd hlabel
  have hbox : q.1 ∈ GridQuotientAD.box c.1 R :=
    GridQuotientAD.same_cell_close 0 R q.1 c.1 (by omega)
      (by
        funext i
        change (q.1 i + 0) / (R : ℤ) = (c.1 i + 0) / (R : ℤ)
        have hi := congrFun hspatial i
        unfold coarseSpatial at hi
        simpa only [add_zero] using hi)
  exact (mem_gridBall_iff P R c q).mpr
    ⟨hqP, hheight, (GridQuotientAD.mem_box_iff c.1 q.1 R).mp hbox⟩

/-- Moving by at most one mesh length changes an integer floor quotient by at most one.
This holds without any nonnegativity assumption on the coordinates. -/
theorem abs_ediv_sub_ediv_le_one (R : ℕ) (x y : ℤ) (hR : 0 < R)
    (hxy : |x - y| ≤ (R : ℤ)) : |x / (R : ℤ) - y / (R : ℤ)| ≤ 1 := by
  have hRp : (0 : ℤ) < R := by exact_mod_cast hR
  obtain ⟨hlo, hhi⟩ := abs_le.mp hxy
  have hl := Int.ediv_le_ediv hRp (show y - (R : ℤ) ≤ x by omega)
  have hu := Int.ediv_le_ediv hRp (show x ≤ y + (R : ℤ) by omega)
  rw [Int.sub_ediv_of_dvd y (dvd_refl (R : ℤ)), Int.ediv_self hRp.ne'] at hl
  rw [Int.add_ediv_of_dvd_right (dvd_refl (R : ℤ)), Int.ediv_self hRp.ne'] at hu
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- The spatial labels met by a ball lie in the three-by-three-by-three neighboring box. -/
theorem coarseSpatial_mem_box_of_mem_gridBall (P : Finset Cell) (R : ℕ)
    (c q : Cell) (hR : 0 < R) (hq : q ∈ gridBall P R c) :
    coarseSpatial R q ∈ GridQuotientAD.box (coarseSpatial R c) 1 := by
  apply (GridQuotientAD.mem_box_iff _ _ _).mpr
  intro i
  exact abs_ediv_sub_ediv_le_one R (q.1 i) (c.1 i) hR
    (((mem_gridBall_iff P R c q).mp hq).2.2 i)

theorem gridBall_coarseSpatial_card_le_27 (P : Finset Cell) (R : ℕ)
    (c : Cell) (hR : 0 < R) :
    ((gridBall P R c).image (coarseSpatial R)).card ≤ 27 := by
  have hsub : (gridBall P R c).image (coarseSpatial R) ⊆
      GridQuotientAD.box (coarseSpatial R c) 1 := by
    intro v hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    exact coarseSpatial_mem_box_of_mem_gridBall P R c q hR hq
  simpa [GridQuotientAD.box_card] using Finset.card_le_card hsub

/-- An occupied-cylinder comparison bounds a ball by at most 27 reference cylinders.
The reference point `d` may be at any height; the ball center need not belong to `P`. -/
theorem gridBall_card_le_27_mul_cylinder (P : Finset Cell) (R K : ℕ)
    (c d : Cell) (hR : 0 < R) (hd : d ∈ P)
    (hcompare : ∀ a ∈ P, ∀ b ∈ P,
      (cylinder P R a).card ≤ K * (cylinder P R b).card) :
    (gridBall P R c).card ≤ (27 * K) * (cylinder P R d).card := by
  have hcap : (gridBall P R c).card ≤
      (K * (cylinder P R d).card) *
        (GridQuotientAD.box (coarseSpatial R c) 1).card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f := coarseSpatial R)
    · intro q hq
      exact coarseSpatial_mem_box_of_mem_gridBall P R c q hR hq
    · intro v _hv
      let S := (gridBall P R c).filter fun q => coarseSpatial R q = v
      change S.card ≤ K * (cylinder P R d).card
      by_cases hS : S.Nonempty
      · obtain ⟨a, ha⟩ := hS
        obtain ⟨haBall, haKey⟩ := Finset.mem_filter.mp ha
        obtain ⟨haP, haHeight, _haClose⟩ := (mem_gridBall_iff P R c a).mp haBall
        have hsub : S ⊆ cylinder P R a := by
          intro q hq
          obtain ⟨hqBall, hqKey⟩ := Finset.mem_filter.mp hq
          obtain ⟨hqP, hqHeight, _hqClose⟩ := (mem_gridBall_iff P R c q).mp hqBall
          apply (mem_cylinder_iff P R a q).mpr
          exact ⟨hqP, Prod.ext (hqHeight.trans haHeight.symm) (hqKey.trans haKey.symm)⟩
        exact (Finset.card_le_card hsub).trans (hcompare a haP d hd)
      · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
  simpa [GridQuotientAD.box_card, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcap

/-- Uniform occupied-cylinder counts give uniform slice-ball counts, including
comparisons between points at different heights. The geometric loss is exactly 27. -/
theorem gridBall_card_comparable (P : Finset Cell) (R K : ℕ)
    (hR : 0 < R)
    (hcompare : ∀ a ∈ P, ∀ b ∈ P,
      (cylinder P R a).card ≤ K * (cylinder P R b).card) :
    ∀ c ∈ P, ∀ d ∈ P,
      (gridBall P R c).card ≤ (27 * K) * (gridBall P R d).card := by
  intro c _hc d hd
  exact (gridBall_card_le_27_mul_cylinder P R K c d hR hd hcompare).trans
    (Nat.mul_le_mul_left (27 * K)
      (Finset.card_le_card (cylinder_subset_gridBall P R d hR)))

end

end NativeSliceGridGeometry
