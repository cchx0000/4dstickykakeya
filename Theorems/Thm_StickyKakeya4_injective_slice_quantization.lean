import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option warningAsError true
namespace InjectiveSliceQuantization

abbrev Index (k l : ℕ) := ((Fin k → ℤ) × (Fin l → ℤ)) × ℤ
abbrev Point (k l : ℕ) := ((Fin k → ℝ) × (Fin l → ℝ)) × ℝ
abbrev Shift (k l : ℕ) := (Fin k → ℤ) → ℤ → Fin l → ℝ

/-- The label map is a translation of the y-indices on each fixed (x,time) slice.
Its inverse subtracts precisely the same integer translation. -/
noncomputable def labelEquiv {k l : ℕ} (τ : ℝ) (S : Shift k l) :
    Index k l ≃ Index k l where
  toFun a := ((a.1.1, fun i => a.1.2 i + ⌊(1 / 2 : ℝ) - S a.1.1 a.2 i / τ⌋), a.2)
  invFun a := ((a.1.1, fun i => a.1.2 i - ⌊(1 / 2 : ℝ) - S a.1.1 a.2 i / τ⌋), a.2)
  left_inv := by rintro ⟨⟨x, y⟩, t⟩; simp
  right_inv := by rintro ⟨⟨x, y⟩, t⟩; simp

/-- Centers of the common grid, including the time coordinate. -/
noncomputable def center {k l : ℕ} (τ : ℝ) (a : Index k l) : Point k l :=
  ((fun i => τ * ((a.1.1 i : ℝ) + 1 / 2),
    fun i => τ * ((a.1.2 i : ℝ) + 1 / 2)), τ * ((a.2 : ℝ) + 1 / 2))

/-- A quotient-grid label interpreted on the deformed slice. -/
noncomputable def deformedPoint {k l : ℕ} (τ : ℝ) (S : Shift k l) (a : Index k l) : Point k l :=
  ((fun i => τ * ((a.1.1 i : ℝ) + 1 / 2),
    fun i => τ * (a.1.2 i : ℝ) + S a.1.1 a.2 i), τ * ((a.2 : ℝ) + 1 / 2))

noncomputable def quantize {k l : ℕ} (τ : ℝ) (S : Shift k l) (a : Index k l) : Point k l :=
  deformedPoint τ S (labelEquiv τ S a)

theorem label_bijective {k l : ℕ} (τ : ℝ) (S : Shift k l) :
    Function.Bijective (labelEquiv τ S : Index k l → Index k l) :=
  (labelEquiv τ S).bijective

theorem center_floor_formula (τ s : ℝ) (j : ℤ) (hτ : τ ≠ 0) :
    ⌊(τ * ((j : ℝ) + 1 / 2) - s) / τ⌋ = j + ⌊(1 / 2 : ℝ) - s / τ⌋ := by
  have he : (τ * ((j : ℝ) + 1 / 2) - s) / τ = (j : ℝ) + (1 / 2 - s / τ) := by
    field_simp
    ring
  rw [he, Int.floor_intCast_add]

theorem unchanged_x_time {k l : ℕ} (τ : ℝ) (S : Shift k l) (a : Index k l) :
    (quantize τ S a).1.1 = (center τ a).1.1 ∧
      (quantize τ S a).2 = (center τ a).2 := ⟨rfl, rfl⟩

/-- This is the requested geometric quantization, not only an abstract label map. -/
theorem quantize_y_formula {k l : ℕ} (τ : ℝ) (S : Shift k l) (a : Index k l)
    (hτ : τ ≠ 0) (i : Fin l) :
    (quantize τ S a).1.2 i =
      τ * (⌊((center τ a).1.2 i - S a.1.1 a.2 i) / τ⌋ : ℝ) + S a.1.1 a.2 i := by
  rw [show (center τ a).1.2 i = τ * ((a.1.2 i : ℝ) + 1 / 2) from rfl,
    center_floor_formula τ (S a.1.1 a.2 i) (a.1.2 i) hτ]
  rfl

/-- The quotient coordinate b is literally an integer multiple of τ. -/
theorem quotient_coordinate_in_grid {k l : ℕ} (τ : ℝ) (S : Shift k l)
    (a : Index k l) (i : Fin l) :
    ∃ j : ℤ, (quantize τ S a).1.2 i - S a.1.1 a.2 i = τ * (j : ℝ) := by
  refine ⟨(labelEquiv τ S a).1.2 i, ?_⟩
  simp [quantize, deformedPoint, labelEquiv]

theorem rounding_error (τ y s : ℝ) (hτ : 0 < τ) :
    0 ≤ y - (τ * (⌊(y - s) / τ⌋ : ℝ) + s) ∧
      y - (τ * (⌊(y - s) / τ⌋ : ℝ) + s) < τ := by
  have hlo := (le_div_iff₀ hτ).1 (Int.floor_le ((y - s) / τ))
  have hhi := (div_lt_iff₀ hτ).1 (Int.lt_floor_add_one ((y - s) / τ))
  constructor <;> nlinarith

/-- No norm bound on S, or on a function producing S, is needed for this movement bound. -/
theorem coordinate_error {k l : ℕ} (τ : ℝ) (S : Shift k l) (a : Index k l)
    (hτ : 0 < τ) (i : Fin l) :
    0 ≤ (center τ a).1.2 i - (quantize τ S a).1.2 i ∧
      (center τ a).1.2 i - (quantize τ S a).1.2 i < τ := by
  rw [quantize_y_formula τ S a hτ.ne' i]
  exact rounding_error τ ((center τ a).1.2 i) (S a.1.1 a.2 i) hτ

/-- One-sided rounding errors yield pairwise distortion below τ, rather than 2τ. -/
theorem pairwise_coordinate_distortion {k l : ℕ} (τ : ℝ) (S : Shift k l)
    (a b : Index k l) (hτ : 0 < τ) (i : Fin l) :
    |((quantize τ S a).1.2 i - (quantize τ S b).1.2 i) -
      ((center τ a).1.2 i - (center τ b).1.2 i)| < τ := by
  obtain ⟨ha₀, ha₁⟩ := coordinate_error τ S a hτ i
  obtain ⟨hb₀, hb₁⟩ := coordinate_error τ S b hτ i
  apply abs_lt.2
  constructor <;> linarith

theorem deformedPoint_injective {k l : ℕ} (τ : ℝ) (S : Shift k l) (hτ : τ ≠ 0) :
    Function.Injective (deformedPoint τ S) := by
  rintro ⟨⟨x, y⟩, t⟩ ⟨⟨x', y'⟩, t'⟩ he
  have hx : x = x' := by
    funext i
    have hi := congrArg (fun p : Point k l => p.1.1 i) he
    dsimp [deformedPoint] at hi
    have hc := add_right_cancel (mul_left_cancel₀ hτ hi)
    exact_mod_cast hc
  have ht : t = t' := by
    have hi := congrArg (fun p : Point k l => p.2) he
    dsimp [deformedPoint] at hi
    have hc := add_right_cancel (mul_left_cancel₀ hτ hi)
    exact_mod_cast hc
  subst x'
  subst t'
  have hy : y = y' := by
    funext i
    have hi := congrArg (fun p : Point k l => p.1.2 i) he
    dsimp [deformedPoint] at hi
    have hc := mul_left_cancel₀ hτ (add_right_cancel hi)
    exact_mod_cast hc
  subst y'
  rfl

theorem quantize_injective {k l : ℕ} (τ : ℝ) (S : Shift k l) (hτ : τ ≠ 0) :
    Function.Injective (quantize τ S) :=
  (deformedPoint_injective τ S hτ).comp (labelEquiv τ S).injective

theorem label_image_card {k l : ℕ} (τ : ℝ) (S : Shift k l) (A : Finset (Index k l)) :
    (A.image (labelEquiv τ S)).card = A.card := by
  classical
  exact Finset.card_image_of_injective _ (labelEquiv τ S).injective

theorem quantize_image_card {k l : ℕ} (τ : ℝ) (S : Shift k l)
    (hτ : τ ≠ 0) (A : Finset (Index k l)) :
    (A.image (quantize τ S)).card = A.card := by
  classical
  exact Finset.card_image_of_injective _ (quantize_injective τ S hτ)

/-- Any finite subset chosen after quantization pulls back to original grid labels
without changing its cardinality. -/
theorem original_label_pullback {k l : ℕ} (τ : ℝ) (S : Shift k l) (hτ : τ ≠ 0)
    (A : Finset (Index k l)) (B : Finset (Point k l)) (hB : B ⊆ A.image (quantize τ S)) :
    ∃ C : Finset (Index k l), C ⊆ A ∧ C.image (quantize τ S) = B ∧ C.card = B.card := by
  classical
  let C := A.filter (fun a => quantize τ S a ∈ B)
  have himage : C.image (quantize τ S) = B := by
    ext z
    simp only [Finset.mem_image, C, Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨_, ha⟩, rfl⟩
      exact ha
    · intro hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (hB hz)
      exact ⟨a, ⟨ha, hz⟩, rfl⟩
  refine ⟨C, Finset.filter_subset _ _, himage, ?_⟩
  rw [← himage, quantize_image_card τ S hτ]

end InjectiveSliceQuantization
