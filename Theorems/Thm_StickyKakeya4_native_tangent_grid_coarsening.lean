import Theorems.Thm_StickyKakeya4_original_height_interval_cap
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace NativeTangentGridCoarsening

open scoped BigOperators
noncomputable section
open Classical

/-- Occupied cells of the literal scalar grid, with the original labels retained. -/
def scalarCells {X : Type*} (P : Finset X) (x : X → ℝ) (r : ℝ) : Finset ℤ :=
  P.image (fun v => ⌊x v / r⌋)

/-- Occupied cells of the literal planar product grid. -/
def planarCells {X : Type*} (P : Finset X) (x : X → ℝ × ℝ) (r : ℝ) : Finset (ℤ × ℤ) :=
  P.image (fun v => (⌊(x v).1 / r⌋, ⌊(x v).2 / r⌋))

/-- Count grid cells occupied by any finite family whose scalar coordinates
lie in an interval. No injectivity or multiplicity hypothesis on labels is used. -/
theorem scalar_interval_grid_card {X : Type*} (P : Finset X) (x : X → ℝ)
    {r c L : ℝ} (hr : 0 < r) (hL : 0 ≤ L)
    (hinterval : ∀ v ∈ P, c ≤ x v ∧ x v ≤ c + L) :
    ((scalarCells P x r).card : ℝ) ≤ L / r + 2 := by
  have hsub : scalarCells P x r ⊆ Finset.Icc ⌊c / r⌋ ⌊(c + L) / r⌋ := by
    intro k hk
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mpr
      ⟨Int.floor_mono (div_le_div_of_nonneg_right (hinterval v hv).1 hr.le),
       Int.floor_mono (div_le_div_of_nonneg_right (hinterval v hv).2 hr.le)⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (OriginalHeightIntervalCap.floor_interval_card r c L hr hL)

/-- Local interval-image version, useful for retaining the original ancestors
whose coordinates meet a prescribed interval. -/
theorem scalar_filtered_interval_grid_card {X : Type*} (P : Finset X) (x : X → ℝ)
    {r c L : ℝ} (hr : 0 < r) (hL : 0 ≤ L) :
    ((scalarCells (P.filter (fun v => c ≤ x v ∧ x v ≤ c + L)) x r).card : ℝ)
      ≤ L / r + 2 := by
  exact scalar_interval_grid_card _ x hr hL (fun v hv => (Finset.mem_filter.mp hv).2)

/-- The planar rectangle count is the product of the two actual integer
interval counts, rather than an assumed endpoint multiplicity. -/
theorem planar_rectangle_grid_card {X : Type*} (P : Finset X) (x : X → ℝ × ℝ)
    {r c₁ c₂ L₁ L₂ : ℝ} (hr : 0 < r) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hrectangle : ∀ v ∈ P,
      (c₁ ≤ (x v).1 ∧ (x v).1 ≤ c₁ + L₁) ∧
      (c₂ ≤ (x v).2 ∧ (x v).2 ≤ c₂ + L₂)) :
    ((planarCells P x r).card : ℝ) ≤ (L₁ / r + 2) * (L₂ / r + 2) := by
  let Q₁ := Finset.Icc ⌊c₁ / r⌋ ⌊(c₁ + L₁) / r⌋
  let Q₂ := Finset.Icc ⌊c₂ / r⌋ ⌊(c₂ + L₂) / r⌋
  have hsub : planarCells P x r ⊆ Q₁ ×ˢ Q₂ := by
    intro k hk
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hk
    have h := hrectangle v hv
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨Int.floor_mono (div_le_div_of_nonneg_right h.1.1 hr.le),
         Int.floor_mono (div_le_div_of_nonneg_right h.1.2 hr.le)⟩,
       Finset.mem_Icc.mpr
        ⟨Int.floor_mono (div_le_div_of_nonneg_right h.2.1 hr.le),
         Int.floor_mono (div_le_div_of_nonneg_right h.2.2 hr.le)⟩⟩
  have h₁ : (Q₁.card : ℝ) ≤ L₁ / r + 2 :=
    OriginalHeightIntervalCap.floor_interval_card r c₁ L₁ hr hL₁
  have h₂ : (Q₂.card : ℝ) ≤ L₂ / r + 2 :=
    OriginalHeightIntervalCap.floor_interval_card r c₂ L₂ hr hL₂
  calc
    ((planarCells P x r).card : ℝ) ≤ ((Q₁ ×ˢ Q₂).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = (Q₁.card : ℝ) * (Q₂.card : ℝ) := by simp only [Finset.card_product, Nat.cast_mul]
    _ ≤ (L₁ / r + 2) * (L₂ / r + 2) :=
      mul_le_mul h₁ h₂ (by positivity) (by positivity)

/-- Filtered rectangle-image bound on the unchanged original label family. -/
theorem planar_filtered_rectangle_grid_card {X : Type*}
    (P : Finset X) (x : X → ℝ × ℝ)
    {r c₁ c₂ L₁ L₂ : ℝ} (hr : 0 < r) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    ((planarCells (P.filter (fun v =>
      (c₁ ≤ (x v).1 ∧ (x v).1 ≤ c₁ + L₁) ∧
      (c₂ ≤ (x v).2 ∧ (x v).2 ≤ c₂ + L₂))) x r).card : ℝ)
      ≤ (L₁ / r + 2) * (L₂ / r + 2) := by
  exact planar_rectangle_grid_card _ x hr hL₁ hL₂
    (fun v hv => (Finset.mem_filter.mp hv).2)

/-- A coarse floor cell is contained in its literal closed interval. -/
lemma coarse_floor_interval {y sigma : ℝ} (hsigma : 0 < sigma) {k : ℤ}
    (hk : ⌊y / sigma⌋ = k) :
    sigma * (k : ℝ) ≤ y ∧ y ≤ sigma * (k : ℝ) + sigma := by
  have hl := (le_div_iff₀ hsigma).mp (Int.floor_le (y / sigma))
  have hu := (div_lt_iff₀ hsigma).mp (Int.lt_floor_add_one (y / sigma))
  rw [hk] at hl hu
  constructor <;> nlinarith

/-- The actual fine cells occupied inside one coarse cell satisfy the
one-dimensional geometric fiber bound. -/
theorem scalar_coarse_fiber_card {X : Type*} (P : Finset X) (x : X → ℝ)
    {r sigma : ℝ} (hr : 0 < r) (hsigma : 0 < sigma) (k : ℤ) :
    ((scalarCells (P.filter (fun v => ⌊x v / sigma⌋ = k)) x r).card : ℝ)
      ≤ sigma / r + 2 := by
  exact scalar_interval_grid_card _ x hr hsigma.le
    (fun v hv => coarse_floor_interval hsigma (Finset.mem_filter.mp hv).2)

/-- The product of the two literal coordinate interval counts gives the
planar coarse-cell fiber bound. -/
theorem planar_coarse_fiber_card {X : Type*} (P : Finset X) (x : X → ℝ × ℝ)
    {r sigma : ℝ} (hr : 0 < r) (hsigma : 0 < sigma) (k : ℤ × ℤ) :
    ((planarCells (P.filter (fun v =>
      (⌊(x v).1 / sigma⌋, ⌊(x v).2 / sigma⌋) = k)) x r).card : ℝ)
      ≤ (sigma / r + 2) ^ 2 := by
  have hrect : ∀ v ∈ P.filter (fun v =>
      (⌊(x v).1 / sigma⌋, ⌊(x v).2 / sigma⌋) = k),
      (sigma * (k.1 : ℝ) ≤ (x v).1 ∧ (x v).1 ≤ sigma * (k.1 : ℝ) + sigma) ∧
      (sigma * (k.2 : ℝ) ≤ (x v).2 ∧ (x v).2 ≤ sigma * (k.2 : ℝ) + sigma) := by
    intro v hv
    have hk := (Finset.mem_filter.mp hv).2
    exact ⟨coarse_floor_interval hsigma (congrArg Prod.fst hk),
      coarse_floor_interval hsigma (congrArg Prod.snd hk)⟩
  simpa only [pow_two] using planar_rectangle_grid_card _ x hr hsigma.le hsigma.le hrect

/-- A union of the actual fiber images covers the entire occupied image.
This works even when a fine cell meets several coarse cells. -/
lemma image_card_le_real_mul_of_fiber_images {X Y Z : Type*}
    [DecidableEq Y] [DecidableEq Z]
    (P : Finset X) (f : X → Y) (g : X → Z) (B : ℝ)
    (hfiber : ∀ k ∈ P.image g,
      (((P.filter (fun v => g v = k)).image f).card : ℝ) ≤ B) :
    ((P.image f).card : ℝ) ≤ B * ((P.image g).card : ℝ) := by
  let Q := P.image g
  let F := fun k => (P.filter (fun v => g v = k)).image f
  have hcover : P.image f ⊆ Q.biUnion F := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_biUnion.mpr ⟨g v, Finset.mem_image_of_mem _ hv,
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hv, rfl⟩)⟩
  calc
    ((P.image f).card : ℝ) ≤ ((Q.biUnion F).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ k ∈ Q, ((F k).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Q, B := Finset.sum_le_sum hfiber
    _ = B * ((P.image g).card : ℝ) := by simp [Q, mul_comm]

/-- Coarsening actual occupied scalar cells of the same original finite family. -/
theorem scalar_grid_coarsening_add_two {X : Type*} (P : Finset X) (x : X → ℝ)
    {r sigma : ℝ} (hr : 0 < r) (hsigma : 0 < sigma) :
    ((scalarCells P x r).card : ℝ) ≤
      (sigma / r + 2) * ((scalarCells P x sigma).card : ℝ) := by
  exact image_card_le_real_mul_of_fiber_images P
    (fun v => ⌊x v / r⌋) (fun v => ⌊x v / sigma⌋) _
    (fun k _hk => scalar_coarse_fiber_card P x hr hsigma k)

/-- Coarsening actual occupied planar cells of the same original finite family. -/
theorem planar_grid_coarsening_add_two {X : Type*} (P : Finset X) (x : X → ℝ × ℝ)
    {r sigma : ℝ} (hr : 0 < r) (hsigma : 0 < sigma) :
    ((planarCells P x r).card : ℝ) ≤
      (sigma / r + 2) ^ 2 * ((planarCells P x sigma).card : ℝ) := by
  exact image_card_le_real_mul_of_fiber_images P
    (fun v => (⌊(x v).1 / r⌋, ⌊(x v).2 / r⌋))
    (fun v => (⌊(x v).1 / sigma⌋, ⌊(x v).2 / sigma⌋)) _
    (fun k _hk => planar_coarse_fiber_card P x hr hsigma k)

lemma ratio_add_two_le_three {r sigma : ℝ} (hr : 0 < r) (hscale : r ≤ sigma) :
    sigma / r + 2 ≤ 3 * sigma / r := by
  have hratio : 1 ≤ sigma / r := (le_div_iff₀ hr).mpr (by simpa using hscale)
  have hid : 3 * sigma / r = 3 * (sigma / r) := by ring
  rw [hid]
  linarith

/-- The complete scalar coarsening chain at an original coarser scale. -/
theorem scalar_grid_coarsening_chain {X : Type*} (P : Finset X) (x : X → ℝ)
    {r sigma : ℝ} (hr : 0 < r) (hscale : r ≤ sigma) :
    ((scalarCells P x r).card : ℝ) ≤
      (sigma / r + 2) * ((scalarCells P x sigma).card : ℝ) ∧
    (sigma / r + 2) * ((scalarCells P x sigma).card : ℝ) ≤
      (3 * sigma / r) * ((scalarCells P x sigma).card : ℝ) := by
  exact ⟨scalar_grid_coarsening_add_two P x hr (hr.trans_le hscale),
    mul_le_mul_of_nonneg_right (ratio_add_two_le_three hr hscale) (by positivity)⟩

/-- The complete planar coarsening chain, with exponent two. -/
theorem planar_grid_coarsening_chain {X : Type*} (P : Finset X) (x : X → ℝ × ℝ)
    {r sigma : ℝ} (hr : 0 < r) (hscale : r ≤ sigma) :
    ((planarCells P x r).card : ℝ) ≤
      (sigma / r + 2) ^ 2 * ((planarCells P x sigma).card : ℝ) ∧
    (sigma / r + 2) ^ 2 * ((planarCells P x sigma).card : ℝ) ≤
      (3 * sigma / r) ^ 2 * ((planarCells P x sigma).card : ℝ) := by
  have hsigma : 0 < sigma := hr.trans_le hscale
  have hrat := ratio_add_two_le_three hr hscale
  have hpow : (sigma / r + 2) ^ 2 ≤ (3 * sigma / r) ^ 2 := by
    nlinarith [show 0 ≤ sigma / r by positivity]
  exact ⟨planar_grid_coarsening_add_two P x hr hsigma,
    mul_le_mul_of_nonneg_right hpow (by positivity)⟩

/-- Convenient scalar endpoint-cell to original sigma-cell bound. -/
theorem scalar_grid_coarsening {X : Type*} (P : Finset X) (x : X → ℝ)
    {r sigma : ℝ} (hr : 0 < r) (hscale : r ≤ sigma) :
    ((scalarCells P x r).card : ℝ) ≤
      (3 * sigma / r) * ((scalarCells P x sigma).card : ℝ) := by
  have h := scalar_grid_coarsening_chain P x hr hscale
  exact h.1.trans h.2

/-- Convenient planar endpoint-cell to original sigma-cell bound. -/
theorem planar_grid_coarsening {X : Type*} (P : Finset X) (x : X → ℝ × ℝ)
    {r sigma : ℝ} (hr : 0 < r) (hscale : r ≤ sigma) :
    ((planarCells P x r).card : ℝ) ≤
      (3 * sigma / r) ^ 2 * ((planarCells P x sigma).card : ℝ) := by
  have h := planar_grid_coarsening_chain P x hr hscale
  exact h.1.trans h.2

/-- Centered-interval version in units of the unchanged grid scale. -/
theorem scalar_centered_grid_card {X : Type*} (P : Finset X) (x : X → ℝ)
    {r R c : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hnear : ∀ v ∈ P, |x v - c| ≤ R * r) :
    ((scalarCells P x r).card : ℝ) ≤ 2 * R + 2 := by
  have hinter : ∀ v ∈ P, c - R * r ≤ x v ∧ x v ≤ (c - R * r) + 2 * R * r := by
    intro v hv
    have h := abs_le.mp (hnear v hv)
    constructor <;> linarith
  have hcard := scalar_interval_grid_card P x hr
    (show 0 ≤ 2 * R * r by positivity) hinter
  have heq : (2 * R * r) / r = 2 * R := by field_simp
  simpa only [heq] using hcard

/-- Centered product-box version in units of the unchanged grid scale. -/
theorem planar_centered_grid_card {X : Type*} (P : Finset X) (x : X → ℝ × ℝ)
    {r R : ℝ} (c : ℝ × ℝ) (hr : 0 < r) (hR : 0 ≤ R)
    (hnear : ∀ v ∈ P,
      |(x v).1 - c.1| ≤ R * r ∧ |(x v).2 - c.2| ≤ R * r) :
    ((planarCells P x r).card : ℝ) ≤ (2 * R + 2) ^ 2 := by
  have hinter : ∀ v ∈ P,
      (c.1 - R * r ≤ (x v).1 ∧ (x v).1 ≤ (c.1 - R * r) + 2 * R * r) ∧
      (c.2 - R * r ≤ (x v).2 ∧ (x v).2 ≤ (c.2 - R * r) + 2 * R * r) := by
    intro v hv
    have h₁ := abs_le.mp (hnear v hv).1
    have h₂ := abs_le.mp (hnear v hv).2
    constructor <;> constructor <;> linarith
  have hcard := planar_rectangle_grid_card P x hr
    (show 0 ≤ 2 * R * r by positivity) (show 0 ≤ 2 * R * r by positivity) hinter
  have heq : (2 * R * r) / r = 2 * R := by field_simp
  simpa only [heq, pow_two] using hcard

/-- Count original scalar ancestors directly when their original grid labels
are injective and the actual coordinates lie near one canonical location. -/
theorem scalar_injective_grid_centered_card {X : Type*} (P : Finset X) (x : X → ℝ)
    {r R c : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hgrid : Set.InjOn (fun v => ⌊x v / r⌋) (↑P))
    (hnear : ∀ v ∈ P, |x v - c| ≤ R * r) :
    (P.card : ℝ) ≤ 2 * R + 2 := by
  have hcard := scalar_centered_grid_card P x hr hR hnear
  simpa only [scalarCells, Finset.card_image_of_injOn hgrid] using hcard

/-- Count original planar ancestors directly from injective original grid
labels and the actual coordinate bounds around one canonical ancestor. -/
theorem planar_injective_grid_centered_card {X : Type*} (P : Finset X) (x : X → ℝ × ℝ)
    {r R : ℝ} (c : ℝ × ℝ) (hr : 0 < r) (hR : 0 ≤ R)
    (hgrid : Set.InjOn (fun v => (⌊(x v).1 / r⌋, ⌊(x v).2 / r⌋)) (↑P))
    (hnear : ∀ v ∈ P,
      |(x v).1 - c.1| ≤ R * r ∧ |(x v).2 - c.2| ≤ R * r) :
    (P.card : ℝ) ≤ (2 * R + 2) ^ 2 := by
  have hcard := planar_centered_grid_card P x c hr hR hnear
  simpa only [planarCells, Finset.card_image_of_injOn hgrid] using hcard

end
end NativeTangentGridCoarsening
