import Theorems.Thm_StickyKakeya4_separated_alignment_patches

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

noncomputable section
open Classical SeparatedAlignmentPatches
open scoped BigOperators

namespace NestedPlaneQuantization

abbrev Point := Fin 3 → ℝ
abbrev Index := Fin 3 → ℤ

def H (A C F : ℝ) (p : Point) : Point :=
  ![p 0, p 1 + A * p 0, p 2 + C * p 0 + F * (p 1 + A * p 0)]

def inverse (A C F : ℝ) (p : Point) : Point :=
  ![p 0, p 1 - A * p 0, p 2 - C * p 0 - F * p 1]

@[simp] theorem inverse_H (A C F : ℝ) (p : Point) : inverse A C F (H A C F p) = p := by
  funext j
  fin_cases j <;> simp [H, inverse]
  ring

@[simp] theorem H_inverse (A C F : ℝ) (p : Point) : H A C F (inverse A C F p) = p := by
  funext j
  fin_cases j <;> simp [H, inverse]
  ring

def coordinateEquiv (A C F : ℝ) : Point ≃ Point where
  toFun := H A C F
  invFun := inverse A C F
  left_inv := inverse_H A C F
  right_inv := H_inverse A C F

theorem H_injective (A C F : ℝ) : Function.Injective (H A C F) :=
  (coordinateEquiv A C F).injective

def correctedSlope (A C F : ℝ) : ℝ := C + F * A

def oldPoint (A B x c d : ℝ) : Point := ![x, c + A * x, d + B * x]
def parameters (F x c d : ℝ) : Point := ![x, c, d - F * c]

/-- The lower plane is exact, with the same A and corrected bottom slope C+FA. -/
theorem lower_representation (A C F : ℝ) (p : Point) :
    H A C F p = oldPoint A (correctedSlope A C F) (p 0) (p 1) (p 2 + F * p 1) := by
  funext j
  fin_cases j <;> simp [H, oldPoint, correctedSlope]
  ring

/-- The same point has exact higher quotient p₂. -/
theorem higher_representation (A C F : ℝ) (p : Point) :
    (H A C F p) 2 - C * (H A C F p) 0 - F * (H A C F p) 1 = p 2 := by
  simp [H]
  ring

/-- Before quantization only the bottom coordinate changes. -/
theorem correction_difference (A B C F x c d : ℝ) :
    H A C F (parameters F x c d) - oldPoint A B x c d =
      ![0, 0, (correctedSlope A C F - B) * x] := by
  funext j
  fin_cases j <;> simp [H, parameters, oldPoint, correctedSlope]
  ring

/-- Exact sup-metric displacement, with no slope-consistency bound assumed. -/
theorem correction_distance (A B C F x c d : ℝ) :
    dist (oldPoint A B x c d) (H A C F (parameters F x c d)) =
      |B - correctedSlope A C F| * |x| := by
  have hlast : dist ((oldPoint A B x c d) 2) ((H A C F (parameters F x c d)) 2) =
      |B - correctedSlope A C F| * |x| := by
    rw [Real.dist_eq]
    change |d + B * x - (d - F * c + C * x + F * (c + A * x))| = _
    rw [show d + B * x - (d - F * c + C * x + F * (c + A * x)) =
      (B - correctedSlope A C F) * x by dsimp [correctedSlope]; ring, abs_mul]
  apply le_antisymm
  · apply (dist_pi_le_iff (mul_nonneg (abs_nonneg _) (abs_nonneg _))).mpr
    intro j
    fin_cases j
    · simp [oldPoint, H, parameters]
      positivity
    · simp [oldPoint, H, parameters]
      positivity
    · exact hlast.le
  · rw [← hlast]
    exact dist_le_pi_dist _ _ 2

def coefficientCost (A C F : ℝ) : ℝ := 1 + |A| + |C| + |F| * (1 + |A|)

theorem coefficientCost_nonneg (A C F : ℝ) : 0 ≤ coefficientCost A C F := by
  unfold coefficientCost
  positivity

/-- Explicit sup Lipschitz bound for the triangular reconstruction. -/
theorem H_dist_le (A C F : ℝ) (p q : Point) :
    dist (H A C F p) (H A C F q) ≤ coefficientCost A C F * dist p q := by
  let r := dist p q
  have hr : 0 ≤ r := dist_nonneg
  have hcoord (j : Fin 3) : |p j - q j| ≤ r := by
    exact (Real.dist_eq _ _).symm ▸ dist_le_pi_dist p q j
  have hmiddle : |(p 1 + A * p 0) - (q 1 + A * q 0)| ≤ r + |A| * r := by
    calc
      _ = |(p 1 - q 1) + A * (p 0 - q 0)| := by congr 1; ring
      _ ≤ |p 1 - q 1| + |A| * |p 0 - q 0| := by simpa only [abs_mul] using abs_add_le (p 1 - q 1) (A * (p 0 - q 0))
      _ ≤ r + |A| * r := by gcongr; exact hcoord 1; exact hcoord 0
  have hbottom : |(p 2 + C * p 0 + F * (p 1 + A * p 0)) -
      (q 2 + C * q 0 + F * (q 1 + A * q 0))| ≤ r + |C| * r + |F| * (r + |A| * r) := by
    calc
      _ = |((p 2 - q 2) + C * (p 0 - q 0)) +
          F * ((p 1 + A * p 0) - (q 1 + A * q 0))| := by congr 1; ring
      _ ≤ |p 2 - q 2| + |C| * |p 0 - q 0| +
          |F| * |(p 1 + A * p 0) - (q 1 + A * q 0)| := by
        calc
          _ ≤ |(p 2 - q 2) + C * (p 0 - q 0)| +
              |F * ((p 1 + A * p 0) - (q 1 + A * q 0))| := abs_add_le _ _
          _ ≤ _ := by rw [abs_mul]; gcongr; simpa only [abs_mul] using abs_add_le (p 2 - q 2) (C * (p 0 - q 0))
      _ ≤ r + |C| * r + |F| * (r + |A| * r) := by
        gcongr
        · exact hcoord 2
        · exact hcoord 0
  apply (dist_pi_le_iff (mul_nonneg (coefficientCost_nonneg A C F) hr)).mpr
  intro j
  fin_cases j
  · simp only [H, Real.dist_eq]
    apply (hcoord 0).trans
    dsimp [coefficientCost]
    nlinarith [mul_nonneg (abs_nonneg A) hr, mul_nonneg (abs_nonneg C) hr,
      mul_nonneg (mul_nonneg (abs_nonneg F) (by positivity : 0 ≤ 1 + |A|)) hr]
  · simp only [H, Real.dist_eq]
    apply hmiddle.trans
    dsimp [coefficientCost]
    nlinarith [mul_nonneg (abs_nonneg C) hr,
      mul_nonneg (mul_nonneg (abs_nonneg F) (by positivity : 0 ≤ 1 + |A|)) hr]
  · simp only [H, Real.dist_eq]
    apply hbottom.trans
    dsimp [coefficientCost]
    nlinarith [mul_nonneg (abs_nonneg A) hr]

/-- Literal parameter lattice, before triangular reconstruction. -/
def realize (μ : ℝ) (k : Index) : Point := fun j => μ * (k j : ℝ)
def quantizedIndex (μ : ℝ) (p : Point) : Index := cell μ p
def snap (μ : ℝ) (p : Point) : Point := realize μ (quantizedIndex μ p)
def quantized (μ A C F x c d : ℝ) : Point := H A C F (snap μ (parameters F x c d))

theorem snap_dist_lt (μ : ℝ) (hμ : 0 < μ) (p : Point) : dist p (snap μ p) < μ := by
  apply (dist_pi_lt_iff hμ).mpr
  intro j
  have h := floor_movement μ (p j) 0 hμ
  simp only [add_zero, sub_zero] at h
  simpa only [Real.dist_eq, snap, realize, quantizedIndex, cell, abs_of_nonneg h.1] using h.2

/-- Original point to actual quantized double-plane point, including the exact
slope discrepancy times the old longitudinal coordinate. -/
theorem quantized_movement (μ : ℝ) (hμ : 0 < μ) (A B C F x c d : ℝ) :
    dist (oldPoint A B x c d) (quantized μ A C F x c d) ≤
      coefficientCost A C F * μ + |B - correctedSlope A C F| * |x| := by
  calc
    _ ≤ dist (oldPoint A B x c d) (H A C F (parameters F x c d)) +
        dist (H A C F (parameters F x c d)) (quantized μ A C F x c d) := dist_triangle _ _ _
    _ ≤ |B - correctedSlope A C F| * |x| + coefficientCost A C F * μ := by
      rw [correction_distance]
      apply add_le_add le_rfl
      exact (H_dist_le A C F _ _).trans (mul_le_mul_of_nonneg_left
        (snap_dist_lt μ hμ _).le (coefficientCost_nonneg A C F))
    _ = _ := add_comm _ _

theorem coefficientCost_le_five (A C F : ℝ) (hA : |A| ≤ 1) (hC : |C| ≤ 1) (hF : |F| ≤ 1) :
    coefficientCost A C F ≤ 5 := by
  dsimp [coefficientCost]
  have hprod : |F| * (1 + |A|) ≤ 1 * (1 + 1) := by gcongr
  linarith

/-- Unit coefficient bounds give the explicit movement 5μ+ηX. -/
theorem quantized_movement_bounded (μ : ℝ) (hμ : 0 < μ) (A B C F x c d η X : ℝ)
    (hA : |A| ≤ 1) (hC : |C| ≤ 1) (hF : |F| ≤ 1)
    (hD : |B - correctedSlope A C F| ≤ η) (hx : |x| ≤ X) :
    dist (oldPoint A B x c d) (quantized μ A C F x c d) ≤ 5 * μ + η * X := by
  apply (quantized_movement μ hμ A B C F x c d).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (coefficientCost_le_five A C F hA hC hF) hμ.le
  · exact mul_le_mul hD hx (abs_nonneg _) ((abs_nonneg _).trans hD)

/-- Quantization changes parameters but preserves both exact representations. -/
theorem quantized_representations (μ A C F x c d : ℝ) :
    let p := snap μ (parameters F x c d)
    quantized μ A C F x c d = oldPoint A (correctedSlope A C F) (p 0) (p 1) (p 2 + F * p 1) ∧
      (quantized μ A C F x c d) 2 - C * (quantized μ A C F x c d) 0 -
        F * (quantized μ A C F x c d) 1 = p 2 :=
  ⟨lower_representation A C F _, higher_representation A C F _⟩

/-- Independent parameter rounding sends a fixed original lower grain into one
rounded (c,q) class. The x coordinate may vary throughout that grain. -/
theorem constant_grain_labels (μ F x x' c d : ℝ) :
    (snap μ (parameters F x c d)) 1 = (snap μ (parameters F x' c d)) 1 ∧
      (snap μ (parameters F x c d)) 2 = (snap μ (parameters F x' c d)) 2 := ⟨rfl, rfl⟩

/-- Alternative pointwise coordinates reconstruct each actual input exactly.
Their rounded labels need not be constant across an approximate old grain. -/
def quantizePoint (μ A C F : ℝ) (p : Point) : Point := H A C F (snap μ (inverse A C F p))

theorem quantizePoint_movement (μ : ℝ) (hμ : 0 < μ) (A C F : ℝ) (p : Point) :
    dist p (quantizePoint μ A C F p) ≤ coefficientCost A C F * μ := by
  calc
    _ = dist (H A C F (inverse A C F p)) (H A C F (snap μ (inverse A C F p))) := by
      rw [H_inverse]
      rfl
    _ ≤ coefficientCost A C F * dist (inverse A C F p) (snap μ (inverse A C F p)) := H_dist_le A C F _ _
    _ ≤ coefficientCost A C F * μ := mul_le_mul_of_nonneg_left
      (snap_dist_lt μ hμ _).le (coefficientCost_nonneg A C F)

theorem quantizePoint_higher_quotient (μ A C F : ℝ) (p : Point) :
    (quantizePoint μ A C F p) 2 - C * (quantizePoint μ A C F p) 0 -
      F * (quantizePoint μ A C F p) 1 = (snap μ (inverse A C F p)) 2 :=
  higher_representation A C F _

/-- A genuine old higher witness stays within its recorded error plus one
parameter-mesh step of the pointwise rounded higher quotient. -/
theorem quantizePoint_quotient_witness (μ : ℝ) (hμ : 0 < μ) (A C F : ℝ) (p : Point)
    (y e : ℝ) (hy : |(inverse A C F p) 2 - y| ≤ e) :
    |(snap μ (inverse A C F p)) 2 - y| ≤ μ + e := by
  have hs : |(snap μ (inverse A C F p)) 2 - (inverse A C F p) 2| ≤ μ := by
    rw [abs_sub_comm, ← Real.dist_eq]
    exact (dist_le_pi_dist _ _ 2).trans (snap_dist_lt μ hμ _).le
  calc
    _ = |((snap μ (inverse A C F p)) 2 - (inverse A C F p) 2) +
      ((inverse A C F p) 2 - y)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ μ + e := add_le_add hs hy

/-- Explicit discrepancy between pointwise inverse quotient and the constant
old grain quotient, including both recorded lower-plane residuals. -/
theorem constant_quotient_difference (A B C F c d : ℝ) (p : Point) :
    (inverse A C F p) 2 - (d - F * c) =
      (B - correctedSlope A C F) * p 0 + (p 2 - (d + B * p 0)) -
        F * (p 1 - (c + A * p 0)) := by
  dsimp [inverse, correctedSlope]
  ring

theorem constant_quotient_error (A B C F c d eᵤ eᵥ : ℝ) (p : Point)
    (hu : |p 1 - (c + A * p 0)| ≤ eᵤ) (hv : |p 2 - (d + B * p 0)| ≤ eᵥ) :
    |(inverse A C F p) 2 - (d - F * c)| ≤
      |B - correctedSlope A C F| * |p 0| + eᵥ + |F| * eᵤ := by
  rw [constant_quotient_difference A B C F c d p]
  calc
    _ ≤ |(B - correctedSlope A C F) * p 0 + (p 2 - (d + B * p 0))| +
      |F * (p 1 - (c + A * p 0))| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le ((B - correctedSlope A C F) * p 0 + (p 2 - (d + B * p 0))) 0
            (F * (p 1 - (c + A * p 0)))
    _ ≤ |(B - correctedSlope A C F) * p 0| + |p 2 - (d + B * p 0)| +
      |F * (p 1 - (c + A * p 0))| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by rw [abs_mul, abs_mul]; gcongr

/-- Approximate old lower points can use constant grain labels, with their
original point errors recorded separately from the slope correction. -/
theorem noisy_constant_grain_movement (μ : ℝ) (hμ : 0 < μ) (A B C F c d eᵤ eᵥ : ℝ)
    (p : Point) (hu : |p 1 - (c + A * p 0)| ≤ eᵤ) (hv : |p 2 - (d + B * p 0)| ≤ eᵥ) :
    dist p (quantized μ A C F (p 0) c d) ≤
      max eᵤ eᵥ + coefficientCost A C F * μ + |B - correctedSlope A C F| * |p 0| := by
  have he : 0 ≤ max eᵤ eᵥ := ((abs_nonneg _).trans hu).trans (le_max_left _ _)
  have hnear : dist p (oldPoint A B (p 0) c d) ≤ max eᵤ eᵥ := by
    apply (dist_pi_le_iff he).mpr
    intro j
    fin_cases j
    · change dist (p 0) (p 0) ≤ _
      simpa only [dist_self] using he
    · exact hu.trans (le_max_left _ _)
    · exact hv.trans (le_max_right _ _)
  calc
    _ ≤ dist p (oldPoint A B (p 0) c d) +
        dist (oldPoint A B (p 0) c d) (quantized μ A C F (p 0) c d) := dist_triangle _ _ _
    _ ≤ max eᵤ eᵥ + (coefficientCost A C F * μ + |B - correctedSlope A C F| * |p 0|) :=
      add_le_add hnear (quantized_movement μ hμ A B C F (p 0) c d)
    _ = _ := by ring

/-- Distinct same-residue parameter indices separate in their first differing
physical coordinate; the triangular shear cancels all earlier coordinates. -/
theorem residue_separation (μ : ℝ) (hμ : 0 < μ) (A C F : ℝ)
    (L : ℕ) (hL : 0 < L) (k l : Index)
    (hc : color L hL k = color L hL l) (hne : k ≠ l) :
    μ * (L : ℝ) ≤ dist (H A C F (realize μ k)) (H A C F (realize μ l)) := by
  have hfirst : ∃ j : Fin 3, k j ≠ l j ∧
      (H A C F (realize μ k)) j - (H A C F (realize μ l)) j =
        μ * ((k j : ℝ) - (l j : ℝ)) := by
    by_cases h0 : k 0 = l 0
    · by_cases h1 : k 1 = l 1
      · have h2 : k 2 ≠ l 2 := by
          intro h2
          apply hne
          funext j
          fin_cases j
          · exact h0
          · exact h1
          · exact h2
        refine ⟨2, h2, ?_⟩
        dsimp [H, realize]
        rw [h0, h1]
        ring
      · refine ⟨1, h1, ?_⟩
        dsimp [H, realize]
        rw [h0]
        ring
    · refine ⟨0, h0, ?_⟩
      dsimp [H, realize]
      ring
  obtain ⟨j, hj, heq⟩ := hfirst
  have hgap := real_residue_spacing hL (residue_eq_emod (congrFun hc j)) hj
  calc
    μ * (L : ℝ) ≤ μ * |(k j : ℝ) - (l j : ℝ)| := mul_le_mul_of_nonneg_left hgap hμ.le
    _ = dist ((H A C F (realize μ k)) j) ((H A C F (realize μ l)) j) := by
      rw [Real.dist_eq, heq, abs_mul, abs_of_pos hμ]
    _ ≤ _ := dist_le_pi_dist _ _ j

/-- Actual original-label selection using one maximum-weight residue class.
No AD, image-cardinality preservation, or tube-direction assertion is made. -/
theorem weighted_quantized_selection {β : Type*} (I : Finset β) (w : β → ℕ)
    (x c d : β → ℝ) (μ : ℝ) (hμ : 0 < μ) (A B C F : ℝ) (L : ℕ) (hL : 0 < L) :
    ∃ E : Finset β, E ⊆ I ∧ (∑ a ∈ I, w a) ≤ L ^ 3 * (∑ a ∈ E, w a) ∧
      (∀ a ∈ E, dist (oldPoint A B (x a) (c a) (d a)) (quantized μ A C F (x a) (c a) (d a)) ≤
        coefficientCost A C F * μ + |B - correctedSlope A C F| * |x a|) ∧
      ∀ p ∈ E.image (fun a => quantized μ A C F (x a) (c a) (d a)),
        ∀ q ∈ E.image (fun a => quantized μ A C F (x a) (c a) (d a)), p ≠ q →
          μ * (L : ℝ) ≤ dist p q := by
  let : Nonempty (Fin 3 → Fin L) := ⟨fun _ => ⟨0, hL⟩⟩
  let f := fun a => color L hL (quantizedIndex μ (parameters F (x a) (c a) (d a)))
  obtain ⟨v, hv⟩ := maximum_weight_color I w f
  let E := I.filter (fun a => f a = v)
  refine ⟨E, Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hv
  · intro a _ha
    exact quantized_movement μ hμ A B C F (x a) (c a) (d a)
  · intro p hp q hq hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    have hc : f a = f b := (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    apply residue_separation μ hμ A C F L hL _ _ hc
    intro heq
    exact hne (congrArg (fun k => H A C F (realize μ k)) heq)

/-- A fixed global bottom-coordinate contraction, not clipping of entries. -/
def bottomHalf (p : Point) : Point := ![p 0, p 1, p 2 / 2]

theorem bottomHalf_injective : Function.Injective bottomHalf := by
  intro p q heq
  funext j
  have h := congrFun heq j
  fin_cases j <;> dsimp [bottomHalf] at h ⊢ <;> linarith

/-- Both planes and their quotient transform together, algebraically exactly. -/
theorem bottomHalf_H (A C F : ℝ) (p : Point) :
    bottomHalf (H A C F p) = H A (C / 2) (F / 2) (bottomHalf p) := by
  funext j
  fin_cases j <;> simp [bottomHalf, H]
  ring

theorem correctedSlope_half (A C F : ℝ) :
    correctedSlope A (C / 2) (F / 2) = correctedSlope A C F / 2 := by
  dsimp [correctedSlope]
  ring

/-- The same fixed contraction transforms the original lower representation. -/
theorem bottomHalf_oldPoint (A B x c d : ℝ) :
    bottomHalf (oldPoint A B x c d) = oldPoint A (B / 2) x c (d / 2) := by
  funext j
  fin_cases j <;> simp [bottomHalf, oldPoint]
  ring

/-- A,C,F initially in [-1,1] give both normalized lower and higher entries
in [-1,1], with the consistency identity preserved exactly. -/
theorem normalized_coefficients (A C F : ℝ) (hA : |A| ≤ 1) (hC : |C| ≤ 1) (hF : |F| ≤ 1) :
    |A| ≤ 1 ∧ |correctedSlope A (C / 2) (F / 2)| ≤ 1 ∧ |C / 2| ≤ 1 ∧ |F / 2| ≤ 1 := by
  have hB : |correctedSlope A C F| ≤ 2 := by
    calc
      _ ≤ |C| + |F| * |A| := by simpa only [correctedSlope, abs_mul] using abs_add_le C (F * A)
      _ ≤ 1 + 1 * 1 := by gcongr
      _ = 2 := by norm_num
  rw [correctedSlope_half, abs_div, abs_div, abs_div]
  norm_num
  exact ⟨hA, by linarith, by linarith, by linarith⟩

theorem bottomHalf_dist_le (p q : Point) : dist (bottomHalf p) (bottomHalf q) ≤ dist p q := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro j
  have hj := dist_le_pi_dist p q j
  fin_cases j
  · exact hj
  · exact hj
  · simp only [bottomHalf, Real.dist_eq] at hj ⊢
    change |p 2 / 2 - q 2 / 2| ≤ dist p q
    rw [← sub_div, abs_div]
    norm_num
    change |p 2 - q 2| ≤ dist p q at hj
    linarith [dist_nonneg (x := p) (y := q)]

/-- The contraction loses at most a factor two of spatial separation. -/
theorem dist_le_two_bottomHalf (p q : Point) : dist p q ≤ 2 * dist (bottomHalf p) (bottomHalf q) := by
  apply (dist_pi_le_iff (mul_nonneg (by norm_num) dist_nonneg)).mpr
  intro j
  have hj := dist_le_pi_dist (bottomHalf p) (bottomHalf q) j
  have hn := dist_nonneg (x := bottomHalf p) (y := bottomHalf q)
  fin_cases j
  · change dist (p 0) (q 0) ≤ _ at hj
    change dist (p 0) (q 0) ≤ 2 * dist (bottomHalf p) (bottomHalf q)
    linarith
  · change dist (p 1) (q 1) ≤ _ at hj
    change dist (p 1) (q 1) ≤ 2 * dist (bottomHalf p) (bottomHalf q)
    linarith
  · change dist (p 2 / 2) (q 2 / 2) ≤ _ at hj
    rw [Real.dist_eq, ← sub_div, abs_div] at hj
    norm_num at hj
    change dist (p 2) (q 2) ≤ 2 * dist (bottomHalf p) (bottomHalf q)
    rw [Real.dist_eq]
    linarith

/-- Movement remains bounded relative to the same contracted original point. -/
theorem contracted_quantized_movement (μ : ℝ) (hμ : 0 < μ) (A B C F x c d : ℝ) :
    dist (bottomHalf (oldPoint A B x c d)) (bottomHalf (quantized μ A C F x c d)) ≤
      coefficientCost A C F * μ + |B - correctedSlope A C F| * |x| :=
  (bottomHalf_dist_le _ _).trans (quantized_movement μ hμ A B C F x c d)

/-- The constant-grain rounded higher label is close to the actual higher
witness, with all lower residual and slope-discrepancy terms retained. -/
theorem constant_quantized_quotient_witness (μ : ℝ) (hμ : 0 < μ)
    (A B C F c d eᵤ eᵥ eₕ y : ℝ) (p : Point)
    (hu : |p 1 - (c + A * p 0)| ≤ eᵤ) (hv : |p 2 - (d + B * p 0)| ≤ eᵥ)
    (hy : |(inverse A C F p) 2 - y| ≤ eₕ) :
    |(snap μ (parameters F (p 0) c d)) 2 - y| ≤
      μ + |B - correctedSlope A C F| * |p 0| + eᵥ + |F| * eᵤ + eₕ := by
  have hs : |(snap μ (parameters F (p 0) c d)) 2 - (d - F * c)| ≤ μ := by
    change |(snap μ (parameters F (p 0) c d)) 2 - (parameters F (p 0) c d) 2| ≤ μ
    rw [abs_sub_comm, ← Real.dist_eq]
    exact (dist_le_pi_dist _ _ 2).trans (snap_dist_lt μ hμ _).le
  have hq : |d - F * c - (inverse A C F p) 2| ≤
      |B - correctedSlope A C F| * |p 0| + eᵥ + |F| * eᵤ := by
    rw [abs_sub_comm]
    exact constant_quotient_error A B C F c d eᵤ eᵥ p hu hv
  calc
    _ ≤ |(snap μ (parameters F (p 0) c d)) 2 - (d - F * c)| + |d - F * c - y| := abs_sub_le _ _ _
    _ ≤ μ + (|d - F * c - (inverse A C F p) 2| + |(inverse A C F p) 2 - y|) :=
      add_le_add hs (abs_sub_le _ _ _)
    _ ≤ μ + ((|B - correctedSlope A C F| * |p 0| + eᵥ + |F| * eᵤ) + eₕ) :=
      add_le_add le_rfl (add_le_add hq hy)
    _ = _ := by ring

/-- Both exact representations also hold for the pointwise reconstruction. -/
theorem quantizePoint_representations (μ A C F : ℝ) (z : Point) :
    let p := snap μ (inverse A C F z)
    quantizePoint μ A C F z = oldPoint A (correctedSlope A C F) (p 0) (p 1) (p 2 + F * p 1) ∧
      (quantizePoint μ A C F z) 2 - C * (quantizePoint μ A C F z) 0 -
        F * (quantizePoint μ A C F z) 1 = p 2 :=
  ⟨lower_representation A C F _, higher_representation A C F _⟩

end NestedPlaneQuantization
