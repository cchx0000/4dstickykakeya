import Theorems.Thm_StickyKakeya4_finite_cyclic_grid_padding
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators
namespace PaddedPhysicalCellWitness

/-- Cyclic padding of the actual fine-grid index controls the actual translated point,
including its real fractional part and every nearby point. -/
theorem nearby_floor_eq_quotient (σ E p z : ℝ) (R q : ℕ)
    (hσ : 0 < σ) (hE : 0 ≤ E) (hR : E + 1 ≤ (R : ℝ))
    (hpad : 4 * (R : ℤ) ≤ (⌊p / σ⌋ + (q : ℤ)) % (64 * R : ℕ) ∧
      (⌊p / σ⌋ + (q : ℤ)) % (64 * R : ℕ) < (60 * R : ℕ))
    (hz : |z - p| ≤ E * σ) :
    ⌊(z + (q : ℝ) * σ) / ((64 * R : ℕ) * σ)⌋ =
      (⌊p / σ⌋ + (q : ℤ)) / (64 * R : ℕ) := by
  let d : ℤ := ⌊p / σ⌋
  let n : ℤ := d + (q : ℤ)
  let c : ℤ := (64 * R : ℕ)
  let k : ℤ := n / c
  let s : ℤ := n % c
  have hRpos : 0 < (R : ℝ) := by linarith
  have hcpos : 0 < (64 * R : ℕ) := by exact_mod_cast (show 0 < 64 * (R : ℝ) by positivity)
  have hcpos' : 0 < ((64 * R : ℕ) : ℝ) := by exact_mod_cast hcpos
  have hdecomp : (s : ℝ) + ((64 * R : ℕ) : ℝ) * (k : ℝ) =
      (d : ℝ) + (q : ℝ) := by
    exact_mod_cast Int.emod_add_mul_ediv n c
  have hfrac : (d : ℝ) + Int.fract (p / σ) = p / σ := Int.floor_add_fract _
  have hflo : 0 ≤ Int.fract (p / σ) := Int.fract_nonneg _
  have hfhi : Int.fract (p / σ) < 1 := Int.fract_lt_one _
  have hnear : |z / σ - p / σ| ≤ E := by
    rw [← sub_div, abs_div, abs_of_pos hσ]
    exact (div_le_iff₀ hσ).2 hz
  obtain ⟨hnearlo, hnearhi⟩ := abs_le.1 hnear
  have hslo : 4 * (R : ℝ) ≤ (s : ℝ) := by exact_mod_cast hpad.1
  have hshi : (s : ℝ) < 60 * (R : ℝ) := by exact_mod_cast hpad.2
  have hlo : (k : ℝ) * ((64 * R : ℕ) : ℝ) ≤ z / σ + (q : ℝ) := by
    nlinarith
  have hhi : z / σ + (q : ℝ) < ((k : ℝ) + 1) * ((64 * R : ℕ) : ℝ) := by
    push_cast at hdecomp ⊢
    nlinarith
  have heq : (z + (q : ℝ) * σ) / ((64 * R : ℕ) * σ) =
      (z / σ + (q : ℝ)) / (64 * R : ℕ) := by
    field_simp
  rw [heq]
  apply Int.floor_eq_iff.2
  exact ⟨(le_div_iff₀ hcpos').2 hlo, (div_lt_iff₀ hcpos').2 hhi⟩

def translate (σ : ℝ) (q : ℕ) (p : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => p i + (q : ℝ) * σ

noncomputable def bin (τ : ℝ) (p : Fin 4 → ℝ) : Fin 4 → ℤ :=
  fun i => ⌊p i / τ⌋

def halfOpenCell (τ : ℝ) (k : Fin 4 → ℤ) : Set (Fin 4 → ℝ) :=
  {p | ∀ i, (k i : ℝ) * τ ≤ p i ∧ p i < ((k i : ℝ) + 1) * τ}

theorem mem_halfOpenCell_bin (τ : ℝ) (hτ : 0 < τ) (p : Fin 4 → ℝ) :
    p ∈ halfOpenCell τ (bin τ p) := by
  intro i
  exact ⟨(le_div_iff₀ hτ).1 (Int.floor_le (p i / τ)),
    (div_lt_iff₀ hτ).1 (Int.lt_floor_add_one (p i / τ))⟩

theorem nearby_same_bin (σ E : ℝ) (R q : ℕ) (p z : Fin 4 → ℝ)
    (hσ : 0 < σ) (hE : 0 ≤ E) (hR : E + 1 ≤ (R : ℝ))
    (hpad : ∀ i, 4 * (R : ℤ) ≤ (⌊p i / σ⌋ + (q : ℤ)) % (64 * R : ℕ) ∧
      (⌊p i / σ⌋ + (q : ℤ)) % (64 * R : ℕ) < (60 * R : ℕ))
    (hz : ∀ i, |z i - p i| ≤ E * σ) :
    bin ((64 * R : ℕ) * σ) (translate σ q z) =
      bin ((64 * R : ℕ) * σ) (translate σ q p) := by
  funext i
  exact (nearby_floor_eq_quotient σ E (p i) (z i) R q hσ hE hR (hpad i) (hz i)).trans
    (nearby_floor_eq_quotient σ E (p i) (p i) R q hσ hE hR (hpad i)
      (by simpa using mul_nonneg hE hσ.le)).symm

theorem nearby_mem_same_halfOpenCell (σ E : ℝ) (R q : ℕ) (p z : Fin 4 → ℝ)
    (hσ : 0 < σ) (hE : 0 ≤ E) (hR : E + 1 ≤ (R : ℝ))
    (hpad : ∀ i, 4 * (R : ℤ) ≤ (⌊p i / σ⌋ + (q : ℤ)) % (64 * R : ℕ) ∧
      (⌊p i / σ⌋ + (q : ℤ)) % (64 * R : ℕ) < (60 * R : ℕ))
    (hz : ∀ i, |z i - p i| ≤ E * σ) :
    translate σ q p ∈ halfOpenCell ((64 * R : ℕ) * σ)
        (bin ((64 * R : ℕ) * σ) (translate σ q p)) ∧
    translate σ q z ∈ halfOpenCell ((64 * R : ℕ) * σ)
        (bin ((64 * R : ℕ) * σ) (translate σ q p)) := by
  have hRpos : 0 < (R : ℝ) := by linarith
  have hτ : 0 < ((64 * R : ℕ) : ℝ) * σ := by push_cast; positivity
  refine ⟨mem_halfOpenCell_bin _ hτ _, ?_⟩
  rw [← nearby_same_bin σ E R q p z hσ hE hR hpad hz]
  exact mem_halfOpenCell_bin _ hτ _

/-- Actual cyclic selection followed by actual coarse-cell witnesses for every nearby point.
The retained labels and their natural-number weights are the original ones. -/
theorem weighted_physical_cell_witness {α : Type*}
    (A : Finset α) (w : α → ℕ) (p : α → Fin 4 → ℝ)
    (σ E : ℝ) (R N : ℕ) (hσ : 0 < σ) (hE : 0 ≤ E)
    (hR : E + 1 ≤ (R : ℝ)) (hN : 0 < N) (hdiv : 64 * R ∣ N) :
    ∃ q : Fin N, ∃ B : Finset α, B ⊆ A ∧
      (∑ a ∈ A, w a) ≤ 2 * (∑ a ∈ B, w a) ∧
      ∀ a ∈ B, ∀ z : Fin 4 → ℝ, (∀ i, |z i - p a i| ≤ E * σ) →
        bin ((64 * R : ℕ) * σ) (translate σ q.val z) =
          bin ((64 * R : ℕ) * σ) (translate σ q.val (p a)) ∧
        translate σ q.val (p a) ∈ halfOpenCell ((64 * R : ℕ) * σ)
          (bin ((64 * R : ℕ) * σ) (translate σ q.val (p a))) ∧
        translate σ q.val z ∈ halfOpenCell ((64 * R : ℕ) * σ)
          (bin ((64 * R : ℕ) * σ) (translate σ q.val (p a))) := by
  have hRpos : 0 < R := by
    exact_mod_cast (show 0 < (R : ℝ) by linarith)
  obtain ⟨q, B, hBA, hw, hpad⟩ := FiniteCyclicGridPadding.cyclic_translation
    (τ := Fin 4) N 64 hN (by norm_num) A w
    (fun a i => ⌊p a i / σ⌋) (fun _ => R)
    (fun _ => hRpos) (fun _ => hdiv) (by norm_num)
  refine ⟨q, B, hBA, hw, ?_⟩
  intro a ha z hz
  have hpad' : ∀ i, 4 * (R : ℤ) ≤ (⌊p a i / σ⌋ + (q.val : ℤ)) % (64 * R : ℕ) ∧
      (⌊p a i / σ⌋ + (q.val : ℤ)) % (64 * R : ℕ) < (60 * R : ℕ) := by
    intro i
    simpa using hpad a ha i
  exact ⟨nearby_same_bin σ E R q.val (p a) z hσ hE hR hpad' hz,
    nearby_mem_same_halfOpenCell σ E R q.val (p a) z hσ hE hR hpad' hz⟩

end PaddedPhysicalCellWitness
