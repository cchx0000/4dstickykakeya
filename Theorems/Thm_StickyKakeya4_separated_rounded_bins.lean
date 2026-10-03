import Theorems.Thm_StickyKakeya4_actual_mass_rounded_selection

set_option autoImplicit false
set_option warningAsError true

namespace SeparatedRoundedBins
noncomputable section
open scoped BigOperators

/-- Select one actual residue class, retaining at least one third of the
original representatives. Counts on every interval can only decrease. -/
theorem exists_residue_subfamily {P : Type*} [DecidableEq P]
    (B : Finset P) (label : P → ℕ) :
    ∃ c < 3, ∃ C ⊆ B, B.card ≤ 3 * C.card ∧ ∀ p ∈ C, label p % 3 = c := by
  classical
  let population : ℕ → ℕ := fun c => (B.filter (fun p => label p % 3 = c)).card
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image (Finset.range 3) population ⟨0, by decide⟩
  have hs : B.card = ∑ i ∈ Finset.range 3, population i := by
    exact Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have hbound : B.card ≤ 3 * population c := by
    calc
      B.card = _ := hs
      _ ≤ ∑ _i ∈ Finset.range 3, population c := Finset.sum_le_sum (fun i hi => hmax i hi)
      _ = _ := by simp
  refine ⟨c, Finset.mem_range.mp hc, B.filter (fun p => label p % 3 = c),
    Finset.filter_subset _ _, hbound, ?_⟩
  intro p hp
  exact (Finset.mem_filter.mp hp).2

/-- Original real positions in distinct equal-residue bins are separated;
no movement to artificial cell centers is used. -/
theorem actual_position_separation {x y origin ρ : ℝ} (hρ : 0 < ρ) {i j : ℕ}
    (hi : (i : ℤ) = ⌊(x-origin)/ρ⌋) (hj : (j : ℤ) = ⌊(y-origin)/ρ⌋)
    (hmod : i % 3 = j % 3) (hne : i ≠ j) : 2 * ρ < |x-y| := by
  have hix : (i : ℝ) ≤ (x-origin)/ρ := by
    have h := Int.floor_le ((x-origin)/ρ)
    rw [← hi] at h
    exact h
  have hix' : (x-origin)/ρ < (i : ℝ)+1 := by
    have h := Int.lt_floor_add_one ((x-origin)/ρ)
    rw [← hi] at h
    exact h
  have hjy : (j : ℝ) ≤ (y-origin)/ρ := by
    have h := Int.floor_le ((y-origin)/ρ)
    rw [← hj] at h
    exact h
  have hjy' : (y-origin)/ρ < (j : ℝ)+1 := by
    have h := Int.lt_floor_add_one ((y-origin)/ρ)
    rw [← hj] at h
    exact h
  have hiLo := (le_div_iff₀ hρ).mp hix
  have hiHi := (div_lt_iff₀ hρ).mp hix'
  have hjLo := (le_div_iff₀ hρ).mp hjy
  have hjHi := (div_lt_iff₀ hρ).mp hjy'
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hgap : i + 3 ≤ j := by omega
    have hgap' : (i : ℝ)+3 ≤ (j : ℝ) := by exact_mod_cast hgap
    have hm := mul_le_mul_of_nonneg_right hgap' hρ.le
    have hd : 2 * ρ < y-x := by nlinarith
    exact hd.trans_le (by simpa only [abs_sub_comm] using le_abs_self (y-x))
  · have hgap : j + 3 ≤ i := by omega
    have hgap' : (j : ℝ)+3 ≤ (i : ℝ) := by exact_mod_cast hgap
    have hm := mul_le_mul_of_nonneg_right hgap' hρ.le
    have hd : 2 * ρ < x-y := by nlinarith
    exact hd.trans_le (le_abs_self (x-y))

/-- Apply deterministic thinning to actual original bin representatives. -/
theorem exists_separated_representatives {P : Type*} [DecidableEq P]
    (B : Finset P) (label : P → ℕ) (position : P → ℝ) (origin ρ : ℝ)
    (hρ : 0 < ρ) (hinj : Set.InjOn label B)
    (hbin : ∀ p ∈ B, (label p : ℤ) = ⌊(position p-origin)/ρ⌋) :
    ∃ C ⊆ B, B.card ≤ 3 * C.card ∧
      ∀ p ∈ C, ∀ q ∈ C, p ≠ q → 2 * ρ < |position p-position q| := by
  obtain ⟨c, _hc, C, hCB, hcard, hres⟩ := exists_residue_subfamily B label
  refine ⟨C, hCB, hcard, ?_⟩
  intro p hp q hq hne
  have hlabel : label p ≠ label q := fun h => hne (hinj (hCB hp) (hCB hq) h)
  exact actual_position_separation hρ (hbin p (hCB hp)) (hbin q (hCB hq))
    ((hres p hp).trans (hres q hq).symm) hlabel
end
end SeparatedRoundedBins
