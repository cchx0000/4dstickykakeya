import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

/-!
Fixed-depth dyadic level selection and the exact parameter interface for
self-uniform refinement. Working levels are actual integer quotients. The
mass exponent and retention cost contain no mesh/aspect-ratio parameter.
-/
namespace DyadicAlignmentParameters

def level (M H j : ℕ) : ℕ := j * M / H
noncomputable def gap (M H : ℕ) : ℕ := ⌈(M : ℝ) / (H : ℝ)⌉₊

@[simp] theorem level_zero (M H : ℕ) : level M H 0 = 0 := by simp [level]
@[simp] theorem level_endpoint (M H : ℕ) (hH : 0 < H) : level M H H = M := by
  exact Nat.mul_div_cancel_left M hH

theorem level_monotone (M H : ℕ) : Monotone (level M H) := by
  intro j k hjk
  exact Nat.div_le_div_right (Nat.mul_le_mul_right M hjk)

theorem level_le_endpoint (M H j : ℕ) (hH : 0 < H) (hj : j ≤ H) :
    level M H j ≤ M := by
  simpa only [level_endpoint M H hH] using level_monotone M H hj

/-- The prepared grid has at most H+1 levels even if some rounded levels repeat. -/
theorem working_levels_card_le (M H : ℕ) :
    ((Finset.range (H + 1)).image (level M H)).card ≤ H + 1 := by
  exact (Finset.card_image_le).trans_eq (Finset.card_range (H + 1))

/-- The implemented integer quotient is literally the stated real floor. -/
theorem level_eq_floor (M H j : ℕ) (hH : 0 < H) :
    level M H j = ⌊((j : ℝ) * (M : ℝ)) / (H : ℝ)⌋₊ := by
  symm
  apply (Nat.floor_eq_iff (by positivity)).mpr
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  constructor
  · apply (le_div_iff₀ hH').mpr
    exact_mod_cast Nat.div_mul_le_self (j * M) H
  · apply (div_lt_iff₀ hH').mpr
    have hh := Nat.lt_mul_div_succ (j * M) hH
    have hh' : j * M < (j * M / H + 1) * H := by simpa only [mul_comm H] using hh
    dsimp [level]
    exact_mod_cast hh'

lemma le_gap_mul (M H : ℕ) (hH : 0 < H) : M ≤ gap M H * H := by
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have h := (div_le_iff₀ hH').mp (Nat.le_ceil ((M : ℝ) / (H : ℝ)))
  exact_mod_cast h

/-- Adjacent working levels differ by at most ceil(M/H), uniformly in j. -/
theorem adjacent_level_le (M H j : ℕ) (hH : 0 < H) :
    level M H (j + 1) ≤ level M H j + gap M H := by
  have hlow := Nat.lt_mul_div_succ (j * M) hH
  have hM := le_gap_mul M H hH
  have hnum : (j + 1) * M < (level M H j + gap M H + 1) * H := by
    dsimp [level] at *
    nlinarith
  have hdiv := (Nat.div_lt_iff_lt_mul hH).mpr hnum
  exact Nat.le_of_lt_succ hdiv

theorem adjacent_gap_le (M H j : ℕ) (hH : 0 < H) :
    level M H (j + 1) - level M H j ≤ gap M H := by
  have h := adjacent_level_le M H j hH
  omega

/-- Every integer level between the endpoints has an actual adjacent bracket.
The construction chooses the largest occupied working index below n. -/
theorem exists_bracketing_levels (M H n : ℕ) (hH : 0 < H) (hn : n ≤ M) :
    ∃ j < H, level M H j ≤ n ∧ n ≤ level M H (j + 1) ∧
      level M H (j + 1) - level M H j ≤ gap M H := by
  classical
  let S := (Finset.range H).filter (fun j => level M H j ≤ n)
  have hS : S.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hH, ?_⟩⟩
    simp
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image S id hS
  obtain ⟨hjH, hjn⟩ := Finset.mem_filter.mp hj
  have hjlt : j < H := Finset.mem_range.mp hjH
  refine ⟨j, hjlt, hjn, ?_, adjacent_gap_le M H j hH⟩
  by_cases hnext : j + 1 < H
  · by_contra hbad
    have hmem : j + 1 ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hnext, by omega⟩
    have hm := hmax (j + 1) hmem
    simp only [id_eq] at hm
    omega
  · have he : j + 1 = H := by omega
    rw [he, level_endpoint M H hH]
    exact hn

/-- The corresponding dyadic radius bracket has the explicit rounding factor. -/
theorem exists_dyadic_bracket (M H n : ℕ) (hH : 0 < H) (hn : n ≤ M) :
    ∃ j < H, (2 : ℝ) ^ level M H j ≤ (2 : ℝ) ^ n ∧
      (2 : ℝ) ^ n ≤ (2 : ℝ) ^ level M H (j + 1) ∧
      (2 : ℝ) ^ level M H (j + 1) ≤
        (2 : ℝ) ^ gap M H * (2 : ℝ) ^ level M H j := by
  obtain ⟨j, hj, hlo, hhi, _hgap⟩ := exists_bracketing_levels M H n hH hn
  refine ⟨j, hj, pow_le_pow_right₀ (by norm_num) hlo,
    pow_le_pow_right₀ (by norm_num) hhi, ?_⟩
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (adjacent_level_le M H j hH)
  simpa only [pow_add, mul_comm] using h

/-- ceil-rounding costs at most two beyond the desired R^(1/H) factor. -/
theorem dyadic_gap_factor_le (M H : ℕ) (hH : 0 < H) :
    (2 : ℝ) ^ gap M H ≤ 2 * ((2 : ℝ) ^ M) ^ ((H : ℝ)⁻¹) := by
  have hceil : ((gap M H : ℕ) : ℝ) ≤ (M : ℝ) / H + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (M : ℝ) / (H : ℝ))).le
  have hpow : (2 : ℝ) ^ ((M : ℝ) / H) = ((2 : ℝ) ^ M) ^ ((H : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast 2 M, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
  calc
    (2 : ℝ) ^ gap M H = (2 : ℝ) ^ ((gap M H : ℕ) : ℝ) :=
      (Real.rpow_natCast 2 (gap M H)).symm
    _ ≤ (2 : ℝ) ^ ((M : ℝ) / H + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil
    _ = (2 : ℝ) ^ ((M : ℝ) / H) * 2 := by rw [Real.rpow_add (by norm_num), Real.rpow_one]
    _ = 2 * ((2 : ℝ) ^ M) ^ ((H : ℝ)⁻¹) := by rw [hpow, mul_comm]

noncomputable def powerBase (R u : ℝ) : ℕ := ⌈R ^ u⌉₊
noncomputable def massExponent (D u : ℝ) : ℕ := ⌈D / u⌉₊

theorem powerBase_ge_two (R u : ℝ) (hR : 1 < R) (hu : 0 < u) :
    2 ≤ powerBase R u := by
  have h : 1 < powerBase R u := Nat.lt_ceil.mpr (by simpa using Real.one_lt_rpow hR hu)
  omega

/-- The rounding used for Q has only a fixed-factor loss. -/
theorem powerBase_le_two_rpow (R u : ℝ) (hR : 1 < R) (hu : 0 < u) :
    (powerBase R u : ℝ) ≤ 2 * R ^ u := by
  have hpow := Real.one_lt_rpow hR hu
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ R ^ u by linarith)
  change (⌈R ^ u⌉₊ : ℝ) ≤ 2 * R ^ u
  linarith

theorem mass_exponent_bound (D u : ℝ) (hu : 0 < u) :
    D ≤ u * (massExponent D u : ℝ) := by
  have h := (div_le_iff₀ hu).mp (Nat.le_ceil (D / u))
  simpa only [massExponent, mul_comm] using h

/-- The original natural-number mass fits Q^L. L=ceil(D/u) contains no R. -/
theorem polynomial_mass_le_power (W : ℕ) (R u D : ℝ)
    (hR : 1 < R) (hu : 0 < u) (hW : (W : ℝ) ≤ R ^ D) :
    W ≤ (powerBase R u) ^ (massExponent D u) := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hmajor : (W : ℝ) ≤ (powerBase R u : ℝ) ^ massExponent D u := by
    calc
      (W : ℝ) ≤ R ^ D := hW
      _ ≤ R ^ (u * (massExponent D u : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hR.le (mass_exponent_bound D u hu)
      _ = (R ^ u) ^ (massExponent D u : ℝ) := Real.rpow_mul hRpos.le _ _
      _ = (R ^ u) ^ massExponent D u := Real.rpow_natCast _ _
      _ ≤ (powerBase R u : ℝ) ^ massExponent D u :=
        pow_le_pow_left₀ (Real.rpow_nonneg hRpos.le _) (Nat.le_ceil (R ^ u)) _
  exact_mod_cast hmajor

/-- The retention cost in the current finite self-uniform theorem, fixed before
R is chosen. The number k of prepared relations is also fixed. -/
noncomputable def retentionCost (k : ℕ) (D u : ℝ) : ℕ :=
  2 * (4 * k) ^ (k * massExponent D u)

noncomputable def absorptionThreshold (C : ℕ) (ζ : ℝ) : ℝ :=
  max 2 ((C : ℝ) ^ ζ⁻¹)

theorem absorptionThreshold_gt_one (C : ℕ) (ζ : ℝ) :
    1 < absorptionThreshold C ζ :=
  lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)

/-- An explicit threshold proves constant absorption, without assuming a power
bound on the constant. -/
theorem constant_le_rpow_of_threshold (C : ℕ) (ζ R : ℝ) (hζ : 0 < ζ)
    (hR : absorptionThreshold C ζ ≤ R) : (C : ℝ) ≤ R ^ ζ := by
  have hb : (C : ℝ) ^ ζ⁻¹ ≤ R := (le_max_right _ _).trans hR
  calc
    (C : ℝ) = ((C : ℝ) ^ ζ⁻¹) ^ ζ := by
      rw [← Real.rpow_mul (Nat.cast_nonneg C), inv_mul_cancel₀ hζ.ne', Real.rpow_one]
    _ ≤ R ^ ζ := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg C) _) hb hζ.le

/-- This supplies Q>=4 for the existing refinement API when needed. -/
theorem powerBase_ge_four_of_threshold (R u : ℝ) (hu : 0 < u)
    (hR : absorptionThreshold 4 u ≤ R) : 4 ≤ powerBase R u := by
  have h := (constant_le_rpow_of_threshold 4 u R hu hR).trans (Nat.le_ceil (R ^ u))
  exact_mod_cast h

/-- The actual fixed retention cost is eventually at most any prescribed
positive power, with a displayed mesh-independent threshold. -/
theorem retention_cost_absorption (k : ℕ) (D u ζ : ℝ) (hζ : 0 < ζ) :
    ∃ R₀ > 1, ∀ R ≥ R₀, (retentionCost k D u : ℝ) ≤ R ^ ζ := by
  exact ⟨absorptionThreshold (retentionCost k D u) ζ,
    absorptionThreshold_gt_one _ _, fun R hR => constant_le_rpow_of_threshold _ _ R hζ hR⟩

/-- One threshold simultaneously supplies the actual Q>=4 API requirement,
the polynomial mass bound, and absorption of the mesh-independent cost. -/
theorem fixed_refinement_parameters (k : ℕ) (D u ζ : ℝ)
    (hu : 0 < u) (hζ : 0 < ζ) :
    ∃ R₀ > 1, ∀ R ≥ R₀,
      4 ≤ powerBase R u ∧ (retentionCost k D u : ℝ) ≤ R ^ ζ ∧
      ∀ W : ℕ, (W : ℝ) ≤ R ^ D → W ≤ (powerBase R u) ^ massExponent D u := by
  let R₀ := max (absorptionThreshold 4 u)
    (absorptionThreshold (retentionCost k D u) ζ)
  have hR₀ : 1 < R₀ := (absorptionThreshold_gt_one 4 u).trans_le (le_max_left _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR
  have h4 : absorptionThreshold 4 u ≤ R := (le_max_left _ _).trans hR
  have hcost : absorptionThreshold (retentionCost k D u) ζ ≤ R :=
    (le_max_right _ _).trans hR
  exact ⟨powerBase_ge_four_of_threshold R u hu h4,
    constant_le_rpow_of_threshold _ ζ R hζ hcost,
    fun W hW => polynomial_mass_le_power W R u D (hR₀.trans_le hR) hu hW⟩

/-- Apply the derived absorption to an ORIGINAL mass-retention inequality. -/
theorem retained_mass_bound (k W W' : ℕ) (D u ζ R : ℝ) (hζ : 0 < ζ)
    (hR : absorptionThreshold (retentionCost k D u) ζ ≤ R)
    (hret : W ≤ retentionCost k D u * W') :
    (W : ℝ) ≤ R ^ ζ * (W' : ℝ) := by
  have hc := constant_le_rpow_of_threshold (retentionCost k D u) ζ R hζ hR
  calc
    (W : ℝ) ≤ (retentionCost k D u : ℝ) * (W' : ℝ) := by exact_mod_cast hret
    _ ≤ R ^ ζ * (W' : ℝ) := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg W')

end DyadicAlignmentParameters
