import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

namespace DyadicHeightBoundaryPadding

open scoped BigOperators

noncomputable section

/-- Actual residues lying in either boundary margin of a dyadic time cell. -/
def badResidues (R : ℕ) (θ : ℝ) : Finset ℕ :=
  (Finset.range R).filter (fun k : ℕ => (k : ℝ) < θ * R ∨ (R : ℝ) - θ * R < (k : ℝ))

def badIndices (B : Finset ℕ) (R : ℕ) (θ : ℝ) : Finset ℕ :=
  B.filter (fun n => n % R ∈ badResidues R θ)

def badUnion (B E : Finset ℕ) (θ : ℝ) : Finset ℕ :=
  E.biUnion (fun e => badIndices B (2 ^ e) θ)

def padded (B E : Finset ℕ) (θ : ℝ) : Finset ℕ := B \ badUnion B E θ

lemma lower_margin_count (R : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    (((Finset.range R).filter (fun k : ℕ => (k : ℝ) < θ * R)).card : ℝ) ≤ θ * R + 1 := by
  have hsub : (Finset.range R).filter (fun k : ℕ => (k : ℝ) < θ * R) ⊆ Finset.range ⌈θ * R⌉₊ := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_ceil.mpr (Finset.mem_filter.mp hk).2)
  have hc : (((Finset.range R).filter (fun k : ℕ => (k : ℝ) < θ * R)).card : ℝ) ≤ (⌈θ * R⌉₊ : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
  exact hc.trans (Nat.ceil_lt_add_one (by positivity : 0 ≤ θ * (R : ℝ))).le

/-- The upper margin reflects into the lower one; integer endpoint errors are
therefore counted explicitly, not discarded as a continuous-measure term. -/
lemma upper_margin_count (R : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    (((Finset.range R).filter (fun k : ℕ => (R : ℝ) - θ * R < (k : ℝ))).card : ℝ) ≤ θ * R + 1 := by
  let U := (Finset.range R).filter (fun k : ℕ => (R : ℝ) - θ * R < (k : ℝ))
  let L := (Finset.range R).filter (fun k : ℕ => (k : ℝ) < θ * R)
  have hc : U.card ≤ L.card := by
    apply Finset.card_le_card_of_injOn (fun k : ℕ => R - 1 - k)
    · intro k hk
      obtain ⟨hkR, hhi⟩ := Finset.mem_filter.mp hk
      have hklt : k < R := Finset.mem_range.mp hkR
      have he : R - 1 - k + k + 1 = R := by omega
      have heR : ((R - 1 - k : ℕ) : ℝ) + k + 1 = R := by exact_mod_cast he
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by change R - 1 - k < R; omega), by change ((R - 1 - k : ℕ) : ℝ) < θ * R; linarith⟩
    · intro k hk l hl he
      have hkR := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      have hlR := Finset.mem_range.mp (Finset.mem_filter.mp hl).1
      change R - 1 - k = R - 1 - l at he
      omega
  exact (Nat.cast_le.mpr hc).trans (lower_margin_count R θ hθ)

lemma bad_residue_count (R : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    ((badResidues R θ).card : ℝ) ≤ 2 * θ * R + 2 := by
  have hcard : (badResidues R θ).card ≤
      ((Finset.range R).filter (fun k : ℕ => (k : ℝ) < θ * R)).card +
      ((Finset.range R).filter (fun k : ℕ => (R : ℝ) - θ * R < (k : ℝ))).card := by
    rw [badResidues, Finset.filter_or]
    exact Finset.card_union_le _ _
  have hc : ((badResidues R θ).card : ℝ) ≤
      (((Finset.range R).filter (fun k : ℕ => (k : ℝ) < θ * R)).card : ℝ) +
      (((Finset.range R).filter (fun k : ℕ => (R : ℝ) - θ * R < (k : ℝ))).card : ℝ) := by exact_mod_cast hcard
  linarith only [hc, lower_margin_count R θ hθ, upper_margin_count R θ hθ]

/-- Literal quotient/remainder encoding bounds the original bad time labels. -/
lemma bad_indices_count_nat (B : Finset ℕ) (N R : ℕ) (θ : ℝ)
    (hR : 0 < R) (hdiv : R ∣ N) (hB : B ⊆ Finset.range N) :
    (badIndices B R θ).card ≤ (N / R) * (badResidues R θ).card := by
  have hmap : (badIndices B R θ).card ≤
      ((Finset.range (N / R)).product (badResidues R θ)).card := by
    apply Finset.card_le_card_of_injOn (fun n => (n / R, n % R))
    · intro n hn
      obtain ⟨hnB, hbad⟩ := Finset.mem_filter.mp hn
      have hnN : n < N := Finset.mem_range.mp (hB hnB)
      have hmul : N / R * R = N := Nat.div_mul_cancel hdiv
      have hquot : n / R < N / R := (Nat.div_lt_iff_lt_mul hR).mpr (by omega)
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hquot, hbad⟩
    · intro n _ m _ he
      have hq := congrArg Prod.fst he
      have hr := congrArg Prod.snd he
      nlinarith only [Nat.mod_add_div n R, Nat.mod_add_div m R, congrArg (fun k : ℕ => R * k) hq, hr]
  simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_range] using hmap

/-- One-scale deletion count with its exact discrete boundary remainder. -/
theorem bad_indices_count (B : Finset ℕ) (N R : ℕ) (θ : ℝ)
    (hR : 0 < R) (hdiv : R ∣ N) (hB : B ⊆ Finset.range N) (hθ : 0 ≤ θ) :
    ((badIndices B R θ).card : ℝ) ≤ 2 * θ * N + 2 * ((N / R : ℕ) : ℝ) := by
  have hc : ((badIndices B R θ).card : ℝ) ≤
      ((N / R : ℕ) : ℝ) * ((badResidues R θ).card : ℝ) := by
    exact_mod_cast bad_indices_count_nat B N R θ hR hdiv hB
  have hm : ((N / R : ℕ) : ℝ) * (R : ℝ) = N := by exact_mod_cast Nat.div_mul_cancel hdiv
  have hbound := mul_le_mul_of_nonneg_left (bad_residue_count R θ hθ)
    (Nat.cast_nonneg (N / R))
  calc
    _ ≤ ((N / R : ℕ) : ℝ) * ((badResidues R θ).card : ℝ) := hc
    _ ≤ ((N / R : ℕ) : ℝ) * (2 * θ * R + 2) := hbound
    _ = 2 * θ * (((N / R : ℕ) : ℝ) * R) + 2 * ((N / R : ℕ) : ℝ) := by ring
    _ = _ := by rw [hm]

lemma sum_two_pow_le (k : ℕ) : (∑ j ∈ Finset.range k, (2 : ℕ) ^ j) ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega

/-- Distinct actual dyadic levels have a geometric reciprocal-scale sum. -/
theorem dyadic_reciprocal_sum (E : Finset ℕ) (M e₀ : ℕ)
    (hE : ∀ e ∈ E, e₀ ≤ e ∧ e ≤ M) :
    (∑ e ∈ E, (2 ^ M / 2 ^ e : ℕ)) ≤ 2 * (2 ^ M / 2 ^ e₀) := by
  classical
  by_cases hne : E.Nonempty
  · obtain ⟨a, ha⟩ := hne
    have he₀ : e₀ ≤ M := (hE a ha).1.trans (hE a ha).2
    have hinj : Set.InjOn (fun e => M - e) (↑E : Set ℕ) := by
      intro e he f hf hef
      have heM := (hE e he).2
      have hfM := (hE f hf).2
      change M - e = M - f at hef
      omega
    have hsub : E.image (fun e => M - e) ⊆ Finset.range (M - e₀ + 1) := by
      intro j hj
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hlo, hhi⟩ := hE e he
      exact Finset.mem_range.mpr (by omega)
    calc
      (∑ e ∈ E, (2 ^ M / 2 ^ e : ℕ)) = ∑ e ∈ E, 2 ^ (M - e) := by
        apply Finset.sum_congr rfl
        intro e he
        exact Nat.pow_div (hE e he).2 (by norm_num)
      _ = ∑ j ∈ E.image (fun e => M - e), (2 : ℕ) ^ j := (Finset.sum_image hinj).symm
      _ ≤ ∑ j ∈ Finset.range (M - e₀ + 1), (2 : ℕ) ^ j := Finset.sum_le_sum_of_subset hsub
      _ ≤ 2 ^ (M - e₀ + 1) := sum_two_pow_le _
      _ = 2 * (2 ^ M / 2 ^ e₀) := by rw [Nat.pow_div he₀ (by norm_num), pow_succ]; ring
  · have hz : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hz, Finset.sum_empty, Nat.zero_le]

/-- Actual deletion across all working levels; the endpoint error sums
geometrically instead of losing one endpoint error per finest mesh cell. -/
theorem bad_union_count (B E : Finset ℕ) (M e₀ : ℕ) (θ : ℝ)
    (hB : B ⊆ Finset.range (2 ^ M))
    (hE : ∀ e ∈ E, e₀ ≤ e ∧ e ≤ M) (hθ : 0 ≤ θ) :
    ((badUnion B E θ).card : ℝ) ≤
      4 * θ * (E.card : ℝ) * (2 ^ M : ℕ) + 4 * ((2 ^ M / 2 ^ e₀ : ℕ) : ℝ) := by
  have hc : ((badUnion B E θ).card : ℝ) ≤
      ∑ e ∈ E, ((badIndices B (2 ^ e) θ).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := E) (t := fun e => badIndices B (2 ^ e) θ))
  have hsum := dyadic_reciprocal_sum E M e₀ hE
  have hsumR : (∑ e ∈ E, ((2 ^ M / 2 ^ e : ℕ) : ℝ)) ≤
      2 * ((2 ^ M / 2 ^ e₀ : ℕ) : ℝ) := by exact_mod_cast hsum
  calc
    _ ≤ ∑ e ∈ E, ((badIndices B (2 ^ e) θ).card : ℝ) := hc
    _ ≤ ∑ e ∈ E, (2 * θ * (2 ^ M : ℕ) + 2 * ((2 ^ M / 2 ^ e : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro e he
      exact bad_indices_count B (2 ^ M) (2 ^ e) θ (by positivity)
        (pow_dvd_pow 2 (hE e he).2) hB hθ
    _ = 2 * θ * (E.card : ℝ) * (2 ^ M : ℕ) +
        2 * (∑ e ∈ E, ((2 ^ M / 2 ^ e : ℕ) : ℝ)) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      ring
    _ ≤ 2 * θ * (E.card : ℝ) * (2 ^ M : ℕ) + 4 * ((2 ^ M / 2 ^ e₀ : ℕ) : ℝ) := by linarith only [hsumR]
    _ ≤ _ := by
      have hx : 0 ≤ θ * (E.card : ℝ) * (2 ^ M : ℕ) := by positivity
      nlinarith only [hx]

lemma bad_union_subset (B E : Finset ℕ) (θ : ℝ) : badUnion B E θ ⊆ B := by
  intro n hn
  obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hn
  exact (Finset.mem_filter.mp he).1

lemma padded_subset (B E : Finset ℕ) (θ : ℝ) : padded B E θ ⊆ B := Finset.sdiff_subset

/-- The deletion count gives retention of ORIGINAL heights, with the discrete
finest-working-scale restriction made explicit. -/
theorem padded_retention (B E : Finset ℕ) (M e₀ : ℕ) (θ q lam : ℝ)
    (hB : B ⊆ Finset.range (2 ^ M)) (hE : ∀ e ∈ E, e₀ ≤ e ∧ e ≤ M)
    (hne : E.Nonempty) (hθ : 0 ≤ θ) (hq : 0 < q) (hlam : 0 < lam)
    (hdensity : lam * (2 ^ M : ℕ) ≤ (B.card : ℝ))
    (hmargin : θ ≤ q * lam / (8 * (E.card : ℝ)))
    (hcutoff : 8 ≤ q * lam * (2 ^ e₀ : ℕ)) :
    (1 - q) * (B.card : ℝ) ≤ ((padded B E θ).card : ℝ) := by
  have hL : (0 : ℝ) < E.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  have hmargin' := (le_div_iff₀ (show 0 < 8 * (E.card : ℝ) by positivity)).mp hmargin
  have hcont := mul_le_mul_of_nonneg_right hmargin' (Nat.cast_nonneg (2 ^ M))
  have hquot : (((2 ^ M / 2 ^ e₀ : ℕ) : ℝ) * (2 ^ e₀ : ℕ)) ≤ (2 ^ M : ℕ) := by
    exact_mod_cast Nat.div_mul_le_self (2 ^ M) (2 ^ e₀)
  have hquot' := mul_le_mul_of_nonneg_left hquot (show 0 ≤ q * lam by positivity)
  have hcutoff' := mul_le_mul_of_nonneg_right hcutoff (Nat.cast_nonneg (2 ^ M / 2 ^ e₀))
  have hdisc : 8 * ((2 ^ M / 2 ^ e₀ : ℕ) : ℝ) ≤ q * lam * (2 ^ M : ℕ) := by
    nlinarith only [hquot', hcutoff']
  have hbad := bad_union_count B E M e₀ θ hB hE hθ
  have hbudget : ((badUnion B E θ).card : ℝ) ≤ q * lam * (2 ^ M : ℕ) := by
    nlinarith only [hbad, hcont, hdisc]
  have hsource := mul_le_mul_of_nonneg_left hdensity hq.le
  have hpart : ((padded B E θ).card : ℝ) + ((badUnion B E θ).card : ℝ) = B.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (bad_union_subset B E θ)
  nlinarith only [hbudget, hsource, hpart]

/-- Retained original indices satisfy both literal residue margins at every
retained working scale. -/
theorem padded_residue_bounds (B E : Finset ℕ) (θ : ℝ) {n e : ℕ}
    (hn : n ∈ padded B E θ) (he : e ∈ E) :
    θ * (2 ^ e : ℕ) ≤ ((n % 2 ^ e : ℕ) : ℝ) ∧
      ((n % 2 ^ e : ℕ) : ℝ) ≤ (2 ^ e : ℕ) - θ * (2 ^ e : ℕ) := by
  obtain ⟨hnB, hnnot⟩ := Finset.mem_sdiff.mp hn
  have hnot : n % 2 ^ e ∉ badResidues (2 ^ e) θ := by
    intro hbad
    exact hnnot (Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_filter.mpr ⟨hnB, hbad⟩⟩)
  have hres : n % 2 ^ e ∈ Finset.range (2 ^ e) := Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))
  have hl : ¬((n % 2 ^ e : ℕ) : ℝ) < θ * (2 ^ e : ℕ) := by
    intro h
    exact hnot (Finset.mem_filter.mpr ⟨hres, Or.inl h⟩)
  have hh : ¬(2 ^ e : ℕ) - θ * (2 ^ e : ℕ) < ((n % 2 ^ e : ℕ) : ℝ) := by
    intro h
    exact hnot (Finset.mem_filter.mpr ⟨hres, Or.inr h⟩)
  exact ⟨le_of_not_gt hl, le_of_not_gt hh⟩

/-- Two actual padded indices in different cells are separated by twice the
boundary margin. This is derived from quotient/remainder identities. -/
theorem different_cells_separated (n m R : ℕ) (θ : ℝ) (_hR : 0 < R)
    (hn : θ * R ≤ ((n % R : ℕ) : ℝ) ∧ ((n % R : ℕ) : ℝ) ≤ (R : ℝ) - θ * R)
    (hm : θ * R ≤ ((m % R : ℕ) : ℝ) ∧ ((m % R : ℕ) : ℝ) ≤ (R : ℝ) - θ * R)
    (hne : n / R ≠ m / R) :
    2 * θ * R ≤ |(n : ℝ) - (m : ℝ)| := by
  have hnid : ((n % R : ℕ) : ℝ) + (R : ℝ) * ((n / R : ℕ) : ℝ) = n := by exact_mod_cast Nat.mod_add_div n R
  have hmid : ((m % R : ℕ) : ℝ) + (R : ℝ) * ((m / R : ℕ) : ℝ) = m := by exact_mod_cast Nat.mod_add_div m R
  have hlo := le_abs_self ((n : ℝ) - (m : ℝ))
  have hhi := neg_le_abs ((n : ℝ) - (m : ℝ))
  rcases lt_or_gt_of_ne hne with h | h
  · have hstep : ((n / R : ℕ) : ℝ) + 1 ≤ ((m / R : ℕ) : ℝ) := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg R)
    nlinarith only [hnid, hmid, hn.2, hm.1, hmul, hhi]
  · have hstep : ((m / R : ℕ) : ℝ) + 1 ≤ ((n / R : ℕ) : ℝ) := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg R)
    nlinarith only [hnid, hmid, hn.1, hm.2, hmul, hlo]

lemma integer_height_separation {n m : ℕ} (hne : n ≠ m) : 1 ≤ |(n : ℝ) - (m : ℝ)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hh : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h
    nlinarith only [hh, neg_le_abs ((n : ℝ) - (m : ℝ))]
  · have hh : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h
    nlinarith only [hh, le_abs_self ((n : ℝ) - (m : ℝ))]

/-- An actual smallest common working ancestor and its actual working
predecessor suffice. The root is explicit, so no global dyadic-ancestor
assertion across unrelated root cells is used. -/
theorem padded_field_bound {X : Type*} [PseudoMetricSpace X]
    (B E : Finset ℕ) (M e₀ : ℕ) (θ K G C : ℝ) (F : ℕ → X)
    (hB : B ⊆ Finset.range (2 ^ M)) (hE : ∀ e ∈ E, e₀ ≤ e ∧ e ≤ M)
    (hroot : M ∈ E) (hmin : e₀ ∈ E) (_hθ : 0 < θ) (hK : 0 ≤ K) (_hG : 0 ≤ G) (hC : 0 ≤ C)
    (hbase : K * (2 ^ e₀ : ℕ) ≤ C) (hcost : K * G ≤ 2 * θ * C)
    (hgap : ∀ a ∈ E, ∀ b ∈ E, a < b →
      (∀ e ∈ E, a < e → e < b → False) → (2 ^ b : ℕ) ≤ G * (2 ^ a : ℕ))
    (hosc : ∀ e ∈ E, ∀ n ∈ B, ∀ m ∈ B, n / 2 ^ e = m / 2 ^ e →
      (2 ^ M : ℕ) * dist (F n) (F m) ≤ K * (2 ^ e : ℕ)) :
    ∀ n ∈ padded B E θ, ∀ m ∈ padded B E θ,
      (2 ^ M : ℕ) * dist (F n) (F m) ≤ C * |(n : ℝ) - (m : ℝ)| := by
  classical
  intro n hn m hm
  have hnB := padded_subset B E θ hn
  have hmB := padded_subset B E θ hm
  by_cases hnm : n = m
  · subst m
    simp
  have hsep := integer_height_separation hnm
  by_cases hfine : n / 2 ^ e₀ = m / 2 ^ e₀
  · exact (hosc e₀ hmin n hnB m hmB hfine).trans
      (hbase.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsep hC))
  · let A := E.filter (fun e => n / 2 ^ e = m / 2 ^ e)
    have hA : A.Nonempty := by
      refine ⟨M, Finset.mem_filter.mpr ⟨hroot, ?_⟩⟩
      rw [Nat.div_eq_of_lt (Finset.mem_range.mp (hB hnB)), Nat.div_eq_of_lt (Finset.mem_range.mp (hB hmB))]
    let b := A.min' hA
    have hbA : b ∈ A := Finset.min'_mem A hA
    obtain ⟨hbE, hbcommon⟩ := Finset.mem_filter.mp hbA
    have he₀b : e₀ < b := by
      have hlo := (hE b hbE).1
      have hne : e₀ ≠ b := by intro h; apply hfine; simpa only [h] using hbcommon
      omega
    let D := E.filter (fun a => a < b)
    have hD : D.Nonempty := ⟨e₀, Finset.mem_filter.mpr ⟨hmin, he₀b⟩⟩
    let a := D.max' hD
    have haD : a ∈ D := Finset.max'_mem D hD
    obtain ⟨haE, hab⟩ := Finset.mem_filter.mp haD
    have hnot : n / 2 ^ a ≠ m / 2 ^ a := by
      intro hsame
      have haA : a ∈ A := Finset.mem_filter.mpr ⟨haE, hsame⟩
      have hh : b ≤ a := Finset.min'_le A a haA
      omega
    have hadj : ∀ e ∈ E, a < e → e < b → False := by
      intro e he hae heb
      have heD : e ∈ D := Finset.mem_filter.mpr ⟨he, heb⟩
      have hh : e ≤ a := Finset.le_max' D e heD
      omega
    have hscale := hgap a haE b hbE hab hadj
    have hpadding := different_cells_separated n m (2 ^ a) θ (by positivity)
      (padded_residue_bounds B E θ hn haE) (padded_residue_bounds B E θ hm haE) hnot
    have hfirst := (hosc b hbE n hnB m hmB hbcommon).trans (mul_le_mul_of_nonneg_left hscale hK)
    calc
      _ ≤ K * (G * (2 ^ a : ℕ)) := hfirst
      _ = (K * G) * (2 ^ a : ℕ) := by ring
      _ ≤ (2 * θ * C) * (2 ^ a : ℕ) := mul_le_mul_of_nonneg_right hcost (Nat.cast_nonneg _)
      _ = C * (2 * θ * (2 ^ a : ℕ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpadding hC


def height (M n : ℕ) : ℝ := (n : ℝ) / (2 ^ M : ℕ)

def paddingMargin (E : Finset ℕ) (q lam : ℝ) : ℝ := q * lam / (8 * (E.card : ℝ))

def lipschitzConstant (E : Finset ℕ) (K G q lam : ℝ) : ℝ :=
  8 * K * G * (E.card : ℝ) / (q * lam)

lemma height_difference (M n m : ℕ) :
    |height M n - height M m| = |(n : ℝ) - (m : ℝ)| / (2 ^ M : ℕ) := by
  unfold height
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 ^ M : ℕ))]

/-- The upper cutoff controls pairs in one smallest working cell. The lower
cutoff is separately used for retention; these two conditions are distinct. -/
theorem numerical_padding_parameters (E : Finset ℕ) (e₀ : ℕ) (K G q lam : ℝ)
    (hne : E.Nonempty) (hK : 0 ≤ K) (hG : 1 ≤ G) (hq : 0 < q) (hlam : 0 < lam)
    (hupper : q * lam * (2 ^ e₀ : ℕ) ≤ 8 * G) :
    0 < paddingMargin E q lam ∧ 0 ≤ lipschitzConstant E K G q lam ∧
      K * (2 ^ e₀ : ℕ) ≤ lipschitzConstant E K G q lam ∧
      K * G ≤ 2 * paddingMargin E q lam * lipschitzConstant E K G q lam := by
  have hL : (0 : ℝ) < E.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  have hLone : (1 : ℝ) ≤ E.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hG0 : 0 ≤ G := by linarith only [hG]
  have hmargin : 0 < paddingMargin E q lam := by unfold paddingMargin; positivity
  have hC : 0 ≤ lipschitzConstant E K G q lam := by unfold lipschitzConstant; positivity
  have hbase : K * (2 ^ e₀ : ℕ) ≤ lipschitzConstant E K G q lam := by
    unfold lipschitzConstant
    apply (le_div_iff₀ (show 0 < q * lam by positivity)).mpr
    have hu := mul_le_mul_of_nonneg_left hupper hK
    have hLbound := mul_le_mul_of_nonneg_left hLone (show 0 ≤ 8 * K * G by positivity)
    nlinarith only [hu, hLbound]
  have hcostEq : 2 * paddingMargin E q lam * lipschitzConstant E K G q lam = 2 * K * G := by
    unfold paddingMargin lipschitzConstant
    field_simp [hq.ne', hlam.ne', hL.ne']
  refine ⟨hmargin, hC, hbase, ?_⟩
  rw [hcostEq]
  have hKG : 0 ≤ K * G := mul_nonneg hK hG0
  linarith only [hKG]

/-- Construct a retained set of ORIGINAL dyadic-height indices, with explicit
mass retention and ordinary Lipschitz control on the same retained set.
The given working levels include one fixed root; the two cutoff inequalities
state exactly the range needed for a least-working-scale selection. -/
theorem exists_padded_lipschitz {X : Type*} [PseudoMetricSpace X]
    (B E : Finset ℕ) (M e₀ : ℕ) (K G q lam : ℝ) (F : ℕ → X)
    (hB : B ⊆ Finset.range (2 ^ M)) (hE : ∀ e ∈ E, e₀ ≤ e ∧ e ≤ M)
    (hroot : M ∈ E) (hmin : e₀ ∈ E)
    (hK : 0 ≤ K) (hG : 1 ≤ G) (hq : 0 < q) (hqone : q < 1) (hlam : 0 < lam)
    (hdensity : lam * (2 ^ M : ℕ) ≤ (B.card : ℝ))
    (hcutoff : 8 ≤ q * lam * (2 ^ e₀ : ℕ))
    (hupper : q * lam * (2 ^ e₀ : ℕ) ≤ 8 * G)
    (hgap : ∀ a ∈ E, ∀ b ∈ E, a < b →
      (∀ e ∈ E, a < e → e < b → False) → (2 ^ b : ℕ) ≤ G * (2 ^ a : ℕ))
    (hosc : ∀ e ∈ E, ∀ n ∈ B, ∀ m ∈ B, n / 2 ^ e = m / 2 ^ e →
      dist (F n) (F m) ≤ K * (((2 ^ e : ℕ) : ℝ) / ((2 ^ M : ℕ) : ℝ))) :
    ∃ S ⊆ B, S.Nonempty ∧ (1 - q) * (B.card : ℝ) ≤ (S.card : ℝ) ∧
      (∀ n ∈ S, ∀ e ∈ E,
        paddingMargin E q lam * (2 ^ e : ℕ) ≤ ((n % 2 ^ e : ℕ) : ℝ) ∧
        ((n % 2 ^ e : ℕ) : ℝ) ≤ (2 ^ e : ℕ) - paddingMargin E q lam * (2 ^ e : ℕ)) ∧
      (∀ n ∈ S, ∀ m ∈ S,
        dist (F n) (F m) ≤ lipschitzConstant E K G q lam * |height M n - height M m|) := by
  have hne : E.Nonempty := ⟨e₀, hmin⟩
  obtain ⟨hθ, hC, hbase, hcost⟩ := numerical_padding_parameters E e₀ K G q lam hne hK hG hq hlam hupper
  let S := padded B E (paddingMargin E q lam)
  have hret := padded_retention B E M e₀ (paddingMargin E q lam) q lam
    hB hE hne hθ.le hq hlam hdensity le_rfl hcutoff
  have hN : (0 : ℝ) < (2 ^ M : ℕ) := by positivity
  have hBpos : (0 : ℝ) < B.card := (mul_pos hlam hN).trans_le hdensity
  have hSpos : (0 : ℝ) < S.card := (mul_pos (sub_pos.mpr hqone) hBpos).trans_le hret
  have hSne : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSpos)
  have hosc' : ∀ e ∈ E, ∀ n ∈ B, ∀ m ∈ B, n / 2 ^ e = m / 2 ^ e →
      (2 ^ M : ℕ) * dist (F n) (F m) ≤ K * (2 ^ e : ℕ) := by
    intro e he n hn m hm hnm
    have hh : dist (F n) (F m) ≤ K * (2 ^ e : ℕ) / (2 ^ M : ℕ) := by
      simpa only [mul_div_assoc] using hosc e he n hn m hm hnm
    have hcross := (le_div_iff₀ hN).mp hh
    nlinarith only [hcross]
  have hfield := padded_field_bound B E M e₀ (paddingMargin E q lam) K G
    (lipschitzConstant E K G q lam) F hB hE hroot hmin hθ hK
    (show 0 ≤ G by linarith only [hG]) hC hbase hcost hgap hosc'
  refine ⟨S, padded_subset B E _, hSne, hret, ?_, ?_⟩
  · intro n hn e he
    exact padded_residue_bounds B E _ hn he
  · intro n hn m hm
    have hh := hfield n hn m hm
    rw [height_difference, ← mul_div_assoc]
    apply (le_div_iff₀ hN).mpr
    nlinarith only [hh]

end
end DyadicHeightBoundaryPadding
