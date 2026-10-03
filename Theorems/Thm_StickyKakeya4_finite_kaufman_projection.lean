import Theorems.Thm_StickyKakeya4_projection_heavy_cells
import Theorems.Thm_StickyKakeya4_projection_annulus_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Finset
open scoped BigOperators

noncomputable section

namespace FiniteKaufmanProjection

open ProjectionHeavyCells

def scales (n : ℕ) : Finset ℝ := (Finset.range (n + 1)).image ProjectionAnnulusEnergy.mesh

def threshold (n : ℕ) (KP KL q : ℝ) : ℝ :=
  8 * KP * KL * ((n : ℝ) + 3) ^ 2 / q ^ 2

theorem scale_ge_mesh {n : ℕ} {r : ℝ} (hr : r ∈ scales n) :
    ProjectionAnnulusEnergy.mesh n ≤ r := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hjn

theorem scales_card_le (n : ℕ) : ((scales n).card : ℝ) ≤ (n : ℝ) + 3 := by
  have h : (scales n).card ≤ n + 1 :=
    (Finset.card_image_le).trans_eq (Finset.card_range (n + 1))
  have hh : ((scales n).card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast h
  linarith

theorem threshold_pos {n : ℕ} {KP KL q : ℝ}
    (hKP : 1 ≤ KP) (hKL : 1 ≤ KL) (hq : 0 < q) : 0 < threshold n KP KL q := by
  unfold threshold
  positivity

theorem threshold_ge_eight {n : ℕ} {KP KL q : ℝ}
    (hKP : 1 ≤ KP) (hKL : 1 ≤ KL) (hq : 0 < q) (hq1 : q ≤ 1) :
    8 * KP ≤ threshold n KP KL q := by
  have hKP0 : 0 ≤ KP := by linarith
  have hL : 1 ≤ ((n : ℝ) + 3) ^ 2 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hprod : 1 ≤ KL * ((n : ℝ) + 3) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hKL) (sub_nonneg.mpr hL)]
  have hq2 : q ^ 2 ≤ 1 := by nlinarith
  unfold threshold
  apply (le_div_iff₀ (sq_pos_of_pos hq)).2
  have hh := mul_le_mul_of_nonneg_left (hq2.trans hprod) (show 0 ≤ 8 * KP by positivity)
  nlinarith only [hh]

theorem heavy_row_bound
    (P : Finset (ℝ × ℝ)) (Lambda : Finset ℝ) (n : ℕ) (KP KL t A r : ℝ)
    (hPnon : P.Nonempty) (hKP : 1 ≤ KP) (hKL : 1 ≤ KL)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hA : 8 * KP ≤ A)
    (hr : ProjectionAnnulusEnergy.mesh n ≤ r)
    (hP : ∀ p ∈ P, |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    (hLambda : ∀ lam ∈ Lambda, |lam| ≤ 1)
    (hFP : ProjectionAnnulusEnergy.PointFrostman P (ProjectionAnnulusEnergy.mesh n) KP t)
    (hFL : ProjectionAnnulusEnergy.SlopeFrostman Lambda (ProjectionAnnulusEnergy.mesh n) KL t) :
    A * (∑ lam ∈ Lambda,
      ((heavy P (projectionCell lam r) (A * r ^ t * P.card)).card : ℝ)) ≤
      8 * KP * KL * ((n : ℝ) + 3) * P.card * Lambda.card := by
  classical
  have hrpos : 0 < r := (ProjectionAnnulusEnergy.mesh_pos n).trans_le hr
  have hN : 0 < (P.card : ℝ) := by exact_mod_cast hPnon.card_pos
  have hc : 0 < r ^ t * (P.card : ℝ) := mul_pos (Real.rpow_pos_of_pos hrpos _) hN
  have hab : 2 * (4 * KP * r ^ t * P.card) ≤ A * r ^ t * P.card := by
    have hh := mul_le_mul_of_nonneg_right hA hc.le
    nlinarith only [hh]
  have hnear : ∀ p ∈ P,
      ((P.filter (fun q => distance p q < 4 * r)).card : ℝ) ≤ 4 * KP * r ^ t * P.card := by
    intro p _hp
    exact ProjectionAnnulusEnergy.near_pairs_bound P (ProjectionAnnulusEnergy.mesh_pos n)
      hr hKP ht ht1 hFP p
  have hlower : (A * r ^ t * P.card / 2) *
      (∑ lam ∈ Lambda, ((heavy P (projectionCell lam r) (A * r ^ t * P.card)).card : ℝ)) ≤
        ProjectionAnnulusEnergy.energy P Lambda r := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun lam _hlam =>
      projection_heavy_mass_le_far_pairs P lam r _ _ hrpos hab hnear)
  have hupper := ProjectionAnnulusEnergy.kaufman_pair_energy P Lambda n KP KL t r
    hKP hKL ht ht1 hr hP hLambda hFP hFL
  apply (mul_le_mul_iff_left₀ hc).mp
  calc
    (A * (∑ lam ∈ Lambda,
        ((heavy P (projectionCell lam r) (A * r ^ t * P.card)).card : ℝ))) *
        (r ^ t * (P.card : ℝ)) =
        2 * ((A * r ^ t * P.card / 2) *
          (∑ lam ∈ Lambda, ((heavy P (projectionCell lam r) (A * r ^ t * P.card)).card : ℝ))) := by ring
    _ ≤ 2 * ProjectionAnnulusEnergy.energy P Lambda r :=
      mul_le_mul_of_nonneg_left hlower (by norm_num)
    _ ≤ 2 * (4 * KP * KL * ((n : ℝ) + 3) * r ^ t * (P.card : ℝ) ^ 2 * Lambda.card) :=
      mul_le_mul_of_nonneg_left hupper (by norm_num)
    _ = (8 * KP * KL * ((n : ℝ) + 3) * P.card * Lambda.card) *
        (r ^ t * (P.card : ℝ)) := by ring

theorem actual_bad_budget
    (P : Finset (ℝ × ℝ)) (Lambda : Finset ℝ) (n : ℕ) (KP KL t q : ℝ)
    (hPnon : P.Nonempty) (hKP : 1 ≤ KP) (hKL : 1 ≤ KL)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1)
    (hP : ∀ p ∈ P, |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    (hLambda : ∀ lam ∈ Lambda, |lam| ≤ 1)
    (hFP : ProjectionAnnulusEnergy.PointFrostman P (ProjectionAnnulusEnergy.mesh n) KP t)
    (hFL : ProjectionAnnulusEnergy.SlopeFrostman Lambda (ProjectionAnnulusEnergy.mesh n) KL t) :
    (∑ lam ∈ Lambda, ((badUnion P (scales n) lam (threshold n KP KL q) t).card : ℝ)) ≤
      q ^ 2 * P.card * Lambda.card := by
  classical
  let A := threshold n KP KL q
  let C := 8 * KP * KL * ((n : ℝ) + 3) * (P.card : ℝ) * Lambda.card
  have hApos : 0 < A := threshold_pos hKP hKL hq
  have hAbound : 8 * KP ≤ A := threshold_ge_eight hKP hKL hq hq1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum : A * (∑ lam ∈ Lambda, ((badUnion P (scales n) lam A t).card : ℝ)) ≤
      ((n : ℝ) + 3) * C := by
    calc
      _ ≤ A * (∑ lam ∈ Lambda, ∑ r ∈ scales n,
          ((heavy P (projectionCell lam r) (A * r ^ t * P.card)).card : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hApos.le
        exact Finset.sum_le_sum (fun lam _hlam => badUnion_card_le_sum P (scales n) lam A t)
      _ = ∑ r ∈ scales n, A * (∑ lam ∈ Lambda,
          ((heavy P (projectionCell lam r) (A * r ^ t * P.card)).card : ℝ)) := by
        rw [Finset.sum_comm]
        rw [Finset.mul_sum]
      _ ≤ ∑ _r ∈ scales n, C := by
        apply Finset.sum_le_sum
        intro r hr
        exact heavy_row_bound P Lambda n KP KL t A r hPnon hKP hKL ht ht1 hAbound
          (scale_ge_mesh hr) hP hLambda hFP hFL
      _ = ((scales n).card : ℝ) * C := by simp
      _ ≤ ((n : ℝ) + 3) * C := mul_le_mul_of_nonneg_right (scales_card_le n) hC
  apply (mul_le_mul_iff_right₀ hApos).mp
  change A * (∑ lam ∈ Lambda, ((badUnion P (scales n) lam A t).card : ℝ)) ≤
    A * (q ^ 2 * P.card * Lambda.card)
  convert hsum using 1
  dsimp [A, C, threshold]
  field_simp

theorem exists_query_scale (n : ℕ) {r : ℝ}
    (hrlo : ProjectionAnnulusEnergy.mesh n ≤ r) (hrhi : r ≤ 1) :
    ∃ h ∈ scales n, 0 < h ∧ h ≤ r ∧ r ≤ 2 * h := by
  classical
  by_cases heq : r = ProjectionAnnulusEnergy.mesh n
  · refine ⟨ProjectionAnnulusEnergy.mesh n, ?_, ProjectionAnnulusEnergy.mesh_pos n, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), rfl⟩
    · exact hrlo
    · rw [heq]
      have hpos := ProjectionAnnulusEnergy.mesh_pos n
      linarith
  · have hrstrict : ProjectionAnnulusEnergy.mesh n < r := lt_of_le_of_ne hrlo (Ne.symm heq)
    obtain ⟨j, hj, hlo, hhi⟩ := ProjectionAnnulusEnergy.exists_annulus n hrstrict (by linarith)
    refine ⟨ProjectionAnnulusEnergy.mesh j, Finset.mem_image.mpr ⟨j, hj, rfl⟩,
      ProjectionAnnulusEnergy.mesh_pos j, ?_, ?_⟩
    · dsimp [ProjectionAnnulusEnergy.annulusScale, ProjectionAnnulusEnergy.mesh] at hlo ⊢
      linarith
    · exact hhi

/-- Full finite Kaufman conclusion on actual original points and slopes.
The energy estimate and all heavy cells are constructed from the literal
Frostman counts, rather than supplied as a projection certificate. -/
theorem finite_kaufman_projection
    (P : Finset (ℝ × ℝ)) (Lambda : Finset ℝ) (n : ℕ) (KP KL t q : ℝ)
    (hPnon : P.Nonempty) (hKP : 1 ≤ KP) (hKL : 1 ≤ KL)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hq : 0 < q) (hq1 : q < 1)
    (hP : ∀ p ∈ P, |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    (hLambda : ∀ lam ∈ Lambda, |lam| ≤ 1)
    (hFP : ProjectionAnnulusEnergy.PointFrostman P (ProjectionAnnulusEnergy.mesh n) KP t)
    (hFL : ProjectionAnnulusEnergy.SlopeFrostman Lambda (ProjectionAnnulusEnergy.mesh n) KL t) :
    ∃ Lambda' : Finset ℝ, Lambda' ⊆ Lambda ∧
      (1 - q) * (Lambda.card : ℝ) ≤ Lambda'.card ∧
      ∀ lam ∈ Lambda', ∃ P' : Finset (ℝ × ℝ), P' ⊆ P ∧
        (1 - q) * (P.card : ℝ) ≤ P'.card ∧
        ∀ Q : Finset (ℝ × ℝ), Q ⊆ P' → q * (P'.card : ℝ) ≤ Q.card →
          ∀ c r : ℝ, ProjectionAnnulusEnergy.mesh n ≤ r → r ≤ 1 →
            ((Q.filter (fun p => |projection lam p - c| ≤ r)).card : ℝ) ≤
              (48 * KP * KL * ((n : ℝ) + 3) ^ 2 / (q ^ 3 * (1 - q))) *
                r ^ t * Q.card := by
  classical
  let A := threshold n KP KL q
  let Bad := fun lam => badUnion P (scales n) lam A t
  let Good := Lambda.filter (fun lam => ((Bad lam).card : ℝ) ≤ q * P.card)
  have hApos : 0 < A := threshold_pos hKP hKL hq
  have hA0 : 0 ≤ A := hApos.le
  have hN0 : 0 ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hqcomp : 0 < 1 - q := sub_pos.mpr hq1
  have hdpos : 0 < q * (1 - q) := mul_pos hq hqcomp
  have hbudget := actual_bad_budget P Lambda n KP KL t q hPnon hKP hKL ht ht1
    hq hq1.le hP hLambda hFP hFL
  have hGood : (1 - q) * (Lambda.card : ℝ) ≤ (Good.card : ℝ) :=
    good_slopes_of_bad_budget P Lambda Bad q hPnon hq hbudget
  refine ⟨Good, Finset.filter_subset _ _, hGood, ?_⟩
  intro lam hlam
  let P' := retained P (scales n) lam A t
  have hret : (1 - q) * (P.card : ℝ) ≤ (P'.card : ℝ) :=
    retained_card_of_good P (scales n) lam A t q (Finset.mem_filter.mp hlam).2
  refine ⟨P', retained_subset P (scales n) lam A t, hret, ?_⟩
  intro Q hQ hQmass c r hrlo hrhi
  obtain ⟨h, hhmem, hh, hhr, hrh⟩ := exists_query_scale n hrlo hrhi
  have hrpos : 0 < r := hh.trans_le hhr
  have hdenom : (q * (1 - q)) * (P.card : ℝ) ≤ (Q.card : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hret hq.le
    nlinarith only [hm, hQmass]
  have hcpos : 0 ≤ (6 * A / (q * (1 - q))) * r ^ t := by positivity
  have hcoefficient : 6 * A / (q * (1 - q)) =
      48 * KP * KL * ((n : ℝ) + 3) ^ 2 / (q ^ 3 * (1 - q)) := by
    dsimp [A, threshold]
    field_simp
    ring
  calc
    ((Q.filter (fun p => |projection lam p - c| ≤ r)).card : ℝ) ≤
        5 * A * h ^ t * P.card :=
      retained_interval_bound P Q (scales n) lam A t c r h hA0 hh hhmem hrh hQ
    _ ≤ 5 * A * r ^ t * P.card := by
      gcongr
    _ ≤ 6 * A * r ^ t * P.card := by
      gcongr
      norm_num
    _ = ((6 * A / (q * (1 - q))) * r ^ t) * ((q * (1 - q)) * P.card) := by
      field_simp
    _ ≤ ((6 * A / (q * (1 - q))) * r ^ t) * Q.card :=
      mul_le_mul_of_nonneg_left hdenom hcpos
    _ = _ := by rw [hcoefficient]

end FiniteKaufmanProjection
