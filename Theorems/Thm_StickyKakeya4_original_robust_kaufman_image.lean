import Theorems.Thm_StickyKakeya4_finite_kaufman_projection
import Theorems.Thm_StickyKakeya4_actual_rounded_additive_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalRobustKaufmanImage
open ProjectionAnnulusEnergy ActualRoundedAdditiveEnergy

/-- A dense original query survives the slope-dependent deletion. -/
lemma dense_intersection {X : Type*} [DecidableEq X]
    (P P' Q : Finset X) {q : ℝ} (hq : 0 ≤ q)
    (hP' : P' ⊆ P) (hQ : Q ⊆ P)
    (hret : (1-q)*(P.card : ℝ) ≤ P'.card)
    (hmass : 2*q*(P.card : ℝ) ≤ Q.card) :
    q*(P.card : ℝ) ≤ (Q ∩ P').card ∧
      q*(P'.card : ℝ) ≤ (Q ∩ P').card := by
  have hu : Q ∪ P' ⊆ P := Finset.union_subset hQ hP'
  have huc : ((Q ∪ P').card : ℝ) ≤ P.card := by
    exact_mod_cast Finset.card_le_card hu
  have he : ((Q ∪ P').card : ℝ) + (Q ∩ P').card = Q.card + P'.card := by
    exact_mod_cast Finset.card_union_add_card_inter Q P'
  have hpc : (P'.card : ℝ) ≤ P.card := by exact_mod_cast Finset.card_le_card hP'
  constructor
  · nlinarith
  · have hmul := mul_le_mul_of_nonneg_left hpc hq
    nlinarith

/-- An original interval profile bounds the actual occupied floor image.
There is no original mesh-membership assumption. -/
lemma floor_image_lower (Q : Finset Point) (lam : ℝ) {delta K : ℝ}
    (hdelta : 0 < delta) (hQ : Q.Nonempty)
    (hprofile : ∀ c : ℝ,
      ((Q.filter (fun p => |projection lam p-c| ≤ delta)).card : ℝ) ≤ K*Q.card) :
    1 ≤ K * (Q.image (fun p => rounded delta (projection lam p))).card := by
  let f := fun p => rounded delta (projection lam p)
  have hfib : ∀ z ∈ Q.image f,
      ((Q.filter (fun p => f p=z)).card : ℝ) ≤ K*Q.card := by
    intro z _hz
    have hsub : Q.filter (fun p => f p=z) ⊆
        Q.filter (fun p => |projection lam p-delta*(z : ℝ)| ≤ delta) := by
      intro p hp
      obtain ⟨hpQ, hpz⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨hpQ, ?_⟩
      have he := round_error hdelta (projection lam p)
      change rounded delta (projection lam p) = z at hpz
      rw [hpz] at he
      exact abs_le.mpr ⟨by linarith, he.2.le⟩
    exact (show ((Q.filter (fun p => f p=z)).card : ℝ) ≤
      (Q.filter (fun p => |projection lam p-delta*(z : ℝ)| ≤ delta)).card by
        exact_mod_cast Finset.card_le_card hsub).trans (hprofile (delta*(z : ℝ)))
  have hcount : (Q.card : ℝ) ≤ (K*Q.card)*(Q.image f).card := by
    calc
      _ = ∑ z ∈ Q.image f, ((Q.filter (fun p => f p=z)).card : ℝ) := by
        exact_mod_cast Finset.card_eq_sum_card_image f Q
      _ ≤ ∑ _z ∈ Q.image f, K*Q.card := Finset.sum_le_sum hfib
      _ = _ := by simp [mul_comm]
  have hpos : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  have he : (K*(Q.image f).card)*(Q.card : ℝ) = (K*Q.card)*(Q.image f).card := by ring
  rw [← he] at hcount
  exact (mul_le_mul_iff_left₀ hpos).mp (by simpa only [one_mul] using hcount)

/-- For most original slopes, every dense original subset has a large literal
projected floor image. The query can depend on the slope. This is a robust
Kaufman bound with its actual exponent, not the stronger OS regular theorem. -/
theorem original_robust_kaufman_image
    (P : Finset Point) (Lambda : Finset ℝ) (n : ℕ) (KP KL t q : ℝ)
    (hPnon : P.Nonempty) (hKP : 1 ≤ KP) (hKL : 1 ≤ KL)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hq : 0 < q) (hq1 : q < 1)
    (hP : ∀ p ∈ P, |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    (hLambda : ∀ lam ∈ Lambda, |lam| ≤ 1)
    (hFP : PointFrostman P (mesh n) KP t)
    (hFL : SlopeFrostman Lambda (mesh n) KL t) :
    ∃ Lambda' : Finset ℝ, Lambda' ⊆ Lambda ∧
      (1-q)*(Lambda.card : ℝ) ≤ Lambda'.card ∧
      ∀ lam ∈ Lambda', ∀ Q : Finset Point, Q ⊆ P →
        2*q*(P.card : ℝ) ≤ Q.card →
        1 ≤ (48*KP*KL*((n : ℝ)+3)^2/(q^3*(1-q))) * (mesh n)^t *
          (Q.image (fun p => rounded (mesh n) (projection lam p))).card := by
  obtain ⟨Lambda', hsub, hmass, hgood⟩ :=
    FiniteKaufmanProjection.finite_kaufman_projection P Lambda n KP KL t q
      hPnon hKP hKL ht ht1 hq hq1 hP hLambda hFP hFL
  refine ⟨Lambda', hsub, hmass, ?_⟩
  intro lam hlam Q hQP hQmass
  obtain ⟨P', hP'P, hret, hprofile⟩ := hgood lam hlam
  obtain ⟨hinterP, hinterP'⟩ := dense_intersection P P' Q hq.le hP'P hQP hret hQmass
  have hinterpos : (0 : ℝ) < (Q ∩ P').card := by
    have hPpos : (0 : ℝ) < P.card := by exact_mod_cast hPnon.card_pos
    exact (mul_pos hq hPpos).trans_le hinterP
  have hnon : (Q ∩ P').Nonempty := Finset.card_pos.mp (by exact_mod_cast hinterpos)
  have hmesh1 : mesh n ≤ 1 := by
    exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
  have hbound := floor_image_lower (Q ∩ P') lam (mesh_pos n) hnon
    (fun c => hprofile (Q ∩ P') Finset.inter_subset_right hinterP' c (mesh n) le_rfl hmesh1)
  have himage : (Q ∩ P').image (fun p => rounded (mesh n) (projection lam p)) ⊆
      Q.image (fun p => rounded (mesh n) (projection lam p)) :=
    Finset.image_subset_image Finset.inter_subset_left
  have hcard : (((Q ∩ P').image (fun p => rounded (mesh n) (projection lam p))).card : ℝ) ≤
      (Q.image (fun p => rounded (mesh n) (projection lam p))).card := by
    exact_mod_cast Finset.card_le_card himage
  have hKPpos : 0 < KP := lt_of_lt_of_le zero_lt_one hKP
  have hKLpos : 0 < KL := lt_of_lt_of_le zero_lt_one hKL
  have hcomp : 0 < 1-q := sub_pos.mpr hq1
  have hmpos := mesh_pos n
  exact hbound.trans (mul_le_mul_of_nonneg_left hcard (by positivity))

end OriginalRobustKaufmanImage
