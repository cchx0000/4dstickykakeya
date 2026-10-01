import Theorems.Thm_StickyKakeya4_three_packet_half_mass
import Theorems.Thm_StickyKakeya4_collision_heavy_edge_decomposition

open Set

noncomputable section

namespace StickyKakeya4

/-- The probability weight on source rows incident to one physical point.
The original `ENNReal` row weight is converted to a real number only after
normalizing by the finite, nonzero pointwise multiplicity. -/
noncomputable def sourcePointNormalizedWeight {n : ℕ}
    (R : FiniteScaleSource n) (x : E4) (i : Fin n) : ℝ := by
  classical
  exact if x ∈ R.shading i then
    (R.weight i).toReal / (sourceFunction R x).toReal
  else 0

theorem sourceFunction_ne_top_of_weight_ne_top {n : ℕ}
    (R : FiniteScaleSource n) (x : E4)
    (hweightTop : ∀ i, R.weight i ≠ ⊤) :
    sourceFunction R x ≠ ⊤ := by
  unfold sourceFunction
  apply ENNReal.sum_ne_top.2
  intro i _hi
  split_ifs
  · exact hweightTop i
  · exact ENNReal.zero_ne_top

theorem sourcePointNormalizedWeight_nonneg {n : ℕ}
    (R : FiniteScaleSource n) (x : E4) (i : Fin n) :
    0 ≤ sourcePointNormalizedWeight R x i := by
  unfold sourcePointNormalizedWeight
  split_ifs
  · positivity
  · exact le_rfl

/-- The incident row law is exactly normalized; no row-count replacement is
made. -/
theorem sum_sourcePointNormalizedWeight_eq_one {n : ℕ}
    (R : FiniteScaleSource n) (x : E4)
    (hweightTop : ∀ i, R.weight i ≠ ⊤)
    (hsourceZero : sourceFunction R x ≠ 0) :
    (∑ i, sourcePointNormalizedWeight R x i) = 1 := by
  classical
  have hsourceTop : sourceFunction R x ≠ ⊤ :=
    sourceFunction_ne_top_of_weight_ne_top R x hweightTop
  have hdenReal : (sourceFunction R x).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hsourceZero, hsourceTop⟩
  have htoReal :
      (∑ i, if x ∈ R.shading i then (R.weight i).toReal else 0) =
        (sourceFunction R x).toReal := by
    unfold sourceFunction
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro i _hi
      split_ifs <;> simp
    · intro i _hi
      split_ifs
      · exact hweightTop i
      · exact ENNReal.zero_ne_top
  calc
    (∑ i, sourcePointNormalizedWeight R x i) =
        (∑ i, if x ∈ R.shading i then (R.weight i).toReal else 0) /
          (sourceFunction R x).toReal := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _hi
      unfold sourcePointNormalizedWeight
      split_ifs <;> simp
    _ = 1 := by rw [htoReal, div_self hdenReal]

theorem sourcePointNormalizedWeight_pos_has_active_row {n : ℕ}
    (R : FiniteScaleSource n) (x : E4) (i : Fin n)
    (hpos : 0 < sourcePointNormalizedWeight R x i) :
    x ∈ R.shading i ∧ R.weight i ≠ 0 := by
  have hshade : x ∈ R.shading i := by
    by_contra hnot
    simp [sourcePointNormalizedWeight, hnot] at hpos
  refine ⟨hshade, ?_⟩
  intro hzero
  simp [sourcePointNormalizedWeight, hshade, hzero] at hpos

/-- The reusable pointwise routing output.  The first branch retains four
actual positive source rows and all six affine-mark separations.  The second
branch retains the three packet centers together with exact coefficient-one
mass conservation and the half-removal estimate. -/
def SourcePointFourOrThreePacketAlternative {n : ℕ}
    (R : FiniteScaleSource n) (x : E4)
    (timeGap : ℝ) (current : ENNReal) : Prop :=
  (∃ i₀ i₁ i₂ i₃,
      x ∈ R.shading i₀ ∧ R.weight i₀ ≠ 0 ∧
      x ∈ R.shading i₁ ∧ R.weight i₁ ≠ 0 ∧
      x ∈ R.shading i₂ ∧ R.weight i₂ ≠ 0 ∧
      x ∈ R.shading i₃ ∧ R.weight i₃ ≠ 0 ∧
      finiteReebSeparated R.fibreMark timeGap i₁ i₀ ∧
      finiteReebSeparated R.fibreMark timeGap i₂ i₀ ∧
      finiteReebSeparated R.fibreMark timeGap i₂ i₁ ∧
      finiteReebSeparated R.fibreMark timeGap i₃ i₀ ∧
      finiteReebSeparated R.fibreMark timeGap i₃ i₁ ∧
      finiteReebSeparated R.fibreMark timeGap i₃ i₂) ∨
    ∃ a b c, ∃ removed continuing : ENNReal,
      removed = current * ENNReal.ofReal
        (finiteThreePacketsMass (sourcePointNormalizedWeight R x)
          R.fibreMark timeGap a b c) ∧
      continuing = current * ENNReal.ofReal
        (finiteOutsideThreePacketsMass (sourcePointNormalizedWeight R x)
          R.fibreMark timeGap a b c) ∧
      current = removed + continuing ∧
      current ≤ removed + removed

/-- Pointwise stopping dichotomy for an actual source population.  At a
positive-multiplicity point, the original weighted rows either contain four
positive incident rows with six strict separations of their affine Reeb marks,
or three actual mark packets remove at least half of the supplied current mass
with exact coefficient-one conservation. -/
theorem sourcePoint_four_incident_mark_samples_or_three_packet_half_removal
    {n : ℕ}
    (R : FiniteScaleSource n) (x : E4)
    (hweightTop : ∀ i, R.weight i ≠ ⊤)
    (hsourceZero : sourceFunction R x ≠ 0)
    (timeGap : ℝ) (current : ENNReal) :
    SourcePointFourOrThreePacketAlternative R x timeGap current := by
  unfold SourcePointFourOrThreePacketAlternative
  have hn : 0 < n := by
    by_contra hnpos
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
    subst n
    apply hsourceZero
    simp [sourceFunction]
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rcases finite_positive_four_samples_or_scaled_three_packet_half_removal
      (sourcePointNormalizedWeight R x) R.fibreMark timeGap
      (sourcePointNormalizedWeight_nonneg R x)
      (sum_sourcePointNormalizedWeight_eq_one R x hweightTop hsourceZero)
      current with hfour | hthree
  · left
    obtain ⟨i₀, i₁, i₂, i₃, hi₀, hi₁, hi₂, hi₃,
      h₁₀, h₂₀, h₂₁, h₃₀, h₃₁, h₃₂⟩ := hfour
    obtain ⟨hi₀shade, hi₀weight⟩ :=
      sourcePointNormalizedWeight_pos_has_active_row R x i₀ hi₀
    obtain ⟨hi₁shade, hi₁weight⟩ :=
      sourcePointNormalizedWeight_pos_has_active_row R x i₁ hi₁
    obtain ⟨hi₂shade, hi₂weight⟩ :=
      sourcePointNormalizedWeight_pos_has_active_row R x i₂ hi₂
    obtain ⟨hi₃shade, hi₃weight⟩ :=
      sourcePointNormalizedWeight_pos_has_active_row R x i₃ hi₃
    exact ⟨i₀, i₁, i₂, i₃,
      hi₀shade, hi₀weight, hi₁shade, hi₁weight,
      hi₂shade, hi₂weight, hi₃shade, hi₃weight,
      h₁₀, h₂₀, h₂₁, h₃₀, h₃₁, h₃₂⟩
  · exact Or.inr hthree

end StickyKakeya4
