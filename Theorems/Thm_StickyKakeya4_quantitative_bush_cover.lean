import Theorems.Thm_StickyKakeya4_time_averaged_bush
import Theorems.Thm_StickyKakeya4_maximal_disjoint_cover

/-!
# Quantitative bush cover of the original collision graph

The pieces are disjoint subsets of the original slope source. Edge mass is
counted only by restricting the whole original ordered graph to endpoint
membership. In particular, choosing a physical bush center never freezes or
replaces the original target variable.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace StickyKakeya4

/-- Restricting both original endpoints preserves product domination with
coefficient one. No reorientation or forgotten endpoint tag occurs. -/
theorem original_graph_restrict_source_square_le
    (σ : Measure E3) [IsFiniteMeasure σ] (Γ : Measure (E3 × E3))
    (hΓ : Γ ≤ σ.prod σ) (T : Set E3) :
    Γ.restrict (T ×ˢ T) ≤ (σ.restrict T).prod (σ.restrict T) := by
  rw [Measure.prod_restrict]
  exact Measure.restrict_mono_measure hΓ _

/-- Any measurable source remainder carrying more than half of the original
ordered graph contains a new physical bush piece of definite original source
mass. Its closest-time/residual support is inherited from the original graph. -/
theorem exists_physical_bush_piece_in_remainder
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ univ ≤ 1)
    (Γ : Measure (E3 × E3)) (hΓ : Γ ≤ σ.prod σ) (hM : 0 < Γ univ)
    (b : E3 → E3) (hb : Measurable b) (u v r : ℝ)
    (huv : u ≤ v) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsupport : ∀ᵐ e ∂Γ, ‖e.1 - e.2‖ ≤ 2 ∧
      ‖collisionResidual (e.1 - e.2) (b e.1 - b e.2)‖ ≤ r ∧
      collisionTime (e.1 - e.2) (b e.1 - b e.2) ∈ Icc u v)
    (T : Set E3) (hT : MeasurableSet T) (hleft : Γ univ / 2 < Γ (T ×ˢ T)) :
    ∃ B : Set E3, MeasurableSet B ∧ B ⊆ T ∧
      ENNReal.ofReal (r * (Γ univ).toReal / (4 * (v - u + 2))) ≤ σ B ∧
      ∃ t ∈ Icc (u - 1) (v + 1), ∃ p : E3, B ⊆ physicalAffineBush b t p (2 * r) := by
  letI : IsFiniteMeasure Γ := isFiniteMeasure_of_le (σ.prod σ) hΓ
  have hMtop : Γ univ ≠ ∞ := measure_ne_top _ _
  have hMreal : 0 < (Γ univ).toReal := ENNReal.toReal_pos hM.ne' hMtop
  have hL : 0 < v - u + 2 := by linarith
  have hσT : (σ.restrict T) univ ≤ 1 := by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (subset_univ T)).trans hσ
  have hΓT := original_graph_restrict_source_square_le σ Γ hΓ T
  have hsupportT : ∀ᵐ e ∂Γ.restrict (T ×ˢ T), ‖e.1 - e.2‖ ≤ 2 ∧
      ‖collisionResidual (e.1 - e.2) (b e.1 - b e.2)‖ ≤ r ∧
      collisionTime (e.1 - e.2) (b e.1 - b e.2) ∈ Icc u v :=
    hsupport.filter_mono (ae_mono Measure.restrict_le_self)
  have hleftreal : (Γ univ).toReal / 2 < (Γ (T ×ˢ T)).toReal := by
    have hh := (ENNReal.toReal_lt_toReal (by finiteness)
      (measure_ne_top Γ (T ×ˢ T))).2 hleft
    simpa using hh
  have hleftpos : 0 < (Γ (T ×ˢ T)).toReal := by linarith
  have hq : 0 ≤ r * (Γ univ).toReal / (4 * (v - u + 2)) := by positivity
  have hbudget : ENNReal.ofReal (r * (Γ univ).toReal / (4 * (v - u + 2))) *
        ENNReal.ofReal (v - u + 2) <
      ENNReal.ofReal r * (Γ.restrict (T ×ˢ T)) univ := by
    rw [Measure.restrict_apply_univ, ← ENNReal.ofReal_mul hq]
    have heq : ENNReal.ofReal r * Γ (T ×ˢ T) =
        ENNReal.ofReal (r * (Γ (T ×ˢ T)).toReal) := by
      rw [ENNReal.ofReal_mul hr.le, ENNReal.ofReal_toReal (measure_ne_top Γ _)]
    rw [heq]
    apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.2
    have heq' : r * (Γ univ).toReal / (4 * (v - u + 2)) * (v - u + 2) =
        r * (Γ univ).toReal / 4 := by field_simp [hL.ne']
    rw [heq']
    nlinarith [mul_pos hr hMreal, mul_lt_mul_of_pos_left hleftreal hr]
  obtain ⟨t, ht, p, hp⟩ := exists_physicalAffineBush_mass_gt_of_budget
    (σ.restrict T) hσT (Γ.restrict (T ×ˢ T)) hΓT b hb u v r hr.le hr1 hsupportT _ hbudget
  refine ⟨physicalAffineBush b t p (2 * r) ∩ T,
    (measurableSet_physicalAffineBush b hb _ _ _).inter hT,
    inter_subset_right, ?_, t, ht, p, inter_subset_left⟩
  rw [Measure.restrict_apply (measurableSet_physicalAffineBush b hb _ _ _)] at hp
  exact hp.le

/-- Endpoint membership captures at least half of the original ordered edge
mass whenever the induced graph on the source complement has mass at most
half. The original second endpoint remains part of every captured edge. -/
theorem original_edge_mass_captured_by_sources
    (Γ : Measure (E3 × E3)) [IsFiniteMeasure Γ]
    (U : Set E3) (hU : MeasurableSet U)
    (hrem : Γ (Uᶜ ×ˢ Uᶜ) ≤ Γ univ / 2) :
    Γ univ / 2 ≤ Γ {e | e.1 ∈ U ∨ e.2 ∈ U} := by
  have hset : {e : E3 × E3 | e.1 ∈ U ∨ e.2 ∈ U} = (Uᶜ ×ˢ Uᶜ)ᶜ := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_prod, Set.mem_univ, and_true]
    tauto
  rw [hset, measure_compl (hU.compl.prod hU.compl) (measure_ne_top _ _)]
  calc
    Γ univ / 2 = Γ univ - Γ univ / 2 := (ENNReal.sub_half (measure_ne_top _ _)).symm
    _ ≤ Γ univ - Γ (Uᶜ ×ˢ Uᶜ) := tsub_le_tsub_left hrem _

/-- Capturing an endpoint event preserves the original coefficient-one
product domination and every original almost-everywhere support condition. -/
theorem original_graph_restriction_preserves_domination_and_support
    (σ : Measure E3) (Γ : Measure (E3 × E3)) (hΓ : Γ ≤ σ.prod σ)
    (E : Set (E3 × E3)) (P : E3 × E3 → Prop) (hP : ∀ᵐ e ∂Γ, P e) :
    Γ.restrict E ≤ σ.prod σ ∧ ∀ᵐ e ∂Γ.restrict E, P e := by
  exact ⟨Measure.restrict_le_self.trans hΓ,
    hP.filter_mono (ae_mono Measure.restrict_le_self)⟩

/-- A real quantitative root-source cover. The pieces are disjoint, each
lies in a genuine `2r` physical bush and has source mass at least `r M/(4L)`.
There are at most `4L/(r M)` pieces and their endpoint union captures at least
half the ORIGINAL ordered edge mass, where `L = v-u+2` and `M = Γ univ`.
This local cover does not assert a global cross-cap or paid stopping bound. -/
theorem exists_quantitative_physical_bush_cover
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ univ ≤ 1)
    (Γ : Measure (E3 × E3)) (hΓ : Γ ≤ σ.prod σ) (hM : 0 < Γ univ)
    (b : E3 → E3) (hb : Measurable b) (u v r : ℝ)
    (huv : u ≤ v) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsupport : ∀ᵐ e ∂Γ, ‖e.1 - e.2‖ ≤ 2 ∧
      ‖collisionResidual (e.1 - e.2) (b e.1 - b e.2)‖ ≤ r ∧
      collisionTime (e.1 - e.2) (b e.1 - b e.2) ∈ Icc u v) :
    ∃ F : Finset (Set E3),
      (F : Set (Set E3)).PairwiseDisjoint id ∧
      (∀ B ∈ F, MeasurableSet B ∧
        ENNReal.ofReal (r * (Γ univ).toReal / (4 * (v - u + 2))) ≤ σ B ∧
        ∃ t ∈ Icc (u - 1) (v + 1), ∃ p : E3,
          B ⊆ physicalAffineBush b t p (2 * r)) ∧
      (F.card : ℝ) ≤ 4 * (v - u + 2) / (r * (Γ univ).toReal) ∧
      Γ ((⋃ B ∈ F, B)ᶜ ×ˢ (⋃ B ∈ F, B)ᶜ) ≤ Γ univ / 2 ∧
      Γ univ / 2 ≤ Γ {e | e.1 ∈ ⋃ B ∈ F, B ∨ e.2 ∈ ⋃ B ∈ F, B} := by
  classical
  letI : IsFiniteMeasure Γ := isFiniteMeasure_of_le (σ.prod σ) hΓ
  have hMreal : 0 < (Γ univ).toReal :=
    ENNReal.toReal_pos hM.ne' (measure_ne_top _ _)
  have hL : 0 < v - u + 2 := by linarith
  let a : ℝ := r * (Γ univ).toReal / (4 * (v - u + 2))
  have ha : 0 < a := by dsimp [a]; positivity
  let P : Set E3 → Prop := fun B =>
    ∃ t ∈ Icc (u - 1) (v + 1), ∃ p : E3, B ⊆ physicalAffineBush b t p (2 * r)
  obtain ⟨F, hF, hcard, hrem⟩ := MaximalDisjointCover.exists_stopped_family
    σ P a ha hσ (fun T => Γ (T ×ˢ T)) (Γ univ / 2) (by
      intro T hT hleft
      obtain ⟨B, hBm, hBT, hBmass, hBP⟩ := exists_physical_bush_piece_in_remainder
        σ hσ Γ hΓ hM b hb u v r huv hr hr1 hsupport T hT hleft
      exact ⟨B, hBm, hBT, hBP, hBmass⟩)
  refine ⟨F, hF.1, ?_, ?_, hrem, ?_⟩
  · intro B hB
    exact ⟨(hF.2 B hB).1, (hF.2 B hB).2.2, (hF.2 B hB).2.1⟩
  · apply (le_div_iff₀ (mul_pos hr hMreal)).2
    dsimp [a] at hcard
    rw [← mul_div_assoc] at hcard
    have hh := (div_le_iff₀ (show 0 < 4 * (v - u + 2) by positivity)).1 hcard
    simpa only [one_mul] using hh
  · apply original_edge_mass_captured_by_sources Γ _ _ hrem
    exact MeasurableSet.biUnion F.countable_toSet (fun B hB => (hF.2 B hB).1)

/-- Restricting only original sources leaves every old target available. -/
theorem original_graph_restrict_source_le
    (σ : Measure E3) [IsFiniteMeasure σ] (Γ : Measure (E3 × E3))
    (hΓ : Γ ≤ σ.prod σ) (T : Set E3) :
    Γ.restrict (T ×ˢ (univ : Set E3)) ≤ (σ.restrict T).prod σ := by
  rw [Measure.restrict_prod_eq_prod_univ]
  exact Measure.restrict_mono_measure hΓ _

/-- Any measurable source remainder carrying more than half of the original
ordered graph contains a new physical bush piece of definite original source
mass. Its closest-time/residual support is inherited from the original graph. -/
theorem exists_physical_bush_piece_in_source_remainder
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ univ ≤ 1)
    (Γ : Measure (E3 × E3)) (hΓ : Γ ≤ σ.prod σ) (hM : 0 < Γ univ)
    (b : E3 → E3) (hb : Measurable b) (u v r : ℝ)
    (huv : u ≤ v) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsupport : ∀ᵐ e ∂Γ, ‖e.1 - e.2‖ ≤ 2 ∧
      ‖collisionResidual (e.1 - e.2) (b e.1 - b e.2)‖ ≤ r ∧
      collisionTime (e.1 - e.2) (b e.1 - b e.2) ∈ Icc u v)
    (T : Set E3) (hT : MeasurableSet T) (hleft : Γ univ / 2 < Γ (T ×ˢ (univ : Set E3))) :
    ∃ B : Set E3, MeasurableSet B ∧ B ⊆ T ∧
      ENNReal.ofReal (r * (Γ univ).toReal / (4 * (v - u + 2))) ≤ σ B ∧
      ∃ t ∈ Icc (u - 1) (v + 1), ∃ p : E3, B ⊆ physicalAffineBush b t p (2 * r) := by
  letI : IsFiniteMeasure Γ := isFiniteMeasure_of_le (σ.prod σ) hΓ
  have hMtop : Γ univ ≠ ∞ := measure_ne_top _ _
  have hMreal : 0 < (Γ univ).toReal := ENNReal.toReal_pos hM.ne' hMtop
  have hL : 0 < v - u + 2 := by linarith
  have hΓT := original_graph_restrict_source_le σ Γ hΓ T
  have hsupportT : ∀ᵐ e ∂Γ.restrict (T ×ˢ (univ : Set E3)), ‖e.1 - e.2‖ ≤ 2 ∧
      ‖collisionResidual (e.1 - e.2) (b e.1 - b e.2)‖ ≤ r ∧
      collisionTime (e.1 - e.2) (b e.1 - b e.2) ∈ Icc u v :=
    hsupport.filter_mono (ae_mono Measure.restrict_le_self)
  have hleftreal : (Γ univ).toReal / 2 < (Γ (T ×ˢ (univ : Set E3))).toReal := by
    have hh := (ENNReal.toReal_lt_toReal (by finiteness)
      (measure_ne_top Γ (T ×ˢ (univ : Set E3)))).2 hleft
    simpa using hh
  have hleftpos : 0 < (Γ (T ×ˢ (univ : Set E3))).toReal := by linarith
  have hq : 0 ≤ r * (Γ univ).toReal / (4 * (v - u + 2)) := by positivity
  have hbudget : ENNReal.ofReal (r * (Γ univ).toReal / (4 * (v - u + 2))) *
        ENNReal.ofReal (v - u + 2) <
      ENNReal.ofReal r * (Γ.restrict (T ×ˢ (univ : Set E3))) univ := by
    rw [Measure.restrict_apply_univ, ← ENNReal.ofReal_mul hq]
    have heq : ENNReal.ofReal r * Γ (T ×ˢ (univ : Set E3)) =
        ENNReal.ofReal (r * (Γ (T ×ˢ (univ : Set E3))).toReal) := by
      rw [ENNReal.ofReal_mul hr.le, ENNReal.ofReal_toReal (measure_ne_top Γ _)]
    rw [heq]
    apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.2
    have heq' : r * (Γ univ).toReal / (4 * (v - u + 2)) * (v - u + 2) =
        r * (Γ univ).toReal / 4 := by field_simp [hL.ne']
    rw [heq']
    nlinarith [mul_pos hr hMreal, mul_lt_mul_of_pos_left hleftreal hr]
  obtain ⟨t, ht, p, hp⟩ := exists_source_bush_mass_gt_of_budget
    (σ.restrict T) σ hσ (Γ.restrict (T ×ˢ (univ : Set E3))) hΓT b hb u v r hr.le hr1 hsupportT _ hbudget
  refine ⟨physicalAffineBush b t p (2 * r) ∩ T,
    (measurableSet_physicalAffineBush b hb _ _ _).inter hT,
    inter_subset_right, ?_, t, ht, p, inter_subset_left⟩
  rw [Measure.restrict_apply (measurableSet_physicalAffineBush b hb _ _ _)] at hp
  exact hp.le

/-- A source-only cover captures half of the original ordered graph without
removing, freezing, swapping, or retagging any target. -/
theorem original_source_edge_mass_captured
    (Γ : Measure (E3 × E3)) [IsFiniteMeasure Γ]
    (U : Set E3) (hU : MeasurableSet U)
    (hrem : Γ (Uᶜ ×ˢ (univ : Set E3)) ≤ Γ univ / 2) :
    Γ univ / 2 ≤ Γ (U ×ˢ (univ : Set E3)) := by
  have hset : U ×ˢ (univ : Set E3) = (Uᶜ ×ˢ (univ : Set E3))ᶜ := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_prod, Set.mem_univ, and_true]
    tauto
  rw [hset, measure_compl (hU.compl.prod MeasurableSet.univ) (measure_ne_top _ _)]
  calc
    Γ univ / 2 = Γ univ - Γ univ / 2 := (ENNReal.sub_half (measure_ne_top _ _)).symm
    _ ≤ Γ univ - Γ (Uᶜ ×ˢ (univ : Set E3)) := tsub_le_tsub_left hrem _

/-- A real quantitative root-source cover. The pieces are disjoint, each
lies in a genuine `2r` physical bush and has source mass at least `r M/(4L)`.
There are at most `4L/(r M)` pieces and their SOURCE union captures at least
half the ORIGINAL ordered edge mass, where `L = v-u+2` and `M = Γ univ`.
All old targets remain available. This local cover does not assert a global cross-cap or paid stopping bound. -/
theorem exists_quantitative_source_bush_cover
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ univ ≤ 1)
    (Γ : Measure (E3 × E3)) (hΓ : Γ ≤ σ.prod σ) (hM : 0 < Γ univ)
    (b : E3 → E3) (hb : Measurable b) (u v r : ℝ)
    (huv : u ≤ v) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsupport : ∀ᵐ e ∂Γ, ‖e.1 - e.2‖ ≤ 2 ∧
      ‖collisionResidual (e.1 - e.2) (b e.1 - b e.2)‖ ≤ r ∧
      collisionTime (e.1 - e.2) (b e.1 - b e.2) ∈ Icc u v) :
    ∃ F : Finset (Set E3),
      (F : Set (Set E3)).PairwiseDisjoint id ∧
      (∀ B ∈ F, MeasurableSet B ∧
        ENNReal.ofReal (r * (Γ univ).toReal / (4 * (v - u + 2))) ≤ σ B ∧
        ∃ t ∈ Icc (u - 1) (v + 1), ∃ p : E3,
          B ⊆ physicalAffineBush b t p (2 * r)) ∧
      (F.card : ℝ) ≤ 4 * (v - u + 2) / (r * (Γ univ).toReal) ∧
      Γ ((⋃ B ∈ F, B)ᶜ ×ˢ (univ : Set E3)) ≤ Γ univ / 2 ∧
      Γ univ / 2 ≤ Γ ((⋃ B ∈ F, B) ×ˢ (univ : Set E3)) := by
  classical
  letI : IsFiniteMeasure Γ := isFiniteMeasure_of_le (σ.prod σ) hΓ
  have hMreal : 0 < (Γ univ).toReal :=
    ENNReal.toReal_pos hM.ne' (measure_ne_top _ _)
  have hL : 0 < v - u + 2 := by linarith
  let a : ℝ := r * (Γ univ).toReal / (4 * (v - u + 2))
  have ha : 0 < a := by dsimp [a]; positivity
  let P : Set E3 → Prop := fun B =>
    ∃ t ∈ Icc (u - 1) (v + 1), ∃ p : E3, B ⊆ physicalAffineBush b t p (2 * r)
  obtain ⟨F, hF, hcard, hrem⟩ := MaximalDisjointCover.exists_stopped_family
    σ P a ha hσ (fun T => Γ (T ×ˢ (univ : Set E3))) (Γ univ / 2) (by
      intro T hT hleft
      obtain ⟨B, hBm, hBT, hBmass, hBP⟩ := exists_physical_bush_piece_in_source_remainder
        σ hσ Γ hΓ hM b hb u v r huv hr hr1 hsupport T hT hleft
      exact ⟨B, hBm, hBT, hBP, hBmass⟩)
  refine ⟨F, hF.1, ?_, ?_, hrem, ?_⟩
  · intro B hB
    exact ⟨(hF.2 B hB).1, (hF.2 B hB).2.2, (hF.2 B hB).2.1⟩
  · apply (le_div_iff₀ (mul_pos hr hMreal)).2
    dsimp [a] at hcard
    rw [← mul_div_assoc] at hcard
    have hh := (div_le_iff₀ (show 0 < 4 * (v - u + 2) by positivity)).1 hcard
    simpa only [one_mul] using hh
  · apply original_source_edge_mass_captured Γ _ _ hrem
    exact MeasurableSet.biUnion F.countable_toSet (fun B hB => (hF.2 B hB).1)


end StickyKakeya4
