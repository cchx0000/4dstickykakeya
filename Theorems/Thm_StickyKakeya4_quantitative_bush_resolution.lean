import Theorems.Thm_StickyKakeya4_quantitative_bush_cover

/-!
# Arbitrarily small original-root tails resolved by physical bushes

The actual time-averaged collision lower bound and finite maximality give a
finite source-only resolution for every positive requested relative tail.
All targets are retained. The kept and tail measures are restrictions of the
original ordered root graph, and sum exactly to that graph. No stopping or
geometric certificate is assumed; the global cross-cap/paid bound is not claimed.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace StickyKakeya4

/-- Any measurable source remainder carrying more than a requested fraction of the original
ordered graph contains a new physical bush piece of definite original source
mass. Its closest-time/residual support is inherited from the original graph. -/
theorem exists_physical_bush_piece_above_relative_tail
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ univ ≤ 1)
    (Γ : Measure (E3 × E3)) (hΓ : Γ ≤ σ.prod σ) (hM : 0 < Γ univ)
    (b : E3 → E3) (hb : Measurable b) (u v r : ℝ)
    (huv : u ≤ v) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsupport : ∀ᵐ e ∂Γ, ‖e.1 - e.2‖ ≤ 2 ∧
      ‖collisionResidual (e.1 - e.2) (b e.1 - b e.2)‖ ≤ r ∧
      collisionTime (e.1 - e.2) (b e.1 - b e.2) ∈ Icc u v)
    (θ : ℝ) (hθ : 0 < θ)
    (T : Set E3) (hT : MeasurableSet T) (hleft : ENNReal.ofReal θ * Γ univ < Γ (T ×ˢ (univ : Set E3))) :
    ∃ B : Set E3, MeasurableSet B ∧ B ⊆ T ∧
      ENNReal.ofReal (r * θ * (Γ univ).toReal / (2 * (v - u + 2))) ≤ σ B ∧
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
  have hleftreal : θ * (Γ univ).toReal < (Γ (T ×ˢ (univ : Set E3))).toReal := by
    have hh := (ENNReal.toReal_lt_toReal (by finiteness)
      (measure_ne_top Γ (T ×ˢ (univ : Set E3)))).2 hleft
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ.le] using hh
  have hleftpos : 0 < (Γ (T ×ˢ (univ : Set E3))).toReal := (mul_pos hθ hMreal).trans hleftreal
  have hq : 0 ≤ r * θ * (Γ univ).toReal / (2 * (v - u + 2)) := by positivity
  have hbudget : ENNReal.ofReal (r * θ * (Γ univ).toReal / (2 * (v - u + 2))) *
        ENNReal.ofReal (v - u + 2) <
      ENNReal.ofReal r * (Γ.restrict (T ×ˢ (univ : Set E3))) univ := by
    rw [Measure.restrict_apply_univ, ← ENNReal.ofReal_mul hq]
    have heq : ENNReal.ofReal r * Γ (T ×ˢ (univ : Set E3)) =
        ENNReal.ofReal (r * (Γ (T ×ˢ (univ : Set E3))).toReal) := by
      rw [ENNReal.ofReal_mul hr.le, ENNReal.ofReal_toReal (measure_ne_top Γ _)]
    rw [heq]
    apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.2
    have heq' : r * θ * (Γ univ).toReal / (2 * (v - u + 2)) * (v - u + 2) =
        r * θ * (Γ univ).toReal / 2 := by field_simp [hL.ne']
    rw [heq']
    nlinarith [mul_pos (mul_pos hr hθ) hMreal, mul_lt_mul_of_pos_left hleftreal hr]
  obtain ⟨t, ht, p, hp⟩ := exists_source_bush_mass_gt_of_budget
    (σ.restrict T) σ hσ (Γ.restrict (T ×ˢ (univ : Set E3))) hΓT b hb u v r hr.le hr1 hsupportT _ hbudget
  refine ⟨physicalAffineBush b t p (2 * r) ∩ T,
    (measurableSet_physicalAffineBush b hb _ _ _).inter hT,
    inter_subset_right, ?_, t, ht, p, inter_subset_left⟩
  rw [Measure.restrict_apply (measurableSet_physicalAffineBush b hb _ _ _)] at hp
  exact hp.le

/-- The retained original source mass is complementary to the requested
relative root tail. This is an ordered source restriction, with all targets. -/
theorem original_source_mass_ge_of_relative_tail
    (Γ : Measure (E3 × E3)) [IsFiniteMeasure Γ]
    (U : Set E3) (hU : MeasurableSet U) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hrem : Γ (Uᶜ ×ˢ (univ : Set E3)) ≤ ENNReal.ofReal θ * Γ univ) :
    ENNReal.ofReal (1 - θ) * Γ univ ≤ Γ (U ×ˢ (univ : Set E3)) := by
  have hset : U ×ˢ (univ : Set E3) = (Uᶜ ×ˢ (univ : Set E3))ᶜ := by
    ext e
    simp
  have hparts : ENNReal.ofReal (1 - θ) + ENNReal.ofReal θ = 1 := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hθ1) hθ]
    simp
  have hsum : ENNReal.ofReal (1 - θ) * Γ univ + ENNReal.ofReal θ * Γ univ =
      Γ univ := by rw [← add_mul, hparts, one_mul]
  apply ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal θ * Γ univ) (by finiteness)
  rw [hsum]
  have hmeas : Γ (U ×ˢ (univ : Set E3)) + Γ (Uᶜ ×ˢ (univ : Set E3)) = Γ univ := by
    rw [hset]
    simpa only [add_comm] using
      (measure_add_measure_compl (μ := Γ) (hU.compl.prod MeasurableSet.univ))
  calc
    Γ univ = Γ (U ×ˢ (univ : Set E3)) + Γ (Uᶜ ×ˢ (univ : Set E3)) := hmeas.symm
    _ ≤ Γ (U ×ˢ (univ : Set E3)) + ENNReal.ofReal θ * Γ univ :=
      add_le_add le_rfl hrem

/-- Exact conservation of the original ordered graph under source-only
resolution. The target factor is the whole original space on both branches. -/
theorem original_source_resolution_decomposition
    (Γ : Measure (E3 × E3)) (U : Set E3) (hU : MeasurableSet U) :
    Γ.restrict (U ×ˢ (univ : Set E3)) +
      Γ.restrict (Uᶜ ×ˢ (univ : Set E3)) = Γ := by
  have hset : Uᶜ ×ˢ (univ : Set E3) = (U ×ˢ (univ : Set E3))ᶜ := by
    ext e
    simp
  rw [hset]
  exact Measure.restrict_add_restrict_compl (hU.prod MeasurableSet.univ)

/-- Quantitative physical source resolution at any requested relative tail
`θ ∈ (0,1)`. Set `L = v-u+2` and `M = Γ univ`. Each piece has original source
mass at least `r θ M/(2L)`, there are at most `2L/(r θ M)` pieces, and the
explicit original-root tail has mass at most `θ M`. Both branches retain every
original target; no center-frozen or reoriented graph is introduced. -/
theorem exists_quantitative_source_bush_resolution
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ univ ≤ 1)
    (Γ : Measure (E3 × E3)) (hΓ : Γ ≤ σ.prod σ) (hM : 0 < Γ univ)
    (b : E3 → E3) (hb : Measurable b) (u v r : ℝ)
    (huv : u ≤ v) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsupport : ∀ᵐ e ∂Γ, ‖e.1 - e.2‖ ≤ 2 ∧
      ‖collisionResidual (e.1 - e.2) (b e.1 - b e.2)‖ ≤ r ∧
      collisionTime (e.1 - e.2) (b e.1 - b e.2) ∈ Icc u v)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ F : Finset (Set E3),
      (F : Set (Set E3)).PairwiseDisjoint id ∧
      (∀ B ∈ F, MeasurableSet B ∧
        ENNReal.ofReal (r * θ * (Γ univ).toReal / (2 * (v - u + 2))) ≤ σ B ∧
        ∃ t ∈ Icc (u - 1) (v + 1), ∃ p : E3,
          B ⊆ physicalAffineBush b t p (2 * r)) ∧
      (F.card : ℝ) ≤ 2 * (v - u + 2) / (r * θ * (Γ univ).toReal) ∧
      let U := ⋃ B ∈ F, B
      Γ.restrict (U ×ˢ (univ : Set E3)) + Γ.restrict (Uᶜ ×ˢ (univ : Set E3)) = Γ ∧
      Γ.restrict (U ×ˢ (univ : Set E3)) ≤ Γ ∧
      Γ.restrict (Uᶜ ×ˢ (univ : Set E3)) ≤ Γ ∧
      (Γ.restrict (Uᶜ ×ˢ (univ : Set E3))) univ ≤ ENNReal.ofReal θ * Γ univ ∧
      ENNReal.ofReal (1 - θ) * Γ univ ≤ (Γ.restrict (U ×ˢ (univ : Set E3))) univ := by
  classical
  letI : IsFiniteMeasure Γ := isFiniteMeasure_of_le (σ.prod σ) hΓ
  have hMreal : 0 < (Γ univ).toReal :=
    ENNReal.toReal_pos hM.ne' (measure_ne_top _ _)
  have hL : 0 < v - u + 2 := by linarith
  let a : ℝ := r * θ * (Γ univ).toReal / (2 * (v - u + 2))
  have ha : 0 < a := by dsimp [a]; positivity
  let P : Set E3 → Prop := fun B =>
    ∃ t ∈ Icc (u - 1) (v + 1), ∃ p : E3, B ⊆ physicalAffineBush b t p (2 * r)
  obtain ⟨F, hF, hcard, hrem⟩ := MaximalDisjointCover.exists_stopped_family
    σ P a ha hσ (fun T => Γ (T ×ˢ (univ : Set E3))) (ENNReal.ofReal θ * Γ univ) (by
      intro T hT hleft
      obtain ⟨B, hBm, hBT, hBmass, hBP⟩ := exists_physical_bush_piece_above_relative_tail
        σ hσ Γ hΓ hM b hb u v r huv hr hr1 hsupport θ hθ T hT hleft
      exact ⟨B, hBm, hBT, hBP, hBmass⟩)
  have hU : MeasurableSet (⋃ B ∈ F, B) :=
    MeasurableSet.biUnion F.countable_toSet (fun B hB => (hF.2 B hB).1)
  refine ⟨F, hF.1, ?_, ?_, ?_⟩
  · intro B hB
    exact ⟨(hF.2 B hB).1, (hF.2 B hB).2.2, (hF.2 B hB).2.1⟩
  · apply (le_div_iff₀ (mul_pos (mul_pos hr hθ) hMreal)).2
    dsimp [a] at hcard
    rw [← mul_div_assoc] at hcard
    have hh := (div_le_iff₀ (show 0 < 2 * (v - u + 2) by positivity)).1 hcard
    simpa only [one_mul] using hh
  · refine ⟨original_source_resolution_decomposition Γ _ hU,
      Measure.restrict_le_self, Measure.restrict_le_self, ?_, ?_⟩
    · simpa only [Measure.restrict_apply_univ] using hrem
    · simpa only [Measure.restrict_apply_univ] using
        original_source_mass_ge_of_relative_tail Γ _ hU θ hθ.le hθ1.le hrem

end StickyKakeya4
