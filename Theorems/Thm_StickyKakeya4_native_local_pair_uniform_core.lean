import Theorems.Thm_StickyKakeya4_native_local_pair_fibers
import Theorems.Thm_StickyKakeya4_native_source_size_bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

noncomputable section
namespace NativeLocalPairUniformCore
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentSelection
open NativeLocalPairFibers SelfUniform

def retentionCost (d g L : ℕ) : ℕ := 2 * (4 * (d + g)) ^ ((d + g) * L)

/-- Append the actual local-pair labels to the old finite relation menu once.
All original relation comparisons and all native pair-fiber lower bounds
hold on the SAME retained original edge set. There is no later heavy cut. -/
theorem exists_retained_scheduled_pair_core {n : ℕ} {D : FiniteScaleSource n}
    {eta a F0 : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hsmall : D.thickness ≤ 1 / 8)
    (A : Finset (Fin n × Index)) (hA : A ⊆ incidences original) (hAne : A.Nonempty)
    (hF0 : 0 < F0) (hsource : ((incidences original).card : ℝ) ≤ F0 * A.card)
    (d g L : ℕ) (hdg : 0 < d + g) (hL : 0 < L)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hrefl : ∀ j x, Rel j x x)
    (hsym : ∀ j x y, Rel j x y → Rel j y x)
    (scales : Fin g → ℕ) (hN : ∀ j, 0 < scales j)
    (hscale : ∀ j, (scales j : ℝ) * D.thickness / 64 ≤ 1) :
    let Q := NativeSourceSizeBounds.radix A.card L
    ∃ E ⊆ A, E.Nonempty ∧
      A.card ≤ retentionCost d g L * E.card ∧
      (∀ j x y, x ∈ E → y ∈ E →
        degree (fun _ : Fin n × Index => 1) (Rel j) E x ≤
          Q ^ 2 * degree (fun _ : Fin n × Index => 1) (Rel j) E y) ∧
      ∀ j e, e ∈ E →
        D.thickness ^ eta * scales j /
          (16384 * (F0 * (retentionCost d g L : ℝ)) * (Q : ℝ) ^ 2) ≤
            (pairFiber D a (scales j) E (localPair D a (scales j) e)).card := by
  let Q := NativeSourceSizeBounds.radix A.card L
  have hQ4 : 4 ≤ Q := NativeSourceSizeBounds.radix_four_le _ _
  have hQpos : 0 < Q := by omega
  have hheight : mass (fun _ : Fin n × Index => 1) A ≤ Q ^ L := by
    simpa only [mass, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using
      NativeSourceSizeBounds.card_le_radix_pow A.card hL
  obtain ⟨E, hEA, hEne, hret, hUniform, hRich⟩ :=
    weighted_self_uniform_grain_refinement
      (β := fun _ : Fin g => Fin n × Index) hdg hQ4
      (fun _ : Fin n × Index => 1) Rel hrefl hsym
      (fun j => localPair D a (scales j)) A hAne (fun _ _ => by norm_num) hheight
  have hretCard : A.card ≤ retentionCost d g L * E.card := by
    simpa only [mass, sum_const, smul_eq_mul, mul_one, retentionCost] using hret
  have hcost : (0 : ℝ) < retentionCost d g L := by
    unfold retentionCost
    positivity
  have hretOriginal : ((incidences original).card : ℝ) ≤
      (F0 * (retentionCost d g L : ℝ)) * E.card := by
    have hh : (A.card : ℝ) ≤ (retentionCost d g L : ℝ) * E.card := by
      exact_mod_cast hretCard
    exact (hsource.trans (mul_le_mul_of_nonneg_left hh hF0.le)).trans_eq (by ring)
  refine ⟨E, hEA, hEne, hretCard, hUniform, ?_⟩
  intro j e he
  exact pair_fiber_lower_of_self_uniform_richness h original horiginal ha hsmall
    (scales j) (hN j) (hscale j) A hA E (mul_pos hF0 hcost)
    Q hQpos hretOriginal e (hRich j e he)

/-- A completely original-source specialization. Native density constructs
nonempty incidence mass; the actual cardinality constructs the radix. -/
theorem exists_original_scheduled_pair_core {n : ℕ} {D : FiniteScaleSource n}
    {eta a : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hsmall : D.thickness ≤ 1 / 8)
    (d g L : ℕ) (hdg : 0 < d + g) (hL : 0 < L)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hrefl : ∀ j x, Rel j x x)
    (hsym : ∀ j x y, Rel j x y → Rel j y x)
    (scales : Fin g → ℕ) (hN : ∀ j, 0 < scales j)
    (hscale : ∀ j, (scales j : ℝ) * D.thickness / 64 ≤ 1) :
    let I := incidences original
    let Q := NativeSourceSizeBounds.radix I.card L
    ∃ E ⊆ I, E.Nonempty ∧
      I.card ≤ retentionCost d g L * E.card ∧
      (∀ j x y, x ∈ E → y ∈ E →
        degree (fun _ : Fin n × Index => 1) (Rel j) E x ≤
          Q ^ 2 * degree (fun _ : Fin n × Index => 1) (Rel j) E y) ∧
      ∀ j e, e ∈ E →
        D.thickness ^ eta * scales j /
          (16384 * (retentionCost d g L : ℝ) * (Q : ℝ) ^ 2) ≤
            (pairFiber D a (scales j) E (localPair D a (scales j) e)).card := by
  have hn : (0 : ℝ) < n := by exact_mod_cast h.1.1
  have hd := h.1.2.1
  have hm := original_incidence_lower_weak h original horiginal hsmall
  have hI : (incidences original).Nonempty := by
    apply card_pos.mp
    by_contra hz
    have hc : (incidences original).card = 0 := by omega
    rw [hc, Nat.cast_zero, mul_zero] at hm
    exact (not_le_of_gt (mul_pos (Real.rpow_pos_of_pos hd eta) hn)) hm
  have result := exists_retained_scheduled_pair_core h original horiginal ha hsmall
    (incidences original) (subset_refl _) hI (F0 := 1) (by norm_num) (by simp)
    d g L hdg hL Rel hrefl hsym scales hN hscale
  simpa only [one_mul] using result

end NativeLocalPairUniformCore
