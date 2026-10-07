import Theorems.Thm_StickyKakeya4_native_local_parent_multiplicity
import Theorems.Thm_StickyKakeya4_native_local_pair_uniform_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

noncomputable section
namespace NativeScheduledLocalMultiplicity
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentSelection
open NativeLocalPairUniformCore NativeLocalParentMultiplicity SelfUniform

/-- One finite uniform core of the current original relation supports every
scheduled local-parent multiplicity transfer. The original relation menu
is retained on that same E, and the native fiber lower bound is derived
internally by the actual scheduled uniform-core constructor. -/
theorem exists_retained_scheduled_multiplicity {n : ℕ} {D : FiniteScaleSource n}
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
      ∀ j p, (parentEdges D a (scales j) p E).Nonempty →
        let Ep := parentEdges D a (scales j) p E
        (Ep.card : ℝ) / (Ep.image Prod.snd).card ≤
          (125 * 175616 * 16384 : ℝ) * (F0 * (retentionCost d g L : ℝ)) *
            (Q : ℝ) ^ 2 * D.thickness ^ (-eta) *
              ((Ep.image (NativeLocalCellCoherence.localPair D a (scales j) p)).card : ℝ) /
                (Ep.image (NativeLocalCellCoherence.localCellLabel D a (scales j) p)).card := by
  let Q := NativeSourceSizeBounds.radix A.card L
  have hQ4 : 4 ≤ Q := NativeSourceSizeBounds.radix_four_le _ _
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hcost : (0 : ℝ) < retentionCost d g L := by
    unfold retentionCost
    positivity
  obtain ⟨E, hEA, hEne, hret, hUniform, hLower⟩ :=
    exists_retained_scheduled_pair_core h original horiginal ha hsmall
      A hA hAne hF0 hsource d g L hdg hL Rel hrefl hsym scales hN hscale
  refine ⟨E, hEA, hEne, hret, hUniform, ?_⟩
  intro j p hp
  exact native_parent_multiplicity_transfer h original horiginal ha
    (scales j) (hN j) p E (hEA.trans hA) (mul_pos hF0 hcost) hQpos (hLower j) hp

/-- Original native input alone supplies the starting incidence mass. One
retained original E preserves every prescribed old relation and transfers
multiplicity in every nonempty original parent at every scheduled scale.
There is no residual, output-capacity, or pair-fiber premise in this endpoint. -/
theorem exists_original_scheduled_multiplicity {n : ℕ} {D : FiniteScaleSource n}
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
      ∀ j p, (parentEdges D a (scales j) p E).Nonempty →
        let Ep := parentEdges D a (scales j) p E
        (Ep.card : ℝ) / (Ep.image Prod.snd).card ≤
          (125 * 175616 * 16384 : ℝ) * (retentionCost d g L : ℝ) *
            (Q : ℝ) ^ 2 * D.thickness ^ (-eta) *
              ((Ep.image (NativeLocalCellCoherence.localPair D a (scales j) p)).card : ℝ) /
                (Ep.image (NativeLocalCellCoherence.localCellLabel D a (scales j) p)).card := by
  let Q := NativeSourceSizeBounds.radix (incidences original).card L
  have hQ4 : 4 ≤ Q := NativeSourceSizeBounds.radix_four_le _ _
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hcost : (0 : ℝ) < retentionCost d g L := by
    unfold retentionCost
    positivity
  obtain ⟨E, hEI, hEne, hret, hUniform, hLower⟩ :=
    exists_original_scheduled_pair_core h original horiginal ha hsmall
      d g L hdg hL Rel hrefl hsym scales hN hscale
  refine ⟨E, hEI, hEne, hret, hUniform, ?_⟩
  intro j p hp
  exact native_parent_multiplicity_transfer h original horiginal ha
    (scales j) (hN j) p E hEI hcost hQpos (hLower j) hp

end NativeScheduledLocalMultiplicity
