import Theorems.Thm_StickyKakeya4_native_local_cell_coherence
import Theorems.Thm_StickyKakeya4_native_local_pair_fibers
import Theorems.Thm_StickyKakeya4_native_local_parent_capacity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

noncomputable section
namespace NativeLocalParentMultiplicity
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentSelection

/-- Restrict the current literal original relation to one original parent.
No old incidence is added and no new source is substituted. -/
def parentEdges {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (E : Finset (Fin n × Index)) : Finset (Fin n × Index) :=
  E.filter (fun z => parentLabel D a N z.1 = p)

lemma parentEdges_subset {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (E : Finset (Fin n × Index)) : parentEdges D a N p E ⊆ E :=
  filter_subset _ _

lemma globalPair_eq_localPair {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (z : Fin n × Index) (hz : parentLabel D a N z.1 = p) :
    NativeLocalPairFibers.localPair D a N z = NativeLocalCellCoherence.localPair D a N p z := by
  simp only [NativeLocalPairFibers.localPair, NativeLocalCellCoherence.localPair,
    NativeLocalCellCoherence.localCellLabel, hz]

/-- A local tube/cell fiber survives parent restriction in full: its tube
coordinate already determines its original parent. -/
lemma parent_fiber_eq_global {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (E : Finset (Fin n × Index)) (b : Fin n × Index)
    (hb : parentLabel D a N b.1 = p) :
    ((parentEdges D a N p E).filter
      (fun z => NativeLocalCellCoherence.localPair D a N p z = b)) =
        NativeLocalPairFibers.pairFiber D a N E b := by
  ext z
  simp only [parentEdges, NativeLocalPairFibers.pairFiber, mem_filter]
  constructor
  · rintro ⟨⟨hz, hp⟩, he⟩
    exact ⟨hz, (globalPair_eq_localPair D a N p z hp).trans he⟩
  · rintro ⟨hz, he⟩
    have hi := congrArg Prod.fst he
    change z.1 = b.1 at hi
    have hp : parentLabel D a N z.1 = p := by rw [hi]; exact hb
    exact ⟨⟨hz, hp⟩, (globalPair_eq_localPair D a N p z hp).symm.trans he⟩

lemma parent_pair_fiber_lower {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (E : Finset (Fin n × Index)) (L : ℝ)
    (hL : ∀ z ∈ E, L ≤ (NativeLocalPairFibers.pairFiber D a N E
      (NativeLocalPairFibers.localPair D a N z)).card)
    (b : Fin n × Index)
    (hb : b ∈ (parentEdges D a N p E).image (NativeLocalCellCoherence.localPair D a N p)) :
    L ≤ (((parentEdges D a N p E).filter
      (fun z => NativeLocalCellCoherence.localPair D a N p z = b)).card : ℝ) := by
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hb
  have hp : parentLabel D a N z.1 = p := (mem_filter.mp hz).2
  rw [parent_fiber_eq_global D a N p E (NativeLocalCellCoherence.localPair D a N p z) hp]
  rw [← globalPair_eq_localPair D a N p z hp]
  exact hL z (mem_filter.mp hz).1

/-- The geometric inverse-image capacity applies to every literal retained
subset, with the original tube label fixed throughout the fiber. -/
lemma retained_pair_fiber_capacity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (E : Finset (Fin n × Index))
    (hE : E ⊆ incidences original) (b : Fin n × Index) :
    (E.filter (fun z => NativeLocalCellCoherence.localPair D a N p z = b)).card ≤
      175616 * N := by
  have hinj := NativeLocalCellCoherence.pairFiber_snd_injective D a N p E b
  have hsub : ((E.filter (fun z => NativeLocalCellCoherence.localPair D a N p z = b)).image
      Prod.snd) ⊆ ((original b.1).filter (fun k => NativeLocalParentCells.cellLabel D a N p b.1 k = b.2)) := by
    intro k hk
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hk
    have hzE := hE (mem_filter.mp hz).1
    have hi := congrArg Prod.fst (mem_filter.mp hz).2
    change z.1 = b.1 at hi
    have he : NativeLocalParentCells.cellLabel D a N p z.1 z.2 = b.2 :=
      congrArg Prod.snd (mem_filter.mp hz).2
    exact mem_filter.mpr ⟨by simpa only [hi] using (mem_incidences original z.1 z.2).mp hzE,
      by simpa only [hi] using he⟩
  rw [← card_image_of_injOn hinj]
  exact (card_le_card hsub).trans
    (NativeLocalParentCapacity.output_cell_fiber_card_le h original horiginal ha N hN p b.1 b.2)

theorem retained_pair_image_capacity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (E : Finset (Fin n × Index))
    (hE : E ⊆ incidences original) :
    E.card ≤ (175616 * N) * (E.image (NativeLocalCellCoherence.localPair D a N p)).card := by
  exact card_le_mul_card_image E (175616 * N)
    (fun b _ => retained_pair_fiber_capacity h original horiginal ha N hN p E hE b)

/-- The same parent restriction combines geometric source capacity with
real-threshold shadow compression. The global lower fibers are preserved
exactly, rather than reselected inside each scale or parent. -/
theorem parent_multiplicity_cross {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (E : Finset (Fin n × Index))
    (hE : E ⊆ incidences original) (L : ℝ)
    (hL : ∀ z ∈ E, L ≤ (NativeLocalPairFibers.pairFiber D a N E
      (NativeLocalPairFibers.localPair D a N z)).card) :
    let Ep := parentEdges D a N p E
    L * (Ep.card : ℝ) * (Ep.image (NativeLocalCellCoherence.localCellLabel D a N p)).card ≤
      (125 * 175616 : ℝ) * N * (Ep.image (NativeLocalCellCoherence.localPair D a N p)).card *
        (Ep.image Prod.snd).card := by
  let Ep := parentEdges D a N p E
  have hEp : Ep ⊆ incidences original := (parentEdges_subset D a N p E).trans hE
  have hshadow := NativeLocalCellCoherence.retained_shadow_compression h original horiginal ha
    N hN p Ep hEp L (parent_pair_fiber_lower D a N p E L hL)
  have hcap : (Ep.card : ℝ) ≤ (175616 * (N : ℝ)) *
      (Ep.image (NativeLocalCellCoherence.localPair D a N p)).card := by
    exact_mod_cast retained_pair_image_capacity h original horiginal ha N hN p Ep hEp
  change L * (Ep.card : ℝ) * (Ep.image (NativeLocalCellCoherence.localCellLabel D a N p)).card ≤ _
  calc
    _ = (Ep.card : ℝ) * (L * (Ep.image (NativeLocalCellCoherence.localCellLabel D a N p)).card) := by ring
    _ ≤ (Ep.card : ℝ) * (125 * (Ep.image Prod.snd).card) :=
      mul_le_mul_of_nonneg_left hshadow (by positivity)
    _ ≤ ((175616 * (N : ℝ)) * (Ep.image (NativeLocalCellCoherence.localPair D a N p)).card) *
        (125 * (Ep.image Prod.snd).card) := mul_le_mul_of_nonneg_right hcap (by positivity)
    _ = _ := by ring

/-- Substituting the native uniform-core lower fiber cancels the relative
scale N exactly. The original eta is unchanged. -/
theorem native_parent_multiplicity_cross {n : ℕ} {D : FiniteScaleSource n} {eta a F Q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (E : Finset (Fin n × Index))
    (hE : E ⊆ incidences original) (hF : 0 < F) (hQ : 0 < Q)
    (hL : ∀ z ∈ E, D.thickness ^ eta * N / (16384 * F * Q ^ 2) ≤
      (NativeLocalPairFibers.pairFiber D a N E (NativeLocalPairFibers.localPair D a N z)).card) :
    let Ep := parentEdges D a N p E
    D.thickness ^ eta * (Ep.card : ℝ) *
        (Ep.image (NativeLocalCellCoherence.localCellLabel D a N p)).card ≤
      (125 * 175616 * 16384 : ℝ) * F * Q ^ 2 *
        (Ep.image (NativeLocalCellCoherence.localPair D a N p)).card * (Ep.image Prod.snd).card := by
  let Ep := parentEdges D a N p E
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : 0 < (16384 : ℝ) * F * Q ^ 2 := by positivity
  have ht := parent_multiplicity_cross h original horiginal ha N hN p E hE
    (D.thickness ^ eta * N / (16384 * F * Q ^ 2)) hL
  change D.thickness ^ eta * (Ep.card : ℝ) *
    (Ep.image (NativeLocalCellCoherence.localCellLabel D a N p)).card ≤ _
  apply (mul_le_mul_iff_left₀ hNr).mp
  calc
    _ = (16384 * F * Q ^ 2) *
        ((D.thickness ^ eta * N / (16384 * F * Q ^ 2)) * (Ep.card : ℝ) *
          (Ep.image (NativeLocalCellCoherence.localCellLabel D a N p)).card) := by
      field_simp [hden.ne']
    _ ≤ (16384 * F * Q ^ 2) *
        ((125 * 175616 : ℝ) * N * (Ep.image (NativeLocalCellCoherence.localPair D a N p)).card *
          (Ep.image Prod.snd).card) := mul_le_mul_of_nonneg_left ht hden.le
    _ = _ := by ring

/-- Native average multiplicity transfer on any nonempty selected original
parent, with one fixed constant and no relative-scale loss remaining. -/
theorem native_parent_multiplicity_transfer {n : ℕ} {D : FiniteScaleSource n} {eta a F Q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (E : Finset (Fin n × Index))
    (hE : E ⊆ incidences original) (hF : 0 < F) (hQ : 0 < Q)
    (hL : ∀ z ∈ E, D.thickness ^ eta * N / (16384 * F * Q ^ 2) ≤
      (NativeLocalPairFibers.pairFiber D a N E (NativeLocalPairFibers.localPair D a N z)).card)
    (hne : (parentEdges D a N p E).Nonempty) :
    let Ep := parentEdges D a N p E
    (Ep.card : ℝ) / (Ep.image Prod.snd).card ≤
      (125 * 175616 * 16384 : ℝ) * F * Q ^ 2 * D.thickness ^ (-eta) *
        ((Ep.image (NativeLocalCellCoherence.localPair D a N p)).card : ℝ) /
          (Ep.image (NativeLocalCellCoherence.localCellLabel D a N p)).card := by
  let Ep := parentEdges D a N p E
  have hold : (0 : ℝ) < (Ep.image Prod.snd).card := by
    exact_mod_cast card_pos.mpr (hne.image Prod.snd)
  have hnew : (0 : ℝ) < (Ep.image (NativeLocalCellCoherence.localCellLabel D a N p)).card := by
    exact_mod_cast card_pos.mpr (hne.image (NativeLocalCellCoherence.localCellLabel D a N p))
  have hd := h.1.2.1
  have hp := Real.rpow_pos_of_pos hd eta
  have ht := native_parent_multiplicity_cross h original horiginal ha N hN p E hE hF hQ hL
  change (Ep.card : ℝ) / (Ep.image Prod.snd).card ≤ _
  apply (div_le_div_iff₀ hold hnew).mpr
  apply (mul_le_mul_iff_right₀ hp).mp
  calc
    _ = D.thickness ^ eta * (Ep.card : ℝ) *
        (Ep.image (NativeLocalCellCoherence.localCellLabel D a N p)).card := by ring
    _ ≤ _ := ht
    _ = _ := by
      rw [Real.rpow_neg hd.le]
      field_simp [hp.ne', Ep]
      rfl

end NativeLocalParentMultiplicity
