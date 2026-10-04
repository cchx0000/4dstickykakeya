import Theorems.Thm_StickyKakeya4_native_common_cubical_mesh
import Theorems.Thm_StickyKakeya4_native_finite_kakeya_exponent
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeCubicalIncidenceCounts
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeFiniteKakeyaExponent
open scoped ENNReal BigOperators

def incidences {n : ℕ} (cells : Fin n → Finset Index) : Finset (Fin n × Index) :=
  univ.biUnion (fun i => (cells i).image (fun k => (i, k)))
def support {n : ℕ} (cells : Fin n → Finset Index) : Finset Index := univ.biUnion cells

lemma mem_incidences {n : ℕ} (cells : Fin n → Finset Index) (i : Fin n) (k : Index) :
    (i, k) ∈ incidences cells ↔ k ∈ cells i := by simp [incidences]

lemma support_eq_image {n : ℕ} (cells : Fin n → Finset Index) :
    support cells = (incidences cells).image Prod.snd := by
  ext k
  simp only [support, mem_biUnion, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨i, hk⟩
    exact ⟨(i, k), (mem_incidences cells i k).mpr hk, rfl⟩
  · rintro ⟨⟨i, l⟩, hp, rfl⟩
    exact ⟨i, (mem_incidences cells i l).mp hp⟩

lemma card_incidences {n : ℕ} (cells : Fin n → Finset Index) :
    (incidences cells).card = ∑ i, (cells i).card := by
  unfold incidences
  rw [card_biUnion]
  · apply sum_congr rfl
    intro i _hi
    exact card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)
  · intro i _hi j _hj hij
    apply disjoint_left.mpr
    rintro p hp hp'
    obtain ⟨k, _hk, rfl⟩ := mem_image.mp hp
    obtain ⟨l, _hl, he⟩ := mem_image.mp hp'
    exact hij (congrArg Prod.fst he).symm

lemma sourceUnion_eq_support_cells {n : ℕ} (D : FiniteScaleSource n)
    (mesh : ℝ) (cells : Fin n → Finset Index) (hw : ∀ i, D.weight i = 1)
    (hcells : ∀ i, D.shading i = wzCellShading mesh cells i) :
    sourceUnion D = ⋃ k ∈ (support cells : Set Index), wzDyadicCell mesh k := by
  rw [sourceUnion_eq_iUnion_shading_of_weights_one D hw]
  simp_rw [hcells]
  ext x
  simp only [wzCellShading, Set.mem_iUnion, mem_coe, support, mem_biUnion, mem_univ, true_and]
  aesop

lemma total_shading_eq_incidence_volume {n : ℕ} (D : FiniteScaleSource n)
    {mesh : ℝ} (hm : 0 < mesh) (cells : Fin n → Finset Index)
    (hcells : ∀ i, D.shading i = wzCellShading mesh cells i) :
    wzTotalShadingVolume D = (incidences cells).card * (ENNReal.ofReal mesh) ^ 4 := by
  unfold wzTotalShadingVolume
  simp_rw [hcells, volume_wzCellShading hm]
  rw [← sum_mul]
  congr 1
  exact_mod_cast (card_incidences cells).symm

lemma union_eq_support_volume {n : ℕ} (D : FiniteScaleSource n)
    {mesh : ℝ} (hm : 0 < mesh) (cells : Fin n → Finset Index)
    (hw : ∀ i, D.weight i = 1)
    (hcells : ∀ i, D.shading i = wzCellShading mesh cells i) :
    volume (sourceUnion D) = (support cells).card * (ENNReal.ofReal mesh) ^ 4 := by
  rw [sourceUnion_eq_support_cells D mesh cells hw hcells]
  have hset : (⋃ k ∈ (support cells : Set Index), wzDyadicCell mesh k) =
      ⋃ k ∈ support cells, wzDyadicCell mesh k := by
    ext x
    simp
  rw [hset, measure_biUnion_finset]
  · simp [volume_wzDyadicCell]
  · intro k _hk l _hl hkl
    exact wzDyadicCell_disjoint hm hkl
  · intro k _hk
    exact measurableSet_wzDyadicCell mesh k

/-- The measure multiplicity is EXACTLY the original finite incidence/support
ratio after choosing the one common cubical mesh. Empty original rows are kept. -/
lemma multiplicity_eq_card_ratio {n : ℕ} (D : FiniteScaleSource n)
    {mesh : ℝ} (hm : 0 < mesh) (cells : Fin n → Finset Index)
    (hw : ∀ i, D.weight i = 1)
    (hcells : ∀ i, D.shading i = wzCellShading mesh cells i) :
    NativeFiniteKakeyaCounts.multiplicity D =
      (incidences cells).card / ((support cells).card : ℝ≥0∞) := by
  unfold NativeFiniteKakeyaCounts.multiplicity
  rw [total_shading_eq_incidence_volume D hm cells hcells,
    union_eq_support_volume D hm cells hw hcells]
  exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

/-- Actual admissible native shadings produce literal original incidence rows
with exact total-mass, union-mass and multiplicity identities. -/
theorem input_exists_incidence_counts {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) :
    ∃ cells : Fin n → Finset Index,
      (∀ i, D.shading i = wzCellShading (D.thickness / 2) cells i) ∧
      wzTotalShadingVolume D =
        (incidences cells).card * (ENNReal.ofReal (D.thickness / 2)) ^ 4 ∧
      volume (sourceUnion D) =
        (support cells).card * (ENNReal.ofReal (D.thickness / 2)) ^ 4 ∧
      NativeFiniteKakeyaCounts.multiplicity D =
        (incidences cells).card / ((support cells).card : ℝ≥0∞) := by
  obtain ⟨cells, hc⟩ := input_exists_common_cells h
  have hm := half_pos h.1.2.1
  have hw := h.1.2.2.2.2.2.1
  exact ⟨cells, hc, total_shading_eq_incidence_volume D hm cells hc,
    union_eq_support_volume D hm cells hw hc, multiplicity_eq_card_ratio D hm cells hw hc⟩

/-- The native extremal branch supplies ORIGINAL finite cell incidences, not
just a volume witness. The displayed count bound retains its exact mesh factor. -/
theorem exists_near_extremal_incidence_counts (hk : 0 < extremalExponent)
    {theta0 delta0 : ℝ} (htheta0 : 0 < theta0) (hdelta0 : 0 < delta0) :
    ∃ theta : ℝ, 0 < theta ∧ theta < theta0 ∧
      ∃ (n : ℕ) (D : FiniteScaleSource n) (cells : Fin n → Finset Index),
        0 < D.thickness ∧ D.thickness < delta0 ∧
        IsWangZakharovNativeFiniteInput D theta ∧
        (∀ i, D.shading i = wzCellShading (D.thickness / 2) cells i) ∧
        (incidences cells).Nonempty ∧
        (support cells).card * (ENNReal.ofReal (D.thickness / 2)) ^ 4 ≤
          (ENNReal.ofReal D.thickness).rpow (extremalExponent - theta) ∧
        (ENNReal.ofReal D.thickness).rpow (-extremalExponent + theta) ≤
          (incidences cells).card / ((support cells).card : ℝ≥0∞) := by
  obtain ⟨theta, htheta, htheta0', n, D, hd, hsmall, hinput, hvol, hmu⟩ :=
    exists_near_extremizer hk htheta0 hdelta0
  obtain ⟨cells, hc, _hS, hU, hM⟩ := input_exists_incidence_counts hinput
  rw [hU] at hvol
  rw [hM] at hmu
  have hne : (incidences cells).Nonempty := by
    apply card_pos.mp
    by_contra hz
    have hc0 : (incidences cells).card = 0 := by omega
    have hp : (0 : ℝ≥0∞) < (ENNReal.ofReal D.thickness).rpow (-extremalExponent + theta) :=
      ENNReal.rpow_pos (by positivity) ENNReal.ofReal_ne_top
    simpa [hc0] using hp.trans_le hmu
  exact ⟨theta, htheta, htheta0', n, D, cells, hd, hsmall, hinput, hc, hne, hvol, hmu⟩
end NativeCubicalIncidenceCounts
