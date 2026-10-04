import Theorems.Thm_StickyKakeya4_native_padded_cell_source
import Theorems.Thm_StickyKakeya4_native_padded_cell_union_bound
import Theorems.Thm_StickyKakeya4_native_padded_cell_fiber_count
import Theorems.Thm_StickyKakeya4_native_original_pruned_mass
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativePaddedSourceMass
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalPaddedCells NativeContractedUnitParent NativeUnitParentNormalization
open NativePaddedCellSource NativePaddedCellUnionBound NativePaddedCellFiberCount NativeOriginalPrunedMass
open scoped ENNReal BigOperators

lemma sum_originalLabel {n : ℕ} {M : Type*} [AddCommMonoid M]
    (R : Finset (Fin n)) (f : Fin n → M) :
    (∑j : Fin R.card,f (originalLabel R j))=∑i∈R,f i := by
  have hh := R.equivFin.symm.sum_comp (fun i : R => f i.val)
  simpa only [originalLabel,Finset.sum_coe_sort] using hh

lemma iUnion_originalLabel {n : ℕ} (R : Finset (Fin n)) (f : Fin n → Set E4) :
    (⋃j : Fin R.card,f (originalLabel R j))=⋃i∈R,f i := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨originalLabel R j,originalLabel_mem R j,hj⟩
  · rintro ⟨i,hi,hx⟩
    refine ⟨R.equivFin ⟨i,hi⟩,?_⟩
    simpa only [originalLabel,Equiv.symm_apply_apply] using hx

lemma sourceUnion_eq_retained {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (a : ℝ) (p : Parent) (hp : ∀i∈R,parentLabel D a 1 i=p) :
    sourceUnion (source h original R a p hp)=
      ⋃i∈R,wzCellShading (D.thickness/128) (cells D original a p) i := by
  rw [sourceUnion_eq_iUnion_shading_of_weights_one _ (fun i=>(source_weights h original R a p hp i).1)]
  change (⋃j : Fin R.card,wzCellShading (D.thickness/128) (cells D original a p) (originalLabel R j))=_
  exact iUnion_originalLabel _ _

/-- The ACTUAL constructed finite source has the joint original-union upper
bound required to carry an original near-extremizer through normalization. -/
theorem source_union_volume_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (p : Parent) (hp : ∀i∈R,parentLabel D a 1 i=p) :
    volume (sourceUnion (source h original R a p hp)) ≤ 625*volume (sourceUnion D) := by
  rw [sourceUnion_eq_retained]
  have hh := output_union_volume_le h original horiginal ha R p
  have hs : (⋃i∈R,D.shading i) ⊆ sourceUnion D := by
    rw [sourceUnion_eq_iUnion_shading_of_weights_one D h.1.2.2.2.2.2.1]
    exact Set.iUnion₂_subset (fun i _hi => Set.subset_iUnion (fun j => D.shading j) i)
  exact hh.trans (mul_le_mul' le_rfl (measure_mono hs))

lemma total_shading_eq_retained {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (a : ℝ) (p : Parent) (hp : ∀i∈R,parentLabel D a 1 i=p) :
    wzTotalShadingVolume (source h original R a p hp)=
      ∑i∈R,volume (wzCellShading (D.thickness/128) (cells D original a p) i) := by
  exact sum_originalLabel (M:=ℝ≥0∞) R (fun i => volume (wzCellShading (D.thickness/128) (cells D original a p) i))

/-- Same-family original shading mass survives in the actual new source. -/
theorem original_shadingMass_le_source {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (p : Parent) (hp : ∀i∈R,parentLabel D a 1 i=p) :
    shadingMass D R ≤ (175616:ℝ≥0∞)*64^4*wzTotalShadingVolume (source h original R a p hp) := by
  rw [total_shading_eq_retained,mul_sum]
  exact sum_le_sum (fun i _hi => original_shading_volume_le h original horiginal ha p i)

lemma unit_tube_volume_comparison {l l' : MarkedLine} (hl : IsValidLine l) (hl' : IsValidLine l')
    {delta delta' : ℝ} (hd : 0 < delta) (hd' : 0 < delta') (hsmall : delta ≤ 1/8)
    (hle : delta' ≤ delta) : volume (markedUnitTube l' delta') ≤ 256*volume (markedUnitTube l delta) := by
  have hu := volume_markedUnitTube_upper_bound hl' hd' (by linarith : delta' ≤ 1)
  have hlower := volume_markedUnitTube_lower_bound hl hd hsmall
  have hm := ENNReal.ofReal_le_ofReal hle
  have hc : ENNReal.ofReal (1/8:ℝ)*(256:ℝ≥0∞)=32 := by
    rw [←ENNReal.ofReal_ofNat,←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/8)]
    norm_num
  calc
    _ ≤ 32*(ENNReal.ofReal delta)^3*ENNReal.ofReal (Real.pi^2/2) :=
      hu.trans (mul_le_mul' (mul_le_mul' le_rfl (pow_le_pow_left' hm 3)) le_rfl)
    _ = (ENNReal.ofReal (1/8:ℝ)*256)*((ENNReal.ofReal delta)^3*ENNReal.ofReal (Real.pi^2/2)) := by rw [hc]; ring
    _ = 256*(ENNReal.ofReal (1/8:ℝ)*(ENNReal.ofReal delta)^3*ENNReal.ofReal (Real.pi^2/2)) := by ring
    _ ≤ _ := mul_le_mul' le_rfl hlower

lemma total_tubes_eq_retained {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (a : ℝ) (p : Parent) (hp : ∀i∈R,parentLabel D a 1 i=p) :
    wzTotalTubeVolume (source h original R a p hp)=
      ∑i∈R,volume (markedUnitTube (NativeContractedUnitParent.line D a p i) (D.thickness/64)) := by
  exact sum_originalLabel (M:=ℝ≥0∞) R (fun i => volume (markedUnitTube (NativeContractedUnitParent.line D a p i) (D.thickness/64)))

theorem source_tubeMass_le_original {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hsmall : D.thickness ≤ 1/8)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (p : Parent)
    (hp : ∀i∈R,parentLabel D a 1 i=p) :
    wzTotalTubeVolume (source h original R a p hp) ≤ 256*tubeMass D R := by
  rw [total_tubes_eq_retained,tubeMass,mul_sum]
  apply sum_le_sum
  intro i hi
  exact unit_tube_volume_comparison (h.1.2.2.2.2.1 i) (contracted_line_common_slab D a p i (hp i hi)).1
    h.1.2.1 (by have hd:=h.1.2.1; positivity) hsmall (by linarith [h.1.2.1])

/-- An exact comparison of ACTUAL densities, written without division and
without assuming any desired output density profile. -/
theorem source_density_cross_bound {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hsmall : D.thickness ≤ 1/8)
    (original : Fin n → Finset Index) (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (p : Parent) (hp : ∀i∈R,parentLabel D a 1 i=p) :
    wzTotalTubeVolume (source h original R a p hp)*shadingMass D R ≤
      (256*175616*64^4:ℝ≥0∞)*tubeMass D R*wzTotalShadingVolume (source h original R a p hp) := by
  have hh := mul_le_mul' (source_tubeMass_le_original h hsmall original R p hp)
    (original_shadingMass_le_source h original horiginal ha R p hp)
  exact hh.trans_eq (by ring)
end NativePaddedSourceMass
