import Theorems.Thm_StickyKakeya4_native_padded_source_mass
import Theorems.Thm_StickyKakeya4_native_dense_retained_unit_parent
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativePaddedSourceDensity
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalPrunedMass NativeDenseRetainedUnitParent NativePaddedCellSource NativePaddedSourceMass
open scoped ENNReal BigOperators

lemma tubeMass_ne_top {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) : tubeMass D R ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro i _hi
  exact ne_top_of_le_ne_top (by finiteness) (tube_volume_upper h i)

lemma realTubeMass_eq_toReal {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) :
    realTubeMass D R=(tubeMass D R).toReal := by
  symm
  apply ENNReal.toReal_sum
  intro i _hi
  exact ne_top_of_le_ne_top (by finiteness) (tube_volume_upper h i)

lemma ofReal_realShadingMass {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) :
    ENNReal.ofReal (realShadingMass D R)=shadingMass D R := by
  rw [realShadingMass_eq_toReal h,ENNReal.ofReal_toReal (shadingMass_ne_top h R)]

lemma ofReal_realTubeMass {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) :
    ENNReal.ofReal (realTubeMass D R)=tubeMass D R := by
  rw [realTubeMass_eq_toReal h,ENNReal.ofReal_toReal (tubeMass_ne_top h R)]

/-- Positive original shading follows from actual retained tube volume and
the density already proved by original-label pruning. -/
lemma retained_shading_pos {n : ℕ} {D : FiniteScaleSource n} {eta zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (hR : R.Nonempty) (hsmall : D.thickness ≤ 1/8)
    (hden : (ENNReal.ofReal D.thickness).rpow zeta*tubeMass D R ≤ shadingMass D R) :
    0 < shadingMass D R := by
  have hT : 0 < tubeMass D R := by
    rw [←ofReal_realTubeMass h]
    exact ENNReal.ofReal_pos.mpr (realTubeMass_pos h R hR hsmall)
  have hd := h.1.2.1
  exact lt_of_lt_of_le
    (ENNReal.mul_pos_iff.mpr ⟨ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hd) ENNReal.ofReal_ne_top,hT⟩) hden

/-- Select an actual whole unit parent using original shading and tube
volumes. Both conclusions concern the unchanged original labels. -/
theorem exists_dense_parent_enn {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (hR : R.Nonempty) (hsmall : D.thickness ≤ 1/8)
    (hden : (ENNReal.ofReal D.thickness).rpow zeta*tubeMass D R ≤ shadingMass D R) :
    ∃p∈R.image (parentLabel D a 1), (parentSubset D R a p).Nonempty ∧
      shadingMass D R ≤ 2*(R.image (parentLabel D a 1)).card*shadingMass D (parentSubset D R a p) ∧
      (ENNReal.ofReal D.thickness).rpow zeta*tubeMass D (parentSubset D R a p) ≤
        2*shadingMass D (parentSubset D R a p) := by
  have hd := h.1.2.1
  obtain ⟨p,hp,hQ,_hpos,hret,hsel⟩ := exists_dense_retained_volume_parent h R a hR
    (retained_shading_pos h R hR hsmall hden) hsmall
  have hsource : D.thickness^zeta*realTubeMass D R ≤ realShadingMass D R := by
    have hh := ENNReal.toReal_mono (shadingMass_ne_top h R) hden
    simpa only [ENNReal.rpow_eq_pow,ENNReal.toReal_mul,←ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hd.le,←realTubeMass_eq_toReal h,←realShadingMass_eq_toReal h] using hh
  have hQden := retained_parent_density h R a hR hsmall p hsource hsel
  refine ⟨p,hp,hQ,?_,?_⟩
  · have hh := ENNReal.ofReal_le_ofReal hret
    simpa only [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2*(R.image (parentLabel D a 1)).card),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat,ENNReal.ofReal_natCast,
      ofReal_realShadingMass h] using hh
  · have hh := ENNReal.ofReal_le_ofReal hQden
    simpa only [ENNReal.ofReal_mul (Real.rpow_pos_of_pos hd zeta).le,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat,
      ofReal_realTubeMass h,ofReal_realShadingMass h,ENNReal.ofReal_rpow_of_pos hd,
      ENNReal.rpow_eq_pow] using hh

/-- The actual cubical new source inherits the selected original parent's
density with an explicit fixed cost. This consumes only the density proved
by the same-label parent selection. -/
theorem source_raw_density {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hsmall : D.thickness ≤ 1/8)
    (original : Fin n → Finset Index) (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (Q : Finset (Fin n)) (p : Parent) (hp : ∀i∈Q,parentLabel D a 1 i=p)
    (hden : (ENNReal.ofReal D.thickness).rpow zeta*tubeMass D Q ≤ 2*shadingMass D Q) :
    (ENNReal.ofReal D.thickness).rpow zeta*wzTotalTubeVolume (source h original Q a p hp) ≤
      (512*175616*64^4:ℝ≥0∞)*wzTotalShadingVolume (source h original Q a p hp) := by
  calc
    _ ≤ (ENNReal.ofReal D.thickness).rpow zeta*(256*tubeMass D Q) :=
      mul_le_mul' le_rfl (source_tubeMass_le_original h hsmall original Q p hp)
    _ = 256*((ENNReal.ofReal D.thickness).rpow zeta*tubeMass D Q) := by ring
    _ ≤ 256*(2*shadingMass D Q) := mul_le_mul' le_rfl hden
    _ ≤ 256*(2*((175616:ℝ≥0∞)*64^4*wzTotalShadingVolume (source h original Q a p hp))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (original_shadingMass_le_source h original horiginal ha Q p hp))
    _ = _ := by ring
end NativePaddedSourceDensity
