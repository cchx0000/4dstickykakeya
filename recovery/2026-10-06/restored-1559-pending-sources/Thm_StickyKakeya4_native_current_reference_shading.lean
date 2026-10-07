import Theorems.Thm_StickyKakeya4_native_actual_relative_coarse_admission

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeCurrentReferenceShading
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeOriginalPrunedMass
open scoped ENNReal BigOperators

/-- Cutting original edges cuts only literal local shading cells on the
unchanged full parent index type. -/
lemma sourceCells_mono {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (T E : Finset (Fin n × Index)) (hTE : T⊆E) (a : ℝ) (N : ℕ) (p : Parent)
    (i : Fin (parentLabels D R a N p).card) :
    sourceCells D R T a N p i⊆sourceCells D R E a N p i := by
  intro k hk
  obtain ⟨j,hj,rfl⟩ := (mem_outputCells D T a N p _ k).mp hk
  exact (mem_outputCells D E a N p _ _).mpr ⟨j,hTE hj,rfl⟩

/-- The sparse current shading is a genuine incidence subset of the native
reference source, without asserting that the sparse shading is native. -/
lemma current_local_incidences_subset {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (T E : Finset (Fin n × Index)) (hTE : T⊆E) (a : ℝ) (N : ℕ) (p : Parent) :
    incidences (sourceCells D R T a N p)⊆incidences (sourceCells D R E a N p) := by
  intro z hz
  exact (mem_incidences _ z.1 z.2).mpr
    (sourceCells_mono D R T E hTE a N p z.1 ((mem_incidences _ z.1 z.2).mp hz))

/-- Exact sparse mass inside the reference source's common fine mesh.
Changing E affects neither that mesh nor the full parent index type. -/
lemma current_local_mass_readback {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (T E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hQT : ∀z∈T,z.1∈parentLabels D R a (2^m) p) :
    ((incidences (sourceCells D R T a (2^m) p)).card:ℝ)*
      ((source h R E a m p).thickness/2)^4=
      (wzTotalShadingVolume (source h R T a m p)).toReal := by
  rw [source_total_shading h R T a m p hQT,source_incidence_card D R T a (2^m) p hQT]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (show 0 ≤ ((2^m:ℕ):ℝ)*D.thickness/128 by
      have hd:=h.1.2.1; positivity),source_thickness]
  ring

/-- Absolute selected mass, derived from the old parent's actual population,
its original edge average, and current incidence retention. No density or
native-input premise is imposed on the sparse current shading. -/
theorem current_local_mass_lower {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (H T : Finset (Fin n × Index)) (hT : T⊆incidences original)
    (m : ℕ) (p : Parent) (hQT : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (population C : ℝ) (hpopulation : 0 ≤ population) (hC : 0 ≤ C)
    (hparent : population*(parentLabels D R a (2^m) p).card ≤ D.thickness*H.card)
    (hretain : (H.card:ℝ) ≤ C*T.card)
    (hpop : D.thickness^zeta*((1/((2^m:ℕ):ℝ))/D.thickness)^3 ≤
      ((parentLabels D R a (2^m) p).card:ℝ)) :
    population*D.thickness^zeta ≤ (16*175616*64^4:ℝ)*C*
      (wzTotalShadingVolume (source h R T a m p)).toReal := by
  have hd := h.1.2.1
  have havg : population*(parentLabels D R a (2^m) p).card ≤ D.thickness*C*T.card :=
    hparent.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hretain hd.le)
  have hraw := selected_parent_mass_le_source h original horiginal ha R T hT m p
  rw [selected_parent_real_shading_eq_card D hd T (parentLabels D R a (2^m) p) hQT] at hraw
  have hscaled := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left hpop hpopulation).trans havg)
    (show 0 ≤ ((2^m:ℕ):ℝ)^3*D.thickness^3 by positivity)
  have hleft : (((2^m:ℕ):ℝ)^3*D.thickness^3)*
      (population*(D.thickness^zeta*((1/((2^m:ℕ):ℝ))/D.thickness)^3))=
      population*D.thickness^zeta := by
    field_simp [hd.ne']
  rw [hleft] at hscaled
  have hraw' := mul_le_mul_of_nonneg_left hraw (show 0 ≤ 16*C by positivity)
  calc
    population*D.thickness^zeta ≤
        (((2^m:ℕ):ℝ)^3*D.thickness^3)*(D.thickness*C*T.card) := hscaled
    _ = (16*C)*(((2^m:ℕ):ℝ)^3*((T.card:ℝ)*(mesh D)^4)) := by
      dsimp [mesh]
      ring
    _ ≤ (16*C)*((175616*64^4:ℝ)*(wzTotalShadingVolume (source h R T a m p)).toReal) := hraw'
    _ = _ := by ring

end NativeCurrentReferenceShading
