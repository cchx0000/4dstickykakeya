import Theorems.Thm_StickyKakeya4_native_shading_independent_representatives
import Theorems.Thm_StickyKakeya4_native_relative_parent_profiles
import Theorems.Thm_StickyKakeya4_native_relative_coarse_point_menu
import Theorems.Thm_StickyKakeya4_native_coarse_point_multiplicity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeRelativeCoarseReadback
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeLocalParentSource NativeCubicalIncidenceCounts NativeRelativeParentLabels
open NativeShadingIndependentRepresentatives NativeRelativeCoarseGeometry
open NativeRelativeCoarsePointMenu
open scoped ENNReal

/-- Original label of a relative representative fixed on the full backbone
before any selected shading is known. -/
def originalRepresentative {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty) (M : ℕ) (q : Parent) : Fin n :=
  NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p)
    (relativeRepresentative h R a m p hQ M q)

/-- Occupied relative parents have a genuine representative in the unchanged
original backbone, independently of every selected shading. -/
theorem originalRepresentative_spec {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty) (M : ℕ) (q : Parent)
    (hq : q ∈ (parentLabels D R a (2^m) p).image (relativeLabel D a (2^m) p M)) :
    originalRepresentative h R a m p hQ M q ∈ parentLabels D R a (2^m) p ∧
      relativeLabel D a (2^m) p M (originalRepresentative h R a m p hQ M q) = q := by
  refine ⟨NativePaddedCellSource.originalLabel_mem _ _,?_⟩
  let Q := parentLabels D R a (2^m) p
  let S := source h R ∅ a m p
  obtain ⟨i,hi,hiq⟩ := mem_image.mp hq
  let j : Fin Q.card := Q.equivFin ⟨i,hi⟩
  have hj : NativePaddedCellSource.originalLabel Q j = i := by
    simp only [NativePaddedCellSource.originalLabel,j,Equiv.symm_apply_apply]
  have hqS : q ∈ (univ : Finset (Fin Q.card)).image (parentLabel S 0 M) := by
    refine mem_image.mpr ⟨j,mem_univ _,?_⟩
    change parentLabel (source h R ∅ a m p) 0 M j = q
    rw [NativeRelativeParentProfiles.source_parentLabel,hj,hiq]
  have hs : parentLabel S 0 M
      (chooseRepresentative S (card_pos.mpr hQ) univ 0 M q) = q := by
    rw [chooseRepresentative,dif_pos hqS]
    exact (Classical.choose_spec (mem_image.mp hqS)).2
  change parentLabel (source h R ∅ a m p) 0 M
    (relativeRepresentative h R a m p hQ M q) = q at hs
  rw [NativeRelativeParentProfiles.source_parentLabel] at hs
  exact hs

theorem originalRepresentative_label {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty) (M : ℕ)
    (i : Fin n) (hi : i ∈ parentLabels D R a (2^m) p) :
    relativeLabel D a (2^m) p M
      (originalRepresentative h R a m p hQ M (relativeLabel D a (2^m) p M i)) =
        relativeLabel D a (2^m) p M i :=
  (originalRepresentative_spec h R a m p hQ M _ (mem_image_of_mem _ hi)).2

/-- Projection of an already-rounded local cell with its unchanged original
tube label. This map contains no selected incidence set. -/
def roundedPair {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty) (M : ℕ)
    (z : Fin n × Index) : Parent × Index :=
  let q := relativeLabel D a (2^m) p M z.1
  (q,wzDyadicCellIndex (32/(M:ℝ))
    (zeroGraphPoint (NativeLocalParentGeometry.line D a (2^m) p
      (originalRepresentative h R a m p hQ M q))
      (NativeOriginalCellChartGeometry.cellCenter (((2^m:ℕ):ℝ)*D.thickness/128) z.2 (3:Fin 4))))

/-- The double projection of a literal original edge; no reweighting or
incidence completion is performed. -/
def doublePair {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty) (M : ℕ)
    (z : Fin n × Index) : Parent × Index :=
  let q := relativeLabel D a (2^m) p M z.1
  (q,doubleLabel D a (2^m) M p
    (originalRepresentative h R a m p hQ M q) z.1 z.2)

lemma roundedPair_localPair {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty) (M : ℕ) (z : Fin n × Index) :
    roundedPair h R a m p hQ M (NativeLocalCellCoherence.localPair D a (2^m) p z) =
      doublePair h R a m p hQ M z := rfl

lemma source_mesh {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent) :
    mesh (source h R E a m p) = ((2^m:ℕ):ℝ)*D.thickness/128 := by
  rw [mesh,source_thickness]
  ring

/-- Exact second-image label after reindexing. Canonical relative
representatives equal the geometrically fixed ones by shading independence. -/
theorem relative_label_readback {n : ℕ} {D : FiniteScaleSource n} {eta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty) (M B : ℕ)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) e)
    (hmesh : (B:ℝ)*(source h R E a m p).thickness/128=32/(M:ℝ))
    (z : Fin (parentLabels D R a (2^m) p).card × Index) :
    NativeCoarseShadingCapacity.label (source h R E a m p) 0 M B
      (NativeCoarseDirectionThinning.representative hS univ 0 M) z =
        roundedPair h R a m p hQ M (originalPair (parentLabels D R a (2^m) p) z) := by
  apply Prod.ext
  · exact NativeRelativeParentProfiles.source_parentLabel h R E a m p M z.1
  · simp only [NativeCoarseShadingCapacity.label,NativeCoarseShadingCapacity.projectedLabel,
      NativeRelativeParentProfiles.source_parentLabel,roundedPair,originalPair]
    rw [←relativeRepresentative_eq_canonical h R E a m p hQ M _ hS,
      zero_front_formula,source_line,source_mesh,hmesh]
    rfl

/-- Deduplication of the first local cells is exactly respected by the
second coarse projection. Both sides are images of the same old E. -/
theorem relative_incidence_image {n : ℕ} {D : FiniteScaleSource n} {eta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty) (M B : ℕ)
    (hE : ∀z∈E,z.1∈parentLabels D R a (2^m) p)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) e)
    (hmesh : (B:ℝ)*(source h R E a m p).thickness/128=32/(M:ℝ)) :
    NativeCoarseShadingCapacity.coarse (source h R E a m p) 0 M B
      (NativeCoarseDirectionThinning.representative hS univ 0 M)
      (incidences (sourceCells D R E a (2^m) p)) =
        E.image (doublePair h R a m p hQ M) := by
  unfold NativeCoarseShadingCapacity.coarse
  calc
    _ = ((incidences (sourceCells D R E a (2^m) p)).image
        (originalPair (parentLabels D R a (2^m) p))).image
          (roundedPair h R a m p hQ M) := by
      rw [image_image]
      apply Finset.image_congr
      intro z _hz
      exact relative_label_readback h R E a m p hQ M B hS hmesh z
    _ = (E.image (NativeLocalCellCoherence.localPair D a (2^m) p)).image
        (roundedPair h R a m p hQ M) := by
      rw [source_incidences_readback D R E a (2^m) p hE]
    _ = _ := by rw [image_image]; rfl

lemma local_source_dyadic {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m : ℕ) (p : Parent)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level) :
    (source h R E a m p).thickness=(2:ℝ)⁻¹^(level-m+6) := by
  rw [source_thickness,NativeLocalParentScales.relative_scale hdy hm,pow_add]
  norm_num
  ring

/-- Literal relative full-shadow multiplicity is the count ratio of the
double-image original edges, with the true local dyadic depth retained. -/
theorem relative_full_multiplicity_readback {n : ℕ} {D : FiniteScaleSource n}
    {eta e : ℝ} (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m ell : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty)
    (hE : ∀z∈E,z.1∈parentLabels D R a (2^m) p)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) e)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level) (hell : ell≤level-m+6) :
    (NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource hS univ 0 (level-m+6) ell
        (incidences (sourceCells D R E a (2^m) p)))).toReal =
      NativeIncidenceMultiplicityTower.multiplicity
        (E.image (doublePair h R a m p hQ (2^ell))) := by
  rw [NativeCoarsePointMultiplicity.full_source_multiplicity_real hS univ 0
    (level-m+6) ell _ (fun z _hz => mem_univ z.1)]
  rw [relative_incidence_image h R E a m p hQ (2^ell)
    (NativeCoarseDyadicShading.block (level-m+6) ell) hE hS
    (NativeCoarseDyadicShading.block_mesh (local_source_dyadic h R E a level m p hdy hm) hell)]

end NativeRelativeCoarseReadback
