import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_core
import Theorems.Thm_StickyKakeya4_native_actual_reference_W_directions

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeNormalizedCellAngularMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeLocalParentGeometry NativeRelativeParentLabels
open NativeNormalizedCellRelativeMenu NativeNormalizedCellRelativeCore
open NativeLocalParentSource

/-- Actual complete normalized slope cells at width8/M=(64/M)/8. -/
def angularCell {n : ℕ} (D : FiniteScaleSource n) (N M : ℕ) (p : Parent)
    (i : Fin n) : Fin 3 → ℤ := fun j => ⌊((M:ℝ)*localSlope D N p i j)/8⌋

def relativeAngle (t : Parent) : Fin 3 → ℤ := fun j => t.1 j/8

/-- Angular quantization is literally a coarsening of the relative phase
label. No projection, slope-plane assumption or angular AD is used. -/
lemma angular_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N M : ℕ)
    (p : Parent) (i : Fin n) :
    angularCell D N M p i=relativeAngle (relativeLabel D a N p M i) := by
  funext j
  simp only [angularCell,relativeAngle,relativeLabel,slope_line]
  have hh := Int.floor_div_natCast ((M:ℝ)*localSlope D N p i j) 8
  norm_num only [Nat.cast_ofNat] at hh
  exact hh

def angularMenu {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m M : ℕ) (p : Parent)
    (E : Finset (Fin n × Index)) (q : Index) : Finset (Fin 3 → ℤ) :=
  (E.filter (fun z => physicalCell D a (2^m) M p z.2=q)).image (fun z => angularCell D (2^m) M p z.1)

/-- The entire actual angular union in one normalized spatial cell is an
image of its geometric relative-phase incidence fiber, with no multiplicity loss. -/
theorem angular_menu_le_degree {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m M : ℕ) (p : Parent) (E : Finset (Fin n × Index)) (q : Index) :
    (angularMenu D a m M p E q).card ≤
      ((E.image (normalizedPair D a m M p)).filter (fun z => z.2=q)).card := by
  let J := (E.image (normalizedPair D a m M p)).filter (fun z => z.2=q)
  have he : angularMenu D a m M p E q=J.image (fun z => relativeAngle z.1) := by
    ext t
    constructor
    · intro ht
      obtain ⟨z,hz,rfl⟩ := mem_image.mp ht
      obtain ⟨hz,hq⟩ := mem_filter.mp hz
      exact mem_image.mpr ⟨normalizedPair D a m M p z,
        mem_filter.mpr ⟨mem_image_of_mem _ hz,hq⟩,(angular_readback D a (2^m) M p z.1).symm⟩
    · intro ht
      obtain ⟨u,hu,rfl⟩ := mem_image.mp ht
      obtain ⟨hu,hq⟩ := mem_filter.mp hu
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hu
      exact mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,hq⟩,angular_readback D a (2^m) M p z.1⟩
  rw [he]
  exact card_image_le

/-- The current source's average relative multiplicity controls the full
actual angular union at widthrho/8, uniformly over every spatialrho-cell. -/
theorem original_angular_menu_upper {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (m M : ℕ) (hM : 0 < M)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*(M:ℝ) ≤ 64)
    (p : Parent) (hp : (parentLabels D R a (2^m) p).Nonempty)
    (E : Finset (Fin n × Index)) (hE : E⊆NativeCubicalIncidenceCounts.incidences original)
    (hlabels : ∀z∈E,z.1∈parentLabels D R a (2^m) p) (Q : ℕ)
    (hPair : NativeJointUniformCoarseRelations.HasUniformFibers E Q
      (NativeRelativeCoarseReadback.doublePair h R a m p hp M))
    (hPoint : NativeJointUniformCoarseRelations.HasUniformFibers E Q
      (fun z => (NativeRelativeCoarseReadback.doublePair h R a m p hp M z).2)) (q : Index) :
    ((angularMenu D a m M p E q).card:ℝ) ≤ 81*(Q:ℝ)^4*
      NativeIncidenceMultiplicityTower.multiplicity
        (E.image (NativeRelativeCoarseReadback.doublePair h R a m p hp M)) := by
  exact (Nat.cast_le.mpr (angular_menu_le_degree D a m M p E q)).trans
    (normalized_cell_degree_upper h original horiginal ha R m M hM hNscale hRelScale p hp E hE hlabels Q hPair hPoint q)

end NativeNormalizedCellAngularMenu
