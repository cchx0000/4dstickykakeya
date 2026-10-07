/- UNVERIFIED exact joint-key descent. The pre-third support-coherence
premise is explicit; it is supplied by the actual configured-cell selection. -/
import Theorems.Thm_StickyKakeya4_native_configured_joint_relation
import Theorems.Thm_StickyKakeya4_native_configured_point_degree_reader
import Theorems.Thm_StickyKakeya4_native_merged_point_offsets
import Theorems.Thm_StickyKakeya4_native_dyadic_parent_cells

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeJointKeyDescent
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeConfiguredJointRelation NativeConfiguredThirdRelation NativeDyadicParentCells
open NativeNormalizedCellRelativeMenu NativeRelativeParentLabels NativeJointUniformCoarseRelations
open NativeRetainedSliceCountTransfer CanonicalConfiguredE4Bridge NativeHorizontalGrainSlice SelfUniform

/-- Relative phase labels use one fixed local line, so their dyadic
ancestor is exact, including the intercept coordinates. -/
theorem relative_ancestor {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (fine coarse : ℕ) (hcf : coarse ≤ fine) (i : Fin n) :
    ancestor fine coarse (relativeLabel D a N p (2^fine) i) =
      relativeLabel D a N p (2^coarse) i := by
  apply Prod.ext
  · funext j
    simp only [ancestor, relativeLabel, Nat.cast_pow, Nat.cast_ofNat]
    exact (floor_dyadic_ancestor _ hcf).symm
  · funext j
    simp only [ancestor, relativeLabel, Nat.cast_pow, Nat.cast_ofNat]
    exact (floor_dyadic_ancestor _ hcf).symm

/-- The original physical grids have the same exact dyadic ancestry. -/
theorem physical_ancestor {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (fine coarse : ℕ) (hcf : coarse ≤ fine) (k : Index) (j : Fin 4) :
    physicalCell D a N (2^fine) p k j / (2^(fine-coarse) : ℕ) =
      physicalCell D a N (2^coarse) p k j := by
  let x := physicalPoint D a N p k j
  have he (f : ℕ) : x / (64 / ((2^f : ℕ) : ℝ)) = (2:ℝ)^f * (x/64) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  change ⌊x / (64 / ((2^fine : ℕ) : ℝ))⌋ / (2^(fine-coarse) : ℕ) =
    ⌊x / (64 / ((2^coarse : ℕ) : ℝ))⌋
  rw [he fine, he coarse]
  exact (floor_dyadic_ancestor (x/64) hcf).symm

section Keys
variable {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
  (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
  (hd : Module.finrank ℝ P = tangentDim s)
  (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
  (R u depth : ℕ) (hR : 0 < R) (hdepth : depth ≤ u+3)
  (U : Finset (Fin n × Index))
  (Hbase : ∀ x ∈ U, ∀ y ∈ U,
    NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R x.2 =
      NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R y.2 →
    physicalCell D a (2^m) (2^(u+6)) p x.2 =
      physicalCell D a (2^m) (2^(u+6)) p y.2)

include hR hdepth Hbase in
/-- Both the physical cell and tube-parent parts descend from the actual
final pair. The required phase guard is depth≤u+3; the mandatory base
coherence depth u+6 is used only for physical-cell ancestry. -/
theorem constant_on_pair (x y : Fin n × Index) (hx : x ∈ U) (hy : y ∈ U)
    (he : geometricPairKey D a m p s P hP hd F Fcfg R u x =
      geometricPairKey D a m p s P hP hd F Fcfg R u y) :
    jointKey D a m p R depth x = jointKey D a m p R depth y := by
  have hp := congrArg Prod.snd he
  have hphase := congrArg Prod.fst he
  have hheight := congrArg (NativeConfiguredPointDegreeReader.height m R) hp
  rw [NativeConfiguredPointDegreeReader.height_readback D a m p s P hP hd F Fcfg R hR x.2,
    NativeConfiguredPointDegreeReader.height_readback D a m p s P hP hd F Fcfg R hR y.2] at hheight
  have hphysical : physicalCell D a (2^m) (2^depth) p x.2 =
      physicalCell D a (2^m) (2^depth) p y.2 := by
    have hbase := Hbase x hx y hy hp
    ext j
    rw [← physical_ancestor D a (2^m) p (u+6) depth (by omega) x.2 j,
      ← physical_ancestor D a (2^m) p (u+6) depth (by omega) y.2 j, hbase]
  have hparent := congrArg (ancestor (u+12) (depth+9)) hphase
  rw [relative_ancestor D a (2^m) p (u+12) (depth+9) (by omega) x.1,
    relative_ancestor D a (2^m) p (u+12) (depth+9) (by omega) y.1] at hparent
  exact Prod.ext hheight (Prod.ext hphysical hparent)

/-- A fixed pre-third witness chooses the total descended label. The
readback below makes it independent of that witness on occupied pairs. -/
def onPair : Parent × E4 → ℤ × (Index × Parent) :=
  NativeMergedPointOffsets.pointOffset U
    (geometricPairKey D a m p s P hP hd F Fcfg R u) (jointKey D a m p R depth)

include hR hdepth Hbase in
lemma onPair_readback (x : Fin n × Index) (hx : x ∈ U) :
    onPair D a m p s P hP hd F Fcfg R u depth U
        (geometricPairKey D a m p s P hP hd F Fcfg R u x) = jointKey D a m p R depth x := by
  obtain ⟨y, hy, he, hval⟩ := NativeMergedPointOffsets.pointOffset_witness U
    (geometricPairKey D a m p s P hP hd F Fcfg R u) (jointKey D a m p R depth)
    (geometricPairKey D a m p s P hP hd F Fcfg R u x) (mem_image_of_mem _ hx)
  exact hval.trans (constant_on_pair D a m p s P hP hd F Fcfg R u depth hR hdepth U Hbase y x hy hx he)

include hR hdepth Hbase in
/-- Every original joint fiber is exactly one class in the deduplicated
G. In particular the original fiber images form a genuine partition. -/
theorem class_image (T : Finset (Fin n × Index)) (hTU : T ⊆ U)
    (x : Fin n × Index) (hx : x ∈ T) :
    let pair := geometricPairKey D a m p s P hP hd F Fcfg R u
    let key := jointKey D a m p R depth
    let cls := onPair D a m p s P hP hd F Fcfg R u depth U
    (T.filter (fun z => key z = key x)).image pair =
      (T.image pair).filter (fun z => cls z = cls (pair x)) := by
  intro pair key cls
  have hr (z : Fin n × Index) (hz : z ∈ T) : cls (pair z) = key z :=
    onPair_readback D a m p s P hP hd F Fcfg R u depth hR hdepth U Hbase z (hTU hz)
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    refine mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mp hw).1, ?_⟩
    rw [hr w (mem_filter.mp hw).1, hr x hx]
    exact (mem_filter.mp hw).2
  · intro hz
    obtain ⟨hz, he⟩ := mem_filter.mp hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    rw [hr w hw, hr x hx] at he
    exact mem_image.mpr ⟨w, mem_filter.mpr ⟨hw, he⟩, rfl⟩

include hR hdepth Hbase in
/-- Reuse the existing weighted population theorem on the actual
well-defined descended label. Pair and joint HU each pay Q². -/
theorem geometric_uniformity (T : Finset (Fin n × Index)) (hTU : T ⊆ U) (Q : ℕ)
    (HP : HasUniformFibers T Q (geometricPairKey D a m p s P hP hd F Fcfg R u))
    (HJ : HasUniformFibers T Q (jointKey D a m p R depth)) :
    HasUniformFibers (T.image (geometricPairKey D a m p s P hP hd F Fcfg R u)) (Q^2)
      (onPair D a m p s P hP hd F Fcfg R u depth U) := by
  let pair := geometricPairKey D a m p s P hP hd F Fcfg R u
  let key := jointKey D a m p R depth
  let cls := onPair D a m p s P hP hd F Fcfg R u depth U
  have HC : HasUniformFibers T Q (fun z => cls (pair z)) := by
    apply NativeConditionedPairMenu.uniformity_congr T key (fun z => cls (pair z)) Q
      (fun z hz => (onPair_readback D a m p s P hP hd F Fcfg R u depth hR hdepth U Hbase z (hTU hz)).symm)
    exact HJ
  have hh := point_class_homogeneity T pair cls Q HP HC
  intro x hx y hy
  simpa only [show (Q^2)^2=Q^4 by ring] using hh x hx y hy

end Keys
end NativeJointKeyDescent
