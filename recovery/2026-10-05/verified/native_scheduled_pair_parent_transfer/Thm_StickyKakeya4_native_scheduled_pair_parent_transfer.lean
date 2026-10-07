import Theorems.Thm_StickyKakeya4_native_coarse_scale_reverse
import Theorems.Thm_StickyKakeya4_native_conditioned_pair_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000

noncomputable section
namespace NativeScheduledPairParentTransfer
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeConditionedPairMenu NativeDyadicParentCells
open NativeCoarseScaleInterpolation

/-- A diagonal conditioned label repeats its own fine phase coordinate.
Thus the actual first-stage diagonal relation is precisely fine-pair equality. -/
lemma diagonal_pair_fiber_eq {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level fine : ℕ) (E : Finset (Fin n × Index)) (x : Fin n × Index) :
    E.filter (fun z => conditionedGlobalPair h R a level fine fine z=
      conditionedGlobalPair h R a level fine fine x)=
      E.filter (fun z => actualPair h R a level fine z=actualPair h R a level fine x) := by
  apply filter_congr
  intro z _hz
  constructor
  · exact fun hz => congrArg Prod.snd hz
  · intro hz
    have hf : parentLabel D a (2^fine) z.1=parentLabel D a (2^fine) x.1 :=
      congrArg (fun v : Parent × Index => v.1) hz
    exact Prod.ext hf hz

theorem diagonal_pair_uniformity {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level fine : ℕ) (E : Finset (Fin n × Index)) (Q : ℕ)
    (HU : HasUniformFibers E Q (conditionedGlobalPair h R a level fine fine)) :
    HasUniformFibers E Q (actualPair h R a level fine) := by
  intro x hx y hy
  rw [←diagonal_pair_fiber_eq h R a level fine E x,←diagonal_pair_fiber_eq h R a level fine E y]
  exact HU x hx y hy

/-- Every finer actual pair determines the literal ancestor of its phase
coordinate, even when the ancestor depth was never installed in a menu. -/
lemma fine_pair_determines_parent {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level m fine : ℕ) (hmf : m ≤ fine) (x y : Fin n × Index)
    (he : actualPair h R a level fine x=actualPair h R a level fine y) :
    parentLabel D a (2^m) x.1=parentLabel D a (2^m) y.1 := by
  have hh := congrArg (fun v : Parent × Index => ancestor fine m v.1) he
  change ancestor fine m (parentLabel D a (2^fine) x.1)=
    ancestor fine m (parentLabel D a (2^fine) y.1) at hh
  simpa only [parent_ancestor_eq D a hmf] using hh

lemma parent_fine_pair_fiber_eq {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level m fine : ℕ) (hmf : m ≤ fine) (E : Finset (Fin n × Index)) (p : Parent)
    (x : Fin n × Index) (hx : parentLabel D a (2^m) x.1=p) :
    (parentEdges D a (2^m) E p).filter
      (fun z => actualPair h R a level fine z=actualPair h R a level fine x)=
      E.filter (fun z => actualPair h R a level fine z=actualPair h R a level fine x) := by
  ext z
  simp only [parentEdges,mem_filter]
  constructor
  · exact fun hz => ⟨hz.1.1,hz.2⟩
  · intro hz
    exact ⟨⟨hz.1,(fine_pair_determines_parent h R a level m fine hmf z x hz.2).trans hx⟩,hz.2⟩

/-- This restriction uses whole finer fibers, not a new conditioned
uniformity assumption at the requested outer parent. -/
theorem parent_fine_pair_uniformity {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level m fine : ℕ) (hmf : m ≤ fine) (E : Finset (Fin n × Index)) (Q : ℕ)
    (HU : HasUniformFibers E Q (actualPair h R a level fine)) (p : Parent) :
    HasUniformFibers (parentEdges D a (2^m) E p) Q (actualPair h R a level fine) := by
  intro x hx y hy
  rw [parent_fine_pair_fiber_eq h R a level m fine hmf E p x (mem_filter.mp hx).2,
    parent_fine_pair_fiber_eq h R a level m fine hmf E p y (mem_filter.mp hy).2]
  exact HU x (mem_filter.mp hx).1 y (mem_filter.mp hy).1

/-- The first-stage diagonal relation supplies the finer-pair uniformity
inside every actual earlier phase parent, with the same radix. -/
theorem diagonal_parent_uniformity {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level m fine : ℕ) (hmf : m ≤ fine) (E : Finset (Fin n × Index)) (Q : ℕ)
    (HU : HasUniformFibers E Q (conditionedGlobalPair h R a level fine fine)) (p : Parent) :
    HasUniformFibers (parentEdges D a (2^m) E p) Q (actualPair h R a level fine) :=
  parent_fine_pair_uniformity h R a level m fine hmf E Q
    (diagonal_pair_uniformity h R a level fine E Q HU) p

/-- A finer actual pair has at most27 coarser actual pair images. Its phase
ancestor is exact; only the three spatial representative-rounding choices remain. -/
theorem coarse_pair_over_fine_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level f fine : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hff : f ≤ fine) (hfL : fine ≤ level) (v : Parent × Index) :
    ((E.filter (fun z => actualPair h R a level fine z=v)).image
      (actualPair h R a level f)).card ≤ 27 := by
  have hs : (E.filter (fun z => actualPair h R a level fine z=v)).image
      (actualPair h R a level f) ⊆
      (coarseMenu (2^(fine-f)) v.2).image (fun q => (ancestor fine f v.1,q)) := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
    obtain ⟨hzE,hzv⟩ := mem_filter.mp hz
    have hh := actual_pair_menu h original horiginal ha R level f fine hdy hff hfL z
      (hR z hzE) ((mem_incidences original z.1 z.2).mp (hE hzE))
    rw [hzv] at hh
    exact mem_image.mpr ⟨(actualPair h R a level f z).2,hh.2,Prod.ext hh.1.symm rfl⟩
  exact (card_le_card hs).trans (card_image_le.trans_eq (coarseMenu_card _ _))

end NativeScheduledPairParentTransfer
