import Theorems.Thm_StickyKakeya4_native_population_parent_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeNestedPopulationSelection
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeActivePhasePopulation
open NativePopulationParentSelection NativeDyadicParentCells NativeCoarseAncestorCounts

/-- A genuine fine phase label has exactly its original full incidence
fiber after restriction to its actual dyadic ancestor. -/
lemma parentEdges_nested_eq {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m c : ℕ) (hmc : m ≤ c) (E : Finset (Fin n × Index)) (p q : Parent)
    (hqp : ancestor c m q=p) :
    parentEdges D a (2^c) (parentEdges D a (2^m) E p) q=parentEdges D a (2^c) E q := by
  ext z
  simp only [parentEdges,mem_filter]
  constructor
  · rintro ⟨⟨hz,_hp⟩,hq⟩
    exact ⟨hz,hq⟩
  · rintro ⟨hz,hq⟩
    refine ⟨⟨hz,?_⟩,hq⟩
    rw [←parent_ancestor_eq D a hmc z.1,hq,hqp]

lemma nested_parent_subset {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m c : ℕ) (hmc : m ≤ c) (E : Finset (Fin n × Index)) (p q : Parent)
    (hqp : ancestor c m q=p) :
    parentEdges D a (2^c) E q⊆parentEdges D a (2^m) E p := by
  rw [←parentEdges_nested_eq D a m c hmc E p q hqp]
  exact filter_subset _ _

/-- Partition the full outer R-parent and its unchanged original E fibers.
One nested parent has the SAME paid population density, with no additional
loss, source selection, or uniformity assumption. -/
theorem exists_nested_population_parent {n : ℕ} (D : FiniteScaleSource n)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (a : ℝ) (m c : ℕ) (hmc : m ≤ c) (p : Parent)
    (hEp : (parentEdges D a (2^m) E p).Nonempty)
    (mu : ℝ) (hmu : 0 < mu)
    (hret : mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card) :
    ∃q∈descendants D R a c m p,ancestor c m q=p ∧
      (parentEdges D a (2^c) E q).Nonempty ∧
      parentEdges D a (2^c) E q⊆parentEdges D a (2^m) E p ∧
      mu*(R.filter (fun i => parentLabel D a (2^c) i=q)).card ≤
        D.thickness*(parentEdges D a (2^c) E q).card := by
  let Rp := R.filter (fun i => parentLabel D a (2^m) i=p)
  let Ep := parentEdges D a (2^m) E p
  have hERp : Ep⊆retained original Rp := by
    rw [←parent_retained_eq D original R a (2^m) p]
    exact filter_subset_filter _ hE
  obtain ⟨q,hq,hRq,hEq,hpop⟩ := exists_population_parent D original Rp Ep hERp hEp a (2^c) mu hmu hret
  have hqdesc : q∈descendants D R a c m p := by
    rwa [←image_parent_fiber_eq_descendants D R a hmc p]
  have hqp : ancestor c m q=p := (mem_filter.mp hqdesc).2
  have hRf : Rp.filter (fun i => parentLabel D a (2^c) i=q)=
      R.filter (fun i => parentLabel D a (2^c) i=q) :=
    fiber_in_ancestor_eq D R a hmc p q hRq
  have hEf : parentEdges D a (2^c) Ep q=parentEdges D a (2^c) E q :=
    parentEdges_nested_eq D a m c hmc E p q hqp
  rw [hRf,hEf] at hpop
  rw [hEf] at hEq
  exact ⟨q,hqdesc,hqp,hEq,nested_parent_subset D a m c hmc E p q hqp,hpop⟩

end NativeNestedPopulationSelection
