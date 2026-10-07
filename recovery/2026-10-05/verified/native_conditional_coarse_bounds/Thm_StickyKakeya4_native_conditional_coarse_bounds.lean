import Theorems.Thm_StickyKakeya4_native_relative_coarse_readback
import Theorems.Thm_StickyKakeya4_native_relative_coarse_multiplicity_bridge
import Theorems.Thm_StickyKakeya4_native_pair_scale_budget
import Theorems.Thm_StickyKakeya4_native_scale_menu_successor
import Theorems.Thm_StickyKakeya4_native_joint_uniform_coarse_relations

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeConditionalCoarseBounds
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentDensityCore NativeLocalParentSource
open NativeIncidenceMultiplicityTower NativeRelativeCoarseReadback NativeRelativeCoarseMultiplicityBridge
open NativeJointUniformCoarseRelations NativePairScaleBudget NativeCoarseDirectionThinning
open scoped ENNReal BigOperators

/-- The original conditional physical shadow compares to the literal relative
full shadow of the admitted local source. Both sides are read from the same
old incidence subset; fixed full-backbone representatives are never replaced. -/
theorem physical_to_relative {n : ℕ} {D : FiniteScaleSource n} {eta a e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (level m f : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmf : m ≤ f) (hf : f ≤ level)
    (p : Parent) (hQ : (parentLabels D R a (2^m) p).Nonempty)
    (hlabels : ∀z∈E,z.1∈parentLabels D R a (2^m) p)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) e)
    (rad : ℕ)
    (hpair : HasUniformFibers E rad (doublePair h R a m p hQ (2^(f-m+6))))
    (hpoint : HasUniformFibers E rad (fun z => (doublePair h R a m p hQ (2^(f-m+6)) z).2)) :
    (NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level f E)).toReal  ≤ 
      (41472:ℝ)*(rad:ℝ)^4*(NativeFiniteKakeyaCounts.multiplicity
        (NativeFullCoarseShadow.fullSource hS univ 0 (level-m+6) (f-m+6)
          (incidences (sourceCells D R E a (2^m) p)))).toReal := by
  let ell := f-m+6
  let repG := representative h R a (2^f)
  let repR := originalRepresentative h R a m p hQ (2^ell)
  have hEq : m+ell-6=f := by dsimp [ell]; omega
  have hER : ∀z∈E,z.1∈R := fun z hz => (mem_filter.mp (hlabels z hz)).1
  have hh := conditional_global_relative_multiplicity h original horiginal ha level m ell hdy
    (by dsimp [ell]; omega) (by omega) p repG repR E hE
    (fun z hz => (mem_filter.mp (hlabels z hz)).2)
    (fun z hz => by
      rw [hEq]
      exact (representative_spec h R a (2^f) (mem_image_of_mem _ (hER z hz))).2)
    (fun z hz => originalRepresentative_label h R a m p hQ (2^ell) z.1 (hlabels z hz))
    rad hpair hpoint
  rw [hEq] at hh
  have hImage : E.image (globalPair D a (2^f) repG) =
      NativeCoarseShadingCapacity.coarse D a (2^f) (NativeCoarseDyadicShading.block level f) repG E := by
    apply image_congr
    intro z _hz
    exact globalPair_eq_actualPair h R a level f hdy hf z
  rw [hImage] at hh
  rw [NativeCoarsePointMultiplicity.full_source_multiplicity_real h R a level f E hER,
    relative_full_multiplicity_readback h R E a level m (f-m+6) p hQ hlabels hS hdy
      (hmf.trans hf) (by omega)]
  exact hh

/-- The lower conditional physical bound uses the exact old incidence tower
and the already-matched original parents, with its own forward 125 comparison.
No inverse relative-time menu is asserted or needed. -/
theorem physical_lower {n : ℕ} {D : FiniteScaleSource n} {eta a kappa seed gamma : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hER : ∀z∈E,z.1∈R) (level m f : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hmf : m ≤ f) (hf : f ≤ level) (p : Parent) (rad : ℕ)
    (hparent : D.thickness^seed*(((2^m:ℕ):ℝ)*D.thickness/64)^(-kappa)  ≤ 
      multiplicity (parentEdges D a (2^m) E p))
    (hchildren : ∀q,(parentEdges D a (2^f) E q).Nonempty →
      multiplicity (parentEdges D a (2^f) E q)  ≤ 
        D.thickness^(-seed)*(((2^f:ℕ):ℝ)*D.thickness/64)^(-kappa))
    (hpair : HasUniformFibers (parentEdges D a (2^m) E p) rad (physicalPair h R a level f))
    (hpoint : HasUniformFibers (parentEdges D a (2^m) E p) rad (physicalPoint h R a level f))
    (hcost : (125:ℝ)*(rad:ℝ)^4 ≤ D.thickness^(-(2*gamma))) :
    D.thickness^(2*seed+2*gamma)*(64/((2^(f-m+6):ℕ):ℝ))^(-kappa)  ≤ 
      (NativeFiniteKakeyaCounts.multiplicity
        (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) E p))).toReal := by
  let Ep := parentEdges D a (2^m) E p
  have hd := h.1.2.1
  have hEp : Ep⊆incidences original := (filter_subset _ _).trans hE
  have hEpR : ∀z∈Ep,z.1∈R := fun z hz => hER z (mem_filter.mp hz).1
  have hbridge := NativeCoarsePointMultiplicity.multiplicity_le_full_source h original horiginal ha
    R Ep hEp hEpR level f hdy hf rad hpair hpoint
  apply NativePairScaleBudget.conditional_lower Ep (parentLabel D a (2^f)) hd
    (by positivity) (by positivity) (by positivity) (relative_local_product hmf)
    rad ENNReal.toReal_nonneg hparent _ hbridge hcost
  intro q hq
  have hn := parent_nonempty Ep (parentLabel D a (2^f)) hq
  change (parentEdges D a (2^f) (parentEdges D a (2^m) E p) q).Nonempty at hn
  have he := NativeScaleMenuSuccessor.nested_parentEdges_eq D a E hmf p q hn
  change multiplicity (parentEdges D a (2^f) (parentEdges D a (2^m) E p) q)  ≤  _
  rw [he]
  exact hchildren q (he ▸ hn)

end NativeConditionalCoarseBounds
