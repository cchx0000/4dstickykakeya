import Theorems.Thm_StickyKakeya4_native_saturated_point_angular_lower
import Theorems.Thm_StickyKakeya4_native_dyadic_parent_cells

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeSaturatedAncestorAngularLower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalPointSaturation NativeJointUniformCoarseRelations NativeActualAngularMenuLower
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeOriginalCellChartGeometry
open NativeOriginalPointAngularLower NativeIncidenceMultiplicityTower NativeOriginalCoarseTupleMenu
open NativeIncidentRankSelection NativePointAngularParentFibers NativeDyadicParentCells

/-- A fine original phase fiber lies in its unique scheduled ancestor.
Only the already installed ancestor formalPair uniformity is used. -/
theorem ancestor_point_fiber_upper {n : ℕ} (D : FiniteScaleSource n)
    (E1 S : Finset (Fin n × Index)) (hS1 : S⊆ E1) (a : ℝ) (c g Q1 : ℕ) (hcg : c≤ g)
    (HRef : HasUniformFibers E1 Q1 (formalPair D a c)) (U : ℝ) (hU : 0≤ U)
    (hUpper : ∀t,(parentEdges D a (2^c) E1 t).Nonempty →
      multiplicity (parentEdges D a (2^c) E1 t)≤ U) (k : Index) (t : Parent) :
    (((pointSet S k).filter (fun z => parentLabel D a (2^g) z.1=t)).card:ℝ)≤ (Q1:ℝ)^2*U := by
  have hsub : (pointSet S k).filter (fun z => parentLabel D a (2^g) z.1=t)⊆ 
      (pointSet S k).filter (fun z => parentLabel D a (2^c) z.1=ancestor g c t) := by
    intro z hz
    obtain ⟨hz,hzt⟩ := mem_filter.mp hz
    refine mem_filter.mpr ⟨hz,?_⟩
    rw [←parent_ancestor_eq D a hcg z.1,hzt]
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans
    (retained_point_parent_fiber_upper D E1 S hS1 a c Q1 HRef U hU hUpper k (ancestor g c t))

/-- On a whole-original-point selection the reference mean controls each
surviving point directly. Thus only Q2 squared is needed, with no second
point-mean comparison and no assumption of off-menu E1 uniformity. -/
theorem saturated_ancestor_point_lower {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E1 E S : Finset (Fin n × Index)) (HS : Saturated E S Prod.snd)
    (hS1 : S⊆ E1) (hS : S⊆ incidences original)
    (m ell c : ℕ) (hell : 3≤ ell) (hcg : c≤ m+ell-3)
    (hscale : ((2^(m+ell-3):ℕ):ℝ)*D.thickness≤ 1) (p : Parent) (Q1 Q2 : ℕ)
    (HRef : HasUniformFibers E1 Q1 (formalPair D a c))
    (HReferencePoint : HasUniformFibers E Q2 Prod.snd)
    (U : ℝ) (hU : 0≤ U)
    (hUpper : ∀t,(parentEdges D a (2^c) E1 t).Nonempty →
      multiplicity (parentEdges D a (2^c) E1 t)≤ U)
    (k : Index) (hk : k∈S.image Prod.snd) :
    multiplicity E≤ 343*(Q1:ℝ)^2*(Q2:ℝ)^2*U*(pointMenu D m ell p S k).card := by
  have hMean : multiplicity E≤ (Q2:ℝ)^2*(pointSet S k).card := by
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
    have hEq := original_fiber_eq E S Prod.snd HS z hz
    change multiplicity E≤ (Q2:ℝ)^2*(S.filter (fun y => y.2=z.2)).card
    rw [hEq]
    exact mean_le_point_fiber E Q2 HReferencePoint z.2 (mem_image_of_mem _ (HS.1 hz))
  have hFib (t : Parent) := ancestor_point_fiber_upper D E1 S hS1 a c (m+ell-3) Q1 hcg HRef U hU hUpper k t
  have hCount : ((pointSet S k).card:ℝ)≤ (Q1:ℝ)^2*U*(pointParents D a (2^(m+ell-3)) S k).card := by
    have hh := FinePointSlabGeometry.card_le_real_mul_of_fibers (pointSet S k)
      (pointParents D a (2^(m+ell-3)) S k) (fun z => parentLabel D a (2^(m+ell-3)) z.1)
      ((Q1:ℝ)^2*U) (fun z hz => mem_image_of_mem _ hz) (fun t _ht => hFib t)
    simpa only [mul_comm] using hh
  have hAngular := pointParents_card_le_angular h original horiginal ha (2^(m+ell-3)) hscale S hS k
  have hAngularR : ((pointParents D a (2^(m+ell-3)) S k).card:ℝ)≤ 
      343*(pointMenu D m ell p S k).card := by
    rw [pointMenu_card D a m ell hell p S k]
    exact_mod_cast hAngular
  calc
    _ ≤  (Q2:ℝ)^2*(pointSet S k).card := hMean
    _ ≤  (Q2:ℝ)^2*((Q1:ℝ)^2*U*(pointParents D a (2^(m+ell-3)) S k).card) :=
      mul_le_mul_of_nonneg_left hCount (sq_nonneg _)
    _ ≤  (Q2:ℝ)^2*((Q1:ℝ)^2*U*(343*(pointMenu D m ell p S k).card)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAngularR (mul_nonneg (sq_nonneg _) hU)) (sq_nonneg _)
    _ = _ := by ring

end NativeSaturatedAncestorAngularLower
