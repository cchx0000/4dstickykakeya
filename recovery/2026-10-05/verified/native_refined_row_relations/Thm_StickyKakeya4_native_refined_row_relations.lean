import Theorems.Thm_StickyKakeya4_native_rank_refined_reference_core
import Theorems.Thm_StickyKakeya4_native_coarse_shading_uniformity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeRefinedRowRelations
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeCubicalIncidenceCounts NativeLocalPairUniformCore
open NativeLocalPairFibers NativeJointUniformCoarseRelations NativeCoarseShadingUniformity
open NativeCoarseDirectionThinning NativeRankRefinedReferenceCore SelfUniform

/-- Spatial coarsening of the actual scheduled fine-parent row keeps that
fine parent's original full-R representative at every spatial depth. -/
def rowPair {n g level : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (schedule : Fin g → Fin (level+1)) (i j : Fin g) (z : Fin n × Index) : Parent × Index :=
  fixedPair D a level (schedule i).val (schedule j).val
    (representative h R a (2^(schedule i).val)) z

/-- Exactly g² extra equality relations, including the fine-row diagonal.
The number is fixed before the second uniformization depth and source cutoff. -/
def rowRelationMenu {n d g level : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) :
    Fin (d+g*g) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.addCases Rel (fun k x y =>
    rowPair h R a schedule (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 x =
      rowPair h R a schedule (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 y)

lemma rowRelationMenu_refl {n d g level : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀j x,Rel j x x) : ∀j x,rowRelationMenu h R a schedule Rel j x x := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro k x
    simpa only [rowRelationMenu,Fin.addCases_left] using H k x
  · intro k x
    simp only [rowRelationMenu,Fin.addCases_right]

lemma rowRelationMenu_symm {n d g level : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀j x y,Rel j x y → Rel j y x) :
    ∀j x y,rowRelationMenu h R a schedule Rel j x y → rowRelationMenu h R a schedule Rel j y x := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro k x y hh
    simpa only [rowRelationMenu,Fin.addCases_left] using
      H k x y (by simpa only [rowRelationMenu,Fin.addCases_left] using hh)
  · intro k x y hh
    simp only [rowRelationMenu,Fin.addCases_right] at hh ⊢
    exact hh.symm

theorem rowRelationMenu_old {n d g level : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (rowRelationMenu h R a schedule Rel j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (rowRelationMenu h R a schedule Rel j) E y) :
    ∀j x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Rel j) E x ≤
      Q^2*degree (fun _ : Fin n × Index => 1) (Rel j) E y := by
  intro j x y hx hy
  simpa only [rowRelationMenu,Fin.addCases_left] using H (Fin.castAdd (g*g) j) x y hx hy

theorem rowRelationMenu_uniformities {n d g level : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (rowRelationMenu h R a schedule Rel j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (rowRelationMenu h R a schedule Rel j) E y) :
    ∀i j,HasUniformFibers E Q (rowPair h R a schedule i j) := by
  intro i j x hx y hy
  let k : Fin (g*g) := finProdFinEquiv (i,j)
  simpa only [rowRelationMenu,Fin.addCases_right,unit_degree_eq_fiber,k,
    Equiv.symm_apply_apply] using H (Fin.natAdd d k) x y hx hy

/-- One actual rank refinement installs the finite spatial row relations,
preserves the caller's relations, and obtains finest-depth richness. Its
retention cost is the ENLARGED G, and E2 is never called an old IsCore. -/
theorem exists_refined_row_core {n d g level : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (hsmall : D.thickness ≤ 1/8) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index))
    (hE1 : E1 ⊆ retained original R) (hE1ne : E1.Nonempty) (hF : F ⊆ E1)
    (F1 : ℕ) (hF1 : 0 < F1) (hret1 : (incidences original).card ≤ F1*E1.card)
    (lambda : ℝ) (hlambda : 0 < lambda) (hrank : lambda*(E1.card:ℝ) ≤ F.card)
    (L2 : ℕ) (hL2 : 0 < L2) (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hrefl : ∀j x,Rel j x x) (hsym : ∀j x y,Rel j x y → Rel j y x) :
    let Q2 := NativeSourceSizeBounds.radix F.card L2
    let G := retentionCost (d+g*g) 1 L2
    ∃E2 ⊆ F,E2.Nonempty ∧ E2 ⊆ retained original R ∧ F.card ≤ G*E2.card ∧
      lambda/((F1:ℝ)*G)*NativeIncidenceMultiplicityTower.multiplicity (incidences original) ≤
        NativeIncidenceMultiplicityTower.multiplicity E2 ∧
      (∀j x y,x∈E2 → y∈E2 → degree (fun _ : Fin n × Index => 1) (Rel j) E2 x ≤
        Q2^2*degree (fun _ : Fin n × Index => 1) (Rel j) E2 y) ∧
      (∀i j,HasUniformFibers E2 Q2 (rowPair h R a schedule i j)) ∧
      (∀e,e∈E2 → D.thickness^eta*(2^level:ℕ)/
        (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E2 (localPair D a (2^level) e)).card) := by
  obtain ⟨E2,hE2F,hE2ne,hE2old,hret2,hnear,hU,hRich,_hImages⟩ :=
    exists_refined_reference_core h original horiginal ha hsmall R E1 F hE1 hE1ne hF
      F1 hF1 hret1 lambda hlambda hrank (d+g*g) 1 L2 (by omega) hL2
      (rowRelationMenu h R a schedule Rel) (rowRelationMenu_refl h R a schedule Rel hrefl)
      (rowRelationMenu_symm h R a schedule Rel hsym)
      (fun _ : Fin 1 => 2^level) (fun _ => by positivity)
      (fun _ => by rw [NativeDyadicParentCells.dyadic_fine_scale hdy]; norm_num)
      0 1 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
  refine ⟨E2,hE2F,hE2ne,hE2old,hret2,hnear,
    rowRelationMenu_old h R a schedule Rel E2 _ hU,
    rowRelationMenu_uniformities h R a schedule Rel E2 _ hU,?_⟩
  exact hRich 0

end NativeRefinedRowRelations
