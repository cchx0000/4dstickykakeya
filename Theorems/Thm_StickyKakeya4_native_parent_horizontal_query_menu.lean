import Theorems.Thm_StickyKakeya4_native_parent_slice_caller_menu
import Theorems.Thm_StickyKakeya4_native_anisotropic_global_source_bridge

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeParentHorizontalQueryMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeCoarseShadingUniformity
open NativeCoarseDirectionThinning SelfUniform

/-- Fixed additional caller size: two short-row equalities per horizontal
scale and the 1+K parent-slice equalities. Values may depend on the source. -/
def size (d K : ℕ) : ℕ := (d+K+K)+(1+K)

def relations {n d K : ℕ} {D : FiniteScaleSource n} {eta : ℝ} {X Y : Type*}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level m : ℕ) (depths : Fin K → ℕ)
    (point : Parent → Index → X) (classes : Parent → Fin K → X → Y)
    (old : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) :
    Fin (size d K) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.addCases
    (Fin.addCases
      (Fin.addCases old (fun j x y =>
        fixedPair D a level (depths j) (depths j) (representative h R a (2^(depths j))) x=
        fixedPair D a level (depths j) (depths j) (representative h R a (2^(depths j))) y))
      (fun j x y =>
        fixedPair D a level (depths j) m (representative h R a (2^(depths j))) x=
        fixedPair D a level (depths j) m (representative h R a (2^(depths j))) y))
    (NativeParentSliceCallerMenu.relations D a (2^m) point classes)

lemma relations_refl {n d K : ℕ} {D : FiniteScaleSource n} {eta : ℝ} {X Y : Type*}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level m : ℕ) (depths : Fin K → ℕ)
    (point : Parent → Index → X) (classes : Parent → Fin K → X → Y)
    (old : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hold : ∀i x,old i x x) :
    ∀i x,relations h R a level m depths point classes old i x x := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i x
        simpa only [relations,Fin.addCases_left] using hold i x
      · intro j x
        simp only [relations,Fin.addCases_left,Fin.addCases_right]
    · intro j x
      simp only [relations,Fin.addCases_left,Fin.addCases_right]
  · intro j x
    simpa only [relations,Fin.addCases_right] using
      NativeParentSliceCallerMenu.relations_refl D a (2^m) point classes j x

lemma relations_symm {n d K : ℕ} {D : FiniteScaleSource n} {eta : ℝ} {X Y : Type*}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level m : ℕ) (depths : Fin K → ℕ)
    (point : Parent → Index → X) (classes : Parent → Fin K → X → Y)
    (old : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hold : ∀i x y,old i x y → old i y x) :
    ∀i x y,relations h R a level m depths point classes old i x y →
      relations h R a level m depths point classes old i y x := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i x y H
        simp only [relations,Fin.addCases_left] at H ⊢
        exact hold i x y H
      · intro j x y H
        simp only [relations,Fin.addCases_left,Fin.addCases_right] at H ⊢
        exact H.symm
    · intro j x y H
      simp only [relations,Fin.addCases_left,Fin.addCases_right] at H ⊢
      exact H.symm
  · intro j x y H
    simp only [relations,Fin.addCases_right] at H ⊢
    exact NativeParentSliceCallerMenu.relations_symm D a (2^m) point classes j x y H

/-- Decode all original queries on the ONE selected E2. No later refinement
is performed and no off-menu uniformity is inferred. -/
theorem uniformities {n d K : ℕ} {D : FiniteScaleSource n} {eta : ℝ} {X Y : Type*}
    [DecidableEq X] [DecidableEq Y]
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level m : ℕ) (depths : Fin K → ℕ)
    (point : Parent → Index → X) (classes : Parent → Fin K → X → Y)
    (old : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀i x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1)
      (relations h R a level m depths point classes old i) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1)
          (relations h R a level m depths point classes old i) E y) :
    (∀i x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (old i) E x ≤
      Q^2*degree (fun _ : Fin n × Index => 1) (old i) E y) ∧
    (∀j,HasUniformFibers E Q
      (fixedPair D a level (depths j) (depths j) (representative h R a (2^(depths j)))) ∧
      HasUniformFibers E Q
      (fixedPair D a level (depths j) m (representative h R a (2^(depths j))))) ∧
    (∀p : Parent,
      HasUniformFibers (parentEdges D a (2^m) E p) Q (fun z => point p z.2) ∧
      ∀j,HasUniformFibers (parentEdges D a (2^m) E p) Q (fun z => classes p j (point p z.2))) ∧
    ∀p : Parent,∀j : Fin K,
      let A := (parentEdges D a (2^m) E p).image (fun z => point p z.2)
      ∀x∈A,∀y∈A,(A.filter (fun z => classes p j z=classes p j x)).card ≤
        Q^4*(A.filter (fun z => classes p j z=classes p j y)).card := by
  have HS : ∀j x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1)
      (NativeParentSliceCallerMenu.relations D a (2^m) point classes j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1)
          (NativeParentSliceCallerMenu.relations D a (2^m) point classes j) E y := by
    intro j x y hx hy
    simpa only [relations,Fin.addCases_right] using H (Fin.natAdd (d+K+K) j) x y hx hy
  refine ⟨?_,?_,?_,?_⟩
  · intro i x y hx hy
    simpa only [relations,Fin.addCases_left] using
      H (Fin.castAdd (1+K) (Fin.castAdd K (Fin.castAdd K i))) x y hx hy
  · intro j
    constructor
    · intro x hx y hy
      simpa only [relations,Fin.addCases_left,Fin.addCases_right,unit_degree_eq_fiber] using
        H (Fin.castAdd (1+K) (Fin.castAdd K (Fin.natAdd d j))) x y hx hy
    · intro x hx y hy
      simpa only [relations,Fin.addCases_left,Fin.addCases_right,unit_degree_eq_fiber] using
        H (Fin.castAdd (1+K) (Fin.natAdd (d+K) j)) x y hx hy
  · exact fun p => NativeParentSliceCallerMenu.parent_uniformities D a (2^m) point classes E Q HS p
  · exact fun p j => NativeParentSliceCallerMenu.parent_occupied_class_counts D a (2^m) point classes E Q HS p j

end NativeParentHorizontalQueryMenu
