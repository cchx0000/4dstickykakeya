import Theorems.Thm_StickyKakeya4_native_relative_coarse_readback
import Theorems.Thm_StickyKakeya4_native_joint_uniform_coarse_relations

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeConditionedPairMenu
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeLocalParentSource NativeJointUniformCoarseRelations
open NativeRelativeCoarseReadback SelfUniform

lemma conditioned_fiber_eq {A P X : Type*} [DecidableEq A] [DecidableEq P] [DecidableEq X]
    (E : Finset A) (parent : A → P) (f : A → X) (p : P) (x : A)
    (hx : parent x=p) :
    (E.filter (fun z => parent z=p)).filter (fun z => f z=f x) =
      E.filter (fun z => (parent z,f z)=(parent x,f x)) := by
  ext z
  simp only [mem_filter,Prod.mk.injEq,hx,and_assoc]

/-- A single conditioned equality relation controls every parent restriction;
there is no relation-menu entry for each source-dependent parent. -/
theorem conditioned_uniformity {A P X : Type*} [DecidableEq A] [DecidableEq P] [DecidableEq X]
    (E : Finset A) (parent : A → P) (f : A → X) (rad : ℕ)
    (H : HasUniformFibers E rad (fun z => (parent z,f z))) (p : P) :
    HasUniformFibers (E.filter (fun z => parent z=p)) rad f := by
  intro x hx y hy
  obtain ⟨hxE,hxp⟩ := mem_filter.mp hx
  obtain ⟨hyE,hyp⟩ := mem_filter.mp hy
  rw [conditioned_fiber_eq E parent f p x hxp,conditioned_fiber_eq E parent f p y hyp]
  exact H x hxE y hyE

lemma uniformity_congr {A X : Type*} [DecidableEq A] [DecidableEq X]
    (E : Finset A) (f g : A → X) (rad : ℕ)
    (heq : ∀z∈E,f z=g z) (H : HasUniformFibers E rad f) :
    HasUniformFibers E rad g := by
  have hf (x : A) (hx : x∈E) : E.filter (fun z => f z=f x)=E.filter (fun z => g z=g x) := by
    apply filter_congr
    intro z hz
    rw [heq z hz,heq x hx]
  intro x hx y hy
  rw [←hf x hx,←hf y hy]
  exact H x hx y hy

/-- Empty-shading representatives are fixed on the full original backbone
before E. The zero branch only makes this a total original-incidence map. -/
def fixedDoublePair {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (m ell : ℕ) (z : Fin n × Index) : Parent × Index :=
  let p := parentLabel D a (2^m) z.1
  if hp : (parentLabels D R a (2^m) p).Nonempty then
    doublePair h R a m p hp (2^ell) z else (0,0)

lemma fixedDoublePair_eq {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (m ell : ℕ) (p : Parent)
    (hp : (parentLabels D R a (2^m) p).Nonempty)
    (z : Fin n × Index) (hz : parentLabel D a (2^m) z.1=p) :
    fixedDoublePair h R a m ell z=doublePair h R a m p hp (2^ell) z := by
  simp only [fixedDoublePair,hz,dif_pos hp]

def conditionedGlobalPair {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level m f : ℕ) (z : Fin n × Index) : Parent × (Parent × Index) :=
  (parentLabel D a (2^m) z.1,physicalPair h R a level f z)

def conditionedGlobalPoint {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level m f : ℕ) (z : Fin n × Index) : Parent × Index :=
  (parentLabel D a (2^m) z.1,physicalPoint h R a level f z)

def conditionedRelativePair {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (m f : ℕ) (z : Fin n × Index) : Parent × (Parent × Index) :=
  (parentLabel D a (2^m) z.1,fixedDoublePair h R a m (f-m+6) z)

def conditionedRelativePoint {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (m f : ℕ) (z : Fin n × Index) : Parent × Index :=
  (parentLabel D a (2^m) z.1,(fixedDoublePair h R a m (f-m+6) z).2)

/-- All four restrictions are literal fibers of four original label maps. -/
theorem conditional_pair_uniformities {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m f rad : ℕ)
    (HG : HasUniformFibers E rad (conditionedGlobalPair h R a level m f))
    (HX : HasUniformFibers E rad (conditionedGlobalPoint h R a level m f))
    (HR : HasUniformFibers E rad (conditionedRelativePair h R a m f))
    (HY : HasUniformFibers E rad (conditionedRelativePoint h R a m f))
    (p : Parent) (hp : (parentLabels D R a (2^m) p).Nonempty) :
    let Ep := parentEdges D a (2^m) E p
    HasUniformFibers Ep rad (physicalPair h R a level f) ∧
    HasUniformFibers Ep rad (physicalPoint h R a level f) ∧
    HasUniformFibers Ep rad (doublePair h R a m p hp (2^(f-m+6))) ∧
    HasUniformFibers Ep rad (fun z => (doublePair h R a m p hp (2^(f-m+6)) z).2) := by
  refine ⟨conditioned_uniformity E (fun z => parentLabel D a (2^m) z.1) _ rad HG p,
    conditioned_uniformity E (fun z => parentLabel D a (2^m) z.1) _ rad HX p,?_,?_⟩
  · apply uniformity_congr _ (fixedDoublePair h R a m (f-m+6)) _ rad
    · intro z hz
      exact fixedDoublePair_eq h R a m (f-m+6) p hp z (mem_filter.mp hz).2
    · exact conditioned_uniformity E (fun z => parentLabel D a (2^m) z.1) _ rad HR p
  · apply uniformity_congr _ (fun z => (fixedDoublePair h R a m (f-m+6) z).2) _ rad
    · intro z hz
      exact congrArg Prod.snd (fixedDoublePair_eq h R a m (f-m+6) p hp z (mem_filter.mp hz).2)
    · exact conditioned_uniformity E (fun z => parentLabel D a (2^m) z.1) _ rad HY p

/-- Four equality relations for each ordered pair of scheduled scales. -/
def pairMenuSize (d g : ℕ) : ℕ := d+(g*g+(g*g+(g*g+g*g)))

lemma pairMenuSize_eq (d g : ℕ) : pairMenuSize d g=d+4*g^2 := by unfold pairMenuSize; ring

def pairRelationMenu {n d g level : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) :
    Fin (pairMenuSize d g) → (Fin n × Index) → (Fin n × Index) → Prop :=
  let ij := fun k : Fin (g*g) => (finProdFinEquiv.symm k : Fin g × Fin g)
  let m := fun k => (schedule (ij k).1).val
  let f := fun k => (schedule (ij k).2).val
  Fin.addCases Rel (Fin.addCases
    (fun k x y => conditionedGlobalPair h R a level (m k) (f k) x =
      conditionedGlobalPair h R a level (m k) (f k) y)
    (Fin.addCases
      (fun k x y => conditionedGlobalPoint h R a level (m k) (f k) x =
        conditionedGlobalPoint h R a level (m k) (f k) y)
      (Fin.addCases
        (fun k x y => conditionedRelativePair h R a (m k) (f k) x =
          conditionedRelativePair h R a (m k) (f k) y)
        (fun k x y => conditionedRelativePoint h R a (m k) (f k) x =
          conditionedRelativePoint h R a (m k) (f k) y))))

lemma pairRelationMenu_refl {n d g level : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀j x,Rel j x x) : ∀j x,pairRelationMenu h R a schedule Rel j x x := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro k x
    simpa only [pairRelationMenu,Fin.addCases_left] using H k x
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro _k _x
      simp only [pairRelationMenu,Fin.addCases_right,Fin.addCases_left]
    · intro k
      refine Fin.addCases ?_ ?_ k
      · intro _k _x
        simp only [pairRelationMenu,Fin.addCases_right,Fin.addCases_left]
      · intro k
        refine Fin.addCases ?_ ?_ k <;> intro _k _x <;>
          simp only [pairRelationMenu,Fin.addCases_right,Fin.addCases_left]

lemma pairRelationMenu_symm {n d g level : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀j x y,Rel j x y → Rel j y x) :
    ∀j x y,pairRelationMenu h R a schedule Rel j x y → pairRelationMenu h R a schedule Rel j y x := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro k x y hh
    simpa only [pairRelationMenu,Fin.addCases_left] using H k x y
      (by simpa only [pairRelationMenu,Fin.addCases_left] using hh)
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro _k _x _y hh
      simp only [pairRelationMenu,Fin.addCases_right,Fin.addCases_left] at hh ⊢
      exact hh.symm
    · intro k
      refine Fin.addCases ?_ ?_ k
      · intro _k _x _y hh
        simp only [pairRelationMenu,Fin.addCases_right,Fin.addCases_left] at hh ⊢
        exact hh.symm
      · intro k
        refine Fin.addCases ?_ ?_ k <;> intro _k _x _y hh <;>
          simp only [pairRelationMenu,Fin.addCases_right,Fin.addCases_left] at hh ⊢ <;> exact hh.symm

/-- The one uniformized old menu supplies every conditioned pair relation. -/
theorem pairRelationMenu_uniformities {n d g level : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (E : Finset (Fin n × Index)) (rad : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (pairRelationMenu h R a schedule Rel j) E x  ≤ 
        rad^2*degree (fun _ : Fin n × Index => 1) (pairRelationMenu h R a schedule Rel j) E y)
    (i j : Fin g) :
    HasUniformFibers E rad (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
    HasUniformFibers E rad (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val) ∧
    HasUniformFibers E rad (conditionedRelativePair h R a (schedule i).val (schedule j).val) ∧
    HasUniformFibers E rad (conditionedRelativePoint h R a (schedule i).val (schedule j).val) := by
  let k : Fin (g*g) := finProdFinEquiv (i,j)
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx y hy
    simpa only [pairRelationMenu,Fin.addCases_right,Fin.addCases_left,unit_degree_eq_fiber,k,
      Equiv.symm_apply_apply] using H (Fin.natAdd d (Fin.castAdd (g*g+(g*g+g*g)) k)) x y hx hy
  · intro x hx y hy
    simpa only [pairRelationMenu,Fin.addCases_right,Fin.addCases_left,unit_degree_eq_fiber,k,
      Equiv.symm_apply_apply] using H (Fin.natAdd d (Fin.natAdd (g*g) (Fin.castAdd (g*g+g*g) k))) x y hx hy
  · intro x hx y hy
    simpa only [pairRelationMenu,Fin.addCases_right,Fin.addCases_left,unit_degree_eq_fiber,k,
      Equiv.symm_apply_apply] using H (Fin.natAdd d (Fin.natAdd (g*g) (Fin.natAdd (g*g) (Fin.castAdd (g*g) k)))) x y hx hy
  · intro x hx y hy
    simpa only [pairRelationMenu,Fin.addCases_right,unit_degree_eq_fiber,k,
      Equiv.symm_apply_apply] using H (Fin.natAdd d (Fin.natAdd (g*g) (Fin.natAdd (g*g) (Fin.natAdd (g*g) k)))) x y hx hy

end NativeConditionedPairMenu
