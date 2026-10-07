import Theorems.Thm_StickyKakeya4_native_joint_local_coarse_upper
import Theorems.Thm_StickyKakeya4_native_coarse_point_multiplicity
import Theorems.Thm_StickyKakeya4_native_parent_average_uniformity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeJointUniformCoarseRelations
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeOriginalParentDensityCore NativeUnitParentNormalization NativeActualLocalAdmission
open NativeFixedCompactKakeyaExponent NativeJointLocalCoarseUpper SelfUniform
open scoped ENNReal BigOperators

def menuSize (d g : ℕ) : ℕ := d+(g+(g+g))

lemma menuSize_eq (d g : ℕ) : menuSize d g = d+3*g := by unfold menuSize; omega

def physicalPair {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level m : ℕ) (z : Fin n × Index) : Parent × Index :=
  NativeCoarseShadingCapacity.label D a (2^m) (NativeCoarseDyadicShading.block level m)
    (NativeCoarseDirectionThinning.representative h R a (2^m)) z

def physicalPoint {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level m : ℕ) (z : Fin n × Index) : Index :=
  NativeCoarsePointMultiplicity.pointLabel D a (2^m) (NativeCoarseDyadicShading.block level m)
    (NativeCoarseDirectionThinning.representative h R a (2^m)) z

def formalPair {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (z : Fin n × Index) : Parent × Index := (parentLabel D a (2^m) z.1,z.2)

/-- Three literal old-incidence equality relations per scheduled scale:
physical coarse pair, physical coarse point, and formal parent/fine point. -/
def relationMenu {n d g level : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) :
    Fin (menuSize d g) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.addCases Rel (Fin.addCases
    (fun j x y => physicalPair h R a level (schedule j).val x = physicalPair h R a level (schedule j).val y)
    (Fin.addCases
      (fun j x y => physicalPoint h R a level (schedule j).val x = physicalPoint h R a level (schedule j).val y)
      (fun j x y => formalPair D a (schedule j).val x = formalPair D a (schedule j).val y)))

def HasUniformFibers {A B : Type*} [DecidableEq A] [DecidableEq B]
    (E : Finset A) (rad : ℕ) (f : A → B) : Prop :=
  ∀x∈E,∀y∈E,(E.filter (fun z => f z=f x)).card ≤
    rad^2*(E.filter (fun z => f z=f y)).card

lemma unit_degree_eq_fiber {A B : Type*} [DecidableEq A] [DecidableEq B]
    (E : Finset A) (f : A → B) (x : A) :
    degree (fun _ : A => 1) (fun x y => f x=f y) E x =
      (E.filter (fun z => f z=f x)).card := by
  rw [degree,card_eq_sum_ones,sum_filter]
  apply sum_congr rfl
  intro z _hz
  by_cases hf : f x=f z
  · simp only [if_pos hf,if_pos hf.symm]
  · simp only [if_neg hf,if_neg (Ne.symm hf)]

/-- Exact analytic outputs retained from the one-E joint construction. -/
def HasJointScale {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m : ℕ) (e zeta theta epsilon : ℝ) : Prop :=
  let rep := NativeCoarseDirectionThinning.representative h R a (2^m)
  (∃ (Q : Finset Parent)
    (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤
      dist (direction (D.line (rep p))) (direction (D.line (rep q)))),
    Q⊆R.image (parentLabel D a (2^m)) ∧ Q.Nonempty ∧
    let C := NativeCoarseCellSource.source h a level m Q rep E hsep
    IsWangZakharovNativeFiniteInput C e ∧ (∀i,C.line i∈fixedCompactClass) ∧
    C.thickness=64/((2^m:ℕ):ℝ) ∧
    D.thickness^(5*zeta) ≤ (wzTotalShadingVolume C).toReal ∧
    (ENNReal.ofReal D.thickness).rpow (7*zeta)*
      NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level m E) ≤
        NativeFiniteKakeyaCounts.multiplicity C ∧
    NativeFiniteKakeyaCounts.multiplicity C ≤
      (ENNReal.ofReal (64/((2^m:ℕ):ℝ))).rpow (-extremalExponent-epsilon)) ∧
  NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level m E) ≤
    (ENNReal.ofReal D.thickness).rpow (-theta)*
      (ENNReal.ofReal (64/((2^m:ℕ):ℝ))).rpow (-extremalExponent-epsilon) ∧
  ∀p,(parentEdges D a (2^m) E p).Nonempty →
    let Ep := parentEdges D a (2^m) E p
    let S := source h R Ep a m p
    IsWangZakharovNativeFiniteInput S e ∧
      (∀i,S.line i ∈ fixedCompactClass) ∧ HasExactTrace h R Ep a m p ∧
      NativeFiniteKakeyaCounts.multiplicity S ≤
        (ENNReal.ofReal S.thickness).rpow (-extremalExponent-epsilon) ∧
      (Ep.card:ℝ)/(Ep.image Prod.snd).card ≤
        D.thickness^(-theta)*S.thickness^(-extremalExponent-epsilon)

/-- The three actual scale relations are built before the one core E is
selected. The physical coarse bridge follows from their derived uniformity;
no degree or geometry certificate is supplied by the caller. -/
theorem joint_uniform_coarse_relations
    (epsilon window theta : ℝ) (hepsilon : 0 < epsilon)
    (hw : 0 < window) (htheta : 0 < theta) (d g : ℕ) (hdg : 0 < d+g) :
    ∃ (e zeta : ℝ) (L : ℕ) (eta0 delta0 : ℝ),
      0 < e ∧ zeta=window*e/32 ∧ 0 < zeta ∧ 0 < L ∧
      0 < eta0 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i ∈ fixedCompactClass) → D.thickness ≤ delta0 → eta ≤ eta0 →
        ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n)) (original : Fin n → Finset Index),
          (∀i,D.shading i = wzCellShading (mesh D) original i) ∧
          D.thickness = (2:ℝ)⁻¹^level ∧
          (∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
          R.Nonempty ∧ n ≤ 2*R.card ∧
          wzTotalShadingVolume D ≤ 2*NativeOriginalPrunedMass.shadingMass D R ∧
          (ENNReal.ofReal D.thickness).rpow zeta*NativeOriginalPrunedMass.tubeMass D R ≤
            NativeOriginalPrunedMass.shadingMass D R ∧
          (∀ U : Set E4, Convex ℝ U →
            ((R.filter (fun i => markedUnitTube (D.line i) D.thickness ⊆ U)).card:ℝ≥0∞) ≤
              (ENNReal.ofReal D.thickness).rpow (-zeta)*volume U*R.card) ∧
          (∀ (ell : Fin (level+1)) (p : Parent),
            (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
              D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
                ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
                D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) ∧
          ∀ schedule : Fin g → Fin (level+1),
            (∀j,1/((2^(schedule j).val:ℕ):ℝ) ≤ D.thickness^window) →
            (∀j,D.thickness/(1/((2^(schedule j).val:ℕ):ℝ)) ≤ D.thickness^window) →
            ∀ (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
              (∀j x,Rel j x x) → (∀j x y,Rel j x y → Rel j y x) →
              ∃ E, IsCore D original R a eta zeta (menuSize d g) g L
                (relationMenu h R a schedule Rel) (fun j => 2^(schedule j).val) E ∧
                (125*175616*16384:ℝ)*(factor (menuSize d g) g L:ℝ)*(coreRadix original R L:ℝ)^2*
                  D.thickness^(-eta) ≤ D.thickness^(-theta) ∧
                (∀j x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Rel j) E x ≤
                  (coreRadix original R L)^2*degree (fun _ : Fin n × Index => 1) (Rel j) E y) ∧
                ∀j,
                  HasJointScale h R E a level (schedule j).val e zeta theta epsilon ∧
                  HasUniformFibers E (coreRadix original R L) (physicalPair h R a level (schedule j).val) ∧
                  HasUniformFibers E (coreRadix original R L) (physicalPoint h R a level (schedule j).val) ∧
                  HasUniformFibers E (coreRadix original R L) (formalPair D a (schedule j).val) ∧
                  NativeIncidenceMultiplicityTower.multiplicity
                    (NativeIncidenceMultiplicityTower.coarse E (parentLabel D a (2^(schedule j).val))) ≤
                    (125:ℝ)*(coreRadix original R L:ℝ)^4*
                      (NativeFiniteKakeyaCounts.multiplicity
                        (NativeFullCoarseShadow.fullSource h R a level (schedule j).val E)).toReal ∧
                  ∀p,(parentEdges D a (2^(schedule j).val) E p).Nonempty →
                    ∀q,(parentEdges D a (2^(schedule j).val) E q).Nonempty →
                      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^(schedule j).val) E p) ≤
                        (coreRadix original R L:ℝ)^2*
                          NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^(schedule j).val) E q) := by
  have hmenu : 0 < menuSize d g+g := by unfold menuSize; omega
  obtain ⟨e,zeta,L,eta0,delta0,he,hzeq,hzeta,hL,heta0,hdelta0,hbase⟩ :=
    joint_same_source_local_coarse_upper epsilon window theta hepsilon hw htheta (menuSize d g) g hmenu
  refine ⟨e,zeta,L,eta0,delta0,he,hzeq,hzeta,hL,heta0,hdelta0,?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hbase n D eta h hDK hsmall heta
  refine ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,?_⟩
  intro schedule hcoarse hfine Rel hrefl hsym
  let T := relationMenu h R a schedule Rel
  have hTrefl : ∀j x,T j x x := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro k x
      simpa only [T,relationMenu,Fin.addCases_left] using hrefl k x
    · intro k
      refine Fin.addCases ?_ ?_ k
      · intro _j _x
        simp only [T,relationMenu,Fin.addCases_right,Fin.addCases_left]
      · intro k
        refine Fin.addCases ?_ ?_ k <;> intro _j _x <;>
          simp only [T,relationMenu,Fin.addCases_right,Fin.addCases_left]
  have hTsym : ∀j x y,T j x y → T j y x := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro k x y hh
      simpa only [T,relationMenu,Fin.addCases_left] using
        hsym k x y (by simpa only [T,relationMenu,Fin.addCases_left] using hh)
    · intro k
      refine Fin.addCases ?_ ?_ k
      · intro _j _x _y hh
        simp only [T,relationMenu,Fin.addCases_right,Fin.addCases_left] at hh ⊢
        exact hh.symm
      · intro k
        refine Fin.addCases ?_ ?_ k <;> intro _j _x _y hh <;>
          simp only [T,relationMenu,Fin.addCases_right,Fin.addCases_left] at hh ⊢ <;> exact hh.symm
  obtain ⟨E,hEcore,hcost,hjoint⟩ := hcore T hTrefl hTsym schedule hcoarse hfine
  have hU := hEcore.2.2.2.1
  refine ⟨E,hEcore,hcost,?_,?_⟩
  · intro j x y hx hy
    simpa only [T,relationMenu,Fin.addCases_left] using
      hU (Fin.castAdd (g+(g+g)) j) x y hx hy
  intro j
  have hpair : HasUniformFibers E (coreRadix original R L)
      (physicalPair h R a level (schedule j).val) := by
    intro x hx y hy
    simpa only [T,relationMenu,Fin.addCases_right,Fin.addCases_left,unit_degree_eq_fiber] using
      hU (Fin.natAdd d (Fin.castAdd (g+g) j)) x y hx hy
  have hpoint : HasUniformFibers E (coreRadix original R L)
      (physicalPoint h R a level (schedule j).val) := by
    intro x hx y hy
    simpa only [T,relationMenu,Fin.addCases_right,Fin.addCases_left,unit_degree_eq_fiber] using
      hU (Fin.natAdd d (Fin.natAdd g (Fin.castAdd g j))) x y hx hy
  have hformal : HasUniformFibers E (coreRadix original R L)
      (formalPair D a (schedule j).val) := by
    intro x hx y hy
    simpa only [T,relationMenu,Fin.addCases_right,unit_degree_eq_fiber] using
      hU (Fin.natAdd d (Fin.natAdd g (Fin.natAdd g j))) x y hx hy
  refine ⟨hjoint j,hpair,hpoint,hformal,?_,?_⟩
  · have hE : E⊆incidences original := hEcore.1.trans (filter_subset _ _)
    have hER : ∀z∈E,z.1∈R := fun z hz => (mem_filter.mp (hEcore.1 hz)).2
    exact NativeCoarsePointMultiplicity.multiplicity_le_full_source h original horiginal ha
      R E hE hER level (schedule j).val hdy (Nat.le_of_lt_succ (schedule j).isLt)
      (coreRadix original R L) hpair hpoint
  · intro p hp q hq
    exact NativeParentAverageUniformity.parent_multiplicity_le E (parentLabel D a (2^(schedule j).val))
      (coreRadix original R L) hformal p hp q hq

end NativeJointUniformCoarseRelations
