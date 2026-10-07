import Theorems.Thm_StickyKakeya4_native_physical_queried_rank_configuration
import Theorems.Thm_StickyKakeya4_native_reference_relative_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeConditionalReferenceMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeLocalParentSource NativeRelativeCoarseReadback
open NativeJointUniformCoarseRelations NativeGenericReferenceData NativeExtraQueriedRankConfiguration
open NativeSquaredGrainQueries NativeMiddleGrainParentBudget

/-- K is fixed before the source. Each candidate middle parent has a fixed
(K+1) by (K+1) two-scale grid, independent of its eventual dyadic level. -/
def queryCount (g K : ℕ) : ℕ := (g+1)*((K+1)*(K+1))
def relationCount (g K : ℕ) : ℕ := queryCount g K+queryCount g K*(1+1)

lemma relation_count (g K : ℕ) : relationCount g K=3*(g+1)*(K+1)^2 := by
  dsimp [relationCount,queryCount]
  ring

def candidate {g K : ℕ} (q : Fin (queryCount g K)) : Fin (g+1) :=
  (finProdFinEquiv.symm q).1

def pair {g K : ℕ} (q : Fin (queryCount g K)) : Fin (K+1) × Fin (K+1) :=
  finProdFinEquiv.symm (finProdFinEquiv.symm q).2

def gridDepth (m K : ℕ) (j : Fin (K+1)) : ℕ := 6+(m-6)*j.val/K

def outerDepth {g K level : ℕ} (schedule : Fin (g+1) → Fin (level+1))
    (q : Fin (queryCount g K)) : ℕ := middleDepth (schedule (candidate q)).val

def sigmaDepth {g K level : ℕ} (schedule : Fin (g+1) → Fin (level+1))
    (q : Fin (queryCount g K)) : ℕ :=
  min (gridDepth (outerDepth schedule q) K (pair q).1)
    (gridDepth (outerDepth schedule q) K (pair q).2)

def rhoDepth {g K level : ℕ} (schedule : Fin (g+1) → Fin (level+1))
    (q : Fin (queryCount g K)) : ℕ :=
  max (gridDepth (outerDepth schedule q) K (pair q).1)
    (gridDepth (outerDepth schedule q) K (pair q).2)

def parentDepth {g K level : ℕ} (schedule : Fin (g+1) → Fin (level+1))
    (q : Fin (queryCount g K)) : ℕ := outerDepth schedule q+sigmaDepth schedule q-6

def relativeScales {g K level : ℕ} (schedule : Fin (g+1) → Fin (level+1))
    (q : Fin (queryCount g K)) (_j : Fin 1) : ℕ :=
  2^(rhoDepth schedule q-sigmaDepth schedule q+6)

lemma gridDepth_bounds (m K : ℕ) (hK : 0< K) (hm : 6≤ m) (j : Fin (K+1)) :
    6≤ gridDepth m K j ∧ gridDepth m K j≤ m := by
  have hj : j.val≤ K := by omega
  have hprod : (m-6)*j.val≤ (m-6)*K := Nat.mul_le_mul_left _ hj
  have hquot : (m-6)*j.val/K≤ m-6 := (Nat.div_le_div_right hprod).trans_eq
    (Nat.mul_div_cancel _ hK)
  dsimp only [gridDepth]
  constructor
  · exact Nat.le_add_right _ _
  · exact (Nat.add_le_add_left hquot 6).trans_eq (Nat.add_sub_of_le hm)

lemma query_bounds {g K level : ℕ} (schedule : Fin (g+1) → Fin (level+1))
    (q : Fin (queryCount g K)) (hK : 0< K) (hm : 6≤ outerDepth schedule q) :
    6≤ sigmaDepth schedule q ∧ sigmaDepth schedule q≤ rhoDepth schedule q ∧
      rhoDepth schedule q≤ outerDepth schedule q := by
  have h1 := gridDepth_bounds _ K hK hm (pair q).1
  have h2 := gridDepth_bounds _ K hK hm (pair q).2
  dsimp [sigmaDepth,rhoDepth]
  omega

lemma query_phase_depth {g K level : ℕ} (schedule : Fin (g+1) → Fin (level+1))
    (q : Fin (queryCount g K)) (hK : 0< K)
    (hstop : 6≤ (schedule (candidate q)).val) :
    outerDepth schedule q+rhoDepth schedule q-6≤ level := by
  have hb := middle_depth_bounds (schedule (candidate q)).val hstop
  have hq := query_bounds schedule q hK hb.1
  have hs := (schedule (candidate q)).isLt
  change outerDepth schedule q+rhoDepth schedule q-6≤ level
  have hphase := hb.2.2.2
  change 2*outerDepth schedule q-6≤ (schedule (candidate q)).val at hphase
  omega

/-- The labels read only D/R/backbone/schedule. E1 and all later refinements
are absent from this factory, so these three relations are installed once
before the actual enlarged first core is selected. -/
def factory (g K : ℕ) : MenuFactory g (relationCount g K) :=
  fun _n _D _eta h a _level R _original schedule =>
    NativeReferenceRelativeMenu.relations h R a (parentDepth schedule) (relativeScales schedule)

lemma factory_refl (g K : ℕ) : MenuRefl (factory g K) := by
  intro n D eta h a level R original schedule
  exact NativeReferenceRelativeMenu.relations_refl h R a _ _

lemma factory_symm (g K : ℕ) : MenuSymm (factory g K) := by
  intro n D eta h a level R original schedule
  exact NativeReferenceRelativeMenu.relations_symm h R a _ _

/-- Read the literal parent, double-pair and point uniformities on the same
Reference.E1 returned by the generic source. Its big dimension/F1 is kept. -/
theorem reference_uniformities {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0< tau} {L g K : ℕ}
    (ref : Reference h tau htau seed e zeta L g)
    (H : HasCallerUniformities ref (factory g K)) (i : Fin (queryCount g K)) :
    (∀x y,x∈ref.E1 → y∈ref.E1 →
      (parentEdges D ref.a (2^(parentDepth ref.schedule i)) ref.E1
        (parentLabel D ref.a (2^(parentDepth ref.schedule i)) x.1)).card≤
      (coreRadix ref.original ref.R L)^2*(parentEdges D ref.a (2^(parentDepth ref.schedule i)) ref.E1
        (parentLabel D ref.a (2^(parentDepth ref.schedule i)) y.1)).card) ∧
    ∀p : Parent,∀hp : (parentLabels D ref.R ref.a (2^(parentDepth ref.schedule i)) p).Nonempty,
      HasUniformFibers (parentEdges D ref.a (2^(parentDepth ref.schedule i)) ref.E1 p)
        (coreRadix ref.original ref.R L)
        (doublePair h ref.R ref.a (parentDepth ref.schedule i) p hp (relativeScales ref.schedule i 0)) ∧
      HasUniformFibers (parentEdges D ref.a (2^(parentDepth ref.schedule i)) ref.E1 p)
        (coreRadix ref.original ref.R L)
        (fun z => (doublePair h ref.R ref.a (parentDepth ref.schedule i) p hp
          (relativeScales ref.schedule i 0) z).2) := by
  have HH := NativeReferenceRelativeMenu.caller_uniformities h ref.R ref.a
    (parentDepth ref.schedule) (relativeScales ref.schedule) ref.E1
    (coreRadix ref.original ref.R L) H i
  exact ⟨HH.1,fun p hp => HH.2 p hp 0⟩

end NativeConditionalReferenceMenu
