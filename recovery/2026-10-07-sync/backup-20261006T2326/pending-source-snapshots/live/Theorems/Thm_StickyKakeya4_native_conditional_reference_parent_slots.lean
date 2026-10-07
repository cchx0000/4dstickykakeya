/- UNVERIFIED source draft. No strict Lean check has run. -/
import Theorems.Thm_StickyKakeya4_native_conditional_reference_menu

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace NativeConditionalReferenceParentSlots
open Classical Finset StickyKakeya4 NativeOriginalParentSelection
open NativeConditionalReferenceMenu NativeMiddleGrainParentBudget
open NativeCommonCubicalMesh NativeOriginalParentDensityCore

/-- The existing (0,0) two-scale query already asks for the outer middle
parent. No extra slot or source refinement is required. -/
def baseQuery (g K : ℕ) (i : Fin (g+1)) : Fin (queryCount g K) :=
  finProdFinEquiv (i,finProdFinEquiv ((0:Fin (K+1)),(0:Fin (K+1))))

lemma parentDepth_baseQuery {g K level : ℕ}
    (schedule : Fin (g+1) → Fin (level+1)) (i : Fin (g+1)) :
    parentDepth schedule (baseQuery g K i)=middleDepth (schedule i).val := by
  simp [parentDepth,outerDepth,sigmaDepth,candidate,pair,gridDepth,baseQuery]

def parentSlot (g K : ℕ) (i : Fin (g+1)) : Fin (relationCount g K) :=
  Fin.castAdd (queryCount g K*(1+1)) (baseQuery g K i)

/-- Exact equality of the relation in the actual coherence menu. This is
the static readback consumed by the prescribed-admission source factory. -/
theorem factory_parent_slot (g K n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (level : ℕ)
    (R : Finset (Fin n)) (original : Fin n → Finset Index)
    (schedule : Fin (g+1) → Fin (level+1)) (i : Fin (g+1)) :
    factory g K n D eta h a level R original schedule (parentSlot g K i)=
      (fun x y => parentLabel D a (2^(middleDepth (schedule i).val)) x.1=
        parentLabel D a (2^(middleDepth (schedule i).val)) y.1) := by
  simp only [factory,NativeReferenceRelativeMenu.relations,parentSlot,Fin.addCases_left,
    parentDepth_baseQuery]

end NativeConditionalReferenceParentSlots
