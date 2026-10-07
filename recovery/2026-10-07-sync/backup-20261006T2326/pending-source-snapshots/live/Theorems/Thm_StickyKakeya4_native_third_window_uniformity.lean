import Theorems.Thm_StickyKakeya4_native_window_XY_relation_menu
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
noncomputable section
namespace NativeThirdWindowUniformity
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeHorizontalGrainSlice NativeGrainQuotientFibers
open NativeThirdXYData NativeThirdXYSourceData NativeReferenceXYGridField NativeRetainedSliceCore
open NativeWindowEncodedCapacities NativeJointUniformCoarseRelations NativeAnisotropicSliceLabels
open NativeSquaredGrainQueries NativeSliceCountComparison
open scoped Matrix.Norms.Elementwise

/-- Decode the square window menu and the actual original-incidence
retention from the SAME third source record. No new core is selected. -/
theorem from_source_data {n d J ell : ℕ} (D : FiniteScaleSource n) (zeta a : ℝ) (m : ℕ)
    (hm : 6 ≤ m) (hJ : 0 < J)
    (plane : Index → Submodule ℝ E4) (E Hgraph S T : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (p : Parent) (population profileLower profileUpper : ℝ) (Qref : ℕ)
    (lambda G Cpre t : ℝ) (hlambda : 0 < lambda) (L3 : ℕ)
    (Extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) (CX : ℝ)
    (hS : S⊆parentEdges D a (2^m) E p)
    (Hdata :
      let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell plane Hgraph P hP hell hell4 hd
        (physicalMesh m (phaseDepth m)/8)
      let F := fixedField D a m ell plane Sq Fraw
      let Rel3 := Fin.addCases (NativeWindowXYRelationMenu.relations (J:=J) D a m ell p P hP hell hell4 hd F) Extra
      HasThirdXYSourceData (J:=J) D zeta a m plane E Hgraph S T P hP hell hell4 hd Fraw p
        population profileLower profileUpper Qref lambda G Cpre t L3 Rel3 CX) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell plane Hgraph P hP hell hell4 hd
      (physicalMesh m (phaseDepth m)/8)
    let F := fixedField D a m ell plane Sq Fraw
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let F3 := refinementCost (((J+1)*(J+1)+d)+2) (J+1) L3
    let loss := G*Cpre*(F3:ℝ)
    T⊆S ∧ T.Nonempty ∧ 0 < loss ∧
      lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ loss*T.card ∧
      ∀i : Fin (J+1),
        let f := NativeFixedHorizontalMenu.depths J m i
        HasUniformFibers T Q3 (fun z => xyPoint D a m ell f f p P hP hell hell4 hd F z.2) ∧
        ∀j,HasUniformFibers T Q3 (fun z => horizontalCoarsen f (NativeWindowXYRelationMenu.depth J m f j)
          (xyPoint D a m ell f f p P hP hell hell4 hd F z.2)) := by
  intro Sq F Q3 F3 loss
  have Hcopy := Hdata.1
  rcases Hcopy with ⟨hTS,hTn,_hCost,_hTH,_hFinal,HExtra,_hOld,_hXY,_hClass,_hGrain,_hKey,
    _hThreshold,hRet,_hAD,_hRead,_hNorm⟩
  have hIpos : (0:ℝ)<(parentEdges D a (2^m) E p).card := by
    exact_mod_cast card_pos.mpr (hTn.mono (hTS.trans hS))
  have hloss : 0 < loss := lt_of_mul_pos_left ((mul_pos hlambda hIpos).trans_le hRet) (Nat.cast_nonneg _)
  refine ⟨hTS,hTn,hloss,hRet,?_⟩
  intro i
  apply NativeWindowXYRelationMenu.caller_uniformities D a m ell hm hJ p P hP hell hell4 hd F T Q3 _ i
  intro j x y hx hy
  simpa only [Fin.addCases_left] using HExtra (Fin.castAdd d j) x y hx hy

end NativeThirdWindowUniformity
