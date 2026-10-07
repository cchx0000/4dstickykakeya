import Theorems.Thm_StickyKakeya4_native_pre_third_height_support
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data
import Theorems.Thm_StickyKakeya4_native_sharp_X_power_algebra
import Theorems.Thm_StickyKakeya4_native_actual_new_cut_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeActualHeightThirdJoin
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeMatrixHeightWholePoint NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric
open NativeTranslatedHeightFreeze NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeNormalizedCellRelativeMenu CanonicalConfiguredE4Bridge NativePreThirdHeightSupport
open NativeThirdXYSourceData NativeSharpXPowerAlgebra NativeRetainedSliceCore
open NativeReferenceXYGridField NativeSpatialAngularGeometry NativeSquaredGrainQueries
open NativeGrainQuotientFibers NativeRetainedSliceBudgetAlgebra NativeOriginalCellChartGeometry
open scoped Matrix.Norms.Elementwise

/-- Exact cost readback for the actual continuation. The old quotient
charge occurs once; the new coherence, height, support and residue cuts
are precisely the natural charge paid by source_new_cut_cost. -/
lemma source_total_charge (q : ℝ) (Kcoh Ksupport normal g R0 : ℕ)
    (meshConstant row r loss rankLoss metric kappa : ℝ) (mesh : Fin Kcoh → ℝ) :
    (quotientCost q *
      (NativeActualNewCutBudget.coherenceCharge Kcoh normal g meshConstant row r loss rankLoss metric kappa mesh : ℝ)) *
      ((((8*R0)*53^(4*Ksupport))*8^4:ℕ):ℝ) =
    quotientCost q *
      (NativeActualNewCutBudget.newCutCharge Kcoh Ksupport normal g R0
        meshConstant row r loss rankLoss metric kappa mesh : ℝ) := by
  simp only [NativeActualNewCutBudget.newCutCharge, Nat.cast_mul]
  ring

/-- The rank-2 branch calls the actual height, support and residue cuts,
then the source continuation exactly once on their common U. The relation
values may depend on that U and its frozen fields; their count d3 is an
input fixed before the source. The original fixedField and raw field are
read back on the same final T. No point saturation of T is asserted. -/
theorem attach_rank_two {n K Jhorizontal d3 : ℕ} {V : Type*} [Zero V]
    {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a zeta : ℝ) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (plane : Index → Submodule ℝ E4)
    (E2 Hgraph S : Finset (Fin n × Index)) (hS : S.Nonempty)
    (hparent : ∀z∈S, parentLabel D a (2^m) z.1 = p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P = 1)
    (hFull : S ⊆ NativeTranslatedGrainHeightSelection.second D a m 2 plane
      (NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
        (by norm_num : 1 ≤ 2) (by norm_num : 2 ≤ 4) hd (physicalMesh m (phaseDepth m)/8)))
    (Fraw : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (hFraw : ∀t, ‖Fraw t‖ ≤ (1/4:ℝ))
    (q tau c1 c2 lambda b population PL PU retain Cgraph Cpre t : ℝ)
    (F1 G Q2 L3 : ℕ)
    (Hnext : ∀U⊆S, ∀Cextra : ℝ, 0 < Cextra → (S.card:ℝ) ≤ Cextra*U.card →
      ∀Rel : Fin d3 → (Fin n × Index) → (Fin n × Index) → Prop,
      (∀j x, Rel j x x) → (∀j x y, Rel j x y → Rel j y x) →
      let Ctotal := Cpre*Cextra
      let Q3 := NativeSourceSizeBounds.radix U.card L3
      let F3 := refinementCost (d3+2) (Jhorizontal+1) L3
      let CX := (Ctotal/quotientCost q)*fiberCoefficient D.thickness eta zeta tau c1 c2
        lambda b F1 G Q2 F3 Q3 q 2
      ∃T, HasThirdXYSourceData (J:=Jhorizontal) D zeta a m plane E2 Hgraph U T P hP
        (by norm_num : 1 ≤ 2) (by norm_num : 2 ≤ 4) hd Fraw p
        population PL PU Q2 retain Cgraph Ctotal t L3 Rel CX)
    (Gfield : ℤ → V) (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (M J : Fin K → ℕ) (hM : ∀j, 0 < M j)
    (hmenu : ∀j, mu m*(R0:ℝ) ≤ 64/(M j:ℝ))
    (hIntegral : ∀j, 64/(M j:ℝ) = (mu m*(R0:ℝ))*(J j:ℝ))
    (relations : Finset (Fin n × Index) → (ℤ → Matrix (Fin 2) (Fin 1) ℝ) →
      (ℤ → V) → Fin d3 → (Fin n × Index) → (Fin n × Index) → Prop)
    (hRefl : ∀U Fcfg Gcfg j x, relations U Fcfg Gcfg j x x)
    (hSymm : ∀U Fcfg Gcfg j x y, relations U Fcfg Gcfg j x y → relations U Fcfg Gcfg j y x) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
        (by norm_num : 1 ≤ 2) (by norm_num : 2 ≤ 4) hd (physicalMesh m (phaseDepth m)/8)
    let F := fixedField D a m 2 plane Sq Fraw
    ∃Bh⊆S.image Prod.snd,let Sh:=edgeLift S Prod.snd Bh
    let Fcfg:=frozen D a m R0 Sh F
    let Gcfg:=frozen D a m R0 Sh Gfield
    (∀t,‖Fcfg t‖≤ (1/4:ℝ)) ∧
    ∃B0⊆Sh.image Prod.snd,let U0:=edgeLift Sh Prod.snd B0
    ∃color : Fin 4 → Fin 8,∃B⊆U0.image Prod.snd,let U:=edgeLift U0 Prod.snd B
      U.Nonempty ∧ U⊆S ∧ S.card≤ (((8*R0)*53^(4*K))*8^4)*U.card ∧
      (∀k∈B,U.filter (fun z => z.2=k)=S.filter (fun z => z.2=k)) ∧
      (∀z∈U,Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))=F (translatedHeight D a m z.2) ∧
        Gcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))=Gfield (translatedHeight D a m z.2)) ∧
      (∀j,∀x∈U,∀y∈U,
        wzDyadicCellIndex ((64/(M j:ℝ))/512)
          (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 x.2)=
        wzDyadicCellIndex ((64/(M j:ℝ))/512)
          (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 y.2) →
        physicalCell D a (2^m) (M j) p x.2=physicalCell D a (2^m) (M j) p y.2) ∧
      (∀j x y,
        ⌊NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 x (3:Fin 4)/((64/(M j:ℝ))/512)⌋=
        ⌊NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 y (3:Fin 4)/((64/(M j:ℝ))/512)⌋ →
        physicalCell D a (2^m) (M j) p x (3:Fin 4)=physicalCell D a (2^m) (M j) p y (3:Fin 4)) ∧
      (∀k∈B,SeparatedAlignmentPatches.color 8 (by norm_num)
        (NativeActualConfiguredResidue.parameter .oneTwo (mu m) R0 F Fcfg
          (NativeActualConfiguredPoint.sourceLabel D a m p .oneTwo P hP hd F k))=color) ∧
      (∀x∈U.image (fun z => NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 z.2),
        ∀y∈U.image (fun z => NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 z.2),
        x≠y → (mu m*(R0:ℝ))/64≤ dist x y) ∧
      (∀z∈U,∀u∈U,
        NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 z.2 (3:Fin 4)≠
          NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 u.2 (3:Fin 4) →
        (mu m*(R0:ℝ))/64≤ dist
          (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 z.2 (3:Fin 4))
          (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 u.2 (3:Fin 4))) ∧
      (∀j,∀x∈U,∀y∈U,
        wzDyadicCellIndex ((64/(M j:ℝ))/64)
          (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 x.2)=
        wzDyadicCellIndex ((64/(M j:ℝ))/64)
          (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 y.2) →
        physicalCell D a (2^m) (M j) p x.2=physicalCell D a (2^m) (M j) p y.2) ∧
      (∀T⊆U,∀z∈T,∀w∈T,
        translatedHeight D a m z.2/((8*R0:ℕ):ℤ)=translatedHeight D a m w.2/((8*R0:ℕ):ℤ) →
        translatedHeight D a m z.2=translatedHeight D a m w.2) ∧
      (∀z∈U, Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Fraw (rawHeight D m z.2)) ∧
      let Cextra : ℝ := ((((8*R0)*53^(4*K))*8^4:ℕ):ℝ)
      let Ctotal := Cpre*Cextra
      let Q3 := NativeSourceSizeBounds.radix U.card L3
      let F3 := refinementCost (d3+2) (Jhorizontal+1) L3
      let CX := (Ctotal/quotientCost q)*fiberCoefficient D.thickness eta zeta tau c1 c2
        lambda b F1 G Q2 F3 Q3 q 2
      ∃T, HasThirdXYSourceData (J:=Jhorizontal) D zeta a m plane E2 Hgraph U T P hP
        (by norm_num : 1 ≤ 2) (by norm_num : 2 ≤ 4) hd Fraw p
        population PL PU Q2 retain Cgraph Ctotal t L3 (relations U Fcfg Gcfg) CX ∧
      T ⊆ U ∧
      (∀z∈T, Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Fraw (rawHeight D m z.2) ∧
        Gcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Gfield (translatedHeight D a m z.2)) ∧
      (∀z∈T, ∀w∈T,
        translatedHeight D a m z.2/((8*R0:ℕ):ℤ) = translatedHeight D a m w.2/((8*R0:ℕ):ℤ) →
        translatedHeight D a m z.2 = translatedHeight D a m w.2) := by
  intro Sq F
  have hF : ∀height, ‖F height‖ ≤ (1/4:ℝ) := fixedField_norm D a m 2 plane Sq Fraw hFraw
  obtain ⟨Bh, hBh, hCfg, B0, hB0, color, B, hB, hU, hUS, hCost, hFiber,
      hFrozen, hFine, hTime, hColor, hSep, hTimeSep, hWide, hSingle⟩ :=
    select_actual_height_support h m hm p S hS hparent .oneTwo P hP hd F Gfield hF
      R0 hR0 hbase M J hM hmenu hIntegral
  let Sh := edgeLift S Prod.snd Bh
  let Fcfg := frozen D a m R0 Sh F
  let Gcfg := frozen D a m R0 Sh Gfield
  let U0 := edgeLift Sh Prod.snd B0
  let U := edgeLift U0 Prod.snd B
  have hRaw (z : Fin n × Index) (hz : z ∈ U) :
      Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Fraw (rawHeight D m z.2) :=
    (hFrozen z hz).1.trans (fixedField_readback D a m 2 plane Sq Fraw z (hFull (hUS hz)))
  let Cextra : ℝ := ((((8*R0)*53^(4*K))*8^4:ℕ):ℝ)
  have hExtra : 0 < Cextra := by dsimp [Cextra]; positivity
  have hExtraCost : (S.card:ℝ) ≤ Cextra*U.card := by exact_mod_cast hCost
  obtain ⟨T, HT⟩ := Hnext U hUS Cextra hExtra hExtraCost
    (relations U Fcfg Gcfg) (hRefl U Fcfg Gcfg) (hSymm U Fcfg Gcfg)
  have hTU : T ⊆ U := HT.1.1
  refine ⟨Bh, hBh, hCfg, B0, hB0, color, B, hB, hU, hUS, hCost, hFiber,
    hFrozen, hFine, hTime, hColor, hSep, hTimeSep, hWide, hSingle, hRaw, T, HT, hTU, ?_, ?_⟩
  · intro z hz
    exact ⟨hRaw z (hTU hz), (hFrozen z (hTU hz)).2⟩
  · exact hSingle T hTU

/-- The rank-3 branch calls the actual height, support and residue cuts,
then the source continuation exactly once on their common U. The relation
values may depend on that U and its frozen fields; their count d3 is an
input fixed before the source. The original fixedField and raw field are
read back on the same final T. No point saturation of T is asserted. -/
theorem attach_rank_three {n K Jhorizontal d3 : ℕ} {V : Type*} [Zero V]
    {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a zeta : ℝ) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (plane : Index → Submodule ℝ E4)
    (E2 Hgraph S : Finset (Fin n × Index)) (hS : S.Nonempty)
    (hparent : ∀z∈S, parentLabel D a (2^m) z.1 = p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P = 2)
    (hFull : S ⊆ NativeTranslatedGrainHeightSelection.second D a m 3 plane
      (NativeWeightedGrainQuotientGeometry.retained D a m 3 plane Hgraph P hP
        (by norm_num : 1 ≤ 3) (by norm_num : 3 ≤ 4) hd (physicalMesh m (phaseDepth m)/8)))
    (Fraw : ℤ → Matrix (Fin 1) (Fin 2) ℝ) (hFraw : ∀t, ‖Fraw t‖ ≤ (1/4:ℝ))
    (q tau c1 c2 lambda b population PL PU retain Cgraph Cpre t : ℝ)
    (F1 G Q2 L3 : ℕ)
    (Hnext : ∀U⊆S, ∀Cextra : ℝ, 0 < Cextra → (S.card:ℝ) ≤ Cextra*U.card →
      ∀Rel : Fin d3 → (Fin n × Index) → (Fin n × Index) → Prop,
      (∀j x, Rel j x x) → (∀j x y, Rel j x y → Rel j y x) →
      let Ctotal := Cpre*Cextra
      let Q3 := NativeSourceSizeBounds.radix U.card L3
      let F3 := refinementCost (d3+2) (Jhorizontal+1) L3
      let CX := (Ctotal/quotientCost q)*fiberCoefficient D.thickness eta zeta tau c1 c2
        lambda b F1 G Q2 F3 Q3 q 3
      ∃T, HasThirdXYSourceData (J:=Jhorizontal) D zeta a m plane E2 Hgraph U T P hP
        (by norm_num : 1 ≤ 3) (by norm_num : 3 ≤ 4) hd Fraw p
        population PL PU Q2 retain Cgraph Ctotal t L3 Rel CX)
    (Gfield : ℤ → V) (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (M J : Fin K → ℕ) (hM : ∀j, 0 < M j)
    (hmenu : ∀j, mu m*(R0:ℝ) ≤ 64/(M j:ℝ))
    (hIntegral : ∀j, 64/(M j:ℝ) = (mu m*(R0:ℝ))*(J j:ℝ))
    (relations : Finset (Fin n × Index) → (ℤ → Matrix (Fin 1) (Fin 2) ℝ) →
      (ℤ → V) → Fin d3 → (Fin n × Index) → (Fin n × Index) → Prop)
    (hRefl : ∀U Fcfg Gcfg j x, relations U Fcfg Gcfg j x x)
    (hSymm : ∀U Fcfg Gcfg j x y, relations U Fcfg Gcfg j x y → relations U Fcfg Gcfg j y x) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 3 plane Hgraph P hP
        (by norm_num : 1 ≤ 3) (by norm_num : 3 ≤ 4) hd (physicalMesh m (phaseDepth m)/8)
    let F := fixedField D a m 3 plane Sq Fraw
    ∃Bh⊆S.image Prod.snd,let Sh:=edgeLift S Prod.snd Bh
    let Fcfg:=frozen D a m R0 Sh F
    let Gcfg:=frozen D a m R0 Sh Gfield
    (∀t,‖Fcfg t‖≤ (1/4:ℝ)) ∧
    ∃B0⊆Sh.image Prod.snd,let U0:=edgeLift Sh Prod.snd B0
    ∃color : Fin 4 → Fin 8,∃B⊆U0.image Prod.snd,let U:=edgeLift U0 Prod.snd B
      U.Nonempty ∧ U⊆S ∧ S.card≤ (((8*R0)*53^(4*K))*8^4)*U.card ∧
      (∀k∈B,U.filter (fun z => z.2=k)=S.filter (fun z => z.2=k)) ∧
      (∀z∈U,Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))=F (translatedHeight D a m z.2) ∧
        Gcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))=Gfield (translatedHeight D a m z.2)) ∧
      (∀j,∀x∈U,∀y∈U,
        wzDyadicCellIndex ((64/(M j:ℝ))/512)
          (NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 x.2)=
        wzDyadicCellIndex ((64/(M j:ℝ))/512)
          (NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 y.2) →
        physicalCell D a (2^m) (M j) p x.2=physicalCell D a (2^m) (M j) p y.2) ∧
      (∀j x y,
        ⌊NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 x (3:Fin 4)/((64/(M j:ℝ))/512)⌋=
        ⌊NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 y (3:Fin 4)/((64/(M j:ℝ))/512)⌋ →
        physicalCell D a (2^m) (M j) p x (3:Fin 4)=physicalCell D a (2^m) (M j) p y (3:Fin 4)) ∧
      (∀k∈B,SeparatedAlignmentPatches.color 8 (by norm_num)
        (NativeActualConfiguredResidue.parameter .twoOne (mu m) R0 F Fcfg
          (NativeActualConfiguredPoint.sourceLabel D a m p .twoOne P hP hd F k))=color) ∧
      (∀x∈U.image (fun z => NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 z.2),
        ∀y∈U.image (fun z => NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 z.2),
        x≠y → (mu m*(R0:ℝ))/64≤ dist x y) ∧
      (∀z∈U,∀u∈U,
        NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 z.2 (3:Fin 4)≠
          NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 u.2 (3:Fin 4) →
        (mu m*(R0:ℝ))/64≤ dist
          (NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 z.2 (3:Fin 4))
          (NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 u.2 (3:Fin 4))) ∧
      (∀j,∀x∈U,∀y∈U,
        wzDyadicCellIndex ((64/(M j:ℝ))/64)
          (NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 x.2)=
        wzDyadicCellIndex ((64/(M j:ℝ))/64)
          (NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 y.2) →
        physicalCell D a (2^m) (M j) p x.2=physicalCell D a (2^m) (M j) p y.2) ∧
      (∀T⊆U,∀z∈T,∀w∈T,
        translatedHeight D a m z.2/((8*R0:ℕ):ℤ)=translatedHeight D a m w.2/((8*R0:ℕ):ℤ) →
        translatedHeight D a m z.2=translatedHeight D a m w.2) ∧
      (∀z∈U, Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Fraw (rawHeight D m z.2)) ∧
      let Cextra : ℝ := ((((8*R0)*53^(4*K))*8^4:ℕ):ℝ)
      let Ctotal := Cpre*Cextra
      let Q3 := NativeSourceSizeBounds.radix U.card L3
      let F3 := refinementCost (d3+2) (Jhorizontal+1) L3
      let CX := (Ctotal/quotientCost q)*fiberCoefficient D.thickness eta zeta tau c1 c2
        lambda b F1 G Q2 F3 Q3 q 3
      ∃T, HasThirdXYSourceData (J:=Jhorizontal) D zeta a m plane E2 Hgraph U T P hP
        (by norm_num : 1 ≤ 3) (by norm_num : 3 ≤ 4) hd Fraw p
        population PL PU Q2 retain Cgraph Ctotal t L3 (relations U Fcfg Gcfg) CX ∧
      T ⊆ U ∧
      (∀z∈T, Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Fraw (rawHeight D m z.2) ∧
        Gcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Gfield (translatedHeight D a m z.2)) ∧
      (∀z∈T, ∀w∈T,
        translatedHeight D a m z.2/((8*R0:ℕ):ℤ) = translatedHeight D a m w.2/((8*R0:ℕ):ℤ) →
        translatedHeight D a m z.2 = translatedHeight D a m w.2) := by
  intro Sq F
  have hF : ∀height, ‖F height‖ ≤ (1/4:ℝ) := fixedField_norm D a m 3 plane Sq Fraw hFraw
  obtain ⟨Bh, hBh, hCfg, B0, hB0, color, B, hB, hU, hUS, hCost, hFiber,
      hFrozen, hFine, hTime, hColor, hSep, hTimeSep, hWide, hSingle⟩ :=
    select_actual_height_support h m hm p S hS hparent .twoOne P hP hd F Gfield hF
      R0 hR0 hbase M J hM hmenu hIntegral
  let Sh := edgeLift S Prod.snd Bh
  let Fcfg := frozen D a m R0 Sh F
  let Gcfg := frozen D a m R0 Sh Gfield
  let U0 := edgeLift Sh Prod.snd B0
  let U := edgeLift U0 Prod.snd B
  have hRaw (z : Fin n × Index) (hz : z ∈ U) :
      Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Fraw (rawHeight D m z.2) :=
    (hFrozen z hz).1.trans (fixedField_readback D a m 3 plane Sq Fraw z (hFull (hUS hz)))
  let Cextra : ℝ := ((((8*R0)*53^(4*K))*8^4:ℕ):ℝ)
  have hExtra : 0 < Cextra := by dsimp [Cextra]; positivity
  have hExtraCost : (S.card:ℝ) ≤ Cextra*U.card := by exact_mod_cast hCost
  obtain ⟨T, HT⟩ := Hnext U hUS Cextra hExtra hExtraCost
    (relations U Fcfg Gcfg) (hRefl U Fcfg Gcfg) (hSymm U Fcfg Gcfg)
  have hTU : T ⊆ U := HT.1.1
  refine ⟨Bh, hBh, hCfg, B0, hB0, color, B, hB, hU, hUS, hCost, hFiber,
    hFrozen, hFine, hTime, hColor, hSep, hTimeSep, hWide, hSingle, hRaw, T, HT, hTU, ?_, ?_⟩
  · intro z hz
    exact ⟨hRaw z (hTU hz), (hFrozen z (hTU hz)).2⟩
  · exact hSingle T hTU

end NativeActualHeightThirdJoin
