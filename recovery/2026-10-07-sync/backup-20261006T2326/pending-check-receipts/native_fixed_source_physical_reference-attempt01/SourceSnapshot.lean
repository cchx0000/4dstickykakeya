/- Preserve the already installed physical shadow slots when packaging the
same fixed-source Reference. No extra refinement or retention cost is used. -/
import Theorems.Thm_StickyKakeya4_native_fixed_source_reference
import Theorems.Thm_StickyKakeya4_native_physical_reference_data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeFixedSourcePhysicalReference
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentDensityCore NativeFixedCompactKakeyaExponent
open NativeGenericReferenceData NativeExtraQueriedRankConfiguration NativeJointUniformCoarseRelations
open NativeConditionedPairMenu NativeAllTwoScaleConfiguration NativeUnitParentNormalization
open NativeFixedSourceReference NativePhysicalReferenceData SelfUniform
open scoped ENNReal

/-- The existing mandatory relation menu already includes physicalPair and
physicalPoint. Export both uniformities on the very same E1 and source. -/
theorem exists_fixed_source_physical_reference
    (tau : ℝ) (htau : 0 < tau) (extraCount : ℕ → ℕ) :
    ∃ (seed e zeta : ℝ) (L g : ℕ) (eta0 delta0 : ℝ),
      0 < seed ∧ seed  ≤  tau/16384 ∧
      0 < e ∧ 0 < zeta ∧ zeta  ≤  seed/256 ∧ 0 < L ∧ 0 < g ∧
      1/(g:ℝ) < min (boundaryWindow tau) ((tau/16)/1000)/4 ∧
      0 < eta0 ∧ eta0  ≤  seed/8 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i∈fixedCompactClass) → 0  ≤  eta → eta  ≤  eta0 →
        D.thickness  ≤  delta0 →
        D.thickness^(-extremalExponent+eta)  ≤  (NativeFiniteKakeyaCounts.multiplicity D).toReal →
        ∀menu : MenuFactory g (extraCount g),MenuRefl menu → MenuSymm menu →
        ∃ref : Reference h tau htau seed e zeta L g,
          ref.dimension=menuSize (pairMenuSize
            (extraCount g+(1+(g+1))) (g+1)) (g+1) ∧
          HasCallerUniformities ref menu ∧ HasPhysicalUniformities ref := by
  obtain ⟨seed,e,zeta,L,g,eta0,delta0,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,
    heta0,hetaSeed,hdelta0,Hsource⟩ :=
    fixed_all_two_scale_extra_configuration tau htau extraCount
  refine ⟨seed,e,zeta,L,g,eta0,delta0,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,
    heta0,hetaSeed,hdelta0,?_⟩
  intro n D eta h hK heta hetaSmall hsmall hnear
  obtain ⟨a,level,R,original,schedule,HB,hgl,hSchedule,Hselect⟩ :=
    Hsource n D eta h hK heta hetaSmall hsmall hnear
  intro menu hMenuRefl hMenuSymm
  let Extra := menu n D eta h a level R original schedule
  obtain ⟨E,hExtra,hCore,hCost,hPoint,hOld,hConditioned,hScales,hFirst,hPairs⟩ :=
    Hselect Extra (hMenuRefl n D eta h a level R original schedule)
      (hMenuSymm n D eta h a level R original schedule)
  let ref : Reference h tau htau seed e zeta L g := {
    a:=a, level:=level, R:=R, original:=original, E1:=E, schedule:=schedule,
    dimension:=menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1),
    relations:=relationMenu h R a schedule (pairRelationMenu h R a schedule
      (NativeInitialExtraRelations.relations D a schedule Extra)),
    backbone:=HB, grid_depth:=hgl, schedule_eq:=hSchedule, core:=hCore, cost:=hCost,
    point:=hPoint, parent_point:=hOld, conditioned:=hConditioned, scales:=hScales,
    middle:=hFirst, pairs:=hPairs }
  refine ⟨ref,rfl,hExtra,?_⟩
  intro j
  have hU := hCore.2.2.2.1
  constructor
  · intro x hx y hy
    simpa only [ref,relationMenu,Fin.addCases_right,Fin.addCases_left,unit_degree_eq_fiber] using
      hU (Fin.natAdd (pairMenuSize (extraCount g+(1+(g+1))) (g+1))
        (Fin.castAdd ((g+1)+(g+1)) j)) x y hx hy
  · intro x hx y hy
    simpa only [ref,relationMenu,Fin.addCases_right,Fin.addCases_left,unit_degree_eq_fiber] using
      hU (Fin.natAdd (pairMenuSize (extraCount g+(1+(g+1))) (g+1))
        (Fin.natAdd (g+1) (Fin.castAdd (g+1) j))) x y hx hy


/-- Public fixed-source entrance with actual volume payment, exact cell
identity and both physical shadow uniformities retained. -/
theorem exists_physical_reference_from_volume_bounds
    (tau : ℝ) (htau : 0< tau) (extraCount : ℕ → ℕ) :
    ∃(seed e zeta : ℝ) (L g : ℕ) (eta0 delta0 : ℝ),
      0< seed ∧ seed ≤ tau/16384 ∧ 0< e ∧ 0< zeta ∧ zeta ≤ seed/256 ∧ 0< L ∧ 0< g ∧
      1/(g:ℝ)< min (boundaryWindow tau) ((tau/16)/1000)/4 ∧
      0< eta0 ∧ eta0 ≤ seed/8 ∧ 0< delta0 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i∈fixedCompactClass) → 0 ≤ eta → eta ≤ eta0 → D.thickness ≤ delta0 →
        ∀(shadeLower unionCost : ℝ),0< unionCost →
        ENNReal.ofReal shadeLower ≤ wzTotalShadingVolume D →
        volume (sourceUnion D) ≤ ENNReal.ofReal (unionCost*D.thickness^extremalExponent) →
        unionCost*D.thickness^eta ≤ shadeLower →
        ∀cells : Fin n → Finset Index,
        (∀i,D.shading i=wzCellShading (mesh D) cells i) →
        ∀menu : MenuFactory g (extraCount g),MenuRefl menu → MenuSymm menu →
        ∃ref : Reference h tau htau seed e zeta L g,
          ref.dimension=menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1) ∧
          HasCallerUniformities ref menu ∧ HasPhysicalUniformities ref ∧ ref.original=cells ∧
          ref.E1⊆incidences cells ∧
          D.thickness^(-extremalExponent+eta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal ∧
          D.thickness^(-extremalExponent+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity ref.E1 := by
  obtain ⟨seed,e,zeta,L,g,eta0,delta0,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,
    heta0,hetaSeed,hdelta0,H⟩ := exists_fixed_source_physical_reference tau htau extraCount
  refine ⟨seed,e,zeta,L,g,eta0,delta0,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,
    heta0,hetaSeed,hdelta0,?_⟩
  intro n D eta h hK heta hetaSmall hsmall shadeLower unionCost hU hShade hUnion hPay
    cells hCells menu hMenuRefl hMenuSymm
  have hnear := native_near_of_volume_bounds h hU hShade hUnion hPay
  obtain ⟨ref,hDimension,hCaller,hPhysical⟩ := H n D eta h hK heta hetaSmall hsmall hnear menu hMenuRefl hMenuSymm
  have hOriginal : ref.original=cells := by
    apply NativeOriginalCellPresentationUnique.cells_eq_of_shading_eq (s:=mesh D) (half_pos h.1.2.1)
    intro i
    exact (ref.backbone.1 i).symm.trans (hCells i)
  have hSubset : ref.E1⊆incidences cells := by
    rw [←hOriginal]
    exact ref.core.1.trans (filter_subset _ _)
  exact ⟨ref,hDimension,hCaller,hPhysical,hOriginal,hSubset,hnear,
    NativeGenericReferenceData.global_near ref heta (hetaSmall.trans hetaSeed) hnear⟩


end NativeFixedSourcePhysicalReference
