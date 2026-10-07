/- UNVERIFIED public fixed-source entrance from actual volume bounds. -/
import Theorems.Thm_StickyKakeya4_native_original_cell_presentation_unique

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeFixedSourceReference
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeFixedCompactKakeyaExponent NativeGenericReferenceData
open NativeExtraQueriedRankConfiguration NativeJointUniformCoarseRelations NativeConditionedPairMenu
open NativeAllTwoScaleConfiguration

/-- All analytic/menu choices precede the given source. Actual shading and
union estimates, with their scalar payment, are the only near-extremality
inputs. The source D is retained literally. Its chosen cell presentation is
proved equal to the supplied original cells, so every later E1 edge retains
the inherited remembered-height and higher-plane witnesses on those cells.
This does not assert lower-profile inheritance under subsequent cuts. -/
theorem exists_reference_from_volume_bounds
    (tau : ℝ) (htau : 0<tau) (extraCount : ℕ → ℕ) :
    ∃(seed e zeta : ℝ) (L g : ℕ) (eta0 delta0 : ℝ),
      0<seed ∧ seed≤tau/16384 ∧ 0<e ∧ 0<zeta ∧ zeta≤seed/256 ∧ 0<L ∧ 0<g ∧
      1/(g:ℝ)<min (boundaryWindow tau) ((tau/16)/1000)/4 ∧
      0<eta0 ∧ eta0≤seed/8 ∧ 0<delta0 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i∈fixedCompactClass) → 0≤eta → eta≤eta0 → D.thickness≤delta0 →
        ∀(shadeLower unionCost : ℝ),0<unionCost →
        ENNReal.ofReal shadeLower≤wzTotalShadingVolume D →
        volume (sourceUnion D)≤ENNReal.ofReal (unionCost*D.thickness^extremalExponent) →
        unionCost*D.thickness^eta≤shadeLower →
        ∀cells : Fin n → Finset Index,
        (∀i,D.shading i=wzCellShading (mesh D) cells i) →
        ∀menu : MenuFactory g (extraCount g),MenuRefl menu → MenuSymm menu →
        ∃ref : Reference h tau htau seed e zeta L g,
          ref.dimension=menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1) ∧
          HasCallerUniformities ref menu ∧ ref.original=cells ∧
          ref.E1⊆incidences cells ∧
          D.thickness^(-extremalExponent+eta)≤(NativeFiniteKakeyaCounts.multiplicity D).toReal ∧
          D.thickness^(-extremalExponent+seed/4)≤NativeIncidenceMultiplicityTower.multiplicity ref.E1 := by
  obtain ⟨seed,e,zeta,L,g,eta0,delta0,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,
    heta0,hetaSeed,hdelta0,H⟩ := exists_fixed_source_reference tau htau extraCount
  refine ⟨seed,e,zeta,L,g,eta0,delta0,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,
    heta0,hetaSeed,hdelta0,?_⟩
  intro n D eta h hK heta hetaSmall hsmall shadeLower unionCost hU hShade hUnion hPay
    cells hCells menu hMenuRefl hMenuSymm
  have hnear := native_near_of_volume_bounds h hU hShade hUnion hPay
  obtain ⟨ref,hDimension,hCaller⟩ := H n D eta h hK heta hetaSmall hsmall hnear menu hMenuRefl hMenuSymm
  have hOriginal : ref.original=cells := by
    apply NativeOriginalCellPresentationUnique.cells_eq_of_shading_eq (s:=mesh D) (half_pos h.1.2.1)
    intro i
    exact (ref.backbone.1 i).symm.trans (hCells i)
  have hSubset : ref.E1⊆incidences cells := by
    rw [←hOriginal]
    exact ref.core.1.trans (filter_subset _ _)
  exact ⟨ref,hDimension,hCaller,hOriginal,hSubset,hnear,
    NativeGenericReferenceData.global_near ref heta (hetaSmall.trans hetaSeed) hnear⟩

end NativeFixedSourceReference
