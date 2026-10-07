/- UNVERIFIED source-cell witness and fixed-arity higher-key factory.
No compiler or imported-axiom check has run. Frozen48 source is unchanged.

oldHeight reads only the SELECTED remembered tagged image B. The source-cell
reader selects one genuine original witness, never asserts that every old
antecedent of a forgotten intermediate pair has the same height.

The higher-key factory reserves1+2(g+1) slots before the source. Its actual
field values and packed isometry may be chosen after the native source S
exists and before the unique second Reference core. It evaluates a frame
on original source-cell centers; S's source and cells are never rotated.
Key comparability below concerns ref.E1 only. A later rank/subset cut needs
its own actual same-core relation query before any profile lower is reused.
-/
import Theorems.Thm_StickyKakeya4_native_remembered_source_construction
import Theorems.Thm_StickyKakeya4_native_actual_higher_transfer_construction_draft_2020
import Theorems.Thm_StickyKakeya4_native_extra_queried_rank_configuration
import Theorems.Thm_StickyKakeya4_native_fixed_source_reference

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeRememberedHigherKeyFactoryDraft2032
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeRememberedSourceMaps NativeLocalCellCoherence NativeTranslatedGrainHeightOverlap
open NativePackedHigherCapacityDraft2006 NativeGenericReferenceData
open NativeExtraQueriedRankConfiguration NativeJointUniformCoarseRelations
open SelfUniform

def oldHeight {nA : ℕ} (B : Finset (ℤ × (Fin nA × Index))) (t : ℤ) : ℤ :=
  if ht : ∃v∈B,finalTime v=t then (Classical.choose ht).1 else 0

theorem oldHeight_readback {nA : ℕ} (B : Finset (ℤ × (Fin nA × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (v : ℤ × (Fin nA × Index)) (hv : v∈B) : oldHeight B (finalTime v)=v.1 := by
  have ht : ∃w∈B,finalTime w=finalTime v := ⟨v,hv,rfl⟩
  simp only [oldHeight,dif_pos ht]
  exact hB (Classical.choose ht) (Classical.choose_spec ht).1 v hv (Classical.choose_spec ht).2

/-- Literal membership of the reindexed local source's cells supplies the
original occurrence and its SELECTED tag, including its exact source time.
This derives the same-old-height fact from the actual source constructor. -/
theorem source_cell_occurrence {n nA : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (C : FiniteScaleSource nA) (R : Finset (Fin nA)) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (i : Fin (parentLabels C R 0 (2^c) pA).card) (k : Index)
    (hk : k∈sourceCells C R (selectedPairs D a m C c pA O B) 0 (2^c) pA i) :
    ∃(v : Fin nA × Index) (z : Fin n × Index),
      v∈selectedPairs D a m C c pA O B ∧ (v,z)∈O ∧
      parentLabel C 0 (2^c) v.1=pA ∧ localCellLabel C 0 (2^c) pA v=k ∧
      taggedKey D a m C c pA (v,z)∈B ∧
      translatedHeight D a m z.2=oldHeight B (k 3) := by
  let j := NativePaddedCellSource.originalLabel (parentLabels C R 0 (2^c) pA) i
  have hk' : k∈outputCells C (selectedPairs D a m C c pA O B) 0 (2^c) pA j := hk
  obtain ⟨l,hl,hlabel⟩ := (mem_outputCells C (selectedPairs D a m C c pA O B) 0 (2^c) pA j k).mp hk'
  obtain ⟨z,hOcc,hTag⟩ := selected_pair_witness D a m C c pA O B (j,l) hl
  have hj : parentLabel C 0 (2^c) j=pA :=
    ((mem_parentLabels C R 0 (2^c) pA j).mp
      (NativePaddedCellSource.originalLabel_mem (parentLabels C R 0 (2^c) pA) i)).2
  have hcell : localCellLabel C 0 (2^c) pA (j,l)=k := hlabel
  have htime : finalTime (taggedKey D a m C c pA ((j,l),z))=k 3 := by
    change localCellLabel C 0 (2^c) pA (j,l) 3=k 3
    exact congrFun hcell 3
  have hHeight := oldHeight_readback B hB (taggedKey D a m C c pA ((j,l),z)) hTag
  rw [htime] at hHeight
  exact ⟨(j,l),z,hl,hOcc,hj,hcell,hTag,hHeight.symm⟩

/-- Every cell surviving the second literal Reference or rank cut still
has a good original witness. Subset membership alone suffices here. -/
theorem retained_cell_occurrence {n nA : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (C : FiniteScaleSource nA) (R : Finset (Fin nA)) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (E : Finset (Fin (parentLabels C R 0 (2^c) pA).card × Index))
    (hE : E⊆incidences (sourceCells C R (selectedPairs D a m C c pA O B) 0 (2^c) pA)) :
    ∀k∈E.image Prod.snd,∃(v : Fin nA × Index) (z : Fin n × Index),
      v∈selectedPairs D a m C c pA O B ∧ (v,z)∈O ∧
      parentLabel C 0 (2^c) v.1=pA ∧ localCellLabel C 0 (2^c) pA v=k ∧
      taggedKey D a m C c pA (v,z)∈B ∧
      translatedHeight D a m z.2=oldHeight B (k 3) := by
  intro k hk
  obtain ⟨e,he,rfl⟩ := mem_image.mp hk
  exact source_cell_occurrence D a m C R c pA O B hB e.1 e.2
    ((mem_incidences _ e.1 e.2).mp (hE he))

/-- The number of relation slots depends on the prepared schedule size,
not on source depth, source height count, or the later coefficient values. -/
def extraCount (g : ℕ) : ℕ := 1+((g+1)+(g+1))

def coarseRatio (level : ℕ) (depth : Fin (level+1)) : ℕ := 2^(level-depth.val)

def coarseXKey (mu : ℝ) (O : E4 ≃ₗᵢ[ℝ] E4) (R : ℕ) (k : Index) : Fin 2 → ℤ :=
  fun j => packedXKey mu O k j/(R:ℤ)

def localXKey (mu : ℝ) (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ)
    (R : ℕ) (k : Index) : (ℤ × ℤ) × (Fin 2 → ℤ) :=
  (packedHigherKey mu O C F k,coarseXKey mu O R k)

def keyRelations {n level g : ℕ} (D : FiniteScaleSource n)
    (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ)
    (schedule : Fin (g+1) → Fin (level+1)) :
    Fin (extraCount g) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.addCases
    (fun _ : Fin 1 => fun x y => packedHigherKey (D.thickness/2) O C F x.2=
      packedHigherKey (D.thickness/2) O C F y.2)
    (Fin.addCases
      (fun j x y => packedCoarseKey (D.thickness/2) O C F (coarseRatio level (schedule j)) x.2=
        packedCoarseKey (D.thickness/2) O C F (coarseRatio level (schedule j)) y.2)
      (fun j x y => localXKey (D.thickness/2) O C F (coarseRatio level (schedule j)) x.2=
        localXKey (D.thickness/2) O C F (coarseRatio level (schedule j)) y.2))

/-- Quantified labels are evaluated after D/backbone/schedule exist and
before E1. The fixed O,C,F are read-only source data, not selected-core data. -/
def factory (g : ℕ) (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ) : MenuFactory g (extraCount g) :=
  fun _n D _eta _h _a _level _R _original schedule => keyRelations D O C F schedule

lemma factory_refl (g : ℕ) (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ) : MenuRefl (factory g O C F) := by
  intro n D eta h a level R original schedule i
  refine Fin.addCases (fun _ _ => rfl) ?_ i
  exact Fin.addCases (fun _ _ => rfl) (fun _ _ => rfl)

lemma factory_symm (g : ℕ) (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ) : MenuSymm (factory g O C F) := by
  intro n D eta h a level R original schedule i
  refine Fin.addCases (fun _ _ _ hh => hh.symm) ?_ i
  exact Fin.addCases (fun _ _ _ hh => hh.symm) (fun _ _ _ hh => hh.symm)

/-- Source-derived point and higher-key labels remain separate. This
reads the actual caller slot comparison on the SAME literal E1 graph. -/
theorem reference_key_uniformities {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ)
    (H : HasCallerUniformities ref (factory g O C F)) :
    HasUniformFibers ref.E1 (NativeOriginalParentDensityCore.coreRadix ref.original ref.R L)
      (fun z => packedHigherKey (D.thickness/2) O C F z.2) ∧
    (∀j,HasUniformFibers ref.E1 (NativeOriginalParentDensityCore.coreRadix ref.original ref.R L)
      (fun z => packedCoarseKey (D.thickness/2) O C F (coarseRatio ref.level (ref.schedule j)) z.2)) ∧
    (∀j,HasUniformFibers ref.E1 (NativeOriginalParentDensityCore.coreRadix ref.original ref.R L)
      (fun z => localXKey (D.thickness/2) O C F (coarseRatio ref.level (ref.schedule j)) z.2)) := by
  constructor
  · intro x hx y hy
    have hh := H (Fin.castAdd ((g+1)+(g+1)) (0:Fin 1)) x hx y hy
    simpa only [factory,keyRelations,Fin.addCases_left,unit_degree_eq_fiber] using hh
  · constructor
    · intro j x hx y hy
      have hh := H (Fin.natAdd 1 (Fin.castAdd (g+1) j)) x hx y hy
      simpa only [factory,keyRelations,Fin.addCases_right,Fin.addCases_left,unit_degree_eq_fiber] using hh
    · intro j x hx y hy
      have hh := H (Fin.natAdd 1 (Fin.natAdd (g+1) j)) x hx y hy
      simpa only [factory,keyRelations,Fin.addCases_right,unit_degree_eq_fiber] using hh

/-- The second Reference parameters and arity precede the native remembered
source. The actual O,C,F values are chosen only AFTER that source exists.
This installs the real finite keys on its literal output incidence graph.
Near extremality is derived by the fixed-source factory from actual volume
estimates; no multiplicity certificate or chosen-source substitution occurs. -/
theorem exists_reference_with_higher_keys (tau : ℝ) (htau : 0<tau) :
    ∃(seed e zeta : ℝ) (L g : ℕ) (eta0 delta0 : ℝ),
      0<seed ∧ seed≤tau/16384 ∧ 0<e ∧ 0<zeta ∧ zeta≤seed/256 ∧ 0<L ∧ 0<g ∧
      1/(g:ℝ)<min (NativeAllTwoScaleConfiguration.boundaryWindow tau) ((tau/16)/1000)/4 ∧
      0<eta0 ∧ eta0≤seed/8 ∧ 0<delta0 ∧
      ∀(n : ℕ) (S : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput S eta),
        (∀i,S.line i∈NativeUnitParentNormalization.fixedCompactClass) →
        0≤eta → eta≤eta0 → S.thickness≤delta0 →
        ∀(shadeLower unionCost : ℝ),0<unionCost →
        ENNReal.ofReal shadeLower≤wzTotalShadingVolume S →
        MeasureTheory.volume (sourceUnion S)≤
          ENNReal.ofReal (unionCost*S.thickness^NativeFixedCompactKakeyaExponent.extremalExponent) →
        unionCost*S.thickness^eta≤shadeLower →
        ∀cells : Fin n → Finset Index,
        (∀i,S.shading i=wzCellShading (mesh S) cells i) →
        ∀(O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ),
        ∃ref : Reference h tau htau seed e zeta L g,
          ref.original=cells ∧ ref.E1⊆incidences cells ∧
          S.thickness^(-NativeFixedCompactKakeyaExponent.extremalExponent+eta)≤
            (NativeFiniteKakeyaCounts.multiplicity S).toReal ∧
          S.thickness^(-NativeFixedCompactKakeyaExponent.extremalExponent+seed/4)≤
            NativeIncidenceMultiplicityTower.multiplicity ref.E1 ∧
          HasCallerUniformities ref (factory g O C F) ∧
          HasUniformFibers ref.E1 (NativeOriginalParentDensityCore.coreRadix cells ref.R L)
            (fun z => packedHigherKey (S.thickness/2) O C F z.2) ∧
          (∀j,HasUniformFibers ref.E1 (NativeOriginalParentDensityCore.coreRadix cells ref.R L)
            (fun z => packedCoarseKey (S.thickness/2) O C F (coarseRatio ref.level (ref.schedule j)) z.2)) ∧
          (∀j,HasUniformFibers ref.E1 (NativeOriginalParentDensityCore.coreRadix cells ref.R L)
            (fun z => localXKey (S.thickness/2) O C F (coarseRatio ref.level (ref.schedule j)) z.2)) := by
  obtain ⟨seed,e,zeta,L,g,eta0,delta0,hs,hst,he,hz,hzs,hL,hg,hgrid,heta0,hetaSeed,hdelta0,H⟩ :=
    NativeFixedSourceReference.exists_reference_from_volume_bounds tau htau extraCount
  refine ⟨seed,e,zeta,L,g,eta0,delta0,hs,hst,he,hz,hzs,hL,hg,hgrid,heta0,hetaSeed,hdelta0,?_⟩
  intro n S eta h hK heta hetaSmall hsmall shadeLower unionCost hU hShade hUnion hPay cells hCells O C F
  obtain ⟨ref,_hDim,hCaller,hOriginal,hSubset,hNear,hCoreNear⟩ :=
    H n S eta h hK heta hetaSmall hsmall shadeLower unionCost hU hShade hUnion hPay cells hCells
      (factory g O C F) (factory_refl g O C F) (factory_symm g O C F)
  have hKeys := reference_key_uniformities ref O C F hCaller
  rw [hOriginal] at hKeys
  exact ⟨ref,hOriginal,hSubset,hNear,hCoreNear,hCaller,hKeys.1,hKeys.2.1,hKeys.2.2⟩

end NativeRememberedHigherKeyFactoryDraft2032
