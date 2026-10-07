/- UNVERIFIED source-record attachment for the deterministic point reader. -/
import Theorems.Thm_StickyKakeya4_native_configured_point_degree_reader
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeConfiguredPointDegreeReader
open Classical Finset StickyKakeya4 NativeOriginalParentSelection
open NativeJointUniformCoarseRelations NativeConfiguredThirdRelation
open NativeRetainedSliceCountTransfer CanonicalConfiguredE4Bridge
open NativeHorizontalGrainSlice NativeReferenceXYGridPoints SelfUniform

/-- Source-facing rank-two readback. The caller comparisons are extracted
from the actual unique third record, with its full enlarged relation table. -/
theorem from_rank_two_source {n d J : ℕ} (D : FiniteScaleSource n)
    (zeta a : ℝ) (m : ℕ)
    (plane : NativeCommonCubicalMesh.Index → Submodule ℝ E4)
    (E Hgraph S T : Finset (Fin n × NativeCommonCubicalMesh.Index))
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = 1)
    (Fraw Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (p : Parent)
    (population PL PU : ℝ) (Qref : ℕ) (lambda G Cpre t : ℝ) (L3 : ℕ)
    (extra : Fin d → (Fin n × NativeCommonCubicalMesh.Index) →
      (Fin n × NativeCommonCubicalMesh.Index) → Prop)
    (CX : ℝ) (R u : ℕ)
    (Hdata :
      let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
        (by norm_num) (by norm_num) hd
        (NativeGrainQuotientFibers.physicalMesh m (NativeSquaredGrainQueries.phaseDepth m)/8)
      let F := NativeReferenceXYGridField.fixedField D a m 2 plane Sq Fraw
      NativeThirdXYSourceData.HasThirdXYSourceData (J:=J)
        D zeta a m plane E Hgraph S T P hP (by norm_num) (by norm_num) hd Fraw p
        population PL PU Qref lambda G Cpre t L3
        (completeRelations D a m p .oneTwo P hP hd F Fcfg R u extra) CX) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
      (by norm_num) (by norm_num) hd
      (NativeGrainQuotientFibers.physicalMesh m (NativeSquaredGrainQueries.phaseDepth m)/8)
    let F := NativeReferenceXYGridField.fixedField D a m 2 plane Sq Fraw
    let pair := geometricPairKey D a m p .oneTwo P hP hd F Fcfg R u
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    HasUniformFibers (T.image pair) (Q3 ^ 2) Prod.snd ∧
      ∀ h : ℤ,
        let Tz := T.filter (fun z => height m R (pair z).2 = h)
        HasUniformFibers Tz Q3 pair ∧
          HasUniformFibers Tz Q3 (fun z => (pair z).2) ∧
          HasUniformFibers (Tz.image pair) (Q3 ^ 2) Prod.snd := by
  intro Sq F pair Q3
  have Hrel := Hdata.1.2.2.2.2.2.1
  exact from_caller D a m p .oneTwo P hP hd F Fcfg R u extra T Q3 Hrel

end NativeConfiguredPointDegreeReader
