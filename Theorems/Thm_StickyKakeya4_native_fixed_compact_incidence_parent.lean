import Theorems.Thm_StickyKakeya4_native_fixed_compact_normalized_near
import Theorems.Thm_StickyKakeya4_native_near_extremal_physical_parent
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeFixedCompactIncidenceParent
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalCellChartGeometry NativeOriginalParentSelection NativeOriginalParentPhysicalData
open NativeNearExtremalPhysicalParent NativeUnitParentNormalization IncidenceBinTransfer
open NativeFixedCompactKakeyaExponent
open scoped ENNReal

/-- The actual normalized fixed-K0 near-extremizer supplies original cubical
incidences with the exact volume and multiplicity identities. -/
theorem exists_near_extremal_incidence_counts (hk : 0 < extremalExponent)
    {theta0 delta0 : ℝ} (htheta0 : 0 < theta0) (hdelta0 : 0 < delta0) :
    ∃theta : ℝ,0 < theta ∧ theta < theta0 ∧
      ∃ (n : ℕ) (D : FiniteScaleSource n) (cells : Fin n → Finset Index),
        0 < D.thickness ∧ D.thickness < delta0 ∧ IsWangZakharovNativeFiniteInput D theta ∧
        (∀i,D.line i∈fixedCompactClass) ∧
        (∀i,D.shading i=wzCellShading (D.thickness/2) cells i) ∧
        (incidences cells).Nonempty ∧
        (support cells).card*(ENNReal.ofReal (D.thickness/2))^4 ≤
          (ENNReal.ofReal D.thickness).rpow (extremalExponent-theta) ∧
        (ENNReal.ofReal D.thickness).rpow (-extremalExponent+theta) ≤
          (incidences cells).card/((support cells).card:ℝ≥0∞) := by
  obtain ⟨theta,htheta,hthSmall,n,D,hd,hsmall,hinput,hDK,hvol,hmu⟩ :=
    NativeFixedCompactNormalizedNear.exists_normalized_source hk htheta0 hdelta0
  obtain ⟨cells,hc,_hS,hU,hM⟩ := input_exists_incidence_counts hinput
  rw [hU] at hvol
  rw [hM] at hmu
  have hne : (incidences cells).Nonempty := by
    apply card_pos.mp
    by_contra hz
    have hc0 : (incidences cells).card=0 := by omega
    have hp : (0:ℝ≥0∞) < (ENNReal.ofReal D.thickness).rpow (-extremalExponent+theta) :=
      ENNReal.rpow_pos (by positivity) ENNReal.ofReal_ne_top
    simpa [hc0] using hp.trans_le hmu
  exact ⟨theta,htheta,hthSmall,n,D,cells,hd,hsmall,hinput,hDK,hc,hne,hvol,hmu⟩

/-- The physical parent is constructed from the actual normalized fixed-K0
near-source. Its complete parent backbone, original labels, density, and
multiplicity loss are literal source counts, with K0 membership retained. -/
theorem exists_near_extremal_physical_parent (hk : 0 < extremalExponent)
    {theta0 delta0 : ℝ} (htheta0 : 0 < theta0) (hdelta0 : 0 < delta0)
    (N : ℕ) (hN : 0 < N) :
    ∃theta : ℝ,0 < theta ∧ theta < theta0 ∧
      ∃ (n : ℕ) (D : FiniteScaleSource n) (cells : Fin n → Finset Index) (a : ℝ) (p : Parent),
        0 < D.thickness ∧ D.thickness < delta0 ∧ IsWangZakharovNativeFiniteInput D theta ∧
        (∀i,D.line i∈fixedCompactClass) ∧
        (∀i,D.shading i=wzCellShading (mesh D) cells i) ∧
        (incidences cells).Nonempty ∧ p∈parents D a N ∧
        (data D cells a N p).Hypotheses ∧ (data D cells a N p).incidences.Nonempty ∧
        (data D cells a N p).δ=D.thickness/8 ∧
        (incidences cells).card ≤ (parents D a N).card*(data D cells a N p).incidences.card ∧
        (backbone D a N p).Nonempty ∧
        (data D cells a N p).lam*(backbone D a N p).card ≤
          (data D cells a N p).δ*(data D cells a N p).incidences.card ∧
        (∀i∈backbone D a N p,∀j,
          |(data D cells a N p).slope i j| ≤ 1 ∧ |(data D cells a N p).offset i j| ≤ 1) ∧
        (support cells).card*(ENNReal.ofReal (D.thickness/2))^4 ≤
          (ENNReal.ofReal D.thickness).rpow (extremalExponent-theta) ∧
        (ENNReal.ofReal D.thickness).rpow (-extremalExponent+theta) ≤
          (parents D a N).card*ENNReal.ofReal (data D cells a N p).oldMultiplicity := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨theta,htheta,hthSmall,n,D,cells,hd,hsmall,hinput,hDK,hc,hne,hvol,hmu⟩ :=
    exists_near_extremal_incidence_counts hk htheta0
      (lt_min hdelta0 (div_pos (by norm_num : (0:ℝ) < 8) hNr))
  have hscale : (N:ℝ)*(D.thickness/8) ≤ 1 := by
    have hh := (le_div_iff₀ hNr).mp (hsmall.le.trans (min_le_right delta0 (8/(N:ℝ))))
    nlinarith
  obtain ⟨a,p,hp,hP,hneP,hdelta,hret,hB,hdensity⟩ :=
    exists_physical_parent hinput cells hc hne N hN hscale
  refine ⟨theta,htheta,hthSmall,n,D,cells,a,p,hd,hsmall.trans_le (min_le_left _ _),
    hinput,hDK,hc,hne,hp,hP,hneP,hdelta,hret,hB,hdensity,?_,hvol,?_⟩
  · intro i hi j
    exact backbone_parameter_bounds D cells a N hN p hi j
  · exact hmu.trans (original_multiplicity_le_parent_ennreal D cells a N p hne hneP hret)
end NativeFixedCompactIncidenceParent
