import Theorems.Thm_StickyKakeya4_native_actual_sparse_reference_admission

/- UNVERIFIED raw original-incidence lower. The admitted reference is the
same Eref-parent source used by retentionFactor. No admission or cell-image
lower is assumed for the sparse current T, and etaRef is kept literally. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000

noncomputable section
namespace NativeOriginalIncidenceMassLower
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeLocalParentSource
open NativeActualSparseReferenceAdmission
open scoped ENNReal

def retentionConstant : ℝ := 1024*175616*NativeOriginalPrunedMass.volumeConstant

/-- Radius-one AD of the actual admitted source supplies its actual
normalized full-parent population. Only its existing native fields are used. -/
lemma native_volume_population_lower {n : ℕ} {S : FiniteScaleSource n} {etaRef : ℝ}
    (href : IsWangZakharovNativeFiniteInput S etaRef) :
    S.thickness^etaRef ≤ S.thickness^3*(n:ℝ) := by
  have hr := href.1.2.1
  have hc := ENNReal.toReal_mono (show (n:ℝ≥0∞) ≠ ⊤ by finiteness)
    (NativeFiniteKakeyaCounts.carrier_count_lower href)
  simp only [ENNReal.rpow_eq_pow,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal hr.le,
    ENNReal.toReal_natCast] at hc
  calc
    _ = S.thickness^3*S.thickness^(etaRef-3) := by
      rw [←Real.rpow_natCast S.thickness 3,←Real.rpow_add hr]
      congr 1
      norm_num only [Nat.cast_ofNat]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (pow_nonneg hr.le 3)

/-- Exact raw cardinality lower with nu=deltaOriginal*rParent^3. Hp is
the literal original parentEdges set, and T is the same retained incidence
set occurring in the actual retention inequality. -/
theorem raw_incidence_lower {n : ℕ} {D : FiniteScaleSource n} {eta etaRef a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref H T : Finset (Fin n × Index)) (m : ℕ) (p : Parent)
    (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef)
    (population cost : ℝ) (hpopulation : 0 < population) (hcost : 0 < cost)
    (hparent : population*(parentLabels D R a (2^m) p).card ≤
      D.thickness*(parentEdges D a (2^m) H p).card)
    (hretain : ((parentEdges D a (2^m) H p).card:ℝ) ≤ cost*T.card) :
    (population/cost)*(source h R Eref a m p).thickness^etaRef ≤
      D.thickness*(source h R Eref a m p).thickness^3*(T.card:ℝ) := by
  let r := (source h R Eref a m p).thickness
  have hr : 0 < r := href.1.2.1
  have hn := native_volume_population_lower href
  have hpar : population*(parentLabels D R a (2^m) p).card ≤ D.thickness*cost*T.card :=
    hparent.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hretain h.1.2.1.le)
  calc
    _ ≤ (population/cost)*(r^3*(parentLabels D R a (2^m) p).card) :=
      mul_le_mul_of_nonneg_left hn (div_nonneg hpopulation.le hcost.le)
    _ = (r^3/cost)*(population*(parentLabels D R a (2^m) p).card) := by ring
    _ ≤ (r^3/cost)*(D.thickness*cost*T.card) :=
      mul_le_mul_of_nonneg_left hpar (by positivity)
    _ = _ := by field_simp [hcost.ne']

/-- The actual sparse-reference retention payment and its actual etaRef
window give the advertised nine-over256 output power on original edges.
No exponent belonging to a different reference is substituted. -/
theorem paid_raw_incidence_lower {n : ℕ} {D : FiniteScaleSource n} {eta etaRef a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref H T : Finset (Fin n × Index)) (m : ℕ) (p : Parent)
    (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef)
    (population cost : ℝ) (hpopulation : 0 < population) (hcost : 0 < cost)
    (hparent : population*(parentLabels D R a (2^m) p).card ≤
      D.thickness*(parentEdges D a (2^m) H p).card)
    (hretain : ((parentEdges D a (2^m) H p).card:ℝ) ≤ cost*T.card)
    (eps eB window : ℝ) (heps : 0 < eps) (heB : 0 < eB) (_hwindow : 0 < window)
    (hetaRef : etaRef ≤ window*eB/256)
    (hscale : eps ≤ (source h R Eref a m p).thickness^window)
    (hF : retentionFactor cost population ≤ eps^(-(eB/32))) :
    retentionConstant*eps^(9*eB/256) ≤
      D.thickness*(source h R Eref a m p).thickness^3*(T.card:ℝ) := by
  let r := (source h R Eref a m p).thickness
  have hr : 0 < r := href.1.2.1
  have hr1 : r ≤ 1 := href.1.2.2.1
  have hpay : retentionFactor cost population*eps^(eB/32) ≤ 1 := by
    rw [Real.rpow_neg heps.le,←one_div] at hF
    exact (le_div_iff₀ (Real.rpow_pos_of_pos heps (eB/32))).mp hF
  have hCoefficient : retentionConstant*eps^(eB/32) ≤ population/cost := by
    calc
      _ = (population/cost)*(retentionFactor cost population*eps^(eB/32)) := by
        unfold retentionFactor retentionConstant
        field_simp [hcost.ne',hpopulation.ne']
      _ ≤ (population/cost)*1 := mul_le_mul_of_nonneg_left hpay (by positivity)
      _ = _ := mul_one _
  have hReferencePower : eps^(eB/256) ≤ r^etaRef := by
    have hh := Real.rpow_le_rpow heps.le hscale (show 0 ≤ eB/256 by positivity)
    have he : ((source h R Eref a m p).thickness^window)^(eB/256)=r^(window*eB/256) := by
      rw [←Real.rpow_mul hr.le]
      congr 1
      ring
    rw [he] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_ge hr hr1 hetaRef)
  have hraw := raw_incidence_lower h R Eref H T m p href population cost hpopulation hcost hparent hretain
  calc
    _ = (retentionConstant*eps^(eB/32))*eps^(eB/256) := by
      rw [mul_assoc,←Real.rpow_add heps]
      congr 2
      ring
    _ ≤ (population/cost)*r^etaRef :=
      mul_le_mul hCoefficient hReferencePower (Real.rpow_nonneg heps.le _) (by positivity)
    _ ≤ _ := hraw

end NativeOriginalIncidenceMassLower
