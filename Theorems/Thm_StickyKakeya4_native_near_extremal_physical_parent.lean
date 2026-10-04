import Theorems.Thm_StickyKakeya4_native_original_parent_physical_data
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeNearExtremalPhysicalParent
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalCellChartGeometry NativeOriginalParentSelection NativeOriginalParentPhysicalData
open NativeFiniteKakeyaExponent IncidenceBinTransfer
open scoped ENNReal

lemma backbone_parameter_bounds {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (p : Parent) {i : Fin n}
    (hi : i ∈ backbone D a N p) (j : Fin 3) :
    |(data D cells a N p).slope i j| ≤ 1 ∧ |(data D cells a N p).offset i j| ≤ 1 := by
  have he := (mem_filter.mp hi).2
  have hs : ⌊(N : ℝ) * slope (D.line i) j⌋ = p.1 j := congrFun (congrArg Prod.fst he) j
  have hb : ⌊(N : ℝ) * shiftedIntercept (D.line i) (mesh D) (shift D a) j⌋ = p.2 j :=
    congrFun (congrArg Prod.snd he) j
  exact ⟨floor_parent_slope_bound hN hs, floor_parent_slope_bound hN hb⟩

lemma oldSupport_card_le {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) :
    (data D cells a N p).oldSupport.card ≤ (support cells).card := by
  have he : (data D cells a N p).oldSupport =
      ((parentIncidences D cells a N p).image Prod.snd).image (chartIndex (shift D a)) := by
    simp only [PhysicalRescalingIncidenceTransfer.Data.oldSupport, oldCells, data,
      chartIncidences, image_image, Function.comp_def]
  rw [he, card_image_of_injective _ (chartIndex_injective _), support_eq_image]
  exact card_le_card (image_subset_image (filter_subset _ _))

lemma original_multiplicity_le_parent {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) (hne : (incidences cells).Nonempty)
    (hneP : (data D cells a N p).incidences.Nonempty)
    (hret : (incidences cells).card ≤ (parents D a N).card * (data D cells a N p).incidences.card) :
    (incidences cells).card / ((support cells).card : ℝ) ≤
      (parents D a N).card * (data D cells a N p).oldMultiplicity := by
  have hU : (0 : ℝ) < (support cells).card := by
    rw [support_eq_image]
    exact_mod_cast card_pos.mpr (hne.image Prod.snd)
  have hP : (0 : ℝ) < (data D cells a N p).oldSupport.card := by
    exact_mod_cast card_pos.mpr (hneP.image Prod.snd)
  change (incidences cells).card / ((support cells).card : ℝ) ≤
    (parents D a N).card * ((data D cells a N p).incidences.card / ((data D cells a N p).oldSupport.card : ℝ))
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hU hP).mpr
  exact_mod_cast Nat.mul_le_mul hret (oldSupport_card_le D cells a N p)

lemma original_multiplicity_le_parent_ennreal {n : ℕ} (D : FiniteScaleSource n)
    (cells : Fin n → Finset Index) (a : ℝ) (N : ℕ) (p : Parent)
    (hne : (incidences cells).Nonempty) (hneP : (data D cells a N p).incidences.Nonempty)
    (hret : (incidences cells).card ≤ (parents D a N).card * (data D cells a N p).incidences.card) :
    (incidences cells).card / ((support cells).card : ℝ≥0∞) ≤
      (parents D a N).card * ENNReal.ofReal (data D cells a N p).oldMultiplicity := by
  have hU : (0 : ℝ) < (support cells).card := by
    rw [support_eq_image]
    exact_mod_cast card_pos.mpr (hne.image Prod.snd)
  have hh := ENNReal.ofReal_le_ofReal (original_multiplicity_le_parent D cells a N p hne hneP hret)
  simpa only [ENNReal.ofReal_div_of_pos hU, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast] using hh

/-- A positive native extremal infimum produces actual original D, actual cell
rows, an occupied original parameter parent, and its completely constructed
physical data. Parent loss and density are literal original counts. -/
theorem exists_near_extremal_physical_parent (hk : 0 < extremalExponent)
    {theta0 delta0 : ℝ} (htheta0 : 0 < theta0) (hdelta0 : 0 < delta0)
    (N : ℕ) (hN : 0 < N) :
    ∃ theta : ℝ, 0 < theta ∧ theta < theta0 ∧
      ∃ (n : ℕ) (D : FiniteScaleSource n) (cells : Fin n → Finset Index) (a : ℝ) (p : Parent),
        0 < D.thickness ∧ D.thickness < delta0 ∧
        IsWangZakharovNativeFiniteInput D theta ∧
        (∀ i, D.shading i = wzCellShading (mesh D) cells i) ∧
        (incidences cells).Nonempty ∧ p ∈ parents D a N ∧
        (data D cells a N p).Hypotheses ∧ (data D cells a N p).incidences.Nonempty ∧
        (data D cells a N p).δ = D.thickness / 8 ∧
        (incidences cells).card ≤ (parents D a N).card * (data D cells a N p).incidences.card ∧
        (backbone D a N p).Nonempty ∧
        (data D cells a N p).lam * (backbone D a N p).card ≤
          (data D cells a N p).δ * (data D cells a N p).incidences.card ∧
        (∀ i ∈ backbone D a N p, ∀ j,
          |(data D cells a N p).slope i j| ≤ 1 ∧ |(data D cells a N p).offset i j| ≤ 1) ∧
        (support cells).card * (ENNReal.ofReal (D.thickness / 2)) ^ 4 ≤
          (ENNReal.ofReal D.thickness).rpow (extremalExponent - theta) ∧
        (ENNReal.ofReal D.thickness).rpow (-extremalExponent + theta) ≤
          (parents D a N).card * ENNReal.ofReal (data D cells a N p).oldMultiplicity := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨theta, htheta, htheta0', n, D, cells, hd, hsmall, hinput, hc, hne, hvol, hmu⟩ :=
    exists_near_extremal_incidence_counts hk htheta0
      (lt_min hdelta0 (div_pos (by norm_num : (0 : ℝ) < 8) hNr))
  have hscale : (N : ℝ) * (D.thickness / 8) ≤ 1 := by
    have hh := (le_div_iff₀ hNr).mp (hsmall.le.trans (min_le_right delta0 (8 / (N : ℝ))))
    nlinarith
  obtain ⟨a, p, hp, hP, hneP, hdelta, hret, hB, hdensity⟩ :=
    exists_physical_parent hinput cells hc hne N hN hscale
  refine ⟨theta, htheta, htheta0', n, D, cells, a, p, hd,
    hsmall.trans_le (min_le_left _ _), hinput, hc, hne, hp, hP, hneP, hdelta,
    hret, hB, hdensity, ?_, hvol, ?_⟩
  · intro i hi j
    exact backbone_parameter_bounds D cells a N hN p hi j
  · exact hmu.trans (original_multiplicity_le_parent_ennreal D cells a N p hne hneP hret)
end NativeNearExtremalPhysicalParent
