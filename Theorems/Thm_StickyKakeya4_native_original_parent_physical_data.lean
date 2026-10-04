import Theorems.Thm_StickyKakeya4_native_original_parent_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeOriginalParentPhysicalData
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalCellChartGeometry NativeOriginalParentSelection IncidenceBinTransfer

lemma exists_common_height {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) :
    ∃ a : ℝ, ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  obtain ⟨_hdir, a, b, hwidth, hcommon⟩ := h.2.1
  exact ⟨a, fun i => (hcommon.2 i).2 a ⟨le_rfl, by linarith⟩⟩

lemma original_cell_in_tube {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀ i, D.shading i = wzCellShading (mesh D) cells i)
    {i : Fin n} {k : Index} (hk : (i, k) ∈ incidences cells) :
    cellCenter (mesh D) k ∈ markedUnitTube (D.line i) (2 * mesh D) := by
  have hm : 0 < mesh D := half_pos h.1.2.1
  have hki := (mem_incidences cells i k).mp hk
  have hx : cellCenter (mesh D) k ∈ D.shading i := by
    rw [hcells i]
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hki, cellCenter_mem hm k⟩⟩
  have hh := h.1.2.2.2.2.2.2.2.2.1 i hx
  have he : 2 * mesh D = D.thickness := by unfold mesh; ring
  rwa [he]

lemma original_cell_bounds {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀ i, D.shading i = wzCellShading (mesh D) cells i) (a : ℝ)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    {i : Fin n} {k : Index} (hk : (i, k) ∈ incidences cells) :
    |(ShearBinFibers.oldCenter (mesh D / 4) (chartIndex (shift D a) k)).2| ≤ 1 ∧
      ∀ j : Fin 3,
        |(ShearBinFibers.oldCenter (mesh D / 4) (chartIndex (shift D a) k)).1 j -
          shiftedIntercept (D.line i) (mesh D) (shift D a) j - slope (D.line i) j *
            (ShearBinFibers.oldCenter (mesh D / 4) (chartIndex (shift D a) k)).2| ≤ 12 * (mesh D / 4) := by
  apply normalized_cell_bounds (D.line i) (h.1.2.2.2.2.1 i) (h.2.1.1 i)
    (half_pos h.1.2.1) _ (ha i) k (original_cell_in_tube h cells hcells hk)
  linarith [h.1.2.2.1]

lemma used_subset_backbone {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) :
    @usedTubes (Fin n) ShearBinFibers.Index (Classical.decEq _) (data D cells a N p).incidences ⊆
      backbone D a N p := by
  intro t ht
  simp only [usedTubes, mem_image] at ht
  obtain ⟨z, hz, rfl⟩ := ht
  change z ∈ chartIncidences D cells a N p at hz
  obtain ⟨⟨i, k⟩, hi, rfl⟩ := mem_image.mp hz
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩

/-- Every physical hypothesis is DERIVED from the actual original admissible
marked lines and actual original cells in the chosen parameter parent. -/
theorem data_hypotheses {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀ i, D.shading i = wzCellShading (mesh D) cells i) (a : ℝ)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (hscale : (N : ℝ) * (D.thickness / 8) ≤ 1)
    (p : Parent) (hp : p ∈ parents D a N)
    (hne : (parentIncidences D cells a N p).Nonempty) :
    (data D cells a N p).Hypotheses := by
  let P := data D cells a N p
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hrho : 0 < 1 / (N : ℝ) := one_div_pos.mpr hNr
  have hdelta : 0 < P.δ := by change 0 < mesh D / 4; exact div_pos (half_pos h.1.2.1) (by norm_num)
  have hsigma : P.σ ≤ 1 := by
    change (N : ℝ) * (mesh D / 4) ≤ 1
    simpa only [mesh, div_div, show (2 : ℝ) * 4 = 8 by norm_num] using hscale
  apply P.hypotheses_of_full_backbone_density (backbone D a N p)
    (used_subset_backbone D cells a N p) hdelta hN hsigma
    (parentDensity_pos D cells a N p h.1.2.1 hp hne)
    (parentDensity_le_one D cells a N p) _ _ _ (full_backbone_density D cells a N p hp)
  · intro i hi j
    have hbi := used_subset_backbone D cells a N p hi
    have he := (mem_filter.mp hbi).2
    have hj : ⌊(N : ℝ) * slope (D.line i) j⌋ = p.1 j := congrFun (congrArg Prod.fst he) j
    change |(slope (D.line i) j - (p.1 j : ℝ) / N) / (1 / (N : ℝ))| ≤ 1
    exact floor_parent_slope_bound hN hj
  · intro z hz
    change z ∈ chartIncidences D cells a N p at hz
    obtain ⟨⟨i, k⟩, hi, rfl⟩ := mem_image.mp hz
    change |(ShearBinFibers.oldCenter (mesh D / 4) (chartIndex (shift D a) k)).2| ≤ 1
    exact (original_cell_bounds h cells hcells a ha (mem_filter.mp hi).1).1
  · intro z hz j
    change z ∈ chartIncidences D cells a N p at hz
    obtain ⟨⟨i, k⟩, hi, rfl⟩ := mem_image.mp hz
    rw [P.residual_eq_original]
    change |((ShearBinFibers.oldCenter (mesh D / 4) (chartIndex (shift D a) k)).1 j -
      shiftedIntercept (D.line i) (mesh D) (shift D a) j - slope (D.line i) j *
        (ShearBinFibers.oldCenter (mesh D / 4) (chartIndex (shift D a) k)).2) / (1 / (N : ℝ))| ≤
      (12 : ℝ) * ((N : ℝ) * (mesh D / 4))
    rw [abs_div, abs_of_pos hrho]
    apply (div_le_iff₀ hrho).mpr
    calc
      _ ≤ 12 * (mesh D / 4) := (original_cell_bounds h cells hcells a ha (mem_filter.mp hi).1).2 j
      _ = _ := by field_simp

lemma mem_data_incidences {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) (i : Fin n) (c : ShearBinFibers.Index) :
    (i, c) ∈ (data D cells a N p).incidences ↔
      ∃ k ∈ cells i, parentLabel D a N i = p ∧ chartIndex (shift D a) k = c := by
  change (i, c) ∈ chartIncidences D cells a N p ↔ _
  constructor
  · intro hx
    obtain ⟨⟨j, k⟩, hjk, he⟩ := mem_image.mp hx
    have hji : j = i := congrArg Prod.fst he
    have hkc : chartIndex (shift D a) k = c := congrArg Prod.snd he
    subst j
    obtain ⟨hki, hlabel⟩ := mem_filter.mp hjk
    exact ⟨k, (mem_incidences cells i k).mp hki, hlabel, hkc⟩
  · rintro ⟨k, hk, hlabel, he⟩
    exact mem_image.mpr ⟨(i, k), mem_filter.mpr ⟨(mem_incidences cells i k).mpr hk, hlabel⟩,
      Prod.ext rfl he⟩

/-- Actual D -> occupied original parameter parent -> actual physical Data.
The original incidence loss and complete-parent density are explicit counts. -/
theorem exists_physical_parent {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀ i, D.shading i = wzCellShading (mesh D) cells i)
    (hne : (incidences cells).Nonempty) (N : ℕ) (hN : 0 < N)
    (hscale : (N : ℝ) * (D.thickness / 8) ≤ 1) :
    ∃ a : ℝ, ∃ p ∈ parents D a N,
      (data D cells a N p).Hypotheses ∧ (data D cells a N p).incidences.Nonempty ∧
      (data D cells a N p).δ = D.thickness / 8 ∧
      (incidences cells).card ≤ (parents D a N).card * (data D cells a N p).incidences.card ∧
      (backbone D a N p).Nonempty ∧
      (data D cells a N p).lam * (backbone D a N p).card ≤
        (data D cells a N p).δ * (data D cells a N p).incidences.card := by
  obtain ⟨a, ha⟩ := exists_common_height h
  obtain ⟨p, hp, hnep, hret⟩ := exists_parent D cells a N hne
  refine ⟨a, p, hp, data_hypotheses h cells hcells a ha N hN hscale p hp hnep,
    hnep.image _, ?_, hret, backbone_nonempty D a N hp, full_backbone_density D cells a N p hp⟩
  change mesh D / 4 = D.thickness / 8
  unfold mesh
  ring
end NativeOriginalParentPhysicalData
