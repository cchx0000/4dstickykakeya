import Theorems.Thm_StickyKakeya4_native_original_cell_chart_geometry
import Theorems.Thm_StickyKakeya4_physical_rescaling_backbone_density
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeOriginalParentSelection
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalCellChartGeometry IncidenceBinTransfer
abbrev Parent := (Fin 3 → ℤ) × (Fin 3 → ℤ)

def mesh {n : ℕ} (D : FiniteScaleSource n) : ℝ := D.thickness / 2
def shift {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) : ℤ := ⌊a / mesh D⌋
def parentLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (i : Fin n) : Parent :=
  (fun j => ⌊(N : ℝ) * slope (D.line i) j⌋,
    fun j => ⌊(N : ℝ) * shiftedIntercept (D.line i) (mesh D) (shift D a) j⌋)
def parents {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) : Finset Parent :=
  univ.image (parentLabel D a N)
def backbone {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent) : Finset (Fin n) :=
  univ.filter (fun i => parentLabel D a N i = p)
def parentIncidences {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) : Finset (Fin n × Index) :=
  (incidences cells).filter (fun z => parentLabel D a N z.1 = p)
def chartIncidences {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) : Finset (Fin n × ShearBinFibers.Index) :=
  (parentIncidences D cells a N p).image (fun z => (z.1, chartIndex (shift D a) z.2))
def parentDensity {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) : ℝ :=
  min 1 ((mesh D / 4) * (parentIncidences D cells a N p).card / (backbone D a N p).card)

/-- Literal original graph parameters and original labels determine every
field, including density computed on the complete selected parent backbone. -/
def data {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) : PhysicalRescalingIncidenceTransfer.Data (Fin n) where
  incidences := chartIncidences D cells a N p
  δ := mesh D / 4
  N := N
  E := 12
  lam := parentDensity D cells a N p
  globalSlope := fun j => (p.1 j : ℝ) / N
  globalOffset := fun j => (p.2 j : ℝ) / N
  tubeSlope := fun i => slope (D.line i)
  tubeOffset := fun i => shiftedIntercept (D.line i) (mesh D) (shift D a)

lemma chartIncidences_card {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) :
    (chartIncidences D cells a N p).card = (parentIncidences D cells a N p).card := by
  apply card_image_of_injective
  intro z w h
  have hf : z.1 = w.1 := congrArg (fun q : Fin n × ShearBinFibers.Index => q.1) h
  have hs : chartIndex (shift D a) z.2 = chartIndex (shift D a) w.2 :=
    congrArg (fun q : Fin n × ShearBinFibers.Index => q.2) h
  exact Prod.ext hf ((chartIndex_injective _) hs)

lemma backbone_nonempty {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    {p : Parent} (hp : p ∈ parents D a N) : (backbone D a N p).Nonempty := by
  obtain ⟨i, _hi, he⟩ := mem_image.mp hp
  exact ⟨i, mem_filter.mpr ⟨mem_univ _, he⟩⟩

lemma parentDensity_pos {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) (hd : 0 < D.thickness)
    (hp : p ∈ parents D a N) (hne : (parentIncidences D cells a N p).Nonempty) :
    0 < parentDensity D cells a N p := by
  have hI : (0 : ℝ) < (parentIncidences D cells a N p).card := by exact_mod_cast card_pos.mpr hne
  have hT : (0 : ℝ) < (backbone D a N p).card := by exact_mod_cast card_pos.mpr (backbone_nonempty D a N hp)
  unfold parentDensity mesh
  positivity

lemma parentDensity_le_one {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) : parentDensity D cells a N p ≤ 1 := min_le_left _ _

lemma full_backbone_density {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) (hp : p ∈ parents D a N) :
    (data D cells a N p).lam * (backbone D a N p).card ≤
      (data D cells a N p).δ * (data D cells a N p).incidences.card := by
  have hT : (0 : ℝ) < (backbone D a N p).card := by exact_mod_cast card_pos.mpr (backbone_nonempty D a N hp)
  change parentDensity D cells a N p * (backbone D a N p).card ≤
    (mesh D / 4) * (chartIncidences D cells a N p).card
  rw [chartIncidences_card]
  exact (le_div_iff₀ hT).mp (min_le_right _ _)

/-- A genuinely occupied original parameter cell is selected by its original
incidence count. The loss is the actual number of original parent labels. -/
theorem exists_parent {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (hne : (incidences cells).Nonempty) :
    ∃ p ∈ parents D a N, (parentIncidences D cells a N p).Nonempty ∧
      (incidences cells).card ≤ (parents D a N).card * (data D cells a N p).incidences.card := by
  have hpar : (parents D a N).Nonempty := by
    obtain ⟨⟨i, k⟩, _hk⟩ := hne
    exact ⟨parentLabel D a N i, mem_image_of_mem _ (mem_univ i)⟩
  obtain ⟨p, hp, hmax⟩ := exists_max_image (parents D a N)
    (fun p => (parentIncidences D cells a N p).card) hpar
  have hret : (incidences cells).card ≤
      (parentIncidences D cells a N p).card * (parents D a N).card := by
    apply card_le_mul_card_image_of_maps_to (f := fun z : Fin n × Index => parentLabel D a N z.1)
    · intro z _hz
      exact mem_image_of_mem _ (mem_univ z.1)
    · exact hmax
  have hne' : (parentIncidences D cells a N p).Nonempty := by
    apply card_pos.mp
    have hi := card_pos.mpr hne
    by_contra hz
    have hz' : (parentIncidences D cells a N p).card = 0 := by omega
    rw [hz', zero_mul] at hret
    omega
  refine ⟨p, hp, hne', ?_⟩
  change (incidences cells).card ≤ (parents D a N).card * (chartIncidences D cells a N p).card
  rw [chartIncidences_card]
  simpa [Nat.mul_comm] using hret

lemma floor_parent_slope_bound {N : ℕ} (hN : 0 < N) {x : ℝ} {k : ℤ}
    (hk : ⌊(N : ℝ) * x⌋ = k) : |(x - (k : ℝ) / N) / (1 / (N : ℝ))| ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo := Int.floor_le ((N : ℝ) * x)
  have hhi := Int.lt_floor_add_one ((N : ℝ) * x)
  rw [hk] at hlo hhi
  have he : (x - (k : ℝ) / N) / (1 / (N : ℝ)) = (N : ℝ) * x - k := by
    field_simp
  rw [he]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
end NativeOriginalParentSelection
