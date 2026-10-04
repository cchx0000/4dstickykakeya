import Theorems.Thm_StickyKakeya4_native_coarse_original_incidences
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeCoarseOriginalGeometry
open Classical Finset IncidenceBinTransfer NativeOriginalSlicePopulation NativeCoarseOriginalIncidences
variable {T : Type*}
/-- Exact nearest-center error of the actual half-open floor cell. -/
theorem scalar_floor_center_error {sigma : ℝ} (hs : 0 < sigma) (x : ℝ) :
    |sigma*((⌊x/sigma⌋:ℝ)+1/2)-x| ≤ sigma/2 := by
  have hlo := (le_div_iff₀ hs).mp (Int.floor_le (x/sigma))
  have hhi := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one (x/sigma))
  exact abs_le.mpr ⟨by linarith only [hlo,hhi],by linarith only [hlo,hhi]⟩
theorem spatial_rounding (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (c : Cell) (j : Fin 3) :
    |(ShearBinFibers.oldCenter P.σ (P.cellBin c)).1 j-(P.center c).1 j| ≤ P.σ/2 := by
  rw [P.cellBin_eq_gridBin]
  exact scalar_floor_center_error (P.scale_pos hP) _
theorem height_rounding (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses) (c : Cell) :
    |(ShearBinFibers.oldCenter P.σ (P.cellBin c)).2-(P.center c).2| ≤ P.σ/2 := by
  rw [P.cellBin_eq_gridBin]
  exact scalar_floor_center_error (P.scale_pos hP) _
/-- The rounded coarse center has the SAME original affine tube parameters,
 transformed by the actual shear. Rounding adds exactly one sigma of error. -/
theorem rounded_residual (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    {t : T} {c : Cell} (hc : (t,c) ∈ P.incidences) (j : Fin 3) :
    |(ShearBinFibers.oldCenter P.σ (P.cellBin c)).1 j-P.offset t j-
      P.slope t j*(ShearBinFibers.oldCenter P.σ (P.cellBin c)).2| ≤ ((P.E:ℝ)+1)*P.σ := by
  have hs := hP.slope_bound t (mem_image_of_mem Prod.fst hc) j
  have hx := spatial_rounding P hP c j
  have ht := height_rounding P hP c
  have he := hP.physical_bound (t,c) hc j
  have hm : |P.slope t j| * |(ShearBinFibers.oldCenter P.σ (P.cellBin c)).2-(P.center c).2| ≤ P.σ/2 := by
    calc
      _ ≤ 1*(P.σ/2) := mul_le_mul hs ht (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  calc
    _ = |P.residual t c j+
      ((ShearBinFibers.oldCenter P.σ (P.cellBin c)).1 j-(P.center c).1 j)-
      P.slope t j*((ShearBinFibers.oldCenter P.σ (P.cellBin c)).2-(P.center c).2)| := by
        congr 1
        unfold PhysicalRescalingIncidenceTransfer.Data.residual
        ring
    _ ≤ |P.residual t c j|+
      |(ShearBinFibers.oldCenter P.σ (P.cellBin c)).1 j-(P.center c).1 j|+
      |P.slope t j*((ShearBinFibers.oldCenter P.σ (P.cellBin c)).2-(P.center c).2)| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ _ := by rw [abs_mul]; linarith only [he,hx,hm]
/-- Physical time is read from the actual coarse point, including rounding. -/
theorem rounded_height_bound (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    {t : T} {c : Cell} (hc : (t,c) ∈ P.incidences) :
    |(ShearBinFibers.oldCenter P.σ (P.cellBin c)).2| ≤ 1+P.σ/2 := by
  have ht := hP.time_bound (t,c) hc
  have he := height_rounding P hP c
  calc
    _ = |((ShearBinFibers.oldCenter P.σ (P.cellBin c)).2-(P.center c).2)+(P.center c).2| := by congr 1; ring
    _ ≤ |(ShearBinFibers.oldCenter P.σ (P.cellBin c)).2-(P.center c).2|+|(P.center c).2| := abs_add_le _ _
    _ ≤ _ := by linarith only [ht,he]
lemma coordinates_scale_space (P : PhysicalRescalingIncidenceTransfer.Data T) (R : ℝ) (c : Cell) (j : Fin 3) :
    (coordinates P R c).1 j=(ShearBinFibers.oldCenter P.σ c).1 j/R := by
  dsimp [coordinates,ShearBinFibers.oldCenter]
  ring
lemma coordinates_scale_height (P : PhysicalRescalingIncidenceTransfer.Data T) (R : ℝ) (c : Cell) :
    height P R c=(ShearBinFibers.oldCenter P.σ c).2/R := by
  dsimp [height,coordinates,ShearBinFibers.oldCenter]
  ring
/-- The concrete normalized incidence residual, on actual image labels. -/
theorem normalized_residual (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (E : Finset (T × Cell)) (hE : E ⊆ P.incidences) {R : ℝ} (hR : 0 < R)
    (c : Cell) (t : T) (hc : (c,t) ∈ incidences P E) (j : Fin 3) :
    |(coordinates P R c).1 j-P.offset t j/R-P.slope t j*height P R c| ≤
      ((P.E:ℝ)+1)*(P.σ/R) := by
  obtain ⟨old,hold,rfl⟩ := (mem_incidences P E c t).mp hc
  rw [coordinates_scale_space,coordinates_scale_height]
  have hid : (ShearBinFibers.oldCenter P.σ (P.cellBin old)).1 j/R-P.offset t j/R-
      P.slope t j*((ShearBinFibers.oldCenter P.σ (P.cellBin old)).2/R)=
      ((ShearBinFibers.oldCenter P.σ (P.cellBin old)).1 j-P.offset t j-
        P.slope t j*(ShearBinFibers.oldCenter P.σ (P.cellBin old)).2)/R := by ring
  rw [hid,abs_div,abs_of_pos hR]
  exact (div_le_div_of_nonneg_right (rounded_residual P hP (hE hold) j) hR.le).trans_eq (by ring)
/-- A genuine original parameter-parent bound also controls transformed
 offsets. It is derived from the literal parent floor label. -/
theorem original_parent_offset_bound {n : ℕ} (D : StickyKakeya4.FiniteScaleSource n)
    (cells : Fin n → Finset NativeCommonCubicalMesh.Index) (a : ℝ) (N : ℕ) (hN : 0 < N)
    (p : NativeOriginalParentSelection.Parent) :
    ∀ t ∈ @usedTubes (Fin n) Cell (Classical.decEq _) (NativeOriginalParentSelection.data D cells a N p).incidences, ∀ j,
      |(NativeOriginalParentSelection.data D cells a N p).offset t j| ≤ 1 := by
  intro t ht j
  have hb := NativeOriginalParentPhysicalData.used_subset_backbone D cells a N p ht
  have he := (mem_filter.mp hb).2
  have hj := congrFun (congrArg Prod.snd he) j
  exact NativeOriginalParentSelection.floor_parent_slope_bound hN hj
/-- One fixed normalization depends only on the already explicit original
 physical error constant; it does not depend on any new point population. -/
def normalization (P : PhysicalRescalingIncidenceTransfer.Data T) : ℝ := 2*((P.E:ℝ)+2)
lemma normalization_pos (P : PhysicalRescalingIncidenceTransfer.Data T) : 0 < normalization P := by
  unfold normalization
  positivity
/-- All actual coarse coordinates fit in the unit box after the SAME common
 space/time normalization, with original tube labels and slopes unchanged. -/
theorem normalized_coordinate_box (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (E : Finset (T × Cell)) (hE : E ⊆ P.incidences)
    (hoff : ∀ t ∈ usedTubes P.incidences, ∀ j, |P.offset t j| ≤ 1)
    (c : Cell) (t : T) (hc : (c,t) ∈ incidences P E) :
    |height P (normalization P) c| ≤ 1 ∧
      ∀ j, |(coordinates P (normalization P) c).1 j| ≤ 1 := by
  obtain ⟨old,hold,rfl⟩ := (mem_incidences P E c t).mp hc
  have ht := rounded_height_bound P hP (hE hold)
  have htime : |(ShearBinFibers.oldCenter P.σ (P.cellBin old)).2| ≤ (3/2:ℝ) := by
    linarith only [ht,hP.scale_le_one]
  have hRn := normalization_pos P
  have hR4 : 4 ≤ normalization P := by
    unfold normalization
    nlinarith only [(show (0:ℝ) ≤ P.E from Nat.cast_nonneg _)]
  constructor
  · rw [coordinates_scale_height,abs_div,abs_of_pos hRn]
    apply (div_le_iff₀ hRn).mpr
    linarith only [htime,hR4]
  · intro j
    have hs := hP.slope_bound t (mem_image_of_mem Prod.fst (hE hold)) j
    have ho := hoff t (mem_image_of_mem Prod.fst (hE hold)) j
    have he := rounded_residual P hP (hE hold) j
    have hst : |P.slope t j| * |(ShearBinFibers.oldCenter P.σ (P.cellBin old)).2| ≤ (3/2:ℝ) := by
      calc
        _ ≤ 1*(3/2:ℝ) := mul_le_mul hs htime (abs_nonneg _) (by norm_num)
        _ = _ := by ring
    have hspace : |(ShearBinFibers.oldCenter P.σ (P.cellBin old)).1 j| ≤ ((P.E:ℝ)+1)*P.σ+1+3/2 := by
      calc
        _ = |((ShearBinFibers.oldCenter P.σ (P.cellBin old)).1 j-P.offset t j-
            P.slope t j*(ShearBinFibers.oldCenter P.σ (P.cellBin old)).2)+P.offset t j+
            P.slope t j*(ShearBinFibers.oldCenter P.σ (P.cellBin old)).2| := by congr 1; ring
        _ ≤ |(ShearBinFibers.oldCenter P.σ (P.cellBin old)).1 j-P.offset t j-
            P.slope t j*(ShearBinFibers.oldCenter P.σ (P.cellBin old)).2|+|P.offset t j|+
            |P.slope t j*(ShearBinFibers.oldCenter P.σ (P.cellBin old)).2| :=
              (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
        _ ≤ _ := by rw [abs_mul]; linarith only [he,ho,hst]
    have hcap : ((P.E:ℝ)+1)*P.σ+1+3/2 ≤ normalization P := by
      have hh := mul_le_mul_of_nonneg_left hP.scale_le_one (show 0 ≤ (P.E:ℝ)+1 by positivity)
      dsimp [normalization]
      nlinarith only [hh,(show (0:ℝ) ≤ P.E from Nat.cast_nonneg _)]
    rw [coordinates_scale_space,abs_div,abs_of_pos hRn]
    exact (div_le_iff₀ hRn).mpr (by simpa only [one_mul] using hspace.trans hcap)
end NativeCoarseOriginalGeometry
