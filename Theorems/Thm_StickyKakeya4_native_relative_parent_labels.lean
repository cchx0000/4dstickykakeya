import Theorems.Thm_StickyKakeya4_native_local_parent_geometry
import Theorems.Thm_StickyKakeya4_native_unit_parent_dyadic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

noncomputable section
namespace NativeRelativeParentLabels
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeLocalParentGeometry NativeContractedUnitParent

/-- The actual contracted local marked line has this graph intercept. -/
theorem actual_local_intercept {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (i : Fin n) (j : Fin 3) :
    intercept (NativeLocalParentGeometry.line D a N p i) j =
      localIntercept D a N p i j / 32 := by
  have hdir : direction (NativeLocalParentGeometry.line D a N p i) (3 : Fin 4) ≠ 0 := by
    unfold NativeLocalParentGeometry.line baseLine
    rw [direction_contractLine]
    exact (NativeGraphMarkedLine.direction_fourth_pos _ _ _).ne'
  have hcenter : rawFrontParam (NativeLocalParentGeometry.line D a N p i, 0) =
      contractPoint (ActualSlopeSource.heightPoint (localIntercept D a N p i) 0) := by
    have hc := contractLine_rawFront (baseLine D a N p i) 0
    simpa only [zero_div, baseLine, NativeGraphMarkedLine.rawFrontParam_eq_center,
      zero_smul, add_zero, NativeLocalParentGeometry.line] using hc.symm
  have hg := raw_graph_identity (NativeLocalParentGeometry.line D a N p i) 0 hdir j
  rw [hcenter] at hg
  simp only [contractPoint, PiLp.smul_apply, smul_eq_mul,
    ActualSlopeSource.heightPoint_castSucc,
    show (3 : Fin 4) = Fin.last 3 by rfl,
    ActualSlopeSource.heightPoint_last, mul_zero, add_zero] at hg
  linarith only [hg]

/-- The quarter-intercept chart is applied to the actual local line at its
own zero-height center. Both fixed contractions are retained explicitly. -/
theorem actual_local_shifted_intercept {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (i : Fin n) (j : Fin 3) :
    shiftedIntercept (NativeLocalParentGeometry.line D a N p i) 1 0 j =
      ((N : ℝ) * shiftedIntercept (D.line i) (mesh D) (shift D a) j - p.2 j) / 512 := by
  rw [shiftedIntercept, actual_local_intercept]
  simp only [Int.cast_zero, zero_mul, mul_zero, add_zero]
  unfold localIntercept
  change (((N : ℝ) * _ - (p.2 j : ℝ)) / 4 / 32) / 4 = _
  ring

def relativeLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (M : ℕ) (i : Fin n) : Parent :=
  (fun j => ⌊(M : ℝ) * slope (NativeLocalParentGeometry.line D a N p i) j⌋,
    fun j => ⌊(M : ℝ) *
      shiftedIntercept (NativeLocalParentGeometry.line D a N p i) 1 0 j⌋)

def projection (p : Parent) (M : ℕ) (z : Parent) : Parent :=
  (fun j => z.1 j - (M : ℤ) * p.1 j,
    fun j => (z.2 j - (M : ℤ) * p.2 j) / 512)

def projectionBox (p : Parent) (M : ℕ) (q : Parent) : Finset Parent :=
  {fun j => q.1 j + (M : ℤ) * p.1 j} ×ˢ
    Fintype.piFinset (fun j =>
      Icc (512 * q.2 j + (M : ℤ) * p.2 j)
        (512 * q.2 j + (M : ℤ) * p.2 j + 511))

/-- The second-scale labels are computed from the SAME original fine
parameter label. In particular there is no new choice of a source family. -/
theorem relativeLabel_eq_projection {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (M : ℕ) (i : Fin n) :
    relativeLabel D a N p M i = projection p M (parentLabel D a (M * N) i) := by
  apply Prod.ext
  · funext j
    change ⌊(M : ℝ) * slope (NativeLocalParentGeometry.line D a N p i) j⌋ = _
    rw [slope_line]
    change ⌊(M : ℝ) * ((N : ℝ) * slope (D.line i) j - (p.1 j : ℝ))⌋ = _
    rw [NativeUnitParentDyadic.floor_sub_integer_mul]
    simp only [projection, parentLabel, Nat.cast_mul, mul_assoc]
  · funext j
    change ⌊(M : ℝ) *
      shiftedIntercept (NativeLocalParentGeometry.line D a N p i) 1 0 j⌋ = _
    rw [actual_local_shifted_intercept, ← mul_div_assoc]
    have hd := Int.floor_div_natCast
      ((M : ℝ) * ((N : ℝ) * shiftedIntercept (D.line i) (mesh D) (shift D a) j -
        (p.2 j : ℝ))) 512
    norm_num only [Nat.cast_ofNat] at hd
    rw [hd, NativeUnitParentDyadic.floor_sub_integer_mul]
    simp only [projection, parentLabel, Nat.cast_mul, mul_assoc]

theorem projection_mem_box (p : Parent) (M : ℕ) (z q : Parent)
    (h : projection p M z = q) : z ∈ projectionBox p M q := by
  apply mem_product.mpr
  constructor
  · apply mem_singleton.mpr
    funext j
    have hh := congrFun (congrArg Prod.fst h) j
    dsimp [projection] at hh
    omega
  · apply Fintype.mem_piFinset.mpr
    intro j
    have hh := congrFun (congrArg Prod.snd h) j
    dsimp [projection] at hh
    apply mem_Icc.mpr
    omega

theorem projectionBox_card (p : Parent) (M : ℕ) (q : Parent) :
    (projectionBox p M q).card = 512 ^ 3 := by
  have hi (j : Fin 3) :
      (Icc (512 * q.2 j + (M : ℤ) * p.2 j)
        (512 * q.2 j + (M : ℤ) * p.2 j + 511)).card = 512 := by
    have hh : ((Icc (512 * q.2 j + (M : ℤ) * p.2 j)
        (512 * q.2 j + (M : ℤ) * p.2 j + 511)).card : ℤ) = 512 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simp [projectionBox, Fintype.card_piFinset, hi]

/-- A relative atom is a union of a fixed number of original atoms. The
count is independent of BOTH scales and of the original source cardinality. -/
theorem relative_atom_original_labels {n : ℕ} (D : FiniteScaleSource n)
    (R : Finset (Fin n)) (a : ℝ) (N : ℕ) (p : Parent) (M : ℕ) (q : Parent) :
    ((R.filter (fun i => relativeLabel D a N p M i = q)).image
      (parentLabel D a (M * N))).card ≤ 512 ^ 3 := by
  apply (card_le_card (show _ ⊆ projectionBox p M q from ?_)).trans_eq
    (projectionBox_card p M q)
  intro z hz
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
  apply projection_mem_box
  rw [← relativeLabel_eq_projection]
  exact (mem_filter.mp hi).2

end NativeRelativeParentLabels
