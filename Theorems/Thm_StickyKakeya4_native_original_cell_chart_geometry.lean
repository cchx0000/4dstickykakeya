import Theorems.Thm_StickyKakeya4_native_cubical_incidence_counts
import Theorems.Thm_StickyKakeya4_collision_flow_overlap_witness
import Theorems.Thm_StickyKakeya4_shear_bin_fibers
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeOriginalCellChartGeometry
open Classical StickyKakeya4 NativeCommonCubicalMesh

def slope (line : MarkedLine) (j : Fin 3) : ℝ :=
  direction line j.castSucc / direction line (3 : Fin 4)
def intercept (line : MarkedLine) (j : Fin 3) : ℝ :=
  offset line j.castSucc - slope line j * offset line (3 : Fin 4)
def cellCenter (mesh : ℝ) (k : Index) : E4 :=
  WithLp.toLp 2 (fun j => mesh * ((k j : ℝ) + 1 / 2))
def chartIndex (shift : ℤ) (k : Index) : ShearBinFibers.Index :=
  (fun j => k j.castSucc, k (3 : Fin 4) - shift)
def shiftedIntercept (line : MarkedLine) (mesh : ℝ) (shift : ℤ) (j : Fin 3) : ℝ :=
  (intercept line j + slope line j * ((shift : ℝ) * mesh)) / 4

lemma coordinate_abs_le_norm (x : E4) (j : Fin 4) : |x j| ≤ ‖x‖ := by
  simpa [Real.dist_eq] using PiLp.dist_apply_le x (0 : E4) j

lemma slope_bound (line : MarkedLine) (hv : IsValidLine line)
    (hc : (1 / 2 : ℝ) ≤ direction line (3 : Fin 4)) (j : Fin 3) : |slope line j| ≤ 2 := by
  have hp : 0 < direction line (3 : Fin 4) := by linarith
  have hj := coordinate_abs_le_norm (direction line) j.castSucc
  rw [hv.1] at hj
  rw [slope, abs_div, abs_of_pos hp, div_le_iff₀ hp]
  linarith

lemma raw_graph_identity (line : MarkedLine) (t : ℝ)
    (hc : direction line (3 : Fin 4) ≠ 0) (j : Fin 3) :
    rawFrontParam (line, t) j.castSucc =
      intercept line j + slope line j * rawFrontParam (line, t) (3 : Fin 4) := by
  simp only [rawFrontParam, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, intercept, slope]
  field_simp [hc]
  ring

lemma raw_height_from_common (line : MarkedLine) (hv : IsValidLine line)
    (hc : direction line (3 : Fin 4) ≠ 0) {a t : ℝ}
    (ha : wzGraphTime line a - mark line ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (ht : t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    |rawFrontParam (line, t) (3 : Fin 4) - a| ≤ 1 := by
  let u := wzGraphTime line a - mark line
  have hu : rawFrontParam (line, u) (3 : Fin 4) = a := by
    rw [← wzGraphPoint_eq_rawFrontParam]
    exact wzGraphPoint_fourth_coordinate line a hc
  have hdif : |t - u| ≤ 1 := by
    dsimp [u]
    exact abs_le.mpr ⟨by linarith [ha.1, ha.2, ht.1, ht.2],
      by linarith [ha.1, ha.2, ht.1, ht.2]⟩
  have hdir : |direction line (3 : Fin 4)| ≤ 1 := by
    simpa [hv.1] using coordinate_abs_le_norm (direction line) (3 : Fin 4)
  have he : rawFrontParam (line, t) (3 : Fin 4) - rawFrontParam (line, u) (3 : Fin 4) =
      (t - u) * direction line (3 : Fin 4) := by
    simp only [rawFrontParam, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [← hu, he, abs_mul]
  exact (mul_le_mul hdif hdir (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

/-- Actual tube membership gives a physical graph residual and height bound,
with explicit constants and a genuine marked-segment witness. -/
theorem tube_point_bounds (line : MarkedLine) (hv : IsValidLine line)
    (hc : (1 / 2 : ℝ) ≤ direction line (3 : Fin 4)) {a delta : ℝ}
    (hd : 0 < delta)
    (ha : wzGraphTime line a - mark line ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    {x : E4} (hx : x ∈ markedUnitTube line delta) :
    |x (3 : Fin 4) - a| ≤ 1 + 2 * delta ∧
      ∀ j : Fin 3, |x j.castSucc - intercept line j - slope line j * x (3 : Fin 4)| ≤ 6 * delta := by
  have hp : 0 < direction line (3 : Fin 4) := by linarith
  obtain ⟨t, ht, hdist⟩ := exists_rawFrontParam_dist_lt_of_infDist_le line x hx hd
  let q := rawFrontParam (line, t)
  have hcoord (j : Fin 4) : |x j - q j| ≤ 2 * delta := by
    have hh : |x j - q j| ≤ dist x q := by simpa [Real.dist_eq] using PiLp.dist_apply_le x q j
    exact hh.trans (by simpa [q, two_mul] using hdist.le)
  constructor
  · calc
      _ ≤ |x (3 : Fin 4) - q (3 : Fin 4)| + |q (3 : Fin 4) - a| := abs_sub_le _ _ _
      _ ≤ 2 * delta + 1 := add_le_add (hcoord _) (raw_height_from_common line hv hp.ne' ha ht)
      _ = _ := by ring
  · intro j
    have hq := raw_graph_identity line t hp.ne' j
    have he : x j.castSucc - intercept line j - slope line j * x (3 : Fin 4) =
        (x j.castSucc - q j.castSucc) - slope line j * (x (3 : Fin 4) - q (3 : Fin 4)) := by
      dsimp [q]
      rw [hq]
      ring
    rw [he]
    calc
      _ ≤ |x j.castSucc - q j.castSucc| + |slope line j * (x (3 : Fin 4) - q (3 : Fin 4))| := abs_sub _ _
      _ = |x j.castSucc - q j.castSucc| + |slope line j| * |x (3 : Fin 4) - q (3 : Fin 4)| := by rw [abs_mul]
      _ ≤ 2 * delta + 2 * (2 * delta) := add_le_add (hcoord _)
        (mul_le_mul (slope_bound line hv hc j) (hcoord _) (abs_nonneg _) (by norm_num))
      _ = _ := by ring

lemma cellCenter_mem {mesh : ℝ} (hm : 0 < mesh) (k : Index) :
    cellCenter mesh k ∈ wzDyadicCell mesh k := by
  intro j
  change (k j : ℝ) * mesh ≤ mesh * ((k j : ℝ) + 1 / 2) ∧
    mesh * ((k j : ℝ) + 1 / 2) < ((k j : ℝ) + 1) * mesh
  constructor <;> nlinarith

lemma chartIndex_injective (shift : ℤ) : Function.Injective (chartIndex shift) := by
  intro k l h
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have hh := congrArg Prod.snd h
    dsimp [chartIndex] at hh
    change k (3 : Fin 4) = l (3 : Fin 4)
    omega
  · exact congrFun (congrArg Prod.fst h) i

lemma chart_center_time (mesh : ℝ) (shift : ℤ) (k : Index) :
    (ShearBinFibers.oldCenter (mesh / 4) (chartIndex shift k)).2 =
      ((cellCenter mesh k) (3 : Fin 4) - (shift : ℝ) * mesh) / 4 := by
  dsimp [ShearBinFibers.oldCenter, chartIndex, cellCenter]
  push_cast
  ring

lemma chart_center_residual (line : MarkedLine) (mesh : ℝ) (shift : ℤ) (k : Index) (j : Fin 3) :
    (ShearBinFibers.oldCenter (mesh / 4) (chartIndex shift k)).1 j -
      shiftedIntercept line mesh shift j - slope line j *
        (ShearBinFibers.oldCenter (mesh / 4) (chartIndex shift k)).2 =
      ((cellCenter mesh k) j.castSucc - intercept line j -
        slope line j * (cellCenter mesh k) (3 : Fin 4)) / 4 := by
  dsimp [ShearBinFibers.oldCenter, chartIndex, shiftedIntercept, cellCenter]
  push_cast
  ring

/-- The integer height translation keeps the original grid labels, and one
fixed contraction places all actual cell centers in the required time window. -/
theorem normalized_cell_bounds (line : MarkedLine) (hv : IsValidLine line)
    (hc : (1 / 2 : ℝ) ≤ direction line (3 : Fin 4)) {a mesh : ℝ}
    (hm : 0 < mesh) (hm1 : mesh ≤ 1 / 2)
    (ha : wzGraphTime line a - mark line ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (k : Index) (hk : cellCenter mesh k ∈ markedUnitTube line (2 * mesh)) :
    |(ShearBinFibers.oldCenter (mesh / 4) (chartIndex ⌊a / mesh⌋ k)).2| ≤ 1 ∧
      ∀ j : Fin 3,
        |(ShearBinFibers.oldCenter (mesh / 4) (chartIndex ⌊a / mesh⌋ k)).1 j -
          shiftedIntercept line mesh ⌊a / mesh⌋ j - slope line j *
            (ShearBinFibers.oldCenter (mesh / 4) (chartIndex ⌊a / mesh⌋ k)).2| ≤ 12 * (mesh / 4) := by
  obtain ⟨hheight, hres⟩ := tube_point_bounds line hv hc (mul_pos (by norm_num) hm) ha hk
  have hlo : (⌊a / mesh⌋ : ℝ) * mesh ≤ a := (le_div_iff₀ hm).mp (Int.floor_le (a / mesh))
  have hhi : a < ((⌊a / mesh⌋ : ℝ) + 1) * mesh :=
    (div_lt_iff₀ hm).mp (Int.lt_floor_add_one (a / mesh))
  constructor
  · rw [chart_center_time]
    obtain ⟨hhlo, hhhi⟩ := abs_le.mp hheight
    apply abs_le.mpr
    constructor <;> nlinarith
  · intro j
    rw [chart_center_residual, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr (by nlinarith [hres j])
end NativeOriginalCellChartGeometry
