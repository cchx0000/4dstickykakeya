import Theorems.Thm_StickyKakeya4_native_global_coarse_rows
import Theorems.Thm_StickyKakeya4_native_coarse_shading_uniformity
import Theorems.Thm_StickyKakeya4_native_coarse_shading_pruning

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

noncomputable section
namespace NativeLastMenuShadingSize
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentSelection NativeOriginalParentDensityCore
open NativeGlobalCoarseRows NativeFixedSizeScaleMenu NativeCoarseShadingCapacity
open NativeCoarseDyadicShading NativeCoarseShadingUniformity
open scoped ENNReal BigOperators

/-- The final clipped menu entry is within one dyadic step of its prescribed
power depth. The estimate is independent of the number of source scales. -/
lemma upperDepth_scale_lower {delta w : ℝ} (level : ℕ)
    (hdy : delta = (2:ℝ)⁻¹^level) :
    delta^(w/2)/2 ≤ ((2^(upperDepth w level):ℕ):ℝ)*delta := by
  have hfloor : (1-w/2)*(level:ℝ) < (upperDepth w level:ℝ)+1 := Nat.lt_floor_add_one _
  have hdelta : delta = (2:ℝ)^(-(level:ℝ)) := by
    simp only [hdy,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,inv_pow]
  have he : delta^(w/2) = (2:ℝ)^(-(level:ℝ)*(w/2)) := by
    rw [hdelta,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    (show -(level:ℝ)*(w/2) ≤ (upperDepth w level:ℝ)-(level:ℝ)+1 by linarith)
  rw [←he,Real.rpow_add (by norm_num : (0:ℝ) < 2),
    Real.rpow_sub (by norm_num : (0:ℝ) < 2),Real.rpow_one,
    Real.rpow_natCast,Real.rpow_natCast] at hh
  have hcancel : (2:ℝ)^(upperDepth w level)/(2:ℝ)^level =
      ((2^(upperDepth w level):ℕ):ℝ)*delta := by
    simp only [hdy,Nat.cast_pow,Nat.cast_ofNat,inv_pow,div_eq_mul_inv]
  rw [hcancel] at hh
  linarith

lemma rowCells_eq_rows {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (level m b : ℕ) (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) :
    rowCells D a level m b rep E p = rows D a (2^m) (block level b) rep E p := rfl

/-- On the same E, every active m-parent has the expected GLOBAL number of
occupied spatial b-cells, simultaneously at every 6 ≤ b ≤ m ≤ level. By
rowCells_eq_ancestor_image these are the ancestors of its actual shading.
No comparison between the occupancies of individual b-cells is asserted. -/
theorem window_core_global_row_bounds {n : ℕ} {D : FiniteScaleSource n}
    {eta zeta a gamma w : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (d g L level : ℕ) (hg : 0 < g) (hw : 0 ≤ w)
    (hdy : D.thickness = (2:ℝ)⁻¹^level)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (E : Finset (Fin n × Index))
    (hcore : IsCore D original R a eta zeta d (g+1) L Rel
      (fun j => 2^(windowSchedule w hw g level j).val) E)
    (hcost : (125*175616*16384:ℝ)*(factor d (g+1) L:ℝ)*(coreRadix original R L:ℝ)^2*
      D.thickness^(-eta) ≤ D.thickness^(-gamma))
    (m b : ℕ) (hbm : b ≤ m) (hml : m ≤ level) (hb6 : 6 ≤ b)
    (rep : Parent → Fin n) (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty) :
    (125/128:ℝ)*D.thickness^(gamma+w/2) ≤
      (64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E p).card ∧
    (64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E p).card ≤
      16*NativeOriginalPrunedMass.volumeConstant := by
  have hd := h.1.2.1
  have hbl := hbm.trans hml
  have hB := block_pos level b
  have hrows := core_projected_row_lower_absorbed h original horiginal ha R d (g+1) L Rel
    (fun j => 2^(windowSchedule w hw g level j).val) E hcore hcost
    (Fin.last g) (2^m) (block level b) hB rep p hp
  rw [windowSchedule_last w hw g level hg] at hrows
  have hl := upperDepth_scale_lower (w := w) level hdy
  have hscaled := mul_le_mul_of_nonneg_left hrows
    (show 0 ≤ 64/((2^b:ℕ):ℝ) by positivity)
  have hc : (64/((2^b:ℕ):ℝ))*(125*D.thickness^gamma*
      ((2^(upperDepth w level):ℕ):ℝ)/(block level b:ℝ)) =
      (125/64:ℝ)*D.thickness^gamma*(((2^(upperDepth w level):ℕ):ℝ)*D.thickness) := by
    rw [block_scale hdy hbl]
    field_simp [hd.ne']
    ring
  rw [hc] at hscaled
  constructor
  · rw [rowCells_eq_rows]
    calc
      _ = ((125/64:ℝ)*D.thickness^gamma)*(D.thickness^(w/2)/2) := by
        rw [Real.rpow_add hd]
        ring
      _ ≤ ((125/64:ℝ)*D.thickness^gamma)*
          (((2^(upperDepth w level):ℕ):ℝ)*D.thickness) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ ≤ _ := hscaled
  · have hu := projected_row_card_upper h original horiginal ha (2^m) (block level b) hB
      (by rw [block_thickness hdy hbl]; exact NativeCoarseShadingPruning.coarse_thickness_le_one b hb6)
      rep E (hcore.1.trans (filter_subset _ _)) p
    simpa only [block_thickness hdy hbl,rowCells_eq_rows] using hu

/-- Exact cubical shading mass of the occupied b-cells. At b=m this is
the literal shading in the full coarse source, without pruning. -/
lemma rowCells_volume {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (level m b : ℕ) (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) :
    (volume (wzCellShading (32/((2^b:ℕ):ℝ))
      (fun _ : Fin 1 => rowCells D a level m b rep E p) 0)).toReal =
      ((rowCells D a level m b rep E p).card:ℝ)*(64/((2^b:ℕ):ℝ))^4/16 := by
  rw [volume_wzCellShading (by positivity)]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 32/((2^b:ℕ):ℝ))]
  ring

/-- The global count law yields actual shading volume, with the expected
third scale power and the same original-delta loss. -/
theorem row_volume_bounds_of_global_count {n : ℕ} {D : FiniteScaleSource n}
    {a loss : ℝ} (hd : 0 < D.thickness) (level m b : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent)
    (hcount : (125/128:ℝ)*D.thickness^loss ≤
      (64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E p).card ∧
      (64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E p).card ≤
        16*NativeOriginalPrunedMass.volumeConstant) :
    (125/2048:ℝ)*D.thickness^loss*(64/((2^b:ℕ):ℝ))^3 ≤
      (volume (wzCellShading (32/((2^b:ℕ):ℝ))
        (fun _ : Fin 1 => rowCells D a level m b rep E p) 0)).toReal ∧
      (volume (wzCellShading (32/((2^b:ℕ):ℝ))
        (fun _ : Fin 1 => rowCells D a level m b rep E p) 0)).toReal ≤
          NativeOriginalPrunedMass.volumeConstant*(64/((2^b:ℕ):ℝ))^3 := by
  have _hd := hd
  constructor
  · calc
      _ = ((125/128:ℝ)*D.thickness^loss)*((64/((2^b:ℕ):ℝ))^3/16) := by ring
      _ ≤ ((64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E p).card)*
          ((64/((2^b:ℕ):ℝ))^3/16) :=
        mul_le_mul_of_nonneg_right hcount.1 (by positivity)
      _ = _ := by rw [rowCells_volume]; ring
  · calc
      _ = ((64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E p).card)*
          ((64/((2^b:ℕ):ℝ))^3/16) := by rw [rowCells_volume]; ring
      _ ≤ (16*NativeOriginalPrunedMass.volumeConstant)*((64/((2^b:ℕ):ℝ))^3/16) :=
        mul_le_mul_of_nonneg_right hcount.2 (by positivity)
      _ = _ := by ring

lemma coefficient_power_lower {delta A loss cost target : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hA : 0 < A)
    (hconstant : 1/A ≤ delta^(-cost)) (hbudget : loss+cost ≤ target) :
    delta^target ≤ A*delta^loss := by
  have hh := mul_le_mul_of_nonneg_right hconstant
    (Real.rpow_pos_of_pos hd cost).le
  have hcancel : delta^(-cost)*delta^cost = 1 := by
    rw [←Real.rpow_add hd,neg_add_cancel,Real.rpow_zero]
  rw [hcancel] at hh
  have hunit : delta^cost ≤ A := by
    have hh' : delta^cost/A ≤ 1 := by
      simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul,mul_one] using hh
    simpa only [one_mul] using (div_le_iff₀ hA).mp hh'
  calc
    _ ≤ delta^(loss+cost) := Real.rpow_le_rpow_of_exponent_ge hd hd1 hbudget
    _ = delta^loss*delta^cost := Real.rpow_add hd _ _
    _ ≤ delta^loss*A := mul_le_mul_of_nonneg_left hunit (Real.rpow_pos_of_pos hd loss).le
    _ = _ := mul_comm _ _

/-- A fixed original-delta cutoff absorbs the displayed numerical constants
in both the global cover count and actual cubical shading mass. -/
theorem absorb_global_count_and_volume {n : ℕ} {D : FiniteScaleSource n}
    {a loss cost target : ℝ} (hd : 0 < D.thickness) (hd1 : D.thickness ≤ 1)
    (hloss : 0 ≤ loss) (hbudget : loss+cost ≤ target)
    (hconstant : (2048/125:ℝ) ≤ D.thickness^(-cost))
    (hupper : 16*NativeOriginalPrunedMass.volumeConstant ≤ D.thickness^(-cost))
    (level m b : ℕ) (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent)
    (hcount : (125/128:ℝ)*D.thickness^loss ≤
      (64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E p).card ∧
      (64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E p).card ≤
        16*NativeOriginalPrunedMass.volumeConstant) :
    (D.thickness^target ≤ (64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E p).card ∧
      (64/((2^b:ℕ):ℝ))*(rowCells D a level m b rep E p).card ≤ D.thickness^(-target)) ∧
    (D.thickness^target*(64/((2^b:ℕ):ℝ))^3 ≤
      (volume (wzCellShading (32/((2^b:ℕ):ℝ))
        (fun _ : Fin 1 => rowCells D a level m b rep E p) 0)).toReal ∧
      (volume (wzCellShading (32/((2^b:ℕ):ℝ))
        (fun _ : Fin 1 => rowCells D a level m b rep E p) 0)).toReal ≤
          D.thickness^(-target)*(64/((2^b:ℕ):ℝ))^3) := by
  have hl := coefficient_power_lower hd hd1 (by norm_num : (0:ℝ) < 125/2048)
    (by norm_num; exact hconstant) hbudget
  have hpow : D.thickness^(-cost) ≤ D.thickness^(-target) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
  have hv := row_volume_bounds_of_global_count hd level m b rep E p hcount
  constructor
  · constructor
    · exact hl.trans ((mul_le_mul_of_nonneg_right (by norm_num : (125/2048:ℝ) ≤ 125/128)
        (Real.rpow_pos_of_pos hd loss).le).trans hcount.1)
    · exact hcount.2.trans (hupper.trans hpow)
  · constructor
    · exact (mul_le_mul_of_nonneg_right hl (by positivity)).trans hv.1
    · apply hv.2.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hV := NativeOriginalPrunedMass.volumeConstant_pos
      exact (show NativeOriginalPrunedMass.volumeConstant ≤ 16*NativeOriginalPrunedMass.volumeConstant by linarith).trans
        (hupper.trans hpow)

end NativeLastMenuShadingSize
