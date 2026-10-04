import Theorems.Thm_StickyKakeya4_native_original_parent_selection
import Theorems.Thm_StickyKakeya4_front_two_probe_direction_firewall
import Theorems.Thm_StickyKakeya4_euclidean_alignment_patches
import Theorems.Thm_StickyKakeya4_original_height_interval_cap
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeOriginalSlopeCubePacking
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry
open scoped BigOperators

/-- The old coordinate slope is exactly the canonical Euclidean graph slope. -/
lemma original_slope_eq_north (line : MarkedLine) :
    EuclideanAlignmentPatches.euclidean (slope line) = northGraphSlope line := by
  ext j
  simp only [EuclideanAlignmentPatches.euclidean, northGraphSlope, PiLp.smul_apply,
    horizontalProjection_apply, smul_eq_mul, NativeOriginalCellChartGeometry.slope]
  exact div_eq_inv_mul _ _

/-- Normalizing the actual lifted original slope recovers the original direction. -/
lemma normalize_original_slope (line : MarkedLine) (hv : IsValidLine line)
    (hc : (1 / 2 : ℝ) ≤ direction line (3 : Fin 4)) :
    NormedSpace.normalize (northSlopeLift
      (EuclideanAlignmentPatches.euclidean (slope line))) = direction line := by
  rw [original_slope_eq_north]
  exact normalize_northSlopeLift line hv (by linarith)

/-- Euclidean direction distance is controlled by the sup distance of the
original graph slopes, through the actual unit-vector normalization. -/
theorem direction_dist_le_eight_slope_dist (line line' : MarkedLine)
    (hv : IsValidLine line) (hv' : IsValidLine line')
    (hc : (1 / 2 : ℝ) ≤ direction line (3 : Fin 4))
    (hc' : (1 / 2 : ℝ) ≤ direction line' (3 : Fin 4)) :
    dist (direction line) (direction line') ≤ 8 * dist (slope line) (slope line') := by
  have hn := northGraphSlope_direction_bound line line' hv hv'
    (by linarith) (by linarith)
  have he := EuclideanAlignmentPatches.euclidean_dist_le_card_mul
    (slope line) (slope line') (dist (slope line) (slope line')) dist_nonneg
    (fun j => by simpa only [Real.dist_eq] using dist_le_pi_dist (slope line) (slope line') j)
  rw [original_slope_eq_north, original_slope_eq_north, dist_eq_norm] at he
  norm_num only [Nat.cast_ofNat] at he
  nlinarith [dist_nonneg (x := slope line) (y := slope line')]

/-- The same estimate with the literal sup norm on three real coordinates. -/
theorem direction_dist_le_eight_slope_norm (line line' : MarkedLine)
    (hv : IsValidLine line) (hv' : IsValidLine line')
    (hc : (1 / 2 : ℝ) ≤ direction line (3 : Fin 4))
    (hc' : (1 / 2 : ℝ) ≤ direction line' (3 : Fin 4)) :
    dist (direction line) (direction line') ≤ 8 * ‖slope line - slope line'‖ := by
  simpa only [dist_eq_norm] using direction_dist_le_eight_slope_dist line line' hv hv' hc hc'

/-- Literal original-slope grid of spacing delta/16. -/
def slopeGrid (delta : ℝ) (line : MarkedLine) : Fin 3 → ℤ :=
  fun j => ⌊slope line j / (delta / 16)⌋

/-- Actual Euclidean delta separation makes the literal floor map injective
on original labels. No packing or separation certificate is assumed for slopes. -/
theorem slopeGrid_injOn {α : Type*} (A : Finset α) (line : α → MarkedLine)
    {delta : ℝ} (hd : 0 < delta)
    (hv : ∀ i ∈ A, IsValidLine (line i))
    (hc : ∀ i ∈ A, (1 / 2 : ℝ) ≤ direction (line i) (3 : Fin 4))
    (hsep : ∀ i ∈ A, ∀ k ∈ A, i ≠ k → delta ≤ dist (direction (line i)) (direction (line k))) :
    Set.InjOn (fun i => slopeGrid delta (line i)) (↑A) := by
  intro i hi k hk heq
  by_contra hne
  have hclose := SeparatedAlignmentPatches.same_cell_dist_lt (delta / 16)
    (by positivity) (slope (line i)) (slope (line k)) heq
  have hdir := direction_dist_le_eight_slope_dist (line i) (line k)
    (hv i hi) (hv k hk) (hc i hi) (hc k hk)
  have hs := hsep i hi k hk hne
  linarith

/-- The explicit finite integer box containing all original grid indices. -/
def gridBox (delta : ℝ) (c : Fin 3 → ℝ) (rho : ℝ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun j => Icc ⌊c j / (delta / 16)⌋ ⌊(c j + rho) / (delta / 16)⌋)

lemma slopeGrid_mem_gridBox {delta rho : ℝ} (hd : 0 < delta) (c : Fin 3 → ℝ)
    (line : MarkedLine) (hc : ∀ j, c j ≤ slope line j ∧ slope line j ≤ c j + rho) :
    slopeGrid delta line ∈ gridBox delta c rho := by
  apply Fintype.mem_piFinset.mpr
  intro j
  exact mem_Icc.mpr ⟨Int.floor_mono (div_le_div_of_nonneg_right (hc j).1 (by positivity)),
    Int.floor_mono (div_le_div_of_nonneg_right (hc j).2 (by positivity))⟩

lemma gridBox_card_le {delta rho : ℝ} (hd : 0 < delta) (hr : 0 ≤ rho)
    (c : Fin 3 → ℝ) :
    ((gridBox delta c rho).card : ℝ) ≤ (16 * rho / delta + 2) ^ 3 := by
  have hcoord (j : Fin 3) := OriginalHeightIntervalCap.floor_interval_card
    (delta / 16) (c j) rho (by positivity) hr
  have hid : rho / (delta / 16) + 2 = 16 * rho / delta + 2 := by ring
  simp_rw [hid] at hcoord
  rw [gridBox, Fintype.card_piFinset, Nat.cast_prod]
  calc
    _ ≤ ∏ _j : Fin 3, (16 * rho / delta + 2) := prod_le_prod
      (fun j _ => Nat.cast_nonneg _) (fun j _ => hcoord j)
    _ = _ := by simp

/-- A cube of side rho contains at most the displayed cubic number of
original labels, proved by injection into the literal delta/16 floor grid. -/
theorem original_cube_card_le {α : Type*} (A : Finset α) (line : α → MarkedLine)
    {delta rho : ℝ} (hd : 0 < delta) (hr : 0 ≤ rho)
    (hv : ∀ i ∈ A, IsValidLine (line i))
    (hc : ∀ i ∈ A, (1 / 2 : ℝ) ≤ direction (line i) (3 : Fin 4))
    (hsep : ∀ i ∈ A, ∀ k ∈ A, i ≠ k → delta ≤ dist (direction (line i)) (direction (line k)))
    (c : Fin 3 → ℝ)
    (hbox : ∀ i ∈ A, ∀ j, c j ≤ slope (line i) j ∧ slope (line i) j ≤ c j + rho) :
    (A.card : ℝ) ≤ (16 * rho / delta + 2) ^ 3 := by
  have hcard : A.card ≤ (gridBox delta c rho).card :=
    card_le_card_of_injOn (fun i => slopeGrid delta (line i))
      (fun i hi => slopeGrid_mem_gridBox hd c (line i) (hbox i hi))
      (slopeGrid_injOn A line hd hv hc hsep)
  exact (Nat.cast_le.mpr hcard).trans (gridBox_card_le hd hr c)

/-- A uniform cubic bound, valid even below the original separation scale. -/
theorem original_cube_card_le_add_one {α : Type*} (A : Finset α) (line : α → MarkedLine)
    {delta rho : ℝ} (hd : 0 < delta) (hr : 0 ≤ rho)
    (hv : ∀ i ∈ A, IsValidLine (line i))
    (hc : ∀ i ∈ A, (1 / 2 : ℝ) ≤ direction (line i) (3 : Fin 4))
    (hsep : ∀ i ∈ A, ∀ k ∈ A, i ≠ k → delta ≤ dist (direction (line i)) (direction (line k)))
    (c : Fin 3 → ℝ)
    (hbox : ∀ i ∈ A, ∀ j, c j ≤ slope (line i) j ∧ slope (line i) j ≤ c j + rho) :
    (A.card : ℝ) ≤ 4096 * (rho / delta + 1) ^ 3 := by
  have hb := original_cube_card_le A line hd hr hv hc hsep c hbox
  have hp : (16 * rho / delta + 2) ^ 3 ≤ (16 * (rho / delta + 1)) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [mul_div_assoc]
    linarith
  calc
    _ ≤ (16 * rho / delta + 2) ^ 3 := hb
    _ ≤ (16 * (rho / delta + 1)) ^ 3 := hp
    _ = _ := by ring

/-- At scales rho at least delta, the literal original-label bound has no
additive scale loss. -/
theorem original_cube_card_le_ratio {α : Type*} (A : Finset α) (line : α → MarkedLine)
    {delta rho : ℝ} (hd : 0 < delta) (hr : delta ≤ rho)
    (hv : ∀ i ∈ A, IsValidLine (line i))
    (hc : ∀ i ∈ A, (1 / 2 : ℝ) ≤ direction (line i) (3 : Fin 4))
    (hsep : ∀ i ∈ A, ∀ k ∈ A, i ≠ k → delta ≤ dist (direction (line i)) (direction (line k)))
    (c : Fin 3 → ℝ)
    (hbox : ∀ i ∈ A, ∀ j, c j ≤ slope (line i) j ∧ slope (line i) j ≤ c j + rho) :
    (A.card : ℝ) ≤ 5832 * (rho / delta) ^ 3 := by
  have hr0 : 0 ≤ rho := hd.le.trans hr
  have hratio : 1 ≤ rho / delta := (le_div_iff₀ hd).mpr (by simpa using hr)
  have hb := original_cube_card_le A line hd (hd.le.trans hr) hv hc hsep c hbox
  have hp : (16 * rho / delta + 2) ^ 3 ≤ (18 * (rho / delta)) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [mul_div_assoc]
    linarith
  calc
    _ ≤ (16 * rho / delta + 2) ^ 3 := hb
    _ ≤ (18 * (rho / delta)) ^ 3 := hp
    _ = _ := by ring

/-- The cube estimate for an actual native source uses its existing validity,
north chart, and original Euclidean direction separation hypotheses. -/
theorem native_cube_card_le_ratio {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (A : Finset (Fin n))
    {rho : ℝ} (hr : D.thickness ≤ rho) (c : Fin 3 → ℝ)
    (hbox : ∀ i ∈ A, ∀ j, c j ≤ slope (D.line i) j ∧ slope (D.line i) j ≤ c j + rho) :
    (A.card : ℝ) ≤ 5832 * (rho / D.thickness) ^ 3 := by
  exact original_cube_card_le_ratio A D.line h.1.2.1 hr
    (fun i _ => h.1.2.2.2.2.1 i) (fun i _ => h.2.1.1 i)
    (fun i _ k _ hne => h.1.2.2.2.2.2.2.2.2.2.1 i k hne) c hbox

/-- Every genuine original parent label lies in its actual slope cube. -/
lemma backbone_slope_cube {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (hN : 0 < N) (p : NativeOriginalParentSelection.Parent)
    {i : Fin n} (hi : i ∈ NativeOriginalParentSelection.backbone D a N p) (j : Fin 3) :
    (p.1 j : ℝ) / N ≤ slope (D.line i) j ∧
      slope (D.line i) j ≤ (p.1 j : ℝ) / N + 1 / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have he := congrFun (congrArg Prod.fst (mem_filter.mp hi).2) j
  change ⌊(N : ℝ) * slope (D.line i) j⌋ = p.1 j at he
  have hlo := Int.floor_le ((N : ℝ) * slope (D.line i) j)
  have hhi := Int.lt_floor_add_one ((N : ℝ) * slope (D.line i) j)
  rw [he] at hlo hhi
  constructor
  · exact (div_le_iff₀ hNR).mpr (by nlinarith)
  · rw [← add_div]
    exact (le_div_iff₀ hNR).mpr (by nlinarith)

/-- The actual full original backbone has a cubic direction-packing upper
bound at scale 1/N, including every inherited original label. -/
theorem native_backbone_card_le {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (N : ℕ)
    (hN : 0 < N) (hscale : (N : ℝ) * D.thickness ≤ 1)
    (p : NativeOriginalParentSelection.Parent) :
    ((NativeOriginalParentSelection.backbone D a N p).card : ℝ) ≤
      5832 * (1 / ((N : ℝ) * D.thickness)) ^ 3 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : D.thickness ≤ 1 / (N : ℝ) :=
    (le_div_iff₀ hNR).mpr (by nlinarith)
  have hb := native_cube_card_le_ratio h (NativeOriginalParentSelection.backbone D a N p)
    hr (fun j => (p.1 j : ℝ) / N) (fun _ hi j => backbone_slope_cube D a N hN p hi j)
  have hid : (1 / (N : ℝ)) / D.thickness = 1 / ((N : ℝ) * D.thickness) := by ring
  simpa only [hid] using hb

/-- The same upper bound is inherited by any retained set of original labels. -/
theorem native_retained_parent_card_le {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (N : ℕ)
    (hN : 0 < N) (hscale : (N : ℝ) * D.thickness ≤ 1)
    (p : NativeOriginalParentSelection.Parent) :
    ((R.filter (fun i => NativeOriginalParentSelection.parentLabel D a N i = p)).card : ℝ) ≤
      5832 * (1 / ((N : ℝ) * D.thickness)) ^ 3 := by
  have hsub : R.filter (fun i => NativeOriginalParentSelection.parentLabel D a N i = p) ⊆
      NativeOriginalParentSelection.backbone D a N p := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩
  exact (show ((R.filter (fun i => NativeOriginalParentSelection.parentLabel D a N i = p)).card : ℝ) ≤
      (NativeOriginalParentSelection.backbone D a N p).card by exact_mod_cast card_le_card hsub).trans
    (native_backbone_card_le h a N hN hscale p)

end NativeOriginalSlopeCubePacking
