import Theorems.Thm_StickyKakeya4_incidence_bin_transfer
import Theorems.Thm_StickyKakeya4_shear_bin_fibers
import Theorems.Thm_StickyKakeya4_tube_bin_count

set_option autoImplicit false
set_option warningAsError true

/-!
# Physical WZ incidence rescaling

The cell map is the actual global affine shear of the original half-open δ-grid
centers, followed by floors at σ = Nδ, with ρ = 1/N. Tube/bin cardinalities are
derived from geometric counting, never assumed. All retained old labels and
weights are unchanged. The chosen ceiling threshold also covers the case m = 1.
-/

noncomputable section
open Classical Finset IncidenceBinTransfer
open scoped BigOperators

namespace PhysicalRescalingIncidenceTransfer

abbrev Cell := ShearBinFibers.Index

/-- Original incidence data and original affine tube parameters. -/
structure Data (T : Type*) where
  incidences : Finset (T × Cell)
  δ : ℝ
  N : ℕ
  E : ℕ
  lam : ℝ
  globalSlope : Fin 3 → ℝ
  globalOffset : Fin 3 → ℝ
  tubeSlope : T → Fin 3 → ℝ
  tubeOffset : T → Fin 3 → ℝ

namespace Data

variable {T : Type*} (P : Data T)

def ρ : ℝ := 1 / (P.N : ℝ)
def σ : ℝ := (P.N : ℝ) * P.δ

/-- The actual transformed center of the original cell; no replacement center is chosen. -/
def center (c : Cell) : ShearBinFibers.Point :=
  ShearBinFibers.shearRescale P.ρ P.globalSlope P.globalOffset (ShearBinFibers.oldCenter P.δ c)

def slope (t : T) (j : Fin 3) : ℝ := (P.tubeSlope t j - P.globalSlope j) / P.ρ
def offset (t : T) (j : Fin 3) : ℝ := (P.tubeOffset t j - P.globalOffset j) / P.ρ

/-- Physical residual of the actual rescaled old center relative to its rescaled old tube. -/
def residual (t : T) (c : Cell) (j : Fin 3) : ℝ :=
  (P.center c).1 j - P.offset t j - P.slope t j * (P.center c).2

/-- One global, tube-independent assignment of original cells to coarse bins. -/
def cellBin (c : Cell) : Cell :=
  ShearBinFibers.actualBin P.δ P.N P.globalSlope P.globalOffset c

/-- Explicit number of spatial choices per time slab in the geometric tube cover. -/
def spatialChoices : ℕ := (2 * P.E + 4) ^ 3

/-- Geometric O(σ⁻¹) coefficient. -/
def K : ℝ := 4 * (P.spatialChoices : ℝ)

/-- The integer cover bound is computed geometrically, not provided by a caller. -/
def M : ℕ := (TubeBinCount.timeBins P.σ).card * P.spatialChoices

/-- The density threshold, including the one-incidence regime. -/
def m : ℕ := max 1 ⌈P.lam * P.N / (2 * P.K)⌉₊

/-- The constant in μ_old ≤ C_E/λ · μ_new is 16(2E+4)^3. -/
def transferConstant : ℝ := 4 * P.K

def keptIncidences : Finset (T × Cell) := kept P.incidences P.cellBin P.m
def newIncidences : Finset (T × Cell) := heavyBins P.incidences P.cellBin P.m
def oldSupport : Finset Cell := oldCells P.incidences
def newSupport : Finset Cell := newCells P.incidences P.cellBin P.m

def oldMultiplicity : ℝ := (P.incidences.card : ℝ) / P.oldSupport.card
def newMultiplicity : ℝ := (P.newIncidences.card : ℝ) / P.newSupport.card

/-- Exactly the geometric and density assumptions; no combinatorial capacity is assumed. -/
structure Hypotheses : Prop where
  delta_pos : 0 < P.δ
  N_pos : 0 < P.N
  scale_le_one : P.σ ≤ 1
  lambda_pos : 0 < P.lam
  lambda_le_one : P.lam ≤ 1
  slope_bound : ∀ t ∈ usedTubes P.incidences, ∀ j, |P.slope t j| ≤ 1
  time_bound : ∀ p ∈ P.incidences, |(P.center p.2).2| ≤ 1
  physical_bound : ∀ p ∈ P.incidences, ∀ j, |P.residual p.1 p.2 j| ≤ (P.E : ℝ) * P.σ
  density : P.lam * (usedTubes P.incidences).card ≤ P.δ * P.incidences.card

/-- The residual is the original physical error divided by ρ, at the same old center. -/
theorem residual_eq_original (t : T) (c : Cell) (j : Fin 3) :
    P.residual t c j =
      ((ShearBinFibers.oldCenter P.δ c).1 j - P.tubeOffset t j -
        P.tubeSlope t j * (ShearBinFibers.oldCenter P.δ c).2) / P.ρ := by
  dsimp [residual, center, slope, offset, ShearBinFibers.shearRescale]
  ring

/-- The physical bin definition coincides with the floor grid used for tube counting. -/
theorem cellBin_eq_gridBin (c : Cell) :
    P.cellBin c = TubeBinCount.gridBin P.σ (P.center c) := rfl

theorem scale_pos (h : P.Hypotheses) : 0 < P.σ := by
  exact mul_pos (by exact_mod_cast h.N_pos) h.delta_pos

theorem K_pos : 0 < P.K := by
  dsimp [K, spatialChoices]
  positivity

/-- The global geometric fiber bound is N, inherited from the actual affine/floor map. -/
theorem incidence_fiber_bound (h : P.Hypotheses) (b : T × Cell) :
    (binFiber P.incidences P.cellBin b).card ≤ P.N := by
  exact (card_binFiber_le_oldCells_fiber P.incidences P.cellBin b).trans
    (ShearBinFibers.actualBin_filter_card_le P.δ h.delta_pos P.N h.N_pos
      P.globalSlope P.globalOffset (oldCells P.incidences) b.2)

/-- All of one tube's actual occupied bins lie in the explicit geometric cover. -/
theorem tube_bins_subset_cover (h : P.Hypotheses) (t : T)
    (ht : t ∈ usedTubes P.incidences) :
    tubeBins P.incidences P.cellBin t ⊆
      ({t} : Finset T).product (TubeBinCount.tubeBins P.σ P.E (P.slope t) (P.offset t)) := by
  intro b hb
  obtain ⟨hb, hbt⟩ := mem_filter.mp hb
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hb
  have hpt : p.1 = t := hbt
  apply mem_product.mpr
  constructor
  · exact mem_singleton.mpr hpt
  · change P.cellBin p.2 ∈ _
    rw [P.cellBin_eq_gridBin]
    apply TubeBinCount.gridBin_mem_tubeBins P.σ P.E (P.slope t) (P.offset t)
      (P.center p.2) (P.scale_pos h) (h.slope_bound t ht) (h.time_bound p hp)
    intro j
    have hres := h.physical_bound p hp j
    simpa only [residual, hpt] using hres

/-- The per-tube bin count is derived from its physical time, slope, and error bounds. -/
theorem tube_bin_bound (h : P.Hypotheses) (t : T)
    (ht : t ∈ usedTubes P.incidences) :
    (tubeBins P.incidences P.cellBin t).card ≤ P.M := by
  have hcard : (tubeBins P.incidences P.cellBin t).card ≤
      (TubeBinCount.tubeBins P.σ P.E (P.slope t) (P.offset t)).card := by
    simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton, one_mul] using
      (card_le_card (P.tube_bins_subset_cover h t ht))
  exact hcard.trans (TubeBinCount.tubeBins_card_le P.σ P.E (P.slope t) (P.offset t))

/-- The computed integer tube bound has the required O(σ⁻¹) normalization. -/
theorem M_mul_scale_le (h : P.Hypotheses) : (P.M : ℝ) * P.σ ≤ P.K := by
  have ht := TubeBinCount.timeBins_card_mul_scale_le P.σ (P.scale_pos h) h.scale_le_one
  dsimp [M, K]
  push_cast
  calc
    ((TubeBinCount.timeBins P.σ).card : ℝ) * P.spatialChoices * P.σ =
        (((TubeBinCount.timeBins P.σ).card : ℝ) * P.σ) * P.spatialChoices := by ring
    _ ≤ 4 * P.spatialChoices := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _)

theorem m_pos : 0 < P.m := by
  dsimp [m]
  omega

/-- The max is redundant at positive density, but makes the one-bin case explicit. -/
theorem m_eq_ceil (h : P.Hypotheses) : P.m = ⌈P.lam * P.N / (2 * P.K)⌉₊ := by
  have hx : 0 < P.lam * P.N / (2 * P.K) :=
    div_pos (mul_pos h.lambda_pos (by exact_mod_cast h.N_pos)) (mul_pos (by norm_num) P.K_pos)
  exact max_eq_right (Nat.one_le_ceil_iff.mpr hx)

/-- Rounding costs strictly less than one incidence per bin, including m = 1. -/
theorem m_sub_one_le (h : P.Hypotheses) :
    ((P.m - 1 : ℕ) : ℝ) ≤ P.lam * P.N / (2 * P.K) := by
  rw [P.m_eq_ceil h]
  have hx : 0 < P.lam * P.N / (2 * P.K) :=
    div_pos (mul_pos h.lambda_pos (by exact_mod_cast h.N_pos)) (mul_pos (by norm_num) P.K_pos)
  exact ((Nat.ceil_eq_iff (Nat.ne_zero_of_lt (Nat.one_le_ceil_iff.mpr hx))).mp rfl).1.le

/-- The threshold is large enough for the multiplicity improvement, even when m = 1. -/
theorem density_le_threshold : P.lam * P.N ≤ 2 * P.K * P.m := by
  have hm := Nat.le_ceil (P.lam * P.N / (2 * P.K))
  have hmax : (⌈P.lam * P.N / (2 * P.K)⌉₊ : ℝ) ≤ P.m := by
    exact_mod_cast (le_max_right 1 ⌈P.lam * P.N / (2 * P.K)⌉₊)
  have := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) P.K_pos)).mp (hm.trans hmax)
  nlinarith

/-- Small λN uses m = 1, so the ceiling causes no scale restriction or loss. -/
theorem m_eq_one_of_small (hsmall : P.lam * P.N ≤ 2 * P.K) : P.m = 1 := by
  have hceil : ⌈P.lam * P.N / (2 * P.K)⌉₊ ≤ 1 := by
    apply Nat.ceil_le.mpr
    have hx : P.lam * P.N / (2 * P.K) ≤ (1 : ℝ) :=
      (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) P.K_pos)).mpr (by simpa using hsmall)
    simpa using hx
  exact max_eq_left hceil

/-- The geometric tube bound and ceiling estimate imply the sharp half-loss budget. -/
theorem half_loss_budget (h : P.Hypotheses) :
    2 * (P.m - 1) * P.M * (usedTubes P.incidences).card ≤ P.incidences.card := by
  have hN : (0 : ℝ) < P.N := by exact_mod_cast h.N_pos
  have hround := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) P.K_pos)).mp
    (P.m_sub_one_le h)
  have hper : 2 * ((P.m - 1 : ℕ) : ℝ) * P.M * P.δ ≤ P.lam := by
    apply (mul_le_mul_iff_right₀ hN).mp
    calc
      (P.N : ℝ) * (2 * ((P.m - 1 : ℕ) : ℝ) * P.M * P.δ) =
          (2 * ((P.m - 1 : ℕ) : ℝ)) * ((P.M : ℝ) * P.σ) := by dsimp [σ]; ring
      _ ≤ (2 * ((P.m - 1 : ℕ) : ℝ)) * P.K :=
        mul_le_mul_of_nonneg_left (P.M_mul_scale_le h) (by positivity)
      _ ≤ (P.N : ℝ) * P.lam := by nlinarith only [hround]
  have htotal : (2 : ℝ) * ((P.m - 1 : ℕ) : ℝ) * P.M *
      (usedTubes P.incidences).card ≤ P.incidences.card := by
    apply (mul_le_mul_iff_right₀ h.delta_pos).mp
    calc
      P.δ * (2 * ((P.m - 1 : ℕ) : ℝ) * P.M * (usedTubes P.incidences).card) =
          (2 * ((P.m - 1 : ℕ) : ℝ) * P.M * P.δ) * (usedTubes P.incidences).card := by ring
      _ ≤ P.lam * (usedTubes P.incidences).card :=
        mul_le_mul_of_nonneg_right hper (Nat.cast_nonneg _)
      _ ≤ P.δ * P.incidences.card := h.density
  exact_mod_cast htotal

/-- At least half of all original incidences survive the concrete physical construction. -/
theorem half_mass (h : P.Hypotheses) : P.incidences.card ≤ 2 * P.keptIncidences.card :=
  card_le_twice_kept P.incidences P.cellBin P.m P.M (P.tube_bin_bound h) (P.half_loss_budget h)

/-- The old pair labels are retained exactly, with no reassignment by tube. -/
theorem retained_old_labels (p : T × Cell) :
    p ∈ P.keptIncidences ↔ p ∈ P.incidences ∧
      P.m ≤ (binFiber P.incidences P.cellBin (p.1, P.cellBin p.2)).card := mem_kept

/-- A retained bin contains its whole original incidence fiber. -/
theorem retained_whole_fiber {b : T × Cell} (hb : b ∈ P.newIncidences) :
    binFiber P.keptIncidences P.cellBin b = binFiber P.incidences P.cellBin b :=
  kept_fiber_eq hb

/-- Arbitrary original additive weights are preserved, including all labels in a retained fiber. -/
theorem retained_weights {A : Type*} [AddCommMonoid A] (w : T × Cell → A) :
    ∑ p ∈ P.keptIncidences, w p =
      ∑ b ∈ P.newIncidences, ∑ p ∈ binFiber P.incidences P.cellBin b, w p :=
  sum_kept_eq_sum_heavy_fibers P.incidences P.cellBin P.m w

/-- Physical residual control stays at the actual rescaled original center after selection. -/
theorem retained_physical_residual (h : P.Hypotheses) {p : T × Cell}
    (hp : p ∈ P.keptIncidences) (j : Fin 3) :
    |(P.center p.2).1 j - P.offset p.1 j - P.slope p.1 j * (P.center p.2).2| ≤
      (P.E : ℝ) * P.σ := h.physical_bound p (kept_subset _ _ _ hp) j

/-- With threshold one, every original old pair survives. -/
theorem retained_eq_original_of_small (hsmall : P.lam * P.N ≤ 2 * P.K) :
    P.keptIncidences = P.incidences := by
  change kept P.incidences P.cellBin P.m = P.incidences
  rw [P.m_eq_one_of_small hsmall]
  exact kept_one_eq _ _

/-- The incidence capacity N is applied to the actual heavy-bin fibers. -/
theorem retained_capacity (h : P.Hypotheses) :
    P.keptIncidences.card ≤ P.N * P.newIncidences.card :=
  card_kept_le P.incidences P.cellBin P.m P.N (fun b _hb => P.incidence_fiber_bound h b)

/-- Every occupied new spatial bin contains m distinct retained original cells. -/
theorem support_gain : P.m * P.newSupport.card ≤ (oldCells P.keptIncidences).card :=
  mul_card_newCells_le_kept P.incidences P.cellBin P.m

/-- Unnormalized multiplicity transfer, with N derived from the global geometric map. -/
theorem cross_multiplicity (h : P.Hypotheses) :
    P.m * P.incidences.card * P.newSupport.card ≤
      2 * P.N * P.newIncidences.card * P.oldSupport.card :=
  multiplicity_transfer P.incidences P.cellBin P.m P.M P.N (P.tube_bin_bound h)
    (fun b _hb => P.incidence_fiber_bound h b) (P.half_loss_budget h)

/-- Density absorbs the fiber capacity: the final constant depends only on physical error E. -/
theorem density_cross_multiplicity (h : P.Hypotheses) :
    P.lam * P.incidences.card * P.newSupport.card ≤
      P.transferConstant * P.newIncidences.card * P.oldSupport.card := by
  have hN : (0 : ℝ) < P.N := by exact_mod_cast h.N_pos
  have hcross : (P.m : ℝ) * P.incidences.card * P.newSupport.card ≤
      2 * P.N * P.newIncidences.card * P.oldSupport.card := by
    exact_mod_cast P.cross_multiplicity h
  apply (mul_le_mul_iff_right₀ hN).mp
  calc
    (P.N : ℝ) * (P.lam * P.incidences.card * P.newSupport.card) =
        (P.lam * P.N) * ((P.incidences.card : ℝ) * P.newSupport.card) := by ring
    _ ≤ (2 * P.K * P.m) * ((P.incidences.card : ℝ) * P.newSupport.card) :=
      mul_le_mul_of_nonneg_right P.density_le_threshold (by positivity)
    _ = (2 * P.K) * ((P.m : ℝ) * P.incidences.card * P.newSupport.card) := by ring
    _ ≤ (2 * P.K) * (2 * P.N * P.newIncidences.card * P.oldSupport.card) :=
      mul_le_mul_of_nonneg_left hcross (mul_nonneg (by norm_num) P.K_pos.le)
    _ = (P.N : ℝ) * (P.transferConstant * P.newIncidences.card * P.oldSupport.card) := by
      dsimp [transferConstant]
      ring

/-- Positive original incidence mass forces both spatial supports to be nonempty. -/
theorem supports_nonempty (h : P.Hypotheses) (hI : P.incidences.Nonempty) :
    P.oldSupport.Nonempty ∧ P.newSupport.Nonempty := by
  have hkept : P.keptIncidences.Nonempty := by
    apply card_pos.mp
    have := P.half_mass h
    have := card_pos.mpr hI
    omega
  constructor
  · exact hI.image Prod.snd
  · change (newCells P.incidences P.cellBin P.m).Nonempty
    rw [newCells_eq_image_oldCells_kept]
    exact (hkept.image Prod.snd).image P.cellBin

/-- Concrete physical WZ multiplicity transfer, including the empty and m = 1 cases. -/
theorem multiplicity_bound (h : P.Hypotheses) :
    P.oldMultiplicity ≤ (P.transferConstant / P.lam) * P.newMultiplicity := by
  by_cases hI : P.incidences.Nonempty
  · have hs := P.supports_nonempty h hI
    have hold : (0 : ℝ) < P.oldSupport.card := by exact_mod_cast card_pos.mpr hs.1
    have hnew : (0 : ℝ) < P.newSupport.card := by exact_mod_cast card_pos.mpr hs.2
    have hratio : P.lam * P.oldMultiplicity ≤ P.transferConstant * P.newMultiplicity := by
      dsimp only [oldMultiplicity, newMultiplicity]
      rw [← mul_div_assoc, ← mul_div_assoc]
      exact (div_le_div_iff₀ hold hnew).mpr (P.density_cross_multiplicity h)
    calc
      P.oldMultiplicity ≤ (P.transferConstant * P.newMultiplicity) / P.lam :=
        (le_div_iff₀ h.lambda_pos).mpr (by nlinarith only [hratio])
      _ = (P.transferConstant / P.lam) * P.newMultiplicity := by ring
  · have hempty : P.incidences = ∅ := not_nonempty_iff_eq_empty.mp hI
    have hold : P.oldMultiplicity = 0 := by simp [oldMultiplicity, hempty]
    rw [hold]
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) P.K_pos.le) h.lambda_pos.le)
      (by dsimp [newMultiplicity]; positivity)

/-- The explicit error-only constant advertised in the transfer statement. -/
theorem transferConstant_eq : P.transferConstant = 16 * ((2 * P.E + 4 : ℕ) : ℝ) ^ 3 := by
  dsimp [transferConstant, K, spatialChoices]
  push_cast
  ring

/-- Retained new incidences are exactly the global images of retained original pairs. -/
theorem retained_bins_exact : bins P.keptIncidences P.cellBin = P.newIncidences :=
  bins_kept_eq P.incidences P.cellBin P.m

/-- Spatial supports use the same global physical bin map as every tube. -/
theorem newSupport_exact : P.newSupport = (oldCells P.keptIncidences).image P.cellBin :=
  newCells_eq_image_oldCells_kept P.incidences P.cellBin P.m

/-- The final multiplicity inequality with the error-only constant written out. -/
theorem multiplicity_bound_explicit (h : P.Hypotheses) :
    P.oldMultiplicity ≤
      (16 * ((2 * P.E + 4 : ℕ) : ℝ) ^ 3 / P.lam) * P.newMultiplicity := by
  rw [← P.transferConstant_eq]
  exact P.multiplicity_bound h

/-- The complete concrete rescaling output from physical geometry and original density alone. -/
theorem physical_rescaling_transfer (h : P.Hypotheses) :
    P.keptIncidences ⊆ P.incidences ∧
    P.incidences.card ≤ 2 * P.keptIncidences.card ∧
    P.keptIncidences.card ≤ P.N * P.newIncidences.card ∧
    P.m * P.newSupport.card ≤ (oldCells P.keptIncidences).card ∧
    P.oldMultiplicity ≤
      (16 * ((2 * P.E + 4 : ℕ) : ℝ) ^ 3 / P.lam) * P.newMultiplicity :=
  ⟨kept_subset _ _ _, P.half_mass h, P.retained_capacity h, P.support_gain,
    P.multiplicity_bound_explicit h⟩

end Data
end PhysicalRescalingIncidenceTransfer
