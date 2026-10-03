import Theorems.Thm_StickyKakeya4_graph_tube_grid_cover
import Theorems.Thm_StickyKakeya4_ad_grid_cover_menus
import Theorems.Thm_StickyKakeya4_finite_cover_profile_epochs

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace ActualTubeFootprintProfiles

open DisjointProfileEpochs FiniteCoverProfileEpochs
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening

noncomputable section

abbrev Point (d : ℕ) := Fin (d + 1) → ℝ
abbrev GridLabel (d : ℕ) := Fin (d + 1) → ℤ

def SupUnit {d : ℕ} (v : Point d) : Prop :=
  (∀ i, |v i| ≤ 1) ∧ ∃ i, |v i| = 1

structure TubeData (d : ℕ) where
  center : Point d
  direction : Point d
  unit : SupUnit direction

def InTube {d : ℕ} (T : TubeData d) (ρ τ : ℝ) (x : Point d) : Prop :=
  ∃ s : ℝ, |s| ≤ τ / 2 ∧ ∀ i, |x i - T.center i - s * T.direction i| ≤ ρ

def axisDirection (d : ℕ) : Point d := fun i => if i = 0 then 1 else 0

lemma axisDirection_unit (d : ℕ) : SupUnit (axisDirection d) := by
  constructor
  · intro i
    simp only [axisDirection]
    split_ifs <;> norm_num
  · exact ⟨0, by simp [axisDirection]⟩

lemma InTube_center {d : ℕ} (T : TubeData d) {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) :
    InTube T ρ τ T.center := by
  refine ⟨0, by simpa using (show 0 ≤ τ / 2 by linarith), ?_⟩
  intro i
  simpa using hρ

variable {α : Type*} [Fintype α] [DecidableEq α] {d : ℕ}

/-- The exact trace, on unchanged original point labels, of one genuine tube. -/
def trace (p : α → Point d) (ρ τ : ℝ) (T : TubeData d) : Finset α := by
  classical
  exact Finset.univ.filter (fun a => InTube T ρ τ (p a))

omit [DecidableEq α] in
@[simp] lemma mem_trace (p : α → Point d) (ρ τ : ℝ) (T : TubeData d) (a : α) :
    a ∈ trace p ρ τ T ↔ InTube T ρ τ (p a) := by
  classical
  simp [trace]

/-- All actual traces, as a finite subfamily of the original powerset. -/
def footprints (p : α → Point d) (ρ τ : ℝ) : Finset (Finset α) := by
  classical
  exact Finset.univ.powerset.filter (fun W => ∃ T : TubeData d, W = trace p ρ τ T)

omit [DecidableEq α] in
lemma mem_footprints (p : α → Point d) (ρ τ : ℝ) (W : Finset α) :
    W ∈ footprints p ρ τ ↔ ∃ T : TubeData d, W = trace p ρ τ T := by
  classical
  simp [footprints]

omit [DecidableEq α] in
lemma trace_mem_footprints (p : α → Point d) (ρ τ : ℝ) (T : TubeData d) :
    trace p ρ τ T ∈ footprints p ρ τ :=
  (mem_footprints p ρ τ _).mpr ⟨T, rfl⟩

omit [DecidableEq α] in
lemma footprints_nonempty (p : α → Point d) (ρ τ : ℝ) : (footprints p ρ τ).Nonempty := by
  let T : TubeData d := ⟨0, axisDirection d, axisDirection_unit d⟩
  exact ⟨trace p ρ τ T, trace_mem_footprints p ρ τ T⟩

/-- Chosen data retains actual center and direction, and their exact trace. -/
def witness (p : α → Point d) (ρ τ : ℝ) (W : Finset α)
    (hW : W ∈ footprints p ρ τ) : TubeData d :=
  Classical.choose ((mem_footprints p ρ τ W).mp hW)

omit [DecidableEq α] in
lemma witness_trace (p : α → Point d) (ρ τ : ℝ) (W : Finset α)
    (hW : W ∈ footprints p ρ τ) : W = trace p ρ τ (witness p ρ τ W hW) :=
  Classical.choose_spec ((mem_footprints p ρ τ W).mp hW)

omit [DecidableEq α] in
lemma point_covered (p : α → Point d) {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) (a : α) :
    ∃ W ∈ footprints p ρ τ, a ∈ W := by
  let T : TubeData d := ⟨p a, axisDirection d, axisDirection_unit d⟩
  refine ⟨trace p ρ τ T, trace_mem_footprints p ρ τ T, ?_⟩
  exact (mem_trace p ρ τ T a).mpr (InTube_center T hρ hτ)

/-- Pointwise segment parameters are selected from genuine tube membership. -/
def parameter (p : α → Point d) (T : TubeData d) (ρ τ : ℝ) (a : α) : ℝ :=
  by
    classical
    exact if h : InTube T ρ τ (p a) then Classical.choose h else 0

omit [Fintype α] [DecidableEq α] in
lemma parameter_spec (p : α → Point d) (T : TubeData d) (ρ τ : ℝ) {a : α}
    (ha : InTube T ρ τ (p a)) :
    |parameter p T ρ τ a| ≤ τ / 2 ∧
      ∀ i, |p a i - T.center i - parameter p T ρ τ a * T.direction i| ≤ ρ := by
  classical
  simp only [parameter, dif_pos ha]
  exact Classical.choose_spec ha

lemma inTube_diameter {T : TubeData d} {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    {x y : Point d} (hx : InTube T ρ τ x) (hy : InTube T ρ τ y) :
    dist x y ≤ τ + 2 * ρ := by
  obtain ⟨s, hs, hxs⟩ := hx
  obtain ⟨u, hu, hyu⟩ := hy
  apply (dist_pi_le_iff (by linarith : 0 ≤ τ + 2 * ρ)).mpr
  intro i
  rw [Real.dist_eq]
  have hsu : |s - u| ≤ τ := by linarith [abs_sub s u]
  have hprod : |(s - u) * T.direction i| ≤ τ := by
    rw [abs_mul]
    simpa using mul_le_mul hsu (T.unit.1 i) (abs_nonneg _) hτ
  have hid : x i - y i =
      (x i - T.center i - s * T.direction i) -
        (y i - T.center i - u * T.direction i) + (s - u) * T.direction i := by ring
  rw [hid]
  have htriangle := abs_add_le
    ((x i - T.center i - s * T.direction i) - (y i - T.center i - u * T.direction i))
    ((s - u) * T.direction i)
  have htriangle' := abs_sub (x i - T.center i - s * T.direction i)
    (y i - T.center i - u * T.direction i)
  linarith [hxs i, hyu i]

omit [DecidableEq α] in
lemma footprint_diameter (p : α → Point d) {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hρτ : ρ ≤ τ)
    {W : Finset α} (hW : W ∈ footprints p ρ τ) {a b : α} (ha : a ∈ W) (hb : b ∈ W) :
    dist (p a) (p b) ≤ 3 * τ := by
  obtain ⟨T, rfl⟩ := (mem_footprints p ρ τ W).mp hW
  have hd := inTube_diameter hρ (hρ.trans hρτ)
    ((mem_trace p ρ τ T a).mp ha) ((mem_trace p ρ τ T b).mp hb)
  linarith

def grid (p : α → Point d) (ρ : ℝ) (a : α) : GridLabel d := fun i => ⌊p a i / ρ⌋

def coverProfile (p : α → Point d) (ρ τ : ℝ) (E : Finset α) : ℕ :=
  (footprints p ρ τ).sup (fun W => ((E ∩ W).image (grid p ρ)).card)

lemma coverProfile_mono (p : α → Point d) (ρ τ : ℝ) : Monotone (coverProfile p ρ τ) :=
  profile_mono (fun _ : Unit => footprints p ρ τ) (fun _ : Unit => grid p ρ) ()

@[simp] lemma coverProfile_empty (p : α → Point d) (ρ τ : ℝ) : coverProfile p ρ τ ∅ = 0 :=
  profile_empty (fun _ : Unit => footprints p ρ τ) (fun _ : Unit => grid p ρ) ()

lemma coverProfile_positive (p : α → Point d) {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    {E : Finset α} (hE : E.Nonempty) : 0 < coverProfile p ρ τ E :=
  profile_positive (fun _ : Unit => footprints p ρ τ) (fun _ : Unit => grid p ρ)
    (fun _ a => point_covered p hρ hτ a) () E hE

lemma finiteProfile_eq {I : Type*} (p : α → Point d) (ρ τ : I → ℝ) (i : I) (E : Finset α) :
    profile (fun i => footprints p (ρ i) (τ i)) (fun i => grid p (ρ i)) i E =
      coverProfile p (ρ i) (τ i) E := rfl

lemma coverProfile_le_card (p : α → Point d) (ρ τ : ℝ) (E : Finset α) :
    coverProfile p ρ τ E ≤ E.card :=
  profile_le_card (fun _ : Unit => footprints p ρ τ) (fun _ : Unit => grid p ρ) () E

/-- An attaining actual tube, with its genuine center and direction, is obtained
from the finite footprint maximum rather than assumed by the caller. -/
theorem exists_maximizing_tube (p : α → Point d) (ρ τ : ℝ) (E : Finset α) :
    ∃ T : TubeData d, ((E ∩ trace p ρ τ T).image (grid p ρ)).card = coverProfile p ρ τ E := by
  obtain ⟨W, hW, hmax⟩ := Finset.exists_mem_eq_sup (footprints p ρ τ)
    (footprints_nonempty p ρ τ) (fun W => ((E ∩ W).image (grid p ρ)).card)
  obtain ⟨T, rfl⟩ := (mem_footprints p ρ τ W).mp hW
  exact ⟨T, hmax.symm⟩

theorem exists_nonempty_maximizing_tube (p : α → Point d) {ρ τ : ℝ}
    (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) (E : Finset α) (hE : E.Nonempty) :
    ∃ T : TubeData d, ((E ∩ trace p ρ τ T).image (grid p ρ)).card = coverProfile p ρ τ E ∧
      (E ∩ trace p ρ τ T).Nonempty := by
  obtain ⟨T, hmax⟩ := exists_maximizing_tube p ρ τ E
  have hpos := coverProfile_positive p hρ hτ hE
  refine ⟨T, hmax, ?_⟩
  exact Finset.image_nonempty.mp (Finset.card_pos.mp (by rwa [hmax]))

/-- The actual geometric grid-cover theorem supplies the linear profile bound. -/
theorem footprint_linear_bound (p : α → Point d) (E : Finset α) {ρ τ : ℝ}
    (hρ : 0 < ρ) (hρτ : ρ ≤ τ) {W : Finset α} (hW : W ∈ footprints p ρ τ) :
    (((E ∩ W).image (grid p ρ)).card : ℝ) * ρ ≤ 9 * (8 ^ d : ℕ) * τ := by
  obtain ⟨T, rfl⟩ := (mem_footprints p ρ τ W).mp hW
  have hactual : ∀ a ∈ E ∩ trace p ρ τ T, InTube T ρ τ (p a) := by
    intro a ha
    exact (mem_trace p ρ τ T a).mp (Finset.mem_inter.mp ha).2
  apply GraphTubeGridCover.segment_occupied_cells_bound (E ∩ trace p ρ τ T) p
    T.center T.direction (parameter p T ρ τ) ρ τ hρ hρτ
  · obtain ⟨i, hi⟩ := T.unit.2
    exact ⟨i, fun hz => by simp [hz] at hi⟩
  · exact T.unit.1
  · intro a ha
    exact (parameter_spec p T ρ τ (hactual a ha)).1
  · intro a ha
    exact (parameter_spec p T ρ τ (hactual a ha)).2

theorem coverProfile_linear_bound (p : α → Point d) (E : Finset α) {ρ τ : ℝ}
    (hρ : 0 < ρ) (hρτ : ρ ≤ τ) :
    (coverProfile p ρ τ E : ℝ) ≤ (9 * (8 ^ d : ℕ)) * (τ / ρ) := by
  obtain ⟨W, hW, hmax⟩ := Finset.exists_mem_eq_sup (footprints p ρ τ)
    (footprints_nonempty p ρ τ) (fun W => ((E ∩ W).image (grid p ρ)).card)
  have hb := footprint_linear_bound p E hρ hρτ hW
  unfold coverProfile
  rw [hmax]
  calc
    (((E ∩ W).image (grid p ρ)).card : ℝ) ≤ (9 * (8 ^ d : ℕ) * τ) / ρ :=
      (le_div_iff₀ hρ).mpr hb
    _ = (9 * (8 ^ d : ℕ)) * (τ / ρ) := by ring

lemma floor_equal_close {ρ x y : ℝ} (hρ : 0 < ρ) (hcell : ⌊x / ρ⌋ = ⌊y / ρ⌋) :
    |x - y| < ρ := by
  have hxlo := Int.floor_le (x / ρ)
  have hxhi := Int.lt_floor_add_one (x / ρ)
  have hylo := Int.floor_le (y / ρ)
  have hyhi := Int.lt_floor_add_one (y / ρ)
  rw [hcell] at hxlo hxhi
  have hnorm : |x / ρ - y / ρ| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  rw [← sub_div, abs_div, abs_of_pos hρ] at hnorm
  simpa only [one_mul] using (div_lt_iff₀ hρ).mp hnorm

omit [Fintype α] [DecidableEq α] in
lemma same_grid_close (p : α → Point d) {ρ : ℝ} (hρ : 0 < ρ)
    {a b : α} (hcell : grid p ρ a = grid p ρ b) (i : Fin (d + 1)) :
    |p a i - p b i| < ρ := floor_equal_close hρ (congrFun hcell i)

/-- A whole-cell fiber lies in width 2ρ with the SAME center, direction and
parameter interval. Its scalar parameter comes from an original trace witness
in the very same original ρ-cell. -/
theorem wholeCells_in_double_width (p : α → Point d) (T : TubeData d)
    (E : Finset α) {ρ τ : ℝ} (hρ : 0 < ρ) {a : α}
    (ha : a ∈ wholeCells (grid p ρ) E (trace p ρ τ T)) :
    InTube T (2 * ρ) τ (p a) := by
  obtain ⟨_, b, hb, hcell⟩ := (FiniteCoverProfileEpochs.mem_wholeCells _ _ _ a).mp ha
  obtain ⟨s, hs, herror⟩ := (mem_trace p ρ τ T b).mp (Finset.mem_inter.mp hb).2
  refine ⟨s, hs, ?_⟩
  intro i
  have hclose := same_grid_close p hρ hcell i
  have hid : p a i - T.center i - s * T.direction i =
      (p a i - p b i) + (p b i - T.center i - s * T.direction i) := by ring
  rw [hid]
  have htri := abs_add_le (p a i - p b i) (p b i - T.center i - s * T.direction i)
  linarith [herror i]

theorem wholeCells_footprint_in_double_width (p : α → Point d) (E : Finset α)
    {ρ τ : ℝ} (hρ : 0 < ρ) {W : Finset α} (hW : W ∈ footprints p ρ τ) {a : α}
    (ha : a ∈ wholeCells (grid p ρ) E W) :
    InTube (witness p ρ τ W hW) (2 * ρ) τ (p a) := by
  rw [witness_trace p ρ τ W hW] at ha
  exact wholeCells_in_double_width p _ E hρ ha

/-- The t-power count comes from original metric AD on an actual carrier,
through the actual diameter of the geometric footprint. No injectivity is
needed for this grid-image bound, and no original source label is changed. -/
theorem footprint_AD_bound (A : Finset (Point d)) (p : α → Point d)
    (hpositions : ∀ a, p a ∈ A) (E : Finset α)
    {δ ρ τ K t : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρτ : ρ ≤ τ) (hτ : τ ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (htd : t ≤ (d + 1 : ℕ))
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1)
    (hAD : ADBounds A δ K t) {W : Finset α} (hW : W ∈ footprints p ρ τ) :
    (((E ∩ W).image (grid p ρ)).card : ℝ) ≤
      (9 : ℝ) ^ (d + 1) * (18 : ℝ) ^ t * K ^ 2 * (τ / ρ) ^ t := by
  classical
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hτpos : 0 < τ := hρ.trans_le hρτ
  have hsubset : (E ∩ W).image p ⊆ A := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact hpositions a
  have hfootdiam : ∀ x ∈ (E ∩ W).image p, ∀ y ∈ (E ∩ W).image p,
      dist x y ≤ 3 * τ := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact footprint_diameter p hρ.le hρτ hW (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
  have hb := ADGridCoverMenus.diameter_subset_occupied_grid_cells_le A ((E ∩ W).image p)
    hδ hδρ (hρτ.trans hτ) (by linarith : ρ ≤ 3 * τ) hK ht htd hdiam hAD hsubset hfootdiam
  have himage : ((E ∩ W).image p).image (ADGridCoverMenus.gridLabel ρ) =
      (E ∩ W).image (grid p ρ) := by
    rw [Finset.image_image]
    rfl
  rw [himage] at hb
  have hratio : (3 * τ) / ρ = 3 * (τ / ρ) := by ring
  rw [hratio, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (div_nonneg hτpos.le hρ.le)] at hb
  have h18 : (18 : ℝ) ^ t = (6 : ℝ) ^ t * (3 : ℝ) ^ t := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [h18]
  nlinarith

/-- Actual geometric footprint profiles satisfy the AD t-power bound. -/
theorem coverProfile_AD_bound (A : Finset (Point d)) (p : α → Point d)
    (hpositions : ∀ a, p a ∈ A) (E : Finset α)
    {δ ρ τ K t : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρτ : ρ ≤ τ) (hτ : τ ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (htd : t ≤ (d + 1 : ℕ))
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1)
    (hAD : ADBounds A δ K t) :
    (coverProfile p ρ τ E : ℝ) ≤
      (9 : ℝ) ^ (d + 1) * (18 : ℝ) ^ t * K ^ 2 * (τ / ρ) ^ t := by
  obtain ⟨W, hW, hmax⟩ := Finset.exists_mem_eq_sup (footprints p ρ τ)
    (footprints_nonempty p ρ τ) (fun W => ((E ∩ W).image (grid p ρ)).card)
  unfold coverProfile
  rw [hmax]
  exact footprint_AD_bound A p hpositions E hδ hδρ hρτ hτ hK ht htd hdiam hAD hW

end
end ActualTubeFootprintProfiles
