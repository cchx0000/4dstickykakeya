import Theorems.Thm_StickyKakeya4_actual_tube_footprint_profiles
import Theorems.Thm_StickyKakeya4_grid_quotient_ad

set_option autoImplicit false
set_option warningAsError true

namespace TubeExpansionCover

open ActualTubeFootprintProfiles FiniteCoverProfileEpochs
open scoped BigOperators
noncomputable section

/-- Literal bounded menu of shifts in the ORIGINAL coordinate axes. -/
def offsets (d C : ℕ) : Finset (GridLabel d) :=
  GridQuotientAD.box (fun _ => 0) C

def shifted {d : ℕ} (T : TubeData d) (rho : ℝ) (k : GridLabel d) : TubeData d where
  center := fun i => T.center i + rho * (k i : ℝ)
  direction := T.direction
  unit := T.unit

lemma offsets_card (d C : ℕ) : (offsets d C).card = (2 * C + 1) ^ (d + 1) :=
  GridQuotientAD.box_card (fun _ => 0) C

lemma floor_error_in_menu {x rho : ℝ} (hrho : 0 < rho) (C : ℕ)
    (hx : |x| ≤ (C : ℝ) * rho) :
    |⌊x / rho⌋| ≤ (C : ℤ) ∧ |x - rho * (⌊x / rho⌋ : ℝ)| ≤ rho := by
  have hnorm : |x / rho| ≤ (C : ℝ) := by
    rw [abs_div, abs_of_pos hrho]
    exact (div_le_iff₀ hrho).mpr hx
  obtain ⟨hl, hu⟩ := abs_le.mp hnorm
  have hfu := Int.floor_mono hu
  have hfl' : -(C : ℤ) ≤ ⌊x / rho⌋ := by
    apply Int.le_floor.mpr
    simpa using hl
  have hfu' : ⌊x / rho⌋ ≤ (C : ℤ) := by simpa using hfu
  have h0 : (⌊x / rho⌋ : ℝ) ≤ x / rho := Int.floor_le _
  have h1 : x / rho < (⌊x / rho⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h0' := (le_div_iff₀ hrho).mp h0
  have h1' := (div_lt_iff₀ hrho).mp h1
  refine ⟨abs_le.mpr ⟨hfl', hfu'⟩, abs_le.mpr ?_⟩
  constructor <;> nlinarith

/-- A width-C*rho tube is covered by the explicit rho tubes, with exactly the
same direction and parameter interval. No enlarged time scale is introduced. -/
theorem in_expanded_tube_exists_shift {d : ℕ} (T : TubeData d)
    {rho tau : ℝ} (hrho : 0 < rho) (C : ℕ) {x : Point d}
    (hx : InTube T ((C : ℝ) * rho) tau x) :
    ∃ k ∈ offsets d C, InTube (shifted T rho k) rho tau x := by
  obtain ⟨s, hs, he⟩ := hx
  let k : GridLabel d := fun i => ⌊(x i - T.center i - s * T.direction i) / rho⌋
  refine ⟨k, ?_, s, hs, ?_⟩
  · apply (GridQuotientAD.mem_box_iff (fun _ => 0) k C).mpr
    intro i
    simpa only [sub_zero, k] using (floor_error_in_menu hrho C (he i)).1
  · intro i
    have h := (floor_error_in_menu hrho C (he i)).2
    convert h using 1
    congr 1
    dsimp [shifted, k]
    ring

/-- Counts of ACTUAL original-cell images in an expanded tube are controlled
by the explicit finite shift menu. -/
theorem expanded_tube_coverCount_le {alpha beta : Type*} [Fintype alpha]
    [DecidableEq alpha] [DecidableEq beta] {d : ℕ}
    (p : alpha → Point d) (cell : alpha → beta) (E : Finset alpha)
    (T : TubeData d) {rho tau : ℝ} (hrho : 0 < rho) (C M : ℕ)
    (hthin : ∀ T' : TubeData d, coverCount cell E (trace p rho tau T') ≤ M) :
    coverCount cell E (trace p ((C : ℝ) * rho) tau T) ≤ (2 * C + 1) ^ (d + 1) * M := by
  classical
  let imageAt (k : GridLabel d) := (E ∩ trace p rho tau (shifted T rho k)).image cell
  have hsub : (E ∩ trace p ((C : ℝ) * rho) tau T).image cell ⊆
      (offsets d C).biUnion imageAt := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨haE, haT⟩ := Finset.mem_inter.mp ha
    obtain ⟨k, hk, haK⟩ := in_expanded_tube_exists_shift T hrho C
      ((mem_trace p _ _ T a).mp haT)
    apply Finset.mem_biUnion.mpr
    exact ⟨k, hk, Finset.mem_image.mpr ⟨a,
      Finset.mem_inter.mpr ⟨haE, (mem_trace p _ _ _ a).mpr haK⟩, rfl⟩⟩
  calc
    coverCount cell E (trace p ((C : ℝ) * rho) tau T)
      ≤ ((offsets d C).biUnion imageAt).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ offsets d C, (imageAt k).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ offsets d C, M := by
      apply Finset.sum_le_sum
      intro k _hk
      exact hthin (shifted T rho k)
    _ = (2 * C + 1) ^ (d + 1) * M := by simp [offsets_card]

/-- The bound is instantiated by the finite maximum of genuine thin-tube
footprints; no separate covering/profile certificate is an input. -/
theorem expanded_tube_le_actual_profile {alpha beta : Type*} [Fintype alpha]
    [DecidableEq alpha] [DecidableEq beta] {d : ℕ}
    (p : alpha → Point d) (cell : alpha → beta) (E : Finset alpha)
    (T : TubeData d) {rho tau : ℝ} (hrho : 0 < rho) (C : ℕ) :
    coverCount cell E (trace p ((C : ℝ) * rho) tau T) ≤
      (2 * C + 1) ^ (d + 1) *
        (footprints p rho tau).sup (fun W => coverCount cell E W) := by
  apply expanded_tube_coverCount_le p cell E T hrho C
  intro T'
  exact Finset.le_sup (trace_mem_footprints p rho tau T')

/-- A center shift ALONG the same original line, retaining its unit direction. -/
def shiftedAlong {d : ℕ} (T : TubeData d) (tau : ℝ) (k : ℤ) : TubeData d where
  center := fun i => T.center i + tau * (k : ℝ) * T.direction i
  direction := T.direction
  unit := T.unit

lemma centered_parameter_rounding {s tau : ℝ} (htau : 0 < tau) (C : ℕ)
    (hs : |s| ≤ (C : ℝ) * tau / 2) :
    let k := ⌊s / tau + (1 : ℝ) / 2⌋
    |k| ≤ (C : ℤ) ∧ |s - tau * (k : ℝ)| ≤ tau / 2 := by
  dsimp
  have hs' : |s / tau| ≤ (C : ℝ) / 2 := by
    rw [abs_div, abs_of_pos htau]
    apply (div_le_iff₀ htau).mpr
    nlinarith
  have hl := (abs_le.mp hs').1
  have hu := (abs_le.mp hs').2
  have hf0 := Int.floor_le (s / tau + (1 : ℝ) / 2)
  have hf1 := Int.lt_floor_add_one (s / tau + (1 : ℝ) / 2)
  have hC : (0 : ℝ) ≤ C := by positivity
  have hlow : -(C : ℤ) ≤ ⌊s / tau + (1 : ℝ) / 2⌋ := by
    have hreal : -(C : ℝ) ≤ s / tau + (1 : ℝ) / 2 := by linarith
    apply Int.le_floor.mpr
    simpa using hreal
  have hhigh : ⌊s / tau + (1 : ℝ) / 2⌋ ≤ (C : ℤ) := by
    have hreal : (⌊s / tau + (1 : ℝ) / 2⌋ : ℝ) < (C : ℝ) + 1 := by linarith
    have hint : ⌊s / tau + (1 : ℝ) / 2⌋ < (C : ℤ) + 1 := by exact_mod_cast hreal
    omega
  refine ⟨abs_le.mpr ⟨hlow, hhigh⟩, ?_⟩
  have hrem : |s / tau - (⌊s / tau + (1 : ℝ) / 2⌋ : ℝ)| ≤ (1 : ℝ) / 2 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hm := mul_le_mul_of_nonneg_right hrem htau.le
  have hid : |s / tau - (⌊s / tau + (1 : ℝ) / 2⌋ : ℝ)| * tau =
      |s - tau * (⌊s / tau + (1 : ℝ) / 2⌋ : ℝ)| := by
    calc
      |s / tau - (⌊s / tau + (1 : ℝ) / 2⌋ : ℝ)| * tau =
          |(s / tau - (⌊s / tau + (1 : ℝ) / 2⌋ : ℝ)) * tau| := by
            rw [abs_mul, abs_of_pos htau]
      _ = _ := by
        congr 1
        field_simp
  rw [hid] at hm
  nlinarith

/-- A length-C*tau tube is covered by 2C+1 literal length-tau tubes.
The width and direction are unchanged. -/
theorem in_long_tube_exists_shift {d : ℕ} (T : TubeData d)
    {rho tau : ℝ} (htau : 0 < tau) (C : ℕ) {x : Point d}
    (hx : InTube T rho ((C : ℝ) * tau) x) :
    ∃ k ∈ Finset.Icc (-(C : ℤ)) C, InTube (shiftedAlong T tau k) rho tau x := by
  obtain ⟨s, hs, he⟩ := hx
  let k := ⌊s / tau + (1 : ℝ) / 2⌋
  have hk := centered_parameter_rounding htau C hs
  refine ⟨k, Finset.mem_Icc.mpr (abs_le.mp hk.1), s - tau * k, hk.2, ?_⟩
  intro i
  convert he i using 1
  congr 1
  dsimp [shiftedAlong]
  ring

lemma alongMenu_card (C : ℕ) :
    (Finset.Icc (-(C : ℤ)) C).card = 2 * C + 1 := by
  rw [Int.card_Icc]
  omega

theorem long_tube_coverCount_le {alpha beta : Type*} [Fintype alpha]
    [DecidableEq alpha] [DecidableEq beta] {d : ℕ}
    (p : alpha → Point d) (cell : alpha → beta) (E : Finset alpha)
    (T : TubeData d) {rho tau : ℝ} (htau : 0 < tau) (C M : ℕ)
    (hthin : ∀ T' : TubeData d, coverCount cell E (trace p rho tau T') ≤ M) :
    coverCount cell E (trace p rho ((C : ℝ) * tau) T) ≤ (2 * C + 1) * M := by
  classical
  let menu := Finset.Icc (-(C : ℤ)) C
  let imageAt (k : ℤ) := (E ∩ trace p rho tau (shiftedAlong T tau k)).image cell
  have hsub : (E ∩ trace p rho ((C : ℝ) * tau) T).image cell ⊆ menu.biUnion imageAt := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨haE, haT⟩ := Finset.mem_inter.mp ha
    obtain ⟨k, hk, haK⟩ := in_long_tube_exists_shift T htau C ((mem_trace p _ _ T a).mp haT)
    apply Finset.mem_biUnion.mpr
    exact ⟨k, hk, Finset.mem_image.mpr ⟨a,
      Finset.mem_inter.mpr ⟨haE, (mem_trace p _ _ _ a).mpr haK⟩, rfl⟩⟩
  calc
    coverCount cell E (trace p rho ((C : ℝ) * tau) T) ≤
        (menu.biUnion imageAt).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ menu, (imageAt k).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ menu, M := by
      apply Finset.sum_le_sum
      intro k _hk
      exact hthin (shiftedAlong T tau k)
    _ = (2 * C + 1) * M := by
      have hc : menu.card = 2 * C + 1 := alongMenu_card C
      simp only [Finset.sum_const, smul_eq_mul, hc]

/-- Both width and length losses are explicit fixed finite covers of the SAME
source's genuine stopped profile. Original point/cell labels are untouched. -/
theorem expanded_long_tube_le_actual_profile {alpha beta : Type*} [Fintype alpha]
    [DecidableEq alpha] [DecidableEq beta] {d : ℕ}
    (p : alpha → Point d) (cell : alpha → beta) (E : Finset alpha)
    (T : TubeData d) {rho tau : ℝ} (hrho : 0 < rho) (htau : 0 < tau) (Cw Ct : ℕ) :
    coverCount cell E (trace p ((Cw : ℝ) * rho) ((Ct : ℝ) * tau) T) ≤
      (2 * Cw + 1) ^ (d + 1) * (2 * Ct + 1) *
        (footprints p rho tau).sup (fun W => coverCount cell E W) := by
  rw [mul_assoc]
  apply expanded_tube_coverCount_le p cell E T hrho Cw
  intro T'
  apply long_tube_coverCount_le p cell E T' htau Ct
  intro T''
  exact Finset.le_sup (trace_mem_footprints p rho tau T'')

/-- Two actual tube parameters are close if their physical points share a
small coordinate neighborhood; a genuinely unit coordinate is used. -/
lemma parameters_close {d : ℕ} (T : TubeData d) (x y : Point d)
    {s t w r : ℝ}
    (hx : ∀ i, |x i - T.center i - s * T.direction i| ≤ w)
    (hy : ∀ i, |y i - T.center i - t * T.direction i| ≤ w)
    (hclose : ∀ i, |x i - y i| ≤ r) : |s - t| ≤ r + 2 * w := by
  obtain ⟨j, hj⟩ := T.unit.2
  have hid : (s - t) * T.direction j =
      (x j - y j) - (x j - T.center j - s * T.direction j) +
        (y j - T.center j - t * T.direction j) := by ring
  have hbound : |(s - t) * T.direction j| ≤ r + 2 * w := by
    rw [hid]
    calc
      |(x j - y j) - (x j - T.center j - s * T.direction j) +
          (y j - T.center j - t * T.direction j)|
        ≤ |(x j - y j) - (x j - T.center j - s * T.direction j)| +
            |y j - T.center j - t * T.direction j| := abs_add_le _ _
      _ ≤ (|x j - y j| + |x j - T.center j - s * T.direction j|) + w :=
        add_le_add (abs_sub _ _) (hy j)
      _ ≤ r + 2 * w := by linarith [hclose j, hx j]
  simpa only [abs_mul, hj, mul_one] using hbound

def recentered {d : ℕ} (T : TubeData d) (t : ℝ) : TubeData d where
  center := fun i => T.center i + t * T.direction i
  direction := T.direction
  unit := T.unit

/-- Restricting a genuine tube to one small spatial neighborhood gives an
explicit short tube; its center is an actual original segment witness. -/
theorem local_tube_containment {d : ℕ} (T : TubeData d) (x y : Point d)
    {w r tau t : ℝ}
    (hy : ∀ i, |y i - T.center i - t * T.direction i| ≤ w)
    (hx : InTube T w tau x) (hclose : ∀ i, |x i - y i| ≤ r) :
    InTube (recentered T t) w (2 * (r + 2 * w)) x := by
  obtain ⟨s, _hs, he⟩ := hx
  refine ⟨s - t, ?_, ?_⟩
  · have hp := parameters_close T x y he hy hclose
    nlinarith
  · intro i
    convert he i using 1
    congr 1
    dsimp [recentered]
    ring

/-- The short length can be bounded by an explicit fixed multiple of r when
its original width is C*rho and rho≤r. -/
theorem local_tube_fixed_length {d : ℕ} (T : TubeData d) (x y : Point d)
    {rho r tau t : ℝ} (C : ℕ) (hscale : rho ≤ r)
    (hy : ∀ i, |y i - T.center i - t * T.direction i| ≤ (C : ℝ) * rho)
    (hx : InTube T ((C : ℝ) * rho) tau x) (hclose : ∀ i, |x i - y i| ≤ r) :
    InTube (recentered T t) ((C : ℝ) * rho) (((2 + 4 * C : ℕ) : ℝ) * r) x := by
  obtain ⟨u, hu, he⟩ := local_tube_containment T x y hy hx hclose
  refine ⟨u, ?_, he⟩
  have hc : (0 : ℝ) ≤ C := by positivity
  push_cast
  nlinarith

/-- A source tube intersected with ONE actual r-cell has a local rho-cover
bound from the SAME original source's width-rho/length-r profile. -/
theorem local_cell_image_le_actual_profile {alpha : Type*} [Fintype alpha]
    [DecidableEq alpha] {d : ℕ} (p : alpha → Point d)
    (E S : Finset alpha) (T : TubeData d) {rho r tau : ℝ} (C : ℕ)
    (hrho : 0 < rho) (hscale : rho ≤ r) (hSE : S ⊆ E)
    (htube : ∀ a ∈ S, InTube T ((C : ℝ) * rho) tau (p a))
    (q : GridLabel d) (hcell : ∀ a ∈ S, grid p r a = q) :
    ((S.image (grid p rho)).card) ≤
      (2 * C + 1) ^ (d + 1) * (2 * (2 + 4 * C) + 1) *
        (footprints p rho r).sup (fun W => coverCount (grid p rho) E W) := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨a0, ha0⟩ := hS
    obtain ⟨t, _ht, he⟩ := htube a0 ha0
    let T0 := recentered T t
    have hr : 0 < r := hrho.trans_le hscale
    have hsub : S ⊆ E ∩ trace p ((C : ℝ) * rho) (((2 + 4 * C : ℕ) : ℝ) * r) T0 := by
      intro a ha
      apply Finset.mem_inter.mpr
      refine ⟨hSE ha, (mem_trace p _ _ T0 a).mpr ?_⟩
      exact local_tube_fixed_length T (p a) (p a0) C hscale he (htube a ha)
        (fun i => (same_grid_close p hr ((hcell a ha).trans (hcell a0 ha0).symm) i).le)
    calc
      (S.image (grid p rho)).card ≤
          ((E ∩ trace p ((C : ℝ) * rho) (((2 + 4 * C : ℕ) : ℝ) * r) T0).image (grid p rho)).card :=
        Finset.card_le_card (Finset.image_subset_image hsub)
      _ ≤ _ := expanded_long_tube_le_actual_profile p (grid p rho) E T0 hrho hr C (2 + 4 * C)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp

end
end TubeExpansionCover
