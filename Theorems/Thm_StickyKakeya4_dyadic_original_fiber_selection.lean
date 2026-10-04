import Theorems.Thm_StickyKakeya4_symmetry_set_difference_step
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace DyadicOriginalFiberSelection

open scoped BigOperators

variable {Ω β : Type*} [DecidableEq β]

def fiber (W : Finset Ω) (f : Ω → β) (y : β) : Finset Ω :=
  W.filter (fun w => f w = y)

def level (W : Finset Ω) (f : Ω → β) (w : Ω) : ℕ :=
  Nat.log 2 (fiber W f (f w)).card

def bin (W : Finset Ω) (f : Ω → β) (j : ℕ) : Finset Ω :=
  W.filter (fun w => level W f w = j)

def levelCount (W : Finset Ω) : ℕ := Nat.log 2 W.card + 1

lemma fiber_card_pos {W : Finset Ω} {f : Ω → β} {y : β}
    (hy : y ∈ W.image f) : 0 < (fiber W f y).card := by
  obtain ⟨w, hw, hwy⟩ := Finset.mem_image.mp hy
  exact Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hwy⟩⟩

lemma fiber_sum (W : Finset Ω) (f : Ω → β) :
    (∑ y ∈ W.image f, (fiber W f y).card) = W.card := by
  unfold fiber
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  exact Finset.filter_eq_self.mpr (fun w hw => Finset.mem_image.mpr ⟨w, hw, rfl⟩)

lemma level_lt (W : Finset Ω) (f : Ω → β) (w : Ω) :
    level W f w < levelCount W := by
  have hc : (fiber W f (f w)).card ≤ W.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hlog := Nat.log_mono_right (b := 2) hc
  exact Nat.lt_succ_of_le hlog

lemma bin_saturated (W : Finset Ω) (f : Ω → β) (j : ℕ)
    {w v : Ω} (hw : w ∈ bin W f j) (hv : v ∈ W) (he : f v = f w) :
    v ∈ bin W f j := by
  obtain ⟨_, hj⟩ := Finset.mem_filter.mp hw
  apply Finset.mem_filter.mpr
  refine ⟨hv, ?_⟩
  simpa only [level, he] using hj

/-- Every selected fiber is literally the full original fiber. -/
lemma fiber_bin_eq (W : Finset Ω) (f : Ω → β) (j : ℕ)
    {y : β} (hy : y ∈ (bin W f j).image f) :
    fiber (bin W f j) f y = fiber W f y := by
  obtain ⟨w, hw, hwy⟩ := Finset.mem_image.mp hy
  ext v
  simp only [fiber, Finset.mem_filter]
  constructor
  · intro hv
    exact ⟨(Finset.mem_filter.mp hv.1).1, hv.2⟩
  · intro hv
    exact ⟨bin_saturated W f j hw hv.1 (hv.2.trans hwy.symm), hv.2⟩

/-- The two-sided dyadic bounds concern the original retained fibers. -/
lemma bin_fiber_bounds (W : Finset Ω) (f : Ω → β) (j : ℕ)
    {y : β} (hy : y ∈ (bin W f j).image f) :
    2 ^ j ≤ (fiber (bin W f j) f y).card ∧
      (fiber (bin W f j) f y).card < 2 ^ (j + 1) := by
  obtain ⟨w, hw, hwy⟩ := Finset.mem_image.mp hy
  have hj : Nat.log 2 (fiber W f y).card = j := by
    have h := (Finset.mem_filter.mp hw).2
    simpa only [level, hwy] using h
  have hcpos : 0 < (fiber W f y).card :=
    fiber_card_pos (Finset.mem_image.mpr ⟨w, (Finset.mem_filter.mp hw).1, hwy⟩)
  have hlo := Nat.pow_log_le_self 2 (Nat.ne_of_gt hcpos)
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (fiber W f y).card
  rw [hj] at hlo hhi
  rw [fiber_bin_eq W f j (Finset.mem_image.mpr ⟨w, hw, hwy⟩)]
  exact ⟨hlo, hhi⟩

/-- There are only `log₂ |W| + 1` actual size classes, and they exhaust W. -/
lemma bin_card_sum (W : Finset Ω) (f : Ω → β) :
    (∑ j ∈ Finset.range (levelCount W), (bin W f j).card) = W.card := by
  unfold bin
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  exact Finset.filter_eq_self.mpr (fun w _ => Finset.mem_range.mpr (level_lt W f w))

/-- An actual maximum-weight dyadic class keeps whole original fibers. -/
theorem exists_dyadic_bin (W : Finset Ω) (f : Ω → β) (hW : W.Nonempty) :
    ∃ j < levelCount W,
      (bin W f j).Nonempty ∧ W.card ≤ levelCount W * (bin W f j).card := by
  have hrange : (Finset.range (levelCount W)).Nonempty := by
    exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (levelCount W))
    (fun j => (bin W f j).card) hrange
  have hmass : W.card ≤ levelCount W * (bin W f j).card := by
    calc
      W.card = ∑ k ∈ Finset.range (levelCount W), (bin W f k).card := (bin_card_sum W f).symm
      _ ≤ ∑ _k ∈ Finset.range (levelCount W), (bin W f j).card :=
        Finset.sum_le_sum (fun k hk => hmax k hk)
      _ = _ := by simp
  refine ⟨j, Finset.mem_range.mp hj, ?_, hmass⟩
  apply Finset.card_pos.mp
  have hpos := hW.card_pos
  nlinarith

/-- Each retained label has at least half the average retained-fiber size.
The average and the fiber both use exactly the same retained original labels. -/
theorem bin_half_average (W : Finset Ω) (f : Ω → β) (j : ℕ)
    {y : β} (hy : y ∈ (bin W f j).image f) :
    (bin W f j).card ≤ 2 * ((bin W f j).image f).card *
      (fiber (bin W f j) f y).card := by
  have hlo := (bin_fiber_bounds W f j hy).1
  calc
    (bin W f j).card = ∑ z ∈ (bin W f j).image f,
        (fiber (bin W f j) f z).card := (fiber_sum _ _).symm
    _ ≤ ∑ _z ∈ (bin W f j).image f, 2 ^ (j + 1) :=
      Finset.sum_le_sum (fun z hz => (bin_fiber_bounds W f j hz).2.le)
    _ = ((bin W f j).image f).card * (2 * 2 ^ j) := by simp [pow_succ, Nat.mul_comm]
    _ ≤ _ := by nlinarith only [Nat.mul_le_mul_left (((bin W f j).image f).card * 2) hlo]

/-- General construction retaining whole fibers of an actual original-label map. -/
theorem exists_original_fiber_refinement (W : Finset Ω) (f : Ω → β) (hW : W.Nonempty) :
    ∃ W' ⊆ W, W'.Nonempty ∧
      W.card ≤ levelCount W * W'.card ∧
      (∀ w ∈ W', ∀ v ∈ W, f v = f w → v ∈ W') ∧
      (∀ y ∈ W'.image f, fiber W' f y = fiber W f y ∧
        W'.card ≤ 2 * (W'.image f).card * (fiber W' f y).card) := by
  obtain ⟨j, _hj, hne, hmass⟩ := exists_dyadic_bin W f hW
  refine ⟨bin W f j, Finset.filter_subset _ _, hne, hmass, ?_, ?_⟩
  · intro w hw v hv he
    exact bin_saturated W f j hw hv he
  · intro y hy
    exact ⟨fiber_bin_eq W f j hy, bin_half_average W f j hy⟩

/-- Exact real-valued form of the lower fiber bound used in growth chains. -/
theorem exists_original_fiber_refinement_real (W : Finset Ω) (f : Ω → β) (hW : W.Nonempty) :
    ∃ W' ⊆ W, W'.Nonempty ∧
      (W.card : ℝ) ≤ (levelCount W : ℝ) * (W'.card : ℝ) ∧
      (∀ w ∈ W', ∀ v ∈ W, f v = f w → v ∈ W') ∧
      (∀ y ∈ W'.image f, fiber W' f y = fiber W f y ∧
        (W'.card : ℝ) / (2 * ((W'.image f).card : ℝ)) ≤ (fiber W' f y).card) := by
  obtain ⟨W', hsub, hne, hmass, hsat, hf⟩ := exists_original_fiber_refinement W f hW
  refine ⟨W', hsub, hne, ?_, hsat, ?_⟩
  · exact_mod_cast hmass
  · intro y hy
    refine ⟨(hf y hy).1, ?_⟩
    have himage : (W'.image f).Nonempty := ⟨y, hy⟩
    have hpos : (0 : ℝ) < 2 * ((W'.image f).card : ℝ) := by
      have hp : (0 : ℝ) < (W'.image f).card := Nat.cast_pos.mpr himage.card_pos
      positivity
    apply (div_le_iff₀ hpos).mpr
    have h := (hf y hy).2
    have hr : (W'.card : ℝ) ≤ 2 * ((W'.image f).card : ℝ) * (fiber W' f y).card := by
      exact_mod_cast h
    nlinarith only [hr]


lemma levelCount_eq_log2 (W : Finset Ω) : levelCount W = Nat.log2 W.card + 1 := by
  rw [Nat.log2_eq_log_two]
  rfl

/-- Saturation means exact preservation of each selected original fiber. -/
lemma fiber_eq_of_saturated {W V : Finset Ω} {f : Ω → β}
    (hsub : W ⊆ V)
    (hsat : ∀ w ∈ W, ∀ v ∈ V, f v = f w → v ∈ W)
    {y : β} (hy : y ∈ W.image f) : fiber W f y = fiber V f y := by
  obtain ⟨w, hw, hwy⟩ := Finset.mem_image.mp hy
  ext v
  simp only [fiber, Finset.mem_filter]
  exact ⟨fun hv => ⟨hsub hv.1, hv.2⟩,
    fun hv => ⟨hsat w hw v hv.1 (hv.2.trans hwy.symm), hv.2⟩⟩

section Symmetry

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

open SymmetrySetDifferenceStep

/-- Dyadic regularization keeps whole ORIGINAL ordered difference fibers,
including every pair of the original Cartesian product with a retained difference. -/
theorem exists_refined_good_pairs (Y S : Finset G) (b : ℝ)
    (hne : (goodPairs Y S b).Nonempty) :
    ∃ W ⊆ S.product S, W.Nonempty ∧
      ((goodPairs Y S b).card : ℝ) ≤
        (levelCount (goodPairs Y S b) : ℝ) * (W.card : ℝ) ∧
      (∀ p ∈ W, ∀ q ∈ S.product S, q.1 - q.2 = p.1 - p.2 → q ∈ W) ∧
      (∀ y ∈ W.image (fun p => p.1 - p.2),
        y ∈ symmetrySet Y b ∧
        fiber W (fun p => p.1 - p.2) y = fiber (S.product S) (fun p => p.1 - p.2) y ∧
        (W.card : ℝ) / (2 * ((W.image (fun p => p.1 - p.2)).card : ℝ)) ≤
          (fiber W (fun p => p.1 - p.2) y).card) := by
  classical
  let d : G × G → G := fun p => p.1 - p.2
  obtain ⟨W, hsub, hW, hmass, hsat, hf⟩ :=
    exists_original_fiber_refinement_real (goodPairs Y S b) d hne
  have hsub0 : W ⊆ S.product S := by
    intro p hp
    have hpp := hsub hp
    exact (show p ∈ S.product S ∧ d p ∈ symmetrySet Y b from by
      simpa only [goodPairs, Finset.mem_filter, d] using hpp).1
  have hsat0 : ∀ p ∈ W, ∀ q ∈ S.product S, d q = d p → q ∈ W := by
    intro p hp q hq he
    apply hsat p hp q
    · have hpp := hsub hp
      have hpsym : d p ∈ symmetrySet Y b :=
        (show p ∈ S.product S ∧ d p ∈ symmetrySet Y b from by
          simpa only [goodPairs, Finset.mem_filter, d] using hpp).2
      simp only [goodPairs, Finset.mem_filter]
      exact ⟨hq, show d q ∈ symmetrySet Y b from he.symm ▸ hpsym⟩
    · exact he
  refine ⟨W, hsub0, hW, hmass, hsat0, ?_⟩
  intro y hy
  have hysym : y ∈ symmetrySet Y b := by
    obtain ⟨p, hp, hpy⟩ := Finset.mem_image.mp hy
    have hpp := hsub hp
    have hpSym : d p ∈ symmetrySet Y b :=
      (show p ∈ S.product S ∧ d p ∈ symmetrySet Y b from by
        simpa only [goodPairs, Finset.mem_filter, d] using hpp).2
    exact hpy ▸ hpSym
  exact ⟨hysym, fiber_eq_of_saturated hsub0 hsat0 hy, (hf y hy).2⟩

/-- The complete original symmetry-difference step followed by exact dyadic
whole-fiber selection. The only mass input is membership in Sym_a(Y). -/
theorem exists_refined_symmetry_pairs (Y S : Finset G) {a : ℝ}
    (ha : 0 < a) (hY : Y.Nonempty) (hS : S.Nonempty) (hSym : S ⊆ symmetrySet Y a) :
    ∃ W ⊆ S.product S, W.Nonempty ∧
      (a ^ 2 / 2) * (S.card : ℝ) ^ 2 ≤
        (levelCount (goodPairs Y S (a ^ 2 / 2)) : ℝ) * (W.card : ℝ) ∧
      (∀ p ∈ W, ∀ q ∈ S.product S, q.1 - q.2 = p.1 - p.2 → q ∈ W) ∧
      (∀ y ∈ W.image (fun p => p.1 - p.2),
        y ∈ symmetrySet Y (a ^ 2 / 2) ∧
        fiber W (fun p => p.1 - p.2) y = fiber (S.product S) (fun p => p.1 - p.2) y ∧
        (W.card : ℝ) / (2 * ((W.image (fun p => p.1 - p.2)).card : ℝ)) ≤
          (fiber W (fun p => p.1 - p.2) y).card) := by
  have hmass := good_pairs_lower Y S ha hY hSym
  have hspos : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hne : (goodPairs Y S (a ^ 2 / 2)).Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : ℝ) < (a ^ 2 / 2) * (S.card : ℝ) ^ 2 := by positivity
    exact Nat.cast_pos.mp (hp.trans_le hmass)
  obtain ⟨W, hsub, hW, hcost, hsat, hf⟩ := exists_refined_good_pairs Y S (a ^ 2 / 2) hne
  exact ⟨W, hsub, hW, hmass.trans hcost, hsat, hf⟩


/-- Initial asymmetric-energy caller with the same actual whole-fiber output. -/
theorem exists_refined_pairs_of_addEnergy (Y S : Finset G) {b : ℝ}
    (hb : 0 < b) (hY : Y.Nonempty) (hS : S.Nonempty)
    (henergy : 2 * b * (Y.card : ℝ) * (S.card : ℝ) ^ 2 ≤ (Finset.addEnergy Y S : ℝ)) :
    ∃ W ⊆ S.product S, W.Nonempty ∧
      b * (S.card : ℝ) ^ 2 ≤
        (levelCount (goodPairs Y S b) : ℝ) * (W.card : ℝ) ∧
      (∀ p ∈ W, ∀ q ∈ S.product S, q.1 - q.2 = p.1 - p.2 → q ∈ W) ∧
      (∀ y ∈ W.image (fun p => p.1 - p.2),
        y ∈ symmetrySet Y b ∧
        fiber W (fun p => p.1 - p.2) y = fiber (S.product S) (fun p => p.1 - p.2) y ∧
        (W.card : ℝ) / (2 * ((W.image (fun p => p.1 - p.2)).card : ℝ)) ≤
          (fiber W (fun p => p.1 - p.2) y).card) := by
  have hmass := good_pairs_lower_of_addEnergy Y S hb hY henergy
  have hspos : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hne : (goodPairs Y S b).Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : ℝ) < b * (S.card : ℝ) ^ 2 := by positivity
    exact Nat.cast_pos.mp (hp.trans_le hmass)
  obtain ⟨W, hsub, hW, hcost, hsat, hf⟩ := exists_refined_good_pairs Y S b hne
  exact ⟨W, hsub, hW, hmass.trans hcost, hsat, hf⟩

end Symmetry

end DyadicOriginalFiberSelection
