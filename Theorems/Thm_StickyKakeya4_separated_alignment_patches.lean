import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

/-!
Concrete periodic patch isolation and shear-grid quantization.
All metric statements use Mathlib's sup metric on finite products of real
coordinates. No AD, isolation, quantization-error, or separation certificate
is assumed. Source labels and their original natural-number weights survive.
-/
namespace SeparatedAlignmentPatches
open scoped BigOperators

abbrev Point (d : ℕ) := Fin d → ℝ
abbrev Cell (d : ℕ) := Fin d → ℤ

noncomputable def cell {d : ℕ} (b : ℝ) (p : Point d) : Cell d :=
  fun i => ⌊p i / b⌋

def residue (L : ℕ) (hL : 0 < L) (k : ℤ) : Fin L :=
  ⟨(k % (L : ℤ)).toNat, by
    have hpos : (0 : ℤ) < L := by exact_mod_cast hL
    have hlo := Int.emod_nonneg k (ne_of_gt hpos)
    have hhi := Int.emod_lt_of_pos k hpos
    omega⟩

def color {d : ℕ} (L : ℕ) (hL : 0 < L) (k : Cell d) : Fin d → Fin L :=
  fun i => residue L hL (k i)

lemma residue_eq_emod {L : ℕ} {hL : 0 < L} {k l : ℤ}
    (h : residue L hL k = residue L hL l) : k % (L : ℤ) = l % (L : ℤ) := by
  have hv := congrArg Fin.val h
  have hpos : (0 : ℤ) < L := by exact_mod_cast hL
  have hk := Int.emod_nonneg k (ne_of_gt hpos)
  have hl := Int.emod_nonneg l (ne_of_gt hpos)
  dsimp [residue] at hv
  omega

lemma integer_residue_spacing {L : ℕ} (hL : 0 < L) {k l : ℤ}
    (hmod : k % (L : ℤ) = l % (L : ℤ)) (hne : k ≠ l) :
    (L : ℤ) ≤ |k - l| := by
  have hm : Int.ModEq (L : ℤ) l k := hmod.symm
  obtain ⟨z, hz⟩ := hm.dvd
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, mul_zero] at hz
    exact hne (sub_eq_zero.mp hz)
  have hzpos : (0 : ℤ) < |z| := abs_pos.mpr hz0
  have hzabs : (1 : ℤ) ≤ |z| := by omega
  have hLnonneg : (0 : ℤ) ≤ L := by positivity
  calc
    (L : ℤ) = |(L : ℤ)| * 1 := by rw [abs_of_nonneg hLnonneg, mul_one]
    _ ≤ |(L : ℤ)| * |z| := mul_le_mul_of_nonneg_left hzabs (abs_nonneg _)
    _ = |k - l| := by rw [hz, abs_mul]

lemma real_residue_spacing {L : ℕ} (hL : 0 < L) {k l : ℤ}
    (hmod : k % (L : ℤ) = l % (L : ℤ)) (hne : k ≠ l) :
    (L : ℝ) ≤ |(k : ℝ) - (l : ℝ)| := by
  exact_mod_cast integer_residue_spacing hL hmod hne

/-- Maximum-weight color is selected from the actual labels; zero weights and
empty source sets are allowed. -/
theorem maximum_weight_color {α β : Type*} [Fintype β] [Nonempty β] [DecidableEq β]
    (A : Finset α) (w : α → ℕ) (f : α → β) :
    ∃ c : β, (∑ a ∈ A, w a) ≤
      Fintype.card β * (∑ a ∈ A.filter (fun a => f a = c), w a) := by
  classical
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image (Finset.univ : Finset β)
    (fun c => ∑ a ∈ A.filter (fun a => f a = c), w a) Finset.univ_nonempty
  refine ⟨c, ?_⟩
  calc
    (∑ a ∈ A, w a) = ∑ c : β, ∑ a ∈ A.filter (fun a => f a = c), w a :=
      (Finset.sum_fiberwise A f w).symm
    _ ≤ ∑ _c : β, ∑ a ∈ A.filter (fun a => f a = c), w a :=
      Finset.sum_le_sum (fun c' hc' => hc c' hc')
    _ = Fintype.card β * (∑ a ∈ A.filter (fun a => f a = c), w a) := by simp

lemma cell_bounds {d : ℕ} (b : ℝ) (hb : 0 < b) (p : Point d) (i : Fin d) :
    (cell b p i : ℝ) * b ≤ p i ∧ p i < ((cell b p i : ℝ) + 1) * b := by
  exact ⟨(le_div_iff₀ hb).mp (Int.floor_le (p i / b)),
    (div_lt_iff₀ hb).mp (Int.lt_floor_add_one (p i / b))⟩

lemma same_cell_dist_lt {d : ℕ} (b : ℝ) (hb : 0 < b) (p q : Point d)
    (hcell : cell b p = cell b q) : dist p q < b := by
  apply (dist_pi_lt_iff hb).mpr
  intro i
  rw [Real.dist_eq]
  obtain ⟨hp₀, hp₁⟩ := cell_bounds b hb p i
  obtain ⟨hq₀, hq₁⟩ := cell_bounds b hb q i
  have he := congrFun hcell i
  rw [he] at hp₀ hp₁
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

lemma close_same_color_cell_eq {d : ℕ} (b R : ℝ) (hb : 0 < b)
    (L : ℕ) (hL : 0 < L) (hR : R ≤ ((L : ℝ) - 1) * b)
    (p q : Point d) (hcolor : color L hL (cell b p) = color L hL (cell b q))
    (hclose : dist p q < R) : cell b p = cell b q := by
  funext i
  by_contra hne
  have hmod := residue_eq_emod (congrFun hcolor i)
  have hgap := real_residue_spacing hL hmod hne
  have hcoord : |p i - q i| < R := by
    rw [← Real.dist_eq]
    exact (dist_le_pi_dist p q i).trans_lt hclose
  obtain ⟨hp₀, hp₁⟩ := cell_bounds b hb p i
  obtain ⟨hq₀, hq₁⟩ := cell_bounds b hb q i
  obtain ⟨hnear₀, hnear₁⟩ := abs_lt.mp hcoord
  have hupper : (cell b p i : ℝ) - (cell b q i : ℝ) < (L : ℝ) := by
    apply (mul_lt_mul_iff_left₀ hb).mp
    nlinarith
  have hlower : -(L : ℝ) < (cell b p i : ℝ) - (cell b q i : ℝ) := by
    apply (mul_lt_mul_iff_left₀ hb).mp
    nlinarith
  exact (not_lt_of_ge hgap) (abs_lt.mpr ⟨hlower, hupper⟩)

/-- Exact local-ball identity for the actual retained original labels. A full
periodic color of ORIGINAL parent cells is retained; no point is moved here.
The ball is the sup-metric open ball. -/
theorem periodic_patch_isolation {α : Type*} {d : ℕ}
    (A : Finset α) (w : α → ℕ) (p : α → Point d)
    (b R : ℝ) (hb : 0 < b) (hsmall : b ≤ R)
    (L : ℕ) (hL : 0 < L) (hgap : R ≤ ((L : ℝ) - 1) * b) :
    ∃ B : Finset α, B ⊆ A ∧
      (∑ x ∈ A, w x) ≤ L ^ d * (∑ x ∈ B, w x) ∧
      ∀ a ∈ B,
        B.filter (fun x => dist (p x) (p a) < R) =
          A.filter (fun x => cell b (p x) = cell b (p a)) := by
  classical
  let : Nonempty (Fin d → Fin L) := ⟨fun _ => ⟨0, hL⟩⟩
  obtain ⟨c, hc⟩ := maximum_weight_color A w (fun x => color L hL (cell b (p x)))
  let B := A.filter (fun x => color L hL (cell b (p x)) = c)
  refine ⟨B, Finset.filter_subset _ _, ?_, ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hc
  · intro a ha
    have hac : color L hL (cell b (p a)) = c := (Finset.mem_filter.mp ha).2
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hclose⟩
      have hxA := (Finset.mem_filter.mp hx).1
      have hxc := (Finset.mem_filter.mp hx).2
      exact ⟨hxA, close_same_color_cell_eq b R hb L hL hgap (p x) (p a)
        (hxc.trans hac.symm) hclose⟩
    · rintro ⟨hxA, hsame⟩
      have hxB : x ∈ B := Finset.mem_filter.mpr ⟨hxA, by rw [hsame]; exact hac⟩
      exact ⟨hxB, (same_cell_dist_lt b hb (p x) (p a) hsame).trans_le hsmall⟩

/-- A fixed explicit spacing choice, ready for patch callers. -/
theorem periodic_patch_at_multiplier {α : Type*} {d : ℕ}
    (A : Finset α) (w : α → ℕ) (p : α → Point d)
    (b : ℝ) (hb : 0 < b) (C : ℕ) (hC : 1 ≤ C) :
    ∃ B : Finset α, B ⊆ A ∧
      (∑ x ∈ A, w x) ≤ (4 * C + 4) ^ d * (∑ x ∈ B, w x) ∧
      ∀ a ∈ B,
        B.filter (fun x => dist (p x) (p a) < (C : ℝ) * b) =
          A.filter (fun x => cell b (p x) = cell b (p a)) := by
  apply periodic_patch_isolation A w p b ((C : ℝ) * b) hb
  · have hc : (1 : ℝ) ≤ C := by exact_mod_cast hC
    nlinarith
  · omega
  · push_cast
    have hc : (0 : ℝ) ≤ C := by positivity
    nlinarith

abbrev ShearPoint (n : ℕ) := ℝ × (Fin n → ℝ)
abbrev ShearIndex (n : ℕ) := ℤ × (Fin n → ℤ)

noncomputable def quantizedIndex {n : ℕ} (μ : ℝ) (α : Fin n → ℝ)
    (p : ShearPoint n) : ShearIndex n :=
  (⌊p.1 / μ⌋, fun i => ⌊(p.2 i - α i * (μ * (⌊p.1 / μ⌋ : ℝ))) / μ⌋)

noncomputable def realize {n : ℕ} (μ : ℝ) (α : Fin n → ℝ)
    (k : ShearIndex n) : ShearPoint n :=
  (μ * (k.1 : ℝ), fun i => μ * (k.2 i : ℝ) + α i * (μ * (k.1 : ℝ)))

noncomputable def quantize {n : ℕ} (μ : ℝ) (α : Fin n → ℝ)
    (p : ShearPoint n) : ShearPoint n := realize μ α (quantizedIndex μ α p)

def shearColor {n : ℕ} (L : ℕ) (hL : 0 < L) (k : ShearIndex n) :
    Fin L × (Fin n → Fin L) :=
  (residue L hL k.1, fun i => residue L hL (k.2 i))

lemma floor_movement (μ y s : ℝ) (hμ : 0 < μ) :
    0 ≤ y - (μ * (⌊(y - s) / μ⌋ : ℝ) + s) ∧
      y - (μ * (⌊(y - s) / μ⌋ : ℝ) + s) < μ := by
  have hlo := (le_div_iff₀ hμ).mp (Int.floor_le ((y - s) / μ))
  have hhi := (div_lt_iff₀ hμ).mp (Int.lt_floor_add_one ((y - s) / μ))
  constructor <;> nlinarith

/-- Each PHYSICAL coordinate moves by less than μ. Rounding the normal
coordinate after the longitudinal coordinate removes any slope-dependent
movement loss; no bound on α is needed. -/
theorem quantization_coordinate_movement {n : ℕ} (μ : ℝ) (hμ : 0 < μ)
    (α : Fin n → ℝ) (p : ShearPoint n) :
    (0 ≤ p.1 - (quantize μ α p).1 ∧ p.1 - (quantize μ α p).1 < μ) ∧
      ∀ i, 0 ≤ p.2 i - (quantize μ α p).2 i ∧
        p.2 i - (quantize μ α p).2 i < μ := by
  constructor
  · simpa [quantize, realize, quantizedIndex] using floor_movement μ p.1 0 hμ
  · intro i
    exact floor_movement μ (p.2 i) (α i * (μ * (⌊p.1 / μ⌋ : ℝ))) hμ

theorem quantization_dist_lt {n : ℕ} (μ : ℝ) (hμ : 0 < μ)
    (α : Fin n → ℝ) (p : ShearPoint n) : dist p (quantize μ α p) < μ := by
  obtain ⟨hx, hy⟩ := quantization_coordinate_movement μ hμ α p
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · rw [Real.dist_eq, abs_of_nonneg hx.1]
    exact hx.2
  · apply (dist_pi_lt_iff hμ).mpr
    intro i
    rw [Real.dist_eq, abs_of_nonneg (hy i).1]
    exact (hy i).2

/-- Same-residue distinct shear-grid indices give separated actual points.
If longitudinal indices differ, that physical coordinate already separates;
otherwise the shear cancels in every normal-coordinate difference. -/
theorem shear_residue_separation {n : ℕ} (μ : ℝ) (hμ : 0 < μ)
    (α : Fin n → ℝ) (L : ℕ) (hL : 0 < L) (k l : ShearIndex n)
    (hc : shearColor L hL k = shearColor L hL l) (hne : k ≠ l) :
    μ * (L : ℝ) ≤ dist (realize μ α k) (realize μ α l) := by
  by_cases hx : k.1 = l.1
  · have hy : k.2 ≠ l.2 := by
      intro h
      exact hne (Prod.ext hx h)
    obtain ⟨i, hi⟩ : ∃ i, k.2 i ≠ l.2 i := by
      by_contra h
      push Not at h
      exact hy (funext h)
    have hci := congrFun (congrArg Prod.snd hc) i
    have hsep := real_residue_spacing hL (residue_eq_emod (hL := hL) hci) hi
    have heq : dist ((realize μ α k).2 i) ((realize μ α l).2 i) =
        μ * |(k.2 i : ℝ) - (l.2 i : ℝ)| := by
      simp only [realize, Real.dist_eq, hx]
      rw [show μ * (k.2 i : ℝ) + α i * (μ * (l.1 : ℝ)) -
          (μ * (l.2 i : ℝ) + α i * (μ * (l.1 : ℝ))) =
          μ * ((k.2 i : ℝ) - (l.2 i : ℝ)) by ring,
        abs_mul, abs_of_pos hμ]
    calc
      μ * (L : ℝ) ≤ μ * |(k.2 i : ℝ) - (l.2 i : ℝ)| := mul_le_mul_of_nonneg_left hsep hμ.le
      _ = dist ((realize μ α k).2 i) ((realize μ α l).2 i) := heq.symm
      _ ≤ dist (realize μ α k).2 (realize μ α l).2 := dist_le_pi_dist _ _ i
      _ ≤ dist (realize μ α k) (realize μ α l) := by rw [Prod.dist_eq]; exact le_max_right _ _
  · have hcx := congrArg Prod.fst hc
    have hsep := real_residue_spacing hL (residue_eq_emod (hL := hL) hcx) hx
    have heq : dist (realize μ α k).1 (realize μ α l).1 =
        μ * |(k.1 : ℝ) - (l.1 : ℝ)| := by
      simp only [realize, Real.dist_eq]
      rw [← mul_sub, abs_mul, abs_of_pos hμ]
    calc
      μ * (L : ℝ) ≤ μ * |(k.1 : ℝ) - (l.1 : ℝ)| := mul_le_mul_of_nonneg_left hsep hμ.le
      _ = dist (realize μ α k).1 (realize μ α l).1 := heq.symm
      _ ≤ dist (realize μ α k) (realize μ α l) := by rw [Prod.dist_eq]; exact le_max_left _ _

/-- Actual maximum-weight residue selection with original-label retention,
separated quantized image, and BOTH near-image directions. -/
theorem weighted_quantized_residue {β : Type*} {n : ℕ}
    (A : Finset β) (w : β → ℕ) (p : β → ShearPoint n)
    (μ : ℝ) (hμ : 0 < μ) (α : Fin n → ℝ) (L : ℕ) (hL : 0 < L) :
    ∃ B : Finset β, B ⊆ A ∧
      (∑ x ∈ A, w x) ≤ L ^ (n + 1) * (∑ x ∈ B, w x) ∧
      (∀ x ∈ B, ∃ z ∈ B.image (fun x => quantize μ α (p x)), dist (p x) z < μ) ∧
      (∀ z ∈ B.image (fun x => quantize μ α (p x)), ∃ x ∈ B, dist (p x) z < μ) ∧
      ∀ z ∈ B.image (fun x => quantize μ α (p x)),
        ∀ z' ∈ B.image (fun x => quantize μ α (p x)), z ≠ z' →
          μ * (L : ℝ) ≤ dist z z' := by
  classical
  let : Nonempty (Fin L × (Fin n → Fin L)) := ⟨(⟨0, hL⟩, fun _ => ⟨0, hL⟩)⟩
  let f := fun x => shearColor L hL (quantizedIndex μ α (p x))
  obtain ⟨c, hc⟩ := maximum_weight_color A w f
  let B := A.filter (fun x => f x = c)
  refine ⟨B, Finset.filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · simpa [Fintype.card_fun, Fintype.card_prod, pow_succ, mul_comm, B] using hc
  · intro x hx
    exact ⟨quantize μ α (p x), Finset.mem_image_of_mem _ hx, quantization_dist_lt μ hμ α (p x)⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨x, hx, quantization_dist_lt μ hμ α (p x)⟩
  · intro z hz z' hz' hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz'
    have hcol : shearColor L hL (quantizedIndex μ α (p x)) =
        shearColor L hL (quantizedIndex μ α (p y)) :=
      (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    have hind : quantizedIndex μ α (p x) ≠ quantizedIndex μ α (p y) := by
      intro he
      exact hne (congrArg (realize μ α) he)
    exact shear_residue_separation μ hμ α L hL _ _ hcol hind

/-- The literal output-mesh specialization: image separation is at least a,
while both near-image errors are strictly below a/10 in the sup metric. -/
theorem weighted_quantization_at_mesh {β : Type*} {n : ℕ}
    (A : Finset β) (w : β → ℕ) (p : β → ShearPoint n)
    (a : ℝ) (ha : 0 < a) (α : Fin n → ℝ) (c : ℕ) (hc : 10 ≤ c) :
    ∃ B : Finset β, B ⊆ A ∧
      (∑ x ∈ A, w x) ≤ c ^ (n + 1) * (∑ x ∈ B, w x) ∧
      (∀ x ∈ B, ∃ z ∈ B.image (fun x => quantize (a / c) α (p x)),
        dist (p x) z < a / 10) ∧
      (∀ z ∈ B.image (fun x => quantize (a / c) α (p x)), ∃ x ∈ B,
        dist (p x) z < a / 10) ∧
      ∀ z ∈ B.image (fun x => quantize (a / c) α (p x)),
        ∀ z' ∈ B.image (fun x => quantize (a / c) α (p x)), z ≠ z' →
          a ≤ dist z z' := by
  have hcpos : 0 < c := by omega
  have hcpos' : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hμ : 0 < a / (c : ℝ) := div_pos ha hcpos'
  have hμle : a / (c : ℝ) ≤ a / 10 := by
    apply (div_le_div_iff₀ hcpos' (by norm_num : (0 : ℝ) < 10)).mpr
    have hc' : (10 : ℝ) ≤ c := by exact_mod_cast hc
    nlinarith
  obtain ⟨B, hBA, hmass, hforward, hback, hsep⟩ :=
    weighted_quantized_residue A w p (a / c) hμ α c hcpos
  refine ⟨B, hBA, hmass, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, hz, hdist⟩ := hforward x hx
    exact ⟨z, hz, hdist.trans_le hμle⟩
  · intro z hz
    obtain ⟨x, hx, hdist⟩ := hback z hz
    exact ⟨x, hx, hdist.trans_le hμle⟩
  · intro z hz z' hz' hne
    simpa only [div_mul_cancel₀ a hcpos'.ne'] using hsep z hz z' hz' hne

end SeparatedAlignmentPatches
