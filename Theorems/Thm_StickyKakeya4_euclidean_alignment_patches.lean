import Theorems.Thm_StickyKakeya4_separated_alignment_patches
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace EuclideanAlignmentPatches
open scoped BigOperators
open SeparatedAlignmentPatches

noncomputable def euclidean {d : ℕ} (p : Point d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 p

lemma coordinate_dist_le {d : ℕ} (p q : Point d) (i : Fin d) :
    |p i - q i| ≤ dist (euclidean p) (euclidean q) := by
  simpa only [euclidean, Real.dist_eq] using PiLp.dist_apply_le (euclidean p) (euclidean q) i

lemma sup_dist_le {d : ℕ} (p q : Point d) :
    dist p q ≤ dist (euclidean p) (euclidean q) := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  simpa only [Real.dist_eq] using coordinate_dist_le p q i

/-- An explicit dimension-only conversion, including dimension zero. -/
theorem euclidean_dist_le_card_mul {d : ℕ} (p q : Point d) (M : ℝ) (hM : 0 ≤ M)
    (hcoord : ∀ i, |p i - q i| ≤ M) :
    dist (euclidean p) (euclidean q) ≤ (d : ℝ) * M := by
  by_cases hd : d = 0
  · subst d
    have hpq : p = q := by funext i; exact Fin.elim0 i
    subst q
    simp
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have hs : dist (euclidean p) (euclidean q) ^ 2 ≤ (d : ℝ) * M ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq]
      calc
        (∑ i : Fin d, dist ((euclidean p) i) ((euclidean q) i) ^ 2) ≤ ∑ _i : Fin d, M ^ 2 := by
          apply Finset.sum_le_sum
          intro i _hi
          have hi : dist ((euclidean p) i) ((euclidean q) i) ≤ M := by
            simpa only [euclidean, Real.dist_eq] using hcoord i
          exact pow_le_pow_left₀ dist_nonneg hi 2
        _ = (d : ℝ) * M ^ 2 := by simp
    have hdd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have hddM := mul_le_mul_of_nonneg_right hdd (sq_nonneg M)
    have hnonneg : 0 ≤ (d : ℝ) * M := mul_nonneg (Nat.cast_nonneg d) hM
    have hdist : 0 ≤ dist (euclidean p) (euclidean q) := dist_nonneg
    nlinarith

lemma same_cell_euclidean_dist_le {d : ℕ} (b : ℝ) (hb : 0 < b) (p q : Point d)
    (hcell : cell b p = cell b q) :
    dist (euclidean p) (euclidean q) ≤ (d : ℝ) * b := by
  apply euclidean_dist_le_card_mul p q b hb.le
  intro i
  have hnear := same_cell_dist_lt b hb p q hcell
  have hi := (dist_le_pi_dist p q i).trans_lt hnear
  simpa only [Real.dist_eq] using hi.le

/-- The exact periodic-patch identity in the EUCLIDEAN open ball. The same
original labels are selected by their actual parent-cell residues. -/
theorem euclidean_periodic_patch_isolation {α : Type*} {d : ℕ}
    (A : Finset α) (w : α → ℕ) (p : α → Point d)
    (b R : ℝ) (hb : 0 < b) (hsmall : ((d : ℝ) + 1) * b ≤ R)
    (L : ℕ) (hL : 0 < L) (hgap : R ≤ ((L : ℝ) - 1) * b) :
    ∃ B : Finset α, B ⊆ A ∧
      (∑ x ∈ A, w x) ≤ L ^ d * (∑ x ∈ B, w x) ∧
      ∀ a ∈ B,
        B.filter (fun x => dist (euclidean (p x)) (euclidean (p a)) < R) =
          A.filter (fun x => cell b (p x) = cell b (p a)) := by
  classical
  have hsmall' : b ≤ R := by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  obtain ⟨B, hBA, hmass, hid⟩ := periodic_patch_isolation A w p b R hb hsmall' L hL hgap
  refine ⟨B, hBA, hmass, ?_⟩
  intro a ha
  ext x
  constructor
  · intro hx
    obtain ⟨hxB, hclose⟩ := Finset.mem_filter.mp hx
    have hsup : dist (p x) (p a) < R := (sup_dist_le (p x) (p a)).trans_lt hclose
    rw [← hid a ha]
    exact Finset.mem_filter.mpr ⟨hxB, hsup⟩
  · intro hx
    have hcell := (Finset.mem_filter.mp hx).2
    have hsupmem : x ∈ B.filter (fun x => dist (p x) (p a) < R) := by
      rw [hid a ha]
      exact hx
    have hnear := same_cell_euclidean_dist_le b hb (p x) (p a) hcell
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hsupmem).1, by nlinarith⟩

/-- Fixed constants for the literal Euclidean patch caller. For d>=1,
C=10*d satisfies the displayed arithmetic hypothesis. -/
theorem euclidean_periodic_patch_at_multiplier {α : Type*} {d : ℕ}
    (A : Finset α) (w : α → ℕ) (p : α → Point d)
    (b : ℝ) (hb : 0 < b) (C : ℕ) (hC : d + 1 ≤ C) :
    ∃ B : Finset α, B ⊆ A ∧
      (∑ x ∈ A, w x) ≤ (4 * C + 4) ^ d * (∑ x ∈ B, w x) ∧
      ∀ a ∈ B,
        B.filter (fun x => dist (euclidean (p x)) (euclidean (p a)) < (C : ℝ) * b) =
          A.filter (fun x => cell b (p x) = cell b (p a)) := by
  apply euclidean_periodic_patch_isolation A w p b ((C : ℝ) * b) hb
  · have hc : (d : ℝ) + 1 ≤ C := by exact_mod_cast hC
    nlinarith
  · omega
  · push_cast
    have hc : (0 : ℝ) ≤ C := by positivity
    nlinarith

noncomputable def shearEuclidean {n : ℕ} (p : ShearPoint n) : EuclideanSpace ℝ (Fin (n + 1)) :=
  euclidean (Fin.cons p.1 p.2)

lemma shear_sup_dist_le {n : ℕ} (p q : ShearPoint n) :
    dist p q ≤ dist (shearEuclidean p) (shearEuclidean q) := by
  rw [Prod.dist_eq, max_le_iff]
  constructor
  · simpa only [shearEuclidean, Fin.cons_zero, Real.dist_eq] using
      coordinate_dist_le (Fin.cons p.1 p.2) (Fin.cons q.1 q.2) 0
  · apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    simpa only [shearEuclidean, Fin.cons_succ, Real.dist_eq] using
      coordinate_dist_le (Fin.cons p.1 p.2) (Fin.cons q.1 q.2) i.succ

/-- Euclidean movement follows from the actual coordinate rounding inequalities. -/
theorem quantization_euclidean_movement {n : ℕ} (μ : ℝ) (hμ : 0 < μ)
    (α : Fin n → ℝ) (p : ShearPoint n) :
    dist (shearEuclidean p) (shearEuclidean (quantize μ α p)) ≤ ((n : ℝ) + 1) * μ := by
  obtain ⟨hx, hy⟩ := quantization_coordinate_movement μ hμ α p
  have h := euclidean_dist_le_card_mul (Fin.cons p.1 p.2)
    (Fin.cons (quantize μ α p).1 (quantize μ α p).2) μ hμ.le
  apply (show dist (shearEuclidean p) (shearEuclidean (quantize μ α p)) ≤
      ((n + 1 : ℕ) : ℝ) * μ from h ?_).trans_eq (by push_cast; rfl)
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero, abs_of_nonneg hx.1] using hx.2.le
  · simpa only [Fin.cons_succ, abs_of_nonneg (hy j).1] using (hy j).2.le

/-- Euclidean residue selection with output separation a and BOTH Hausdorff
inclusions at error below a/10. The original label weights are unchanged. -/
theorem weighted_euclidean_quantization_at_mesh {β : Type*} {n : ℕ}
    (A : Finset β) (w : β → ℕ) (p : β → ShearPoint n)
    (a : ℝ) (ha : 0 < a) (α : Fin n → ℝ) (c : ℕ) (hc : 20 * (n + 1) ≤ c) :
    ∃ B : Finset β, B ⊆ A ∧
      (∑ x ∈ A, w x) ≤ c ^ (n + 1) * (∑ x ∈ B, w x) ∧
      (∀ x ∈ B, ∃ z ∈ B.image (fun x => shearEuclidean (quantize (a / c) α (p x))),
        dist (shearEuclidean (p x)) z < a / 10) ∧
      (∀ z ∈ B.image (fun x => shearEuclidean (quantize (a / c) α (p x))),
        ∃ x ∈ B, dist (shearEuclidean (p x)) z < a / 10) ∧
      ∀ z ∈ B.image (fun x => shearEuclidean (quantize (a / c) α (p x))),
        ∀ z' ∈ B.image (fun x => shearEuclidean (quantize (a / c) α (p x))), z ≠ z' →
          a ≤ dist z z' := by
  classical
  have hc10 : 10 ≤ c := by omega
  have hcpos : 0 < c := by omega
  have hcpos' : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hμ : 0 < a / (c : ℝ) := div_pos ha hcpos'
  have hmov : ∀ x, dist (shearEuclidean (p x))
      (shearEuclidean (quantize (a / c) α (p x))) < a / 10 := by
    intro x
    have hbound := quantization_euclidean_movement (a / c) hμ α (p x)
    have hc' : 20 * ((n : ℝ) + 1) ≤ c := by exact_mod_cast hc
    have hdim : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hμeq : a / (c : ℝ) * c = a := div_mul_cancel₀ _ hcpos'.ne'
    have hnonneg := mul_le_mul_of_nonneg_right hc' hμ.le
    have hlt : ((n : ℝ) + 1) * (a / c) < a / 10 := by nlinarith
    exact hbound.trans_lt hlt
  obtain ⟨B, hBA, hmass, _hf, _hb, hsep⟩ := weighted_quantization_at_mesh A w p a ha α c hc10
  refine ⟨B, hBA, hmass, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨_, Finset.mem_image_of_mem _ hx, hmov x⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨x, hx, hmov x⟩
  · intro z hz z' hz' hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz'
    have hne' : quantize (a / c) α (p x) ≠ quantize (a / c) α (p y) := by
      intro he
      exact hne (congrArg shearEuclidean he)
    have hs := hsep _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy) hne'
    exact hs.trans (shear_sup_dist_le _ _)

end EuclideanAlignmentPatches
