import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option warningAsError true

namespace GridQuotientAD

noncomputable section

abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev Point (k l : ℕ) := Lattice k × Lattice l

def box {d : ℕ} (a : Lattice d) (R : ℕ) : Finset (Lattice d) :=
  Fintype.piFinset fun i => Finset.Icc (a i - R) (a i + R)

theorem mem_box_iff {d : ℕ} (a x : Lattice d) (R : ℕ) :
    x ∈ box a R ↔ ∀ i, |x i - a i| ≤ (R : ℤ) := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  constructor <;> intro h i <;> have := h i <;> omega

theorem box_card {d : ℕ} (a : Lattice d) (R : ℕ) :
    (box a R).card = (2 * R + 1) ^ d := by
  simp only [box, Fintype.card_piFinset]
  have hc (i : Fin d) : (Finset.Icc (a i - R) (a i + R)).card = 2 * R + 1 := by
    rw [Int.card_Icc]
    omega
  simp [hc]

def ambientBox {k l : ℕ} (A : Finset (Point k l)) (a : Point k l) (R : ℕ) :=
  A.filter fun p => p.1 ∈ box a.1 R ∧ p.2 ∈ box a.2 R

def quotientBox {k l : ℕ} (A : Finset (Point k l)) (y : Lattice l) (R : ℕ) :=
  (A.image Prod.snd).filter fun z => z ∈ box y R

def slab {k l : ℕ} (A : Finset (Point k l)) (y : Lattice l) (R : ℕ) :=
  A.filter fun p => p.2 ∈ box y R

def fiber {k l : ℕ} (A : Finset (Point k l)) (y : Lattice l) :=
  A.filter fun p => p.2 = y

theorem ambientBox_card_le_fiber_capacity {k l : ℕ}
    (A : Finset (Point k l)) (a : Point k l) (R : ℕ) :
    (ambientBox A a R).card ≤ (2 * R + 1) ^ k * (quotientBox A a.2 R).card := by
  apply Finset.card_le_mul_card_image_of_maps_to (f := Prod.snd)
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpA, hpx, hpy⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p, hpA, rfl⟩, hpy⟩
  · intro y _hy
    rw [← box_card a.1 R]
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
    · intro p hp q hq hpq
      have hp' := (Finset.mem_filter.mp hp).2
      have hq' := (Finset.mem_filter.mp hq).2
      exact Prod.ext hpq (hp'.trans hq'.symm)

theorem slab_card_eq_sum_fibers {k l : ℕ}
    (A : Finset (Point k l)) (y : Lattice l) (R : ℕ) :
    (slab A y R).card = ∑ z ∈ quotientBox A y R, (fiber A z).card := by
  have hmap : ∀ p ∈ slab A y R, p.2 ∈ quotientBox A y R := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpA, hpy⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p, hpA, rfl⟩, hpy⟩
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  ext p
  have hzbox := (Finset.mem_filter.mp hz).2
  simp only [slab, fiber, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hp, _hbox⟩, heq⟩
    exact ⟨hp, heq⟩
  · rintro ⟨hp, heq⟩
    exact ⟨⟨hp, heq.symm ▸ hzbox⟩, heq⟩

theorem dense_fibers_le_slab {k l : ℕ}
    (A : Finset (Point k l)) (y : Lattice l) (R : ℕ) (L : ℝ)
    (hdense : ∀ z ∈ A.image Prod.snd, L ≤ ((fiber A z).card : ℝ)) :
    L * ((quotientBox A y R).card : ℝ) ≤ ((slab A y R).card : ℝ) := by
  rw [slab_card_eq_sum_fibers, Nat.cast_sum]
  calc
    L * ((quotientBox A y R).card : ℝ) = ∑ _z ∈ quotientBox A y R, L := by
      simp [mul_comm]
    _ ≤ ∑ z ∈ quotientBox A y R, ((fiber A z).card : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      exact hdense z (Finset.mem_filter.mp hz).1

def cellKey {k : ℕ} (N R : ℕ) (x : Lattice k) : Lattice k :=
  fun i => (x i + N) / (R : ℤ)

def cellKeys (k N R : ℕ) : Finset (Lattice k) :=
  Fintype.piFinset fun _ => Finset.Icc 0 ((2 * N / R : ℕ) : ℤ)

theorem cellKeys_card (k N R : ℕ) :
    (cellKeys k N R).card = (2 * N / R + 1) ^ k := by
  have hc : (Finset.Icc (0 : ℤ) ((2 * N / R : ℕ) : ℤ)).card = 2 * N / R + 1 := by
    have hq : (0 : ℤ) ≤ ((2 * N / R : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [Int.card_Icc]
    omega
  simp only [cellKeys, Fintype.card_piFinset, hc, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem cellKey_mem {k : ℕ} (N R : ℕ) (x : Lattice k)
    (hR : 1 ≤ R) (hx : ∀ i, |x i| ≤ (N : ℤ)) :
    cellKey N R x ∈ cellKeys k N R := by
  apply Fintype.mem_piFinset.mpr
  intro i
  rcases abs_le.mp (hx i) with ⟨hl, hu⟩
  apply Finset.mem_Icc.mpr
  constructor
  · exact Int.ediv_nonneg (by omega) (by omega)
  · change (x i + (N : ℤ)) / (R : ℤ) ≤ ((2 * N / R : ℕ) : ℤ)
    change (x i + (N : ℤ)) / (R : ℤ) ≤ ((2 * N : ℕ) : ℤ) / (R : ℤ)
    apply Int.ediv_le_ediv (by omega : (0 : ℤ) < R)
    push_cast
    omega

theorem same_cell_close {k : ℕ} (N R : ℕ) (x z : Lattice k)
    (hR : 1 ≤ R) (hcell : cellKey N R x = cellKey N R z) :
    x ∈ box z R := by
  apply (mem_box_iff z x R).mpr
  intro i
  have heq : (x i + (N : ℤ)) / (R : ℤ) = (z i + (N : ℤ)) / (R : ℤ) :=
    congrFun hcell i
  have hRp : (0 : ℤ) < R := by omega
  have hx0 := Int.emod_nonneg (x i + (N : ℤ)) hRp.ne'
  have hz0 := Int.emod_nonneg (z i + (N : ℤ)) hRp.ne'
  have hx1 := Int.emod_lt_of_pos (x i + (N : ℤ)) hRp
  have hz1 := Int.emod_lt_of_pos (z i + (N : ℤ)) hRp
  have hxE := Int.mul_ediv_add_emod (x i + (N : ℤ)) (R : ℤ)
  have hzE := Int.mul_ediv_add_emod (z i + (N : ℤ)) (R : ℤ)
  rw [heq] at hxE
  apply abs_le.mpr
  constructor <;> omega

theorem box_same_center_pair {d : ℕ} (y x z : Lattice d) (R : ℕ)
    (hx : x ∈ box y R) (hz : z ∈ box y R) : x ∈ box z (2 * R) := by
  rw [mem_box_iff] at hx hz ⊢
  intro i
  rcases abs_le.mp (hx i) with ⟨hx0, hx1⟩
  rcases abs_le.mp (hz i) with ⟨hz0, hz1⟩
  apply abs_le.mpr
  push_cast
  constructor <;> omega

theorem box_mono {d : ℕ} (a : Lattice d) {R S : ℕ} (hRS : R ≤ S) :
    box a R ⊆ box a S := by
  intro x hx
  rw [mem_box_iff] at hx ⊢
  intro i
  exact (hx i).trans (by exact_mod_cast hRS)

theorem slab_card_le_cells_mul {k l : ℕ}
    (A : Finset (Point k l)) (y : Lattice l) (N R : ℕ) (U : ℝ)
    (hR : 1 ≤ R) (hU : 0 ≤ U)
    (hbounded : ∀ p ∈ A, ∀ i, |p.1 i| ≤ (N : ℤ))
    (hupper : ∀ a ∈ A, ((ambientBox A a (2 * R)).card : ℝ) ≤ U) :
    ((slab A y R).card : ℝ) ≤ ((2 * N / R + 1 : ℕ) : ℝ) ^ k * U := by
  have hmap : ∀ p ∈ slab A y R, cellKey N R p.1 ∈ cellKeys k N R := by
    intro p hp
    exact cellKey_mem N R p.1 hR (hbounded p (Finset.mem_filter.mp hp).1)
  have hcellbound (v : Lattice k) :
      (((slab A y R).filter fun p => cellKey N R p.1 = v).card : ℝ) ≤ U := by
    let S := (slab A y R).filter fun p => cellKey N R p.1 = v
    change (S.card : ℝ) ≤ U
    by_cases hS : S.Nonempty
    · obtain ⟨a, ha⟩ := hS
      rcases Finset.mem_filter.mp ha with ⟨haB, haC⟩
      rcases Finset.mem_filter.mp haB with ⟨haA, hay⟩
      have hsub : S ⊆ ambientBox A a (2 * R) := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpB, hpC⟩
        rcases Finset.mem_filter.mp hpB with ⟨hpA, hpy⟩
        apply Finset.mem_filter.mpr
        refine ⟨hpA, ?_, box_same_center_pair y p.2 a.2 R hpy hay⟩
        exact box_mono a.1 (by omega : R ≤ 2 * R)
          (same_cell_close N R p.1 a.1 hR (hpC.trans haC.symm))
      have hc : (S.card : ℝ) ≤ ((ambientBox A a (2 * R)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact hc.trans (hupper a haA)
    · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      simpa [this] using hU
  rw [Finset.card_eq_sum_card_fiberwise hmap, Nat.cast_sum]
  calc
    _ ≤ ∑ _v ∈ cellKeys k N R, U := by
      apply Finset.sum_le_sum
      intro v _hv
      exact hcellbound v
    _ = ((2 * N / R + 1 : ℕ) : ℝ) ^ k * U := by simp [cellKeys_card]

theorem cell_count_scaled_le (k N R : ℕ) (hR : 1 ≤ R) (hRN : R ≤ N) :
    ((2 * N / R + 1 : ℕ) : ℝ) ^ k * (R : ℝ) ^ k ≤ (3 : ℝ) ^ k * (N : ℝ) ^ k := by
  have hnat : (2 * N / R + 1) * R ≤ 3 * N := by
    have := Nat.div_mul_le_self (2 * N) R
    nlinarith
  have hreal : ((2 * N / R + 1 : ℕ) : ℝ) * (R : ℝ) ≤ 3 * (N : ℝ) := by
    exact_mod_cast hnat
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hreal k

theorem quotient_lower {k l : ℕ}
    (A : Finset (Point k l)) (a : Point k l) (R : ℕ) (c t : ℝ)
    (hR : 1 ≤ R)
    (hlower : c * (R : ℝ) ^ t ≤ ((ambientBox A a R).card : ℝ)) :
    (c / (3 : ℝ) ^ k) * (R : ℝ) ^ (t - k) ≤
      ((quotientBox A a.2 R).card : ℝ) := by
  have hRp : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hcap : ((ambientBox A a R).card : ℝ) ≤
      ((2 * R + 1 : ℕ) : ℝ) ^ k * ((quotientBox A a.2 R).card : ℝ) := by
    exact_mod_cast ambientBox_card_le_fiber_capacity A a R
  have hcoef : ((2 * R + 1 : ℕ) : ℝ) ^ k ≤ (3 : ℝ) ^ k * (R : ℝ) ^ k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hmain := hlower.trans (hcap.trans
    (mul_le_mul_of_nonneg_right hcoef (by positivity)))
  rw [Real.rpow_sub_natCast hRp.ne']
  calc
    c / (3 : ℝ) ^ k * ((R : ℝ) ^ t / (R : ℝ) ^ k) =
        (c * (R : ℝ) ^ t) / ((3 : ℝ) ^ k * (R : ℝ) ^ k) := by ring
    _ ≤ ((quotientBox A a.2 R).card : ℝ) :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hmain])

theorem quotient_upper {k l : ℕ}
    (A : Finset (Point k l)) (y : Lattice l) (N R : ℕ) (lam K t : ℝ)
    (hR : 1 ≤ R) (hRN : R ≤ N) (hlam : 0 < lam) (hK : 0 ≤ K)
    (hbounded : ∀ p ∈ A, ∀ i, |p.1 i| ≤ (N : ℤ))
    (hdense : ∀ z ∈ A.image Prod.snd,
      lam * (N : ℝ) ^ k ≤ ((fiber A z).card : ℝ))
    (hupper : ∀ a ∈ A,
      ((ambientBox A a (2 * R)).card : ℝ) ≤ K * ((2 * R : ℕ) : ℝ) ^ t) :
    ((quotientBox A y R).card : ℝ) ≤
      ((3 : ℝ) ^ k * (2 : ℝ) ^ t * K / lam) * (R : ℝ) ^ (t - k) := by
  have hRp : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hU : 0 ≤ K * ((2 * R : ℕ) : ℝ) ^ t := by positivity
  have htotal := (dense_fibers_le_slab A y R (lam * (N : ℝ) ^ k) hdense).trans
    (slab_card_le_cells_mul A y N R (K * ((2 * R : ℕ) : ℝ) ^ t)
      hR hU hbounded hupper)
  have hscaled :
      (lam * (N : ℝ) ^ k * ((quotientBox A y R).card : ℝ)) * (R : ℝ) ^ k ≤
        ((3 : ℝ) ^ k * (N : ℝ) ^ k) * (K * ((2 * R : ℕ) : ℝ) ^ t) := by
    calc
      _ ≤ (((2 * N / R + 1 : ℕ) : ℝ) ^ k *
          (K * ((2 * R : ℕ) : ℝ) ^ t)) * (R : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right htotal (by positivity)
      _ = (((2 * N / R + 1 : ℕ) : ℝ) ^ k * (R : ℝ) ^ k) *
          (K * ((2 * R : ℕ) : ℝ) ^ t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (cell_count_scaled_le k N R hR hRN) hU
  have hcancel : lam * ((quotientBox A y R).card : ℝ) * (R : ℝ) ^ k ≤
      (3 : ℝ) ^ k * (K * ((2 * R : ℕ) : ℝ) ^ t) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hNp k)).mp
    nlinarith only [hscaled]
  have hpow : ((2 * R : ℕ) : ℝ) ^ t = (2 : ℝ) ^ t * (R : ℝ) ^ t := by
    push_cast
    exact Real.mul_rpow (by norm_num) hRp.le
  rw [hpow] at hcancel
  rw [Real.rpow_sub_natCast hRp.ne']
  calc
    ((quotientBox A y R).card : ℝ) ≤
        ((3 : ℝ) ^ k * (2 : ℝ) ^ t * K * (R : ℝ) ^ t) /
          (lam * (R : ℝ) ^ k) := by
      apply (le_div_iff₀ (mul_pos hlam (pow_pos hRp k))).mpr
      nlinarith only [hcancel]
    _ = ((3 : ℝ) ^ k * (2 : ℝ) ^ t * K / lam) *
        ((R : ℝ) ^ t / (R : ℝ) ^ k) := by ring

/-- Dense bounded lattice fibers lower the ambient AD exponent by their dimension.
The upper hypothesis reaches integer radius `2N`, because an occupied cell over a
quotient `R`-box is recentered at an actual point and fits in radius `2R`.
No quotient count or covering-number certificate is assumed. -/
theorem quotient_AD {k l : ℕ}
    (A : Finset (Point k l)) (N : ℕ) (lam c K t : ℝ)
    (hlam : 0 < lam) (hK : 0 ≤ K) (hkt : (k : ℝ) ≤ t)
    (htdim : t ≤ ((k + l : ℕ) : ℝ))
    (hbounded : ∀ p ∈ A, ∀ i, |p.1 i| ≤ (N : ℤ))
    (hdense : ∀ z ∈ A.image Prod.snd,
      lam * (N : ℝ) ^ k ≤ ((fiber A z).card : ℝ))
    (hlower : ∀ a ∈ A, ∀ R : ℕ, 1 ≤ R → R ≤ N →
      c * (R : ℝ) ^ t ≤ ((ambientBox A a R).card : ℝ))
    (hupper : ∀ a ∈ A, ∀ S : ℕ, 1 ≤ S → S ≤ 2 * N →
      ((ambientBox A a S).card : ℝ) ≤ K * (S : ℝ) ^ t) :
    0 ≤ t - k ∧ ∀ y ∈ A.image Prod.snd, ∀ R : ℕ, 1 ≤ R → R ≤ N →
      (c / (3 : ℝ) ^ k) * (R : ℝ) ^ (t - k) ≤ ((quotientBox A y R).card : ℝ) ∧
      ((quotientBox A y R).card : ℝ) ≤
        ((3 : ℝ) ^ k * (2 : ℝ) ^ (k + l) * K / lam) * (R : ℝ) ^ (t - k) := by
  refine ⟨sub_nonneg.mpr hkt, ?_⟩
  intro y hy R hR hRN
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
  constructor
  · exact quotient_lower A a R c t hR (hlower a ha R hR hRN)
  · have h2 : (2 : ℝ) ^ t ≤ (2 : ℝ) ^ (k + l) := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) htdim
    have hcoeff := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 3 ^ k)) hK) hlam.le
    exact (quotient_upper A a.2 N R lam K t hR hRN hlam hK hbounded hdense
      (fun a ha => hupper a ha (2 * R) (by omega) (by omega))).trans
        (mul_le_mul_of_nonneg_right hcoeff (by positivity))

end
end GridQuotientAD
