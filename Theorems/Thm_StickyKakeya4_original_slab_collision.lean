import Theorems.Thm_StickyKakeya4_original_polynomial_slab
import Theorems.Thm_StickyKakeya4_original_slab_overlap
import Theorems.Thm_StickyKakeya4_original_slab_relation
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalSlabCollision
open ActualRoundedAdditiveEnergy OriginalPolynomialSlab OriginalSlabOverlap
open OriginalSlabRelation NativeTangentGridCoarsening

lemma original_box_projection {n : ℕ} (v x : Fin (n+1) → ℝ) {lo d : ℝ}
    (hv : ∀ i, (1/2:ℝ) ≤ v i ∧ v i ≤ 1) (hd : 0 ≤ d)
    (hx : ∀ i, lo ≤ x i ∧ x i ≤ lo+d) :
    lo*(∑ i, v i) ≤ ∑ i, v i*x i ∧
      (∑ i, v i*x i) ≤ lo*(∑ i, v i)+((n:ℝ)+1)*d := by
  have hlo : (∑ i, v i*lo) ≤ ∑ i, v i*x i :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i).1
      ((by norm_num : (0:ℝ) ≤ 1/2).trans (hv i).1))
  have hhi : (∑ i, v i*x i) ≤ ∑ i, v i*(lo+d) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i).2
      ((by norm_num : (0:ℝ) ≤ 1/2).trans (hv i).1))
  have hvsum : (∑ i, v i) ≤ (n:ℝ)+1 := by
    calc
      _ ≤ ∑ _i : Fin (n+1), (1:ℝ) := Finset.sum_le_sum (fun i _ => (hv i).2)
      _ = _ := by simp
  rw [← Finset.sum_mul] at hlo hhi
  have hm := mul_le_mul_of_nonneg_right hvsum hd
  constructor <;> nlinarith only [hlo,hhi,hm]

def slabRadius (n : ℕ) (d L : ℝ) : ℕ :=
  ⌈(4*((n:ℝ)+3)*d+4)/L⌉₊

lemma slabRadius_bounds {n : ℕ} {d L : ℝ}
    (hn : 1 ≤ n) (hd : 0 ≤ d) (hL : 0 < L) :
    4*((n:ℝ)+3)*d+4 < ((slabRadius n d L:ℝ)+1)^n*L ∧
      (slabRadius n d L:ℝ) < (4*((n:ℝ)+3)*d+4)/L+1 := by
  let C : ℝ := 4*((n:ℝ)+3)*d+4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hr := Nat.le_ceil (C/L)
  have hr' := Nat.ceil_lt_add_one (div_nonneg hC hL.le)
  have hbase : (1:ℝ) ≤ (slabRadius n d L:ℝ)+1 :=
    le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hpow : (slabRadius n d L:ℝ)+1 ≤ ((slabRadius n d L:ℝ)+1)^n := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase hn
  have hsmall : C/L < (slabRadius n d L:ℝ)+1 := by
    change C/L ≤ (slabRadius n d L:ℝ) at hr
    linarith only [hr]
  have hprod := (div_lt_iff₀ hL).mp hsmall
  refine ⟨?_,hr'⟩
  exact hprod.trans_le (mul_le_mul_of_nonneg_right hpow hL.le)

/-- Enough explicit lattice copies of an actual large projected image force
a collision between two different original copies. The copy count is a
numerical parameter choice; its image upper bound is proved from the box. -/
theorem exists_original_slab_collision (n : ℕ)
    (P : Finset (Fin (n+1) → ℝ)) (v : Fin (n+1) → ℝ)
    {delta lo d L : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hd : 0 < d) (hL : 0 < L) (hn : 1 ≤ n)
    (hv : ∀ i, (1/2:ℝ) ≤ v i ∧ v i ≤ 1)
    (hbox : ∀ x∈P, ∀ i, lo ≤ x i ∧ x i ≤ lo+d)
    (himage : L ≤ delta*((P.image (fun x => rounded delta (∑ i, v i*x i))).card:ℝ)) :
    ∃ tau∈slabVectors n (slabRadius n d L) v,
      ∃ sigma∈slabVectors n (slabRadius n d L) v, tau≠sigma ∧
      ∃ x∈P, ∃ y∈P,
        rounded delta (∑ i, v i*shiftPoint d tau x i)=
          rounded delta (∑ i, v i*shiftPoint d sigma y i) := by
  let R := slabRadius n d L
  have hcopies := (slabRadius_bounds hn hd.le hL).1
  change 4*((n:ℝ)+3)*d+4 < ((R:ℝ)+1)^n*L at hcopies
  let I := P.image (fun x => rounded delta (∑ i, v i*x i))
  let T := slabVectors n R v
  have hw : ∀ j∈I, ∃ x∈P, rounded delta (∑ i, v i*x i)=j :=
    fun j hj => Finset.mem_image.mp hj
  let rep : ℤ → Fin (n+1) → ℝ := fun j =>
    if hj : j∈I then Classical.choose (hw j hj) else 0
  have hrep (j : ℤ) (hj : j∈I) : rep j∈P ∧ rounded delta (∑ i, v i*rep j i)=j := by
    dsimp [rep]
    rw [dif_pos hj]
    exact Classical.choose_spec (hw j hj)
  let value : ℤ → ℝ := fun j => (∑ i, v i*rep j i)/delta
  let shift : (Fin (n+1) → ℤ) → ℝ := fun tau => 2*d*(∑ i, v i*(tau i:ℝ))/delta
  let total : (Fin (n+1) → ℤ) × ℤ → ℝ :=
    fun p => (∑ i, v i*rep p.2 i)+2*d*(∑ i, v i*(p.1 i:ℝ))
  let f := fun p : (Fin (n+1) → ℤ) × ℤ => ⌊value p.2+shift p.1⌋
  have hvalue : ∀ j∈I, ⌊value j⌋=j := fun j hj => (hrep j hj).2
  have hcode (p : (Fin (n+1) → ℤ) × ℤ) : f p=rounded delta (total p) := by
    unfold f rounded
    congr 1
    dsimp [value,shift,total]
    ring
  have htotal (tau : Fin (n+1) → ℤ) (j : ℤ) :
      total (tau,j)=∑ i, v i*shiftPoint d tau (rep j) i := by
    dsimp [total,shiftPoint]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hnear : ∀ p∈T.product I,
      |total p-lo*(∑ i, v i)| ≤ (((n:ℝ)+3)*d/delta)*delta := by
    intro p hp
    obtain ⟨htau,hj⟩ := Finset.mem_product.mp hp
    obtain ⟨a,_ha,haeq⟩ := Finset.mem_image.mp htau
    have hv0 : 0 < v 0 := lt_of_lt_of_le (by norm_num) (hv 0).1
    have ht := slabVector_projection hv0 a
    have ht' : 0 ≤ (∑ i, v i*(p.1 i:ℝ)) ∧ (∑ i, v i*(p.1 i:ℝ)) ≤ 1 := by
      rw [← haeq]
      exact ⟨ht.1,ht.2.le.trans (hv 0).2⟩
    have hx := original_box_projection v (rep p.2) hv hd.le (hbox _ (hrep p.2 hj).1)
    have he : (((n:ℝ)+3)*d/delta)*delta=((n:ℝ)+3)*d := by field_simp
    rw [he]
    dsimp [total]
    apply abs_le.mpr
    constructor <;> nlinarith only [hx.1,hx.2,
      mul_nonneg hd.le ht'.1,mul_le_mul_of_nonneg_left ht'.2 hd.le]
  have hJ : (((T.product I).image f).card:ℝ) ≤ 2*(((n:ℝ)+3)*d/delta)+2 := by
    have him : (T.product I).image f=
        (T.product I).image (fun p => rounded delta (total p)) := by
      apply Finset.image_congr
      intro p _hp
      exact hcode p
    rw [him]
    exact scalar_centered_grid_card (T.product I) total hdelta (by positivity) hnear
  have hTcard : (T.card:ℝ)=((R:ℝ)+1)^n := by
    dsimp [T]
    rw [slabVectors_card]
    simp only [Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  have hmass : ((R:ℝ)+1)^n*L ≤ delta*((T.card:ℝ)*I.card) := by
    change L ≤ delta*(I.card:ℝ) at himage
    have hh := mul_le_mul_of_nonneg_left himage (show 0 ≤ ((R:ℝ)+1)^n by positivity)
    change ((R:ℝ)+1)^n*L ≤ delta*((T.card:ℝ)*I.card)
    rw [hTcard]
    change L ≤ delta*(I.card:ℝ) at himage
    nlinarith only [hh]
  have hlarge : 2*(((T.product I).image f).card:ℝ) < (T.card:ℝ)*I.card := by
    have hh := mul_le_mul_of_nonneg_left hJ hdelta.le
    have he : delta*(2*(((n:ℝ)+3)*d/delta)+2)=2*((n:ℝ)+3)*d+2*delta := by
      field_simp
    rw [he] at hh
    apply (mul_lt_mul_iff_right₀ hdelta).mp
    nlinarith only [hh,hmass,hcopies,hdelta1]
  obtain ⟨tau,htau,sigma,hsigma,hneq,i,hi,j,hj,hcell⟩ :=
    exists_original_translated_floor_collision T I shift value hvalue hlarge
  refine ⟨tau,htau,sigma,hsigma,hneq,rep i,(hrep i hi).1,rep j,(hrep j hj).1,?_⟩
  change f (tau,i)=f (sigma,j) at hcell
  rw [hcode,hcode,htotal,htotal] at hcell
  exact hcell

end OriginalSlabCollision
