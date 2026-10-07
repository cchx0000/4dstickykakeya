import Theorems.Thm_StickyKakeya4_grid_quotient_ad
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeQuotientLatticeCounts
open Classical Finset GridQuotientAD
open scoped BigOperators

/-- A bounded product lattice is partitioned into actual occupied N-cells.
Every cell lies in an N-box about one of its own points. -/
theorem global_card_le {k l : ℕ} (A : Finset (Point k l)) (N : ℕ)
    (hN : 1≤N) (U : ℝ) (hU : 0≤U)
    (hx : ∀p∈A,∀i,|p.1 i|≤((2*N:ℕ):ℤ))
    (hy : ∀p∈A,∀i,|p.2 i|≤((2*N:ℕ):ℤ))
    (H : ∀p∈A,((ambientBox A p N).card:ℝ)≤U) :
    (A.card:ℝ)≤(5:ℝ)^(k+l)*U := by
  let key : Point k l → Point k l := fun p => (cellKey (2*N) N p.1,cellKey (2*N) N p.2)
  let menu := cellKeys k (2*N) N ×ˢ cellKeys l (2*N) N
  have hmap : ∀p∈A,key p∈menu := by
    intro p hp
    exact mem_product.mpr ⟨cellKey_mem (2*N) N p.1 hN (hx p hp),
      cellKey_mem (2*N) N p.2 hN (hy p hp)⟩
  have hcell (z : Point k l) : ((A.filter (fun p => key p=z)).card:ℝ)≤U := by
    by_cases hn : (A.filter (fun p => key p=z)).Nonempty
    · obtain ⟨p,hp⟩ := hn
      have hs : A.filter (fun q => key q=z)⊆ambientBox A p N := by
        intro q hq
        have he : key q=key p := (mem_filter.mp hq).2.trans (mem_filter.mp hp).2.symm
        exact mem_filter.mpr ⟨(mem_filter.mp hq).1,
          same_cell_close (2*N) N q.1 p.1 hN (congrArg Prod.fst he),
          same_cell_close (2*N) N q.2 p.2 hN (congrArg Prod.snd he)⟩
      exact (Nat.cast_le.mpr (card_le_card hs)).trans (H p (mem_filter.mp hp).1)
    · rw [not_nonempty_iff_eq_empty.mp hn,card_empty,Nat.cast_zero]
      exact hU
  have hdiv : 2*(2*N)/N=4 := by
    rw [show 2*(2*N)=N*4 by omega]
    exact Nat.mul_div_cancel_left 4 (by omega)
  have hmenu : menu.card=5^(k+l) := by
    simp only [menu,card_product,cellKeys_card,hdiv]
    norm_num only
    exact (pow_add 5 k l).symm
  rw [card_eq_sum_card_fiberwise hmap,Nat.cast_sum]
  calc
    _ ≤ ∑_z∈menu,U := sum_le_sum (fun z _ => hcell z)
    _ = (5:ℝ)^(k+l)*U := by simp only [sum_const,nsmul_eq_mul,hmenu,Nat.cast_pow,Nat.cast_ofNat]

/-- Global quotient count is obtained by summing the genuine full X fibers. -/
theorem global_quotient_card_le {k l : ℕ} (A : Finset (Point k l))
    (N : ℕ) (hN : 1≤N) (lam K t : ℝ) (hlam : 0 < lam)
    (H : (A.card:ℝ)≤K*(N:ℝ)^t)
    (hdense : ∀y∈A.image Prod.snd,lam*(N:ℝ)^k≤((fiber A y).card:ℝ)) :
    ((A.image Prod.snd).card:ℝ)≤(K/lam)*(N:ℝ)^(t-k) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hsum : lam*(N:ℝ)^k*((A.image Prod.snd).card:ℝ)≤(A.card:ℝ) := by
    rw [card_eq_sum_card_image (f:=Prod.snd),Nat.cast_sum]
    calc
      _ = ∑_y∈A.image Prod.snd,lam*(N:ℝ)^k := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun y hy => hdense y hy)
  have he : (N:ℝ)^t=(N:ℝ)^(t-k)*(N:ℝ)^k := by
    rw [←Real.rpow_natCast,←Real.rpow_add hNp]
    congr 1
    ring
  have hh := hsum.trans H
  rw [he] at hh
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlam).2
  have hc := (mul_le_mul_iff_left₀ (pow_pos hNp k)).mp (show
      ((A.image Prod.snd).card:ℝ)*lam*(N:ℝ)^k≤K*(N:ℝ)^(t-k)*(N:ℝ)^k by
    nlinarith only [hh])
  exact hc

/-- The endpoint upper bound through 2N and the full-fiber density produce
both local quotient bounds and a global count, on the identical product set. -/
theorem quotient_counts {k l : ℕ} (A : Finset (Point k l)) (N : ℕ)
    (hN : 1≤N) (lam c K t : ℝ) (hlam : 0 < lam) (hK : 0≤K)
    (hkt : (k:ℝ)≤t) (htdim : t≤((k+l:ℕ):ℝ))
    (hx : ∀p∈A,∀i,|p.1 i|≤(N:ℤ))
    (hy : ∀p∈A,∀i,|p.2 i|≤((2*N:ℕ):ℤ))
    (hdense : ∀y∈A.image Prod.snd,lam*(N:ℝ)^k≤((fiber A y).card:ℝ))
    (hlower : ∀p∈A,∀R:ℕ,1≤R → R≤N → c*(R:ℝ)^t≤((ambientBox A p R).card:ℝ))
    (hupper : ∀p∈A,∀R:ℕ,1≤R → R≤2*N → ((ambientBox A p R).card:ℝ)≤K*(R:ℝ)^t) :
    (0≤t-k ∧ ∀y∈A.image Prod.snd,∀R:ℕ,1≤R → R≤N →
      (c/(3:ℝ)^k)*(R:ℝ)^(t-k)≤((quotientBox A y R).card:ℝ) ∧
      ((quotientBox A y R).card:ℝ)≤
        ((3:ℝ)^k*(2:ℝ)^(k+l)*K/lam)*(R:ℝ)^(t-k)) ∧
      ((A.image Prod.snd).card:ℝ)≤((5:ℝ)^(k+l)*K/lam)*(N:ℝ)^(t-k) := by
  refine ⟨quotient_AD A N lam c K t hlam hK hkt htdim hx hdense hlower hupper,?_⟩
  apply global_quotient_card_le A N hN lam ((5:ℝ)^(k+l)*K) t hlam _ hdense
  have hh := global_card_le A N hN (K*(N:ℝ)^t) (by positivity)
    (fun p hp i => (hx p hp i).trans (by omega)) hy
    (fun p hp => hupper p hp N hN (by omega))
  simpa only [mul_assoc] using hh

end NativeQuotientLatticeCounts
