import Theorems.Thm_StickyKakeya4_native_coarse_weighted_pruning
import Theorems.Thm_StickyKakeya4_native_padded_source_count_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeCoarsePruningBudget
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeDyadicParentCells
open NativeCoarseWeightedPruning NativePaddedSourceCountBudget
open scoped BigOperators

/-- Original AD lower occupancy and actual direction packing bound the
number of occupied original cells at every requested scale. -/
theorem original_occupied_count {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (N : ℕ) (hN : 0<N)
    (H : ∀p : Parent,(R.filter (fun i => parentLabel D a N i=p)).Nonempty →
      D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3  ≤
        ((R.filter (fun i => parentLabel D a N i=p)).card:ℝ)) :
    ((R.image (parentLabel D a N)).card:ℝ)  ≤  373248*D.thickness^(-zeta)*(N:ℝ)^3 := by
  let P := R.image (parentLabel D a N)
  have hd:=h.1.2.1
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hz := Real.rpow_pos_of_pos hd zeta
  have hsum : (∑p∈P,((R.filter (fun i => parentLabel D a N i=p)).card:ℝ))=(R.card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_image (parentLabel D a N) R).symm
  have hl : (P.card:ℝ)*(D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3)  ≤
      373248*(1/D.thickness)^3 := by
    calc
      _ = ∑_p∈P,D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3 := by simp
      _  ≤  ∑p∈P,((R.filter (fun i => parentLabel D a N i=p)).card:ℝ) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨i,hi,hip⟩ := mem_image.mp hp
        exact H p ⟨i,mem_filter.mpr ⟨hi,hip⟩⟩
      _ = (R.card:ℝ) := hsum
      _  ≤  n := by
        have hh : R.card ≤ n := by simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ R)
        exact_mod_cast hh
      _  ≤  _ := original_card_upper h
  have he : (373248*D.thickness^(-zeta)*(N:ℝ)^3)*
      (D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3)=373248*(1/D.thickness)^3 := by
    rw [Real.rpow_neg hd.le]
    field_simp [hd.ne',hNr.ne',hz.ne']
  apply (mul_le_mul_iff_left₀ (show 0 < D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3 by positivity)).mp
  rw [he]
  exact hl

def target (delta t : ℝ) (m : ℕ) (ell : Fin (m+1)) : ℝ :=
  delta^t*(((2^m:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3

lemma occupied_threshold_charge {delta zeta t : ℝ} (hd : 0 < delta) (m k C : ℕ)
    (hC : (C:ℝ) ≤ 373248*delta^(-zeta)*((2^k:ℕ):ℝ)^3) :
    (C:ℝ)*(delta^t*(((2^m:ℕ):ℝ)/((2^k:ℕ):ℝ))^3)  ≤
      373248*delta^(t-zeta)*((2^m:ℕ):ℝ)^3 := by
  calc
    _  ≤  (373248*delta^(-zeta)*((2^k:ℕ):ℝ)^3)*
        (delta^t*(((2^m:ℕ):ℝ)/((2^k:ℕ):ℝ))^3) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ = _ := by
      have hpow : delta^(-zeta)*delta^t=delta^(t-zeta) := by
        rw [←Real.rpow_add hd]
        congr 1
        ring
      calc
        _ = 373248*(delta^(-zeta)*delta^t)*((2^m:ℕ):ℝ)^3 := by field_simp
        _ = _ := by rw [hpow]

/-- The true deletion ledger has only a logarithmic number of equal charges.
After multiplying by the actual per-coarse-tube volume bound, the rho^-3
factor cancels its rho^3 volume. An extra delta power pays this finite loss. -/
theorem weighted_pruning_power_budget {n : ℕ} {D : FiniteScaleSource n} {eta zeta a t U : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (m : ℕ)
    (H : ∀ell : Fin (m+1),∀p : Parent,
      (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
        D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3  ≤
          ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ))
    (Q : Finset Parent) (hQ : Q⊆R.image (parentLabel D a (2^m)))
    (weight : Parent → ℝ) (hU : 0 ≤ U) (hweight : ∀p∈Q,weight p ≤ U) :
    ∃S⊆Q,
      (∑p∈Q,weight p)  ≤  (∑p∈S,weight p)+
        746496*U*(m+1)*D.thickness^(t-zeta)*((2^m:ℕ):ℝ)^3 ∧
      ∀ell : Fin (m+1),∀p : Parent,
        (S.filter (fun q => ancestor m ell.val q=p)).Nonempty →
          D.thickness^t*(((2^m:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3  ≤
            ((S.filter (fun q => ancestor m ell.val q=p)).card:ℝ) := by
  have hd := h.1.2.1
  let T := target D.thickness t m
  obtain ⟨S,hSQ,hshade,hterminal⟩ := original_color_weighted_pruning D R a m Q hQ T weight hU hweight
  have hcharge (ell : ActiveCarrierPruningLevel T) :
      ((R.image (parentLabel D a (2^ell.1.val))).card:ℝ)*T ell.1  ≤
        373248*D.thickness^(t-zeta)*((2^m:ℕ):ℝ)^3 :=
    occupied_threshold_charge h.1.2.1 m ell.1.val _
      (original_occupied_count h R (2^ell.1.val) (by positivity) (H ell.1))
  have hsum : (∑ell : ActiveCarrierPruningLevel T,
      ((R.image (parentLabel D a (2^ell.1.val))).card:ℝ)*T ell.1)  ≤
        (m+1:ℕ)*(373248*D.thickness^(t-zeta)*((2^m:ℕ):ℝ)^3) := by
    calc
      _  ≤  ∑_ell : ActiveCarrierPruningLevel T,373248*D.thickness^(t-zeta)*((2^m:ℕ):ℝ)^3 :=
        sum_le_sum (fun ell _hell => hcharge ell)
      _ = (Fintype.card (ActiveCarrierPruningLevel T):ℝ)*
          (373248*D.thickness^(t-zeta)*((2^m:ℕ):ℝ)^3) := by simp
      _  ≤  _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (Fintype.card_subtype_le (fun ell : Fin (m+1) => 1 ≤ T ell)).trans_eq (Fintype.card_fin (m+1)))
        (by positivity)
  refine ⟨S,hSQ,?_,hterminal⟩
  apply hshade.trans
  apply add_le_add le_rfl
  have hh := mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hU)
  convert hh using 1
  push_cast
  ring

end NativeCoarsePruningBudget
