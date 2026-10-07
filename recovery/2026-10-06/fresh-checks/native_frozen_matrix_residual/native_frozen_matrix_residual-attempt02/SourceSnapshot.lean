import Theorems.Thm_StickyKakeya4_native_frozen_time_field
import Theorems.Thm_StickyKakeya4_native_matrix_height_interface

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeFrozenMatrixResidual
open Classical Finset NativeMatrixHeightWholePoint NativeFrozenTimeField
open scoped BigOperators Matrix.Norms.Elementwise

/-- Changing the matrix keeps the same tangent, normal and offset marks.
Its physical residual cost is derived entry by entry. -/
theorem matrix_residual_transfer {k l : ℕ}
    (Fold Fnew : Matrix (Fin l) (Fin k) ℝ) (x : Fin k → ℝ) (n xi : Fin l → ℝ)
    (delta B E : ℝ) (hD : ‖Fnew-Fold‖≤delta) (hB : 0≤B)
    (hx : ∀j,|x j|≤B)
    (hres : ∀i,|n i-∑j : Fin k,Fold i j*x j-xi i|≤E) :
    ∀i,|n i-∑j : Fin k,Fnew i j*x j-xi i|≤E+(k:ℝ)*delta*B := by
  intro i
  have hentry (j : Fin k) : |Fnew i j-Fold i j|≤delta := by
    have hc : |Fnew i j-Fold i j|≤‖Fnew-Fold‖ := by
      simpa only [Matrix.sub_apply,Real.norm_eq_abs] using
        (Matrix.norm_entry_le_entrywise_sup_norm (Fnew-Fold) (i:=i) (j:=j))
    exact hc.trans hD
  have hdelta : 0≤delta := (norm_nonneg _).trans hD
  have hdiff : |∑j : Fin k,(Fnew i j-Fold i j)*x j|≤(k:ℝ)*delta*B := by
    calc
      _ ≤ ∑j : Fin k,|(Fnew i j-Fold i j)*x j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑_j : Fin k,delta*B := by
        apply sum_le_sum
        intro j _hj
        rw [abs_mul]
        exact mul_le_mul (hentry j) (hx j) (abs_nonneg _) hdelta
      _ = _ := by simp [mul_assoc]
  have he : n i-∑j : Fin k,Fnew i j*x j-xi i=
      (n i-∑j : Fin k,Fold i j*x j-xi i)-∑j : Fin k,(Fnew i j-Fold i j)*x j := by
    simp only [sub_mul,sum_sub_distrib]
    ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add (hres i) hdiff)

/-- One matrix-selected source supplies the frozen configuration field,
all working-height bounds, and the new affine residual on the SAME original
incidences. Neither new field coherence nor its residual is an input. -/
theorem select_frozen_matrix_with_residual {P T : Type*}
    (ell : ℕ) (hell : ell=2 ∨ ell=3) (K : ℕ)
    (S : Finset P) (weight : P → ℕ) (height : P → ℝ)
    (F : P → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (I : P → T → Prop) (tangent : T → Fin (ell-1) → ℝ)
    (normal : T → Fin (4-ell) → ℝ) (xi : P → Fin (4-ell) → ℝ)
    (L delta B E : ℝ) (hL : 0≤L) (hd : 0<delta) (hB : 0≤B)
    (hF : ∀p∈S,‖F p‖≤1/4)
    (N : Fin (K+1) → ℕ) (hN : ∀i,0<N i) (hN0 : N 0=1)
    (hLip : ∀p∈S,∀q∈S,‖F p-F q‖≤L*|height p-height q|)
    (htan : ∀p∈S,∀t,I p t → ∀j,|tangent t j|≤B)
    (hres : ∀p∈S,∀t,I p t → ∀i,
      |normal t i-∑j : Fin (ell-1),F p i j*tangent t j-xi p i|≤E) :
    ∃Spre⊆S,mass S weight≤(modulus L)^(2*(K+1))*mass Spre weight ∧
      (∀h,‖field Spre height F delta h‖≤1/4) ∧
      (∀p∈Spre,‖field Spre height F delta ⌊height p/delta⌋-F p‖≤delta) ∧
      (∀i : Fin (K+1),∀p∈Spre,∀q∈Spre,
        ⌊height p/(delta*(N i:ℝ))⌋=⌊height q/(delta*(N i:ℝ))⌋ →
          ‖field Spre height F delta ⌊height p/delta⌋-
            field Spre height F delta ⌊height q/delta⌋‖≤delta*(N i:ℝ)) ∧
      ∀p∈Spre,∀t,I p t → ∀i,
        |normal t i-∑j : Fin (ell-1),(field Spre height F delta ⌊height p/delta⌋) i j*tangent t j-
          xi p i|≤E+2*delta*B := by
  obtain ⟨Spre,hsub,hret,_hretR,hcoh⟩ := NativeMatrixHeightInterface.select_matrix_points
    ell hell (K+1) S weight height (fun p => p) F L delta hL hd
    (fun i => delta*(N i:ℝ)) (fun _ => 0)
    (fun i => by
      have hn : (1:ℝ)≤N i := by exact_mod_cast (show 1≤N i by exact hN i)
      nlinarith only [hn,hd]) hLip
  have H (i : Fin (K+1)) (p : P) (hp : p∈Spre) (q : P) (hq : q∈Spre)
      (he : ⌊height p/(delta*(N i:ℝ))⌋=⌊height q/(delta*(N i:ℝ))⌋) :
      dist (F p) (F q)≤delta*(N i:ℝ) := by
    rw [dist_eq_norm]
    exact (hcoh i p hp q hq (by simpa only [heightCell,sub_zero] using he)).le
  have Hbase (p : P) (hp : p∈Spre) : ‖field Spre height F delta ⌊height p/delta⌋-F p‖≤delta := by
    have hh := field_close_to_original Spre height F delta delta (fun p hp q hq he => by
      simpa only [hN0,Nat.cast_one,mul_one] using H 0 p hp q hq
        (by simpa only [hN0,Nat.cast_one,mul_one] using he)) hp
    simpa only [dist_eq_norm] using hh
  refine ⟨Spre,hsub,hret,field_norm_le Spre height F delta (1/4) (by norm_num)
    (fun p hp => hF p (hsub hp)),Hbase,?_,?_⟩
  · intro i p hp q hq he
    simpa only [dist_eq_norm] using frozen_field_coarse Spre Spre (Subset.refl _) height F
      delta (N i) (delta*(N i:ℝ)) (H i) hp hq he
  · intro p hp t hit i
    have hh := matrix_residual_transfer (F p) (field Spre height F delta ⌊height p/delta⌋)
      (tangent t) (normal t) (xi p) delta B E (Hbase p hp) hB
      (htan p (hsub hp) t hit) (hres p (hsub hp) t hit) i
    have hk : ((ell-1:ℕ):ℝ)≤2 := by rcases hell with rfl | rfl <;> norm_num
    exact hh.trans (by nlinarith [mul_nonneg hd.le hB])

end NativeFrozenMatrixResidual
