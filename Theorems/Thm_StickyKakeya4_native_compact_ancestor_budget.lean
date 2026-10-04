import Theorems.Thm_StickyKakeya4_native_original_ancestor_pruning
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeCompactAncestorBudget
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCompactParentRetention
open NativeOriginalAncestorPruning
open scoped BigOperators

def target (delta etaNew : ℝ) (N : ℕ) : ℝ := delta^etaNew*((1/(N:ℝ))/delta)^3

lemma active_scale_budget {delta etaNew L : ℝ} {N : ℕ}
    (hd : 0<delta) (hL : 0<L) (hN : 0<N)
    (hsmall : delta^etaNew*L^3≤1) (hactive : 1≤target delta etaNew N) :
    delta*(L*N)≤1 := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  let x := delta*(L*N)
  have hx : 0<x := by dsimp [x]; positivity
  have hid : target delta etaNew N*x^3=delta^etaNew*L^3 := by
    dsimp [target,x]
    field_simp
  have hp : x^3≤1 := by
    calc
      _ ≤ target delta etaNew N*x^3 := le_mul_of_one_le_left (by positivity) hactive
      _ = _ := hid
      _ ≤ _ := hsmall
  by_contra hn
  have hlarge : 1<x := lt_of_not_ge hn
  have hprod : 0<(x-1)*(x^2+x+1) := mul_pos (by linarith) (by positivity)
  nlinarith

lemma cell_target_charge {delta eta etaNew C : ℝ} {N M : ℕ}
    (hd : 0<delta) (hN : 0<N)
    (hcount : (M:ℝ)≤C*delta^(-2*eta)*(N:ℝ)^3) :
    (M:ℝ)*target delta etaNew N≤C*delta^(etaNew-2*eta-3) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have ht : 0≤target delta etaNew N := by dsimp [target]; positivity
  have hpow : delta^(-2*eta)*delta^etaNew/delta^3=delta^(etaNew-2*eta-3) := by
    rw [←Real.rpow_add hd,←Real.rpow_natCast delta 3,←Real.rpow_sub hd]
    congr 1
    ring
  calc
    _ ≤ (C*delta^(-2*eta)*(N:ℝ)^3)*target delta etaNew N :=
      mul_le_mul_of_nonneg_right hcount ht
    _ = C*(delta^(-2*eta)*delta^etaNew/delta^3) := by
      dsimp [target]
      field_simp
    _ = _ := by rw [hpow]

/-- Concrete original graph-cell pruning with its complete loss bound. All
fine active scales satisfy the chart budget automatically; inactive scales
need no deletion because one original retained tube already meets the target. -/
theorem compact_original_ancestor_pruning (K : Set MarkedLine) (hK : IsCompact K) :
    ∃ C L : ℝ, 0<C ∧ 6≤L ∧ ∀ (n d : ℕ) (D : FiniteScaleSource n)
      (eta etaNew a : ℝ) (N : Fin d→ℕ),
      IsWangZakharovNativeFiniteInput D eta → (∀ i,D.line i∈K) →
      (∀ i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) →
      (∀ ell,0<N ell) → D.thickness^etaNew*L^3≤1 →
      ∃ R : Finset (Fin n),
        (n:ℝ)≤R.card+2*C*d*D.thickness^(etaNew-2*eta-3) ∧
        ∀ ell p,(R.filter (fun i=>parentLabel D a (N ell) i=p)).Nonempty →
          target D.thickness etaNew (N ell)≤
            ((R.filter (fun i=>parentLabel D a (N ell) i=p)).card:ℝ) := by
  obtain ⟨C,L,hC,hL,hcount⟩ := compact_parent_bound K hK
  refine ⟨C,L,hC,hL,?_⟩
  intro n d D eta etaNew a N h hDK ha hN hsmall
  let target' := fun ell : Fin d=>target D.thickness etaNew (N ell)
  obtain ⟨R,hret,hterminal⟩ := original_parent_pruning D a N target'
  have hcharge (ell : ActiveCarrierPruningLevel target') :
      ((parents D a (N ell.1)).card:ℝ)*target' ell.1≤C*D.thickness^(etaNew-2*eta-3) := by
    have hscale := active_scale_budget h.1.2.1 (by linarith : 0<L) (hN ell.1) hsmall ell.2
    exact cell_target_charge h.1.2.1 (hN ell.1) (hcount n D eta a (N ell.1) h hDK ha (hN ell.1) hscale)
  have hcard : Fintype.card (ActiveCarrierPruningLevel target')≤d := by
    exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin d)
  have hsum : (∑ell : ActiveCarrierPruningLevel target',
      ((parents D a (N ell.1)).card:ℝ)*target' ell.1)≤
      (d:ℝ)*(C*D.thickness^(etaNew-2*eta-3)) := by
    calc
      _ ≤ ∑_ell : ActiveCarrierPruningLevel target',C*D.thickness^(etaNew-2*eta-3) :=
        sum_le_sum (fun ell _=>hcharge ell)
      _ = (Fintype.card (ActiveCarrierPruningLevel target'):ℝ)*(C*D.thickness^(etaNew-2*eta-3)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (mul_nonneg hC.le (Real.rpow_pos_of_pos h.1.2.1 _).le)
  refine ⟨R,?_,hterminal⟩
  nlinarith only [hret,hsum]

end NativeCompactAncestorBudget
