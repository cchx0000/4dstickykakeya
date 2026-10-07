import Theorems.Thm_StickyKakeya4_native_approximate_fiber_count
import Theorems.Thm_StickyKakeya4_backward_fiber_grains

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeApproximateFiberIteration
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeCubicalDiameterCount NativeApproximateFiberCount BackwardFiberGrains
open scoped BigOperators

def radius (h : ℝ) (i : ℕ) : ℝ := (4:ℝ)^i*h

lemma radius_pos {h : ℝ} (hh : 0 < h) (i : ℕ) : 0 < radius h i := by
  unfold radius
  positivity

lemma le_radius {h : ℝ} (hh : 0 ≤ h) (i : ℕ) : h ≤ radius h i := by
  simpa only [radius,one_mul] using
    mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4) : (1:ℝ) ≤ 4^i) hh

lemma radius_succ (h : ℝ) (i : ℕ) : radius h (i+1)=4*radius h i := by
  simp only [radius,pow_succ]
  ring

def directionAt {n : ℕ} (v : Fin n → E4) (i : ℕ) : E4 :=
  if hi : i < n then v ⟨i,hi⟩ else 0

lemma directionAt_eq {n : ℕ} (v : Fin n → E4) (i : Fin n) : directionAt v i.val=v i := by
  simp only [directionAt,dif_pos i.isLt]

/-- Every factor uses the original h-neighborhood at the next actual layer. -/
def predecessorMinimum {n : ℕ} (mesh : ℝ) (A : ℕ → Finset Index)
    (v : Fin n → E4) (h : ℝ) (i : ℕ) : ℕ :=
  minimumPredecessor mesh (A i) (A (i+1)) (Submodule.span ℝ {directionAt v i}) h

def overlap (mesh q h : ℝ) (i : ℕ) : ℕ :=
  capacity mesh (4*radius h i+(8*radius h i/q)*2)

lemma fiber_mono_radius (mesh : ℝ) (A : Finset Index) (P : Submodule ℝ E4) (x : E4)
    {h H : ℝ} (hH : h ≤ H) : fiber mesh A P x h ⊆ fiber mesh A P x H := by
  intro k hk
  exact mem_filter.mpr ⟨(mem_filter.mp hk).1,(mem_filter.mp hk).2.trans hH⟩

/-- Exact finite counting through approximate fibers. The numerator factors
are computed from the thin original h-fibers; they are allowed to be zero. -/
theorem iterated_count {n : ℕ} (A : ℕ → Finset Index) (v : Fin n → E4)
    {mesh : ℝ} (hm : 0 < mesh) (q h : ℝ) (hq : 0 < q) (hh : 0 < h)
    (htrans : ∀i : Fin n,q ≤ Metric.infDist (v i) (prefixSpan v i.val:Set E4))
    (hv : ∀i : Fin n,‖v i‖ ≤ 2) :
    ∀ell : ℕ,ell ≤ n → ∀x∈A ell,
      (∏i∈range ell,predecessorMinimum mesh A v h i) ≤
        (∏i∈range ell,overlap mesh q h i)*
          (fiber mesh (A 0) (prefixSpan v ell) (cellCenter mesh x) (radius h ell)).card := by
  intro ell
  induction ell with
  | zero =>
    intro _hell x hx
    simp only [range_zero,prod_empty,one_mul,prefixSpan_zero,radius,pow_zero,one_mul]
    apply one_le_card.mpr
    refine ⟨x,mem_filter.mpr ⟨hx,?_⟩⟩
    rw [sub_self,Metric.infDist_zero_of_mem (show (0:E4)∈(⊥:Submodule ℝ E4) by simp)]
    exact hh.le
  | succ ell ih =>
    intro hell x hx
    have hi : ell < n := by omega
    let i : Fin n := ⟨ell,hi⟩
    have hdir : directionAt v ell=v i := directionAt_eq v i
    have hP : prefixSpan v (ell+1)=prefixSpan v ell⊔Submodule.span ℝ {directionAt v ell} := by
      rw [prefixSpan_succ,hdir]
      exact congrArg (fun Q => prefixSpan v ell⊔Q) (directionSpan_eq v i)
    let B := fiber mesh (A ell) (Submodule.span ℝ {directionAt v ell})
      (cellCenter mesh x) (radius h ell)
    let G := ∏j∈range ell,predecessorMinimum mesh A v h j
    let D := ∏j∈range ell,overlap mesh q h j
    have hminimum : predecessorMinimum mesh A v h ell ≤ B.card := by
      apply (minimumPredecessor_le mesh (A ell) (A (ell+1))
        (Submodule.span ℝ {directionAt v ell}) h x hx).trans
      exact card_le_card (fiber_mono_radius mesh (A ell) _ _ (le_radius hh.le ell))
    have hpoint : ∀y∈B,G ≤ D*(fiber mesh (A 0) (prefixSpan v ell)
        (cellCenter mesh y) (radius h ell)).card := by
      intro y hy
      exact ih (by omega) y (mem_filter.mp hy).1
    have hsum : B.card*G ≤ D*(∑y∈B,(fiber mesh (A 0) (prefixSpan v ell)
        (cellCenter mesh y) (radius h ell)).card) := by
      calc
        _ = ∑_y∈B,G := by simp
        _ ≤ ∑y∈B,D*(fiber mesh (A 0) (prefixSpan v ell)
            (cellCenter mesh y) (radius h ell)).card := sum_le_sum hpoint
        _ = _ := by rw [mul_sum]
    have hstep := backward_fiber_sum_bound (A 0) (A ell) hm (prefixSpan v ell)
      (directionAt v ell) q (radius h ell) 2 hq (radius_pos hh ell) (by norm_num)
      (by simpa only [hdir] using htrans i) (by simpa only [hdir] using hv i) (cellCenter mesh x)
    change (∑y∈B,(fiber mesh (A 0) (prefixSpan v ell) (cellCenter mesh y) (radius h ell)).card) ≤
      overlap mesh q h ell*(fiber mesh (A 0) (prefixSpan v ell⊔Submodule.span ℝ {directionAt v ell})
        (cellCenter mesh x) (4*radius h ell)).card at hstep
    rw [←hP,←radius_succ] at hstep
    rw [prod_range_succ,prod_range_succ]
    change G*predecessorMinimum mesh A v h ell ≤
      (D*overlap mesh q h ell)*(fiber mesh (A 0) (prefixSpan v (ell+1))
        (cellCenter mesh x) (radius h (ell+1))).card
    calc
      _ ≤ G*B.card := Nat.mul_le_mul_left G hminimum
      _ = B.card*G := Nat.mul_comm _ _
      _ ≤ D*(∑y∈B,(fiber mesh (A 0) (prefixSpan v ell)
          (cellCenter mesh y) (radius h ell)).card) := hsum
      _ ≤ D*(overlap mesh q h ell*(fiber mesh (A 0) (prefixSpan v (ell+1))
          (cellCenter mesh x) (radius h (ell+1))).card) := Nat.mul_le_mul_left D hstep
      _ = _ := (Nat.mul_assoc _ _ _).symm

lemma overlap_le_common {mesh q h C : ℝ} (hm : 0 < mesh) (hq : 0 < q) (hq1 : q ≤ 1)
    (hh : 0 < h) (hC : 1 ≤ C) (hwidth : h ≤ C*mesh) (i : ℕ) (hi : i ≤ 4) :
    (overlap mesh q h i:ℝ) ≤ (41*(256*C)/q)^4 := by
  have hp : (4:ℝ)^i ≤ 256 := by
    simpa only [show (4:ℝ)^4=256 by norm_num] using
      pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) hi
  have hr : radius h i ≤ (256*C)*mesh := by
    have h1 := mul_le_mul_of_nonneg_right hp hh.le
    have h2 := mul_le_mul_of_nonneg_left hwidth (by norm_num : (0:ℝ) ≤ 256)
    dsimp [radius]
    nlinarith
  exact capacity_le_transverse_power hm (radius_pos hh i) hq hq1 (by nlinarith) hr

/-- For at most four directions, all loss factors have one explicit bound.
The underlying geometric mesh is unchanged throughout the iteration. -/
theorem iterated_lower_bound {n : ℕ} (A : ℕ → Finset Index) (v : Fin n → E4)
    {mesh : ℝ} (hm : 0 < mesh) (q h C : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hh : 0 < h) (hC : 1 ≤ C) (hwidth : h ≤ C*mesh)
    (htrans : ∀i : Fin n,q ≤ Metric.infDist (v i) (prefixSpan v i.val:Set E4))
    (hv : ∀i : Fin n,‖v i‖ ≤ 2) (ell : ℕ) (hell : ell ≤ n) (hell4 : ell ≤ 4)
    (x : Index) (hx : x∈A ell) :
    ((∏i∈range ell,predecessorMinimum mesh A v h i):ℝ)/((41*(256*C)/q)^4)^ell ≤
      ((fiber mesh (A 0) (prefixSpan v ell) (cellCenter mesh x) (radius h ell)).card:ℝ) := by
  have hn := iterated_count A v hm q h hq hh htrans hv ell hell x hx
  have hp : ((∏i∈range ell,overlap mesh q h i):ℝ) ≤ ((41*(256*C)/q)^4)^ell := by
    calc
      _ ≤ ∏_i∈range ell,(41*(256*C)/q)^4 := by
        apply prod_le_prod (fun i _hi => Nat.cast_nonneg _)
        intro i hi
        exact overlap_le_common hm hq hq1 hh hC hwidth i (by have hi' := mem_range.mp hi; omega)
      _ = _ := by simp
  have hreal : ((∏i∈range ell,predecessorMinimum mesh A v h i):ℝ) ≤
      ((∏i∈range ell,overlap mesh q h i):ℝ)*
        ((fiber mesh (A 0) (prefixSpan v ell) (cellCenter mesh x) (radius h ell)).card:ℝ) := by
    exact_mod_cast hn
  have hC0 : 0 < C := by linarith
  have hpos : 0 < ((41*(256*C)/q)^4)^ell := by positivity
  apply (div_le_iff₀ hpos).mpr
  have hh' := hreal.trans (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))
  simpa only [mul_comm] using hh'

theorem full_lower_bound {n : ℕ} (A : ℕ → Finset Index) (v : Fin n → E4) (hn : n ≤ 4)
    {mesh : ℝ} (hm : 0 < mesh) (q h C : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hh : 0 < h) (hC : 1 ≤ C) (hwidth : h ≤ C*mesh)
    (htrans : ∀i : Fin n,q ≤ Metric.infDist (v i) (prefixSpan v i.val:Set E4))
    (hv : ∀i : Fin n,‖v i‖ ≤ 2) (x : Index) (hx : x∈A n) :
    ((∏i∈range n,predecessorMinimum mesh A v h i):ℝ)/((41*(256*C)/q)^4)^n ≤
      ((fiber mesh (A 0) (Submodule.span ℝ (Set.range v)) (cellCenter mesh x) (radius h n)).card:ℝ) := by
  simpa only [prefixSpan_full] using iterated_lower_bound A v hm q h C hq hq1 hh hC hwidth htrans hv n le_rfl hn x hx

end NativeApproximateFiberIteration
