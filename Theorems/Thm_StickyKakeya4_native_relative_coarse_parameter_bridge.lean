import Theorems.Thm_StickyKakeya4_native_relative_parent_labels
import Theorems.Thm_StickyKakeya4_native_dyadic_parent_cells

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
namespace NativeRelativeCoarseParameterBridge
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeRelativeParentLabels
open NativeDyadicParentCells

/-- The six-level global ancestor, coordinate by coordinate. -/
def globalProjection (z : Parent) : Parent :=
  (fun j => z.1 j/64,fun j => z.2 j/64)

/-- One relative label determines one global slope label and eight global
intercept labels per coordinate. Here M=64*T is the relative scale integer. -/
def globalBox (p : Parent) (T : ℕ) (q : Parent) : Finset Parent :=
  {fun j => (q.1 j+64*(T:ℤ)*p.1 j)/64} ×ˢ
    Fintype.piFinset (fun j => Icc (8*q.2 j+(T:ℤ)*p.2 j) (8*q.2 j+(T:ℤ)*p.2 j+7))

lemma globalProjection_mem_box (p : Parent) (T : ℕ) (z q : Parent)
    (h : NativeRelativeParentLabels.projection p (64*T) z=q) :
    globalProjection z ∈ globalBox p T q := by
  apply mem_product.mpr
  constructor
  · apply mem_singleton.mpr
    funext j
    have hh := congrFun (congrArg Prod.fst h) j
    dsimp [NativeRelativeParentLabels.projection] at hh
    change z.1 j/64=(q.1 j+64*(T:ℤ)*p.1 j)/64
    congr 1
    omega
  · apply Fintype.mem_piFinset.mpr
    intro j
    have hh := congrFun (congrArg Prod.snd h) j
    dsimp [NativeRelativeParentLabels.projection] at hh
    rw [mul_assoc] at hh
    change z.2 j/64 ∈ Icc (8*q.2 j+(T:ℤ)*p.2 j) (8*q.2 j+(T:ℤ)*p.2 j+7)
    apply mem_Icc.mpr
    omega

lemma globalBox_card (p : Parent) (T : ℕ) (q : Parent) :
    (globalBox p T q).card = 512 := by
  have hi (j : Fin 3) :
      (Icc (8*q.2 j+(T:ℤ)*p.2 j) (8*q.2 j+(T:ℤ)*p.2 j+7)).card = 8 := by
    have hh : ((Icc (8*q.2 j+(T:ℤ)*p.2 j) (8*q.2 j+(T:ℤ)*p.2 j+7)).card : ℤ) = 8 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simp [globalBox,Fintype.card_piFinset,hi]

lemma dyadic_globalProjection {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m ell : ℕ) (hell : 6 ≤ ell) (i : Fin n) :
    globalProjection (parentLabel D a (2^(m+ell)) i) = parentLabel D a (2^(m+ell-6)) i := by
  rw [←parent_ancestor_eq D a (Nat.sub_le (m+ell) 6) i]
  have hgap : m+ell-(m+ell-6)=6 := by omega
  simp only [ancestor,hgap,globalProjection]
  norm_num

/-- This correspondence uses the exact actual /512 relative intercept and
the actual global depth f=m+ell-6. The original tube label is unchanged. -/
theorem relative_global_box {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m ell : ℕ) (hell : 6 ≤ ell) (p : Parent) (i : Fin n) :
    parentLabel D a (2^(m+ell-6)) i ∈
      globalBox p (2^(ell-6)) (relativeLabel D a (2^m) p (2^ell) i) := by
  rw [←dyadic_globalProjection D a m ell hell i]
  apply globalProjection_mem_box
  have hM : (2:ℕ)^ell=64*2^(ell-6) := by
    calc
      _ = 2^(6+(ell-6)) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num
  have hprod : (2:ℕ)^ell*2^m=2^(m+ell) := by rw [pow_add,Nat.mul_comm]
  have hh := relativeLabel_eq_projection D a (2^m) p (2^ell) i
  rw [hprod] at hh
  simpa only [hM] using hh.symm

/-- At most512 original global f-parents occur over one relative M-parent.
This bound applies to any literal retained subset, in particular the fixed
old N-parent, without a reverse spatial-menu assertion. -/
theorem relative_fiber_global_labels_card_le {n : ℕ} (D : FiniteScaleSource n)
    (R : Finset (Fin n)) (a : ℝ) (m ell : ℕ) (hell : 6 ≤ ell) (p q : Parent) :
    ((R.filter (fun i => relativeLabel D a (2^m) p (2^ell) i=q)).image
      (parentLabel D a (2^(m+ell-6)))).card ≤ 512 := by
  rw [←globalBox_card p (2^(ell-6)) q]
  apply card_le_card
  intro u hu
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hu
  have hh := relative_global_box D a m ell hell p i
  rwa [(mem_filter.mp hi).2] at hh

end NativeRelativeCoarseParameterBridge
