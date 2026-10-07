import Theorems.Thm_StickyKakeya4_native_capped_old_ancestors

set_option autoImplicit false
set_option warningAsError true

noncomputable section
namespace NativeTerminalOldAncestorFiber
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCappedOldAncestors

/-- At the actual output phase an old-ancestor fiber is the singleton of
the very same full-source index. This is independent of any population law. -/
theorem terminal_fiber_eq_singleton {n : ℕ} (D : FiniteScaleSource n)
    (R : Finset (Fin n)) (a : ℝ) (b : ℕ)
    (i : Fin (R.image (parentLabel D a (2^b))).card) :
    (univ : Finset (Fin (R.image (parentLabel D a (2^b))).card)).filter
      (fun j => oldAncestor D R a b b j=oldAncestor D R a b b i) = {i} := by
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  exact (terminal_injective D R a b).eq_iff

/-- The capped terminal branch has exact carrier population one. -/
theorem terminal_fiber_card {n : ℕ} (D : FiniteScaleSource n)
    (R : Finset (Fin n)) (a : ℝ) (b k : ℕ) (hk : k=b)
    (i : Fin (R.image (parentLabel D a (2^b))).card) :
    ((univ : Finset (Fin (R.image (parentLabel D a (2^b))).card)).filter
      (fun j => oldAncestor D R a b k j=oldAncestor D R a b k i)).card = 1 := by
  subst k
  rw [terminal_fiber_eq_singleton, card_singleton]

end NativeTerminalOldAncestorFiber
