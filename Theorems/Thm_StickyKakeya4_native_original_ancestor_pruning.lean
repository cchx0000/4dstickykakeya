import Theorems.Thm_StickyKakeya4_native_compact_parent_retention
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeOriginalAncestorPruning
open Classical Finset StickyKakeya4 NativeOriginalParentSelection
open scoped BigOperators

/-- Specialize the existing one-charge-per-cell deletion to the actual
original graph labels. The finite coding stores those labels exactly. Only
active real thresholds enter the original occupied-cell loss ledger. -/
theorem original_parent_pruning {n d : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : Fin d→ℕ) (target : Fin d→ℝ) :
    ∃ R : Finset (Fin n),
      (n:ℝ)≤R.card+2*∑ ell : ActiveCarrierPruningLevel target,
        ((parents D a (N ell.1)).card:ℝ)*target ell.1 ∧
      ∀ ell p,(R.filter (fun i=>parentLabel D a (N ell) i=p)).Nonempty →
        target ell≤((R.filter (fun i=>parentLabel D a (N ell) i=p)).card:ℝ) := by
  let pool : Finset Parent := univ.biUnion fun ell : Fin d=>parents D a (N ell)
  let code : Fin d→Fin n→pool := fun ell i=>
    ⟨parentLabel D a (N ell) i,mem_biUnion.mpr ⟨ell,mem_univ _,mem_image_of_mem _ (mem_univ i)⟩⟩
  let menus : Fin d→Finset pool := fun ell=>univ.image (code ell)
  have hmenu (ell : Fin d) : (menus ell).card=(parents D a (N ell)).card := by
    have he : (menus ell).image Subtype.val=parents D a (N ell) := by
      simp only [menus,image_image]
      rfl
    rw [←he]
    exact (card_image_of_injective _ Subtype.val_injective).symm
  obtain ⟨R,_hR,hsize,hterminal⟩ := exists_terminal_carrier_pruning_with_varying_cells
    (fun ell : ActiveCarrierPruningLevel target=>menus ell.1) (univ:Finset (Fin n))
    (fun ell : ActiveCarrierPruningLevel target=>code ell.1)
    (fun ell : ActiveCarrierPruningLevel target=>⌈target ell.1⌉₊)
    (fun ell i _hi=>mem_image_of_mem _ (mem_univ i))
  refine ⟨R,?_,?_⟩
  · have hs : (n:ℝ)≤R.card+
        ((∑ell : ActiveCarrierPruningLevel target,(menus ell.1).card*⌈target ell.1⌉₊:ℕ):ℝ) := by
      exact_mod_cast (show n≤R.card+∑ell : ActiveCarrierPruningLevel target,
        (menus ell.1).card*⌈target ell.1⌉₊ by simpa only [card_univ,Fintype.card_fin] using hsize)
    have hc := active_carrier_ceiling_charge_le_two_mul menus target
    simp only [hmenu] at hc hs
    exact hs.trans (add_le_add le_rfl hc)
  · intro ell p hne
    by_cases ht : 1≤target ell
    · obtain ⟨i,hi⟩ := hne
      have hip : parentLabel D a (N ell) i=p := (mem_filter.mp hi).2
      have hpool : p∈pool := by
        rw [←hip]
        exact (code ell i).property
      let pp : pool := ⟨p,hpool⟩
      have he : pointsInCell R (code ell) pp=R.filter (fun i=>parentLabel D a (N ell) i=p) := by
        ext j
        simp only [pointsInCell,mem_filter,code,pp,Subtype.mk.injEq]
      have hh := hterminal ⟨ell,ht⟩ pp (by rw [he]; exact ⟨i,hi⟩)
      change ⌈target ell⌉₊≤(pointsInCell R (code ell) pp).card at hh
      rw [he] at hh
      exact (Nat.le_ceil (target ell)).trans (by exact_mod_cast hh)
    · exact (le_of_not_ge ht).trans (by exact_mod_cast one_le_card.mpr hne)

end NativeOriginalAncestorPruning
