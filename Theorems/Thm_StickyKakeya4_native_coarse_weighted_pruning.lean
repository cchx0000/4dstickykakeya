import Theorems.Thm_StickyKakeya4_native_coarse_ancestor_counts
import Theorems.Thm_StickyKakeya4_native_original_ancestor_pruning
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
noncomputable section
namespace NativeCoarseWeightedPruning
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeDyadicParentCells
open scoped BigOperators

/-- Finite deletion acts on the actual selected coarse labels. Each occupied
ancestor is charged once. The bound concerns the given label set, so it also
applies after directional coloring without asserting inherited lower AD. -/
theorem ancestor_pruning (Q : Finset Parent) (m : ℕ) (target : Fin (m+1) → ℝ) :
    ∃ S ⊆ Q,
      (Q.card:ℝ)  ≤  S.card+2*∑ell : ActiveCarrierPruningLevel target,
        ((Q.image (ancestor m ell.1.val)).card:ℝ)*target ell.1 ∧
      ∀ell : Fin (m+1),∀p : Parent,
        (S.filter (fun q => ancestor m ell.val q=p)).Nonempty →
          target ell  ≤  ((S.filter (fun q => ancestor m ell.val q=p)).card:ℝ) := by
  let pool : Finset Parent := univ.biUnion fun ell : Fin (m+1) => Q.image (ancestor m ell.val)
  let code : Fin (m+1) → Q → pool := fun ell q =>
    ⟨ancestor m ell.val q.val,mem_biUnion.mpr ⟨ell,mem_univ _,mem_image_of_mem _ q.property⟩⟩
  let menus : Fin (m+1) → Finset pool := fun ell => univ.image (code ell)
  have hmenu (ell : Fin (m+1)) : (menus ell).card=(Q.image (ancestor m ell.val)).card := by
    have he : (menus ell).image Subtype.val=Q.image (ancestor m ell.val) := by
      ext p
      simp only [menus,image_image,mem_image,mem_univ,true_and,code]
      constructor
      · rintro ⟨q,hq⟩
        exact ⟨q.val,q.property,hq⟩
      · rintro ⟨q,hq,hqp⟩
        exact ⟨⟨q,hq⟩,hqp⟩
    rw [←he]
    exact (card_image_of_injective _ Subtype.val_injective).symm
  obtain ⟨V,_hV,hsize,hterminal⟩ := exists_terminal_carrier_pruning_with_varying_cells
    (fun ell : ActiveCarrierPruningLevel target => menus ell.1) (univ:Finset Q)
    (fun ell : ActiveCarrierPruningLevel target => code ell.1)
    (fun ell : ActiveCarrierPruningLevel target => ⌈target ell.1⌉₊)
    (fun ell q _hq => mem_image_of_mem _ (mem_univ q))
  let S := V.image Subtype.val
  have hSQ : S⊆Q := by
    intro p hp
    obtain ⟨q,_hq,rfl⟩ := mem_image.mp hp
    exact q.property
  have hcard : V.card=S.card := (card_image_of_injective _ Subtype.val_injective).symm
  refine ⟨S,hSQ,?_,?_⟩
  · have hs : (Q.card:ℝ)  ≤  S.card+
        ((∑ell : ActiveCarrierPruningLevel target,(menus ell.1).card*⌈target ell.1⌉₊:ℕ):ℝ) := by
      exact_mod_cast (show Q.card ≤ S.card+∑ell : ActiveCarrierPruningLevel target,
        (menus ell.1).card*⌈target ell.1⌉₊ by simpa only [card_univ,Fintype.card_coe,hcard] using hsize)
    have hc := active_carrier_ceiling_charge_le_two_mul menus target
    simp only [hmenu] at hc hs
    exact hs.trans (add_le_add le_rfl hc)
  · intro ell p hne
    by_cases ht : 1 ≤ target ell
    · obtain ⟨q,hq⟩ := hne
      obtain ⟨v,hv,hvq⟩ := mem_image.mp (mem_filter.mp hq).1
      have hcode : (code ell v).val=p := by
        change ancestor m ell.val v.val=p
        rw [hvq]
        exact (mem_filter.mp hq).2
      let pp : pool := ⟨p,hcode ▸ (code ell v).property⟩
      have he : (pointsInCell V (code ell) pp).image Subtype.val=
          S.filter (fun q => ancestor m ell.val q=p) := by
        ext q'
        simp only [pointsInCell,mem_image,mem_filter,code,pp,Subtype.mk.injEq,S]
        constructor
        · rintro ⟨v',⟨hv',hp'⟩,rfl⟩
          exact ⟨⟨v',hv',rfl⟩,hp'⟩
        · rintro ⟨⟨v',hv',rfl⟩,hp'⟩
          exact ⟨v',⟨hv',hp'⟩,rfl⟩
      have hc : (pointsInCell V (code ell) pp).card=
          (S.filter (fun q => ancestor m ell.val q=p)).card := by
        rw [←he,card_image_of_injective _ Subtype.val_injective]
      have hvp : code ell v=pp := Subtype.ext hcode
      have hocc : (pointsInCell V (code ell) pp).Nonempty := by
        refine ⟨v,?_⟩
        simpa only [pointsInCell,mem_filter] using And.intro hv hvp
      have hh := hterminal ⟨ell,ht⟩ pp hocc
      change ⌈target ell⌉₊ ≤ (pointsInCell V (code ell) pp).card at hh
      rw [hc] at hh
      exact (Nat.le_ceil (target ell)).trans (by exact_mod_cast hh)
    · exact (le_of_not_ge ht).trans (by exact_mod_cast one_le_card.mpr hne)

/-- A lost label is charged by its actual shading upper bound. This converts
the finite deletion ledger into shading-mass retention on the SAME subset. -/
lemma weighted_loss {Q S : Finset Parent} (hSQ : S⊆Q) (weight : Parent → ℝ)
    {U charge : ℝ} (hU : 0 ≤ U) (hweight : ∀p∈Q,weight p ≤ U)
    (hcount : (Q.card:ℝ) ≤ S.card+charge) :
    (∑p∈Q,weight p)  ≤  (∑p∈S,weight p)+U*charge := by
  have hcard : ((Q\S).card:ℝ) ≤ charge := by
    have hh : ((Q\S).card:ℝ)+(S.card:ℝ)=(Q.card:ℝ) := by
      exact_mod_cast card_sdiff_add_card_eq_card hSQ
    linarith
  have hw : (∑p∈Q\S,weight p) ≤ U*charge := by
    calc
      _  ≤  ∑_p∈Q\S,U := sum_le_sum (fun p hp => hweight p (mem_sdiff.mp hp).1)
      _ = U*((Q\S).card:ℝ) := by simp [mul_comm]
      _  ≤  _ := mul_le_mul_of_nonneg_left hcard hU
  have he := sum_sdiff hSQ (f:=weight)
  linarith

/-- The ancestor menu after coloring is bounded by the original complete
coarse tree, with exact negative-coordinate dyadic nesting. -/
lemma ancestor_menu_subset {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) (a : ℝ)
    {k m : ℕ} (hkm : k ≤ m) {Q : Finset Parent}
    (hQ : Q⊆R.image (parentLabel D a (2^m))) :
    Q.image (ancestor m k)⊆R.image (parentLabel D a (2^k)) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
  obtain ⟨i,hi,rfl⟩ := mem_image.mp (hQ hq)
  rw [parent_ancestor_eq D a hkm]
  exact mem_image_of_mem _ hi

/-- The retained color is genuinely pruned at all its dyadic ancestor levels,
with its lost ACTUAL shading charged against the ORIGINAL occupied menus.
The hypotheses contain only an upper bound on each existing shading weight. -/
theorem original_color_weighted_pruning {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (m : ℕ) (Q : Finset Parent) (hQ : Q⊆R.image (parentLabel D a (2^m)))
    (target : Fin (m+1) → ℝ) (weight : Parent → ℝ) {U : ℝ} (hU : 0 ≤ U)
    (hweight : ∀p∈Q,weight p ≤ U) :
    ∃S⊆Q,
      (∑p∈Q,weight p)  ≤  (∑p∈S,weight p)+
        2*U*∑ell : ActiveCarrierPruningLevel target,
          ((R.image (parentLabel D a (2^ell.1.val))).card:ℝ)*target ell.1 ∧
      ∀ell : Fin (m+1),∀p : Parent,
        (S.filter (fun q => ancestor m ell.val q=p)).Nonempty →
          target ell  ≤  ((S.filter (fun q => ancestor m ell.val q=p)).card:ℝ) := by
  obtain ⟨S,hSQ,hcount,hterminal⟩ := ancestor_pruning Q m target
  have hledger : (∑ell : ActiveCarrierPruningLevel target,
      ((Q.image (ancestor m ell.1.val)).card:ℝ)*target ell.1)  ≤
        ∑ell : ActiveCarrierPruningLevel target,
          ((R.image (parentLabel D a (2^ell.1.val))).card:ℝ)*target ell.1 := by
    apply sum_le_sum
    intro ell _hell
    apply mul_le_mul_of_nonneg_right _ (le_trans (by norm_num) ell.property)
    exact_mod_cast card_le_card (ancestor_menu_subset D R a (by omega : ell.1.val ≤ m) hQ)
  have hw := weighted_loss hSQ weight hU hweight hcount
  refine ⟨S,hSQ,?_,hterminal⟩
  calc
    _  ≤  _ := hw
    _  ≤  _ := by
      apply add_le_add le_rfl
      have hh := mul_le_mul_of_nonneg_left hledger (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hU)
      convert hh using 1
      ring

end NativeCoarseWeightedPruning
