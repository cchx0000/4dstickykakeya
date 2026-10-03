import Theorems.Thm_StickyKakeya4_self_uniform_incidence_refinement

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1600000

namespace CompatibleTupleSelection

open SelfUniform

variable {α : Type*}

lemma mass_eq_sum_partition {β : Type*} [DecidableEq β]
    (w : α → ℕ) (A : Finset α) (f : α → β) :
    mass w A = ∑ t ∈ A.image f, mass w (A.filter (fun x => f x = t)) := by
  classical
  exact (Finset.sum_fiberwise_of_maps_to
    (fun x hx => Finset.mem_image_of_mem f hx) w).symm

/-- Choosing a maximum-weight occupied fiber loses at most the number of
occupied fibers. Empty sets and zero weights are permitted. -/
theorem weighted_fiber_selection {β : Type*} [DecidableEq β]
    (w : α → ℕ) (A : Finset α) (f : α → β) (b : ℕ)
    (hcard : (A.image f).card ≤ b) :
    ∃ E ⊆ A, mass w A ≤ b * mass w E ∧
      ∀ x y, x ∈ E → y ∈ E → f x = f y := by
  classical
  by_cases hne : A.Nonempty
  · obtain ⟨t, _ht, hmax⟩ := Finset.exists_max_image (A.image f)
      (fun t => mass w (A.filter (fun x => f x = t))) (hne.image f)
    refine ⟨A.filter (fun x => f x = t), Finset.filter_subset _ _, ?_, ?_⟩
    · calc
        mass w A = ∑ u ∈ A.image f, mass w (A.filter (fun x => f x = u)) :=
          mass_eq_sum_partition w A f
        _ ≤ ∑ _u ∈ A.image f, mass w (A.filter (fun x => f x = t)) :=
          Finset.sum_le_sum (fun u hu => hmax u hu)
        _ = (A.image f).card * mass w (A.filter (fun x => f x = t)) := by simp
        _ ≤ b * mass w (A.filter (fun x => f x = t)) :=
          Nat.mul_le_mul_right _ hcard
    · intro x y hx hy
      exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  · have hA : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst A
    exact ⟨∅, Finset.Subset.refl _, by simp [mass], by simp⟩

/-- Independently select a maximum-weight angular fiber in each occupied
spatial cell. The retained set has one angular state per occupied cell. -/
theorem weighted_spatial_selection {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]
    (w : α → ℕ) (A : Finset α) (q : α → σ) (k : α → τ) (b : ℕ)
    (hmenu : ∀ t, ((A.filter (fun x => q x = t)).image k).card ≤ b) :
    ∃ E ⊆ A, mass w A ≤ b * mass w E ∧
      ∀ x y, x ∈ E → y ∈ E → q x = q y → k x = k y := by
  classical
  choose C hCsub hCmass hCuniform using
    (fun t => weighted_fiber_selection w (A.filter (fun x => q x = t)) k b (hmenu t))
  let E := (A.image q).biUnion C
  have hdisj : Set.PairwiseDisjoint (↑(A.image q)) C := by
    intro t _ht u _hu htu
    apply Finset.disjoint_left.mpr
    intro x hxt hxu
    exact htu ((Finset.mem_filter.mp (hCsub t hxt)).2.symm.trans
      (Finset.mem_filter.mp (hCsub u hxu)).2)
  have hEmass : mass w E = ∑ t ∈ A.image q, mass w (C t) := by
    exact Finset.sum_biUnion hdisj
  refine ⟨E, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, _ht, hxt⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp (hCsub t hxt)).1
  · calc
      mass w A = ∑ t ∈ A.image q, mass w (A.filter (fun x => q x = t)) :=
        mass_eq_sum_partition w A q
      _ ≤ ∑ t ∈ A.image q, b * mass w (C t) :=
        Finset.sum_le_sum (fun t _ht => hCmass t)
      _ = b * mass w E := by rw [hEmass, Finset.mul_sum]
  · intro x y hx hy hxy
    obtain ⟨t, _ht, hxt⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨u, _hu, hyu⟩ := Finset.mem_biUnion.mp hy
    have htu : t = u := (Finset.mem_filter.mp (hCsub t hxt)).2.symm.trans
      (hxy.trans (Finset.mem_filter.mp (hCsub u hyu)).2)
    subst u
    exact hCuniform t x y hxt hyu

/-- Construct a compatible angular choice through finitely many nested spatial
partitions. The successor menu bound is conditioned on the previous angular
state in the ORIGINAL set `A`. No bound on unconditioned successor menus and
no pre-existing coherent selection is assumed.

At each stage the construction independently chooses a maximum-weight angular
fiber in every spatial cell. Angular-state types and spatial-cell types may
vary with the stage. Spatial refinement is sufficient; an additional angular
ancestor axiom is not needed to construct the all-stage compatibility. -/
theorem weighted_compatible_selection
    {σ τ : ℕ → Type*} [∀ j, DecidableEq (σ j)] [∀ j, DecidableEq (τ j)]
    (w : α → ℕ) (A : Finset α) (q : ∀ j, α → σ j)
    (k : ∀ j, α → τ j) (b : ℕ → ℕ) (N : ℕ)
    (hq : ∀ j, j + 1 < N → ∀ x y, q (j + 1) x = q (j + 1) y → q j x = q j y)
    (hroot : ∀ t, ((A.filter (fun x => q 0 x = t)).image (k 0)).card ≤ b 0)
    (hstep : ∀ j, j + 1 < N → ∀ t u,
      ((A.filter (fun x => q (j + 1) x = t ∧ k j x = u)).image (k (j + 1))).card
        ≤ b (j + 1)) :
    ∃ E ⊆ A, mass w A ≤ (∏ j ∈ Finset.range N, b j) * mass w E ∧
      ∀ j, j < N → ∀ x y, x ∈ E → y ∈ E → q j x = q j y → k j x = k j y := by
  classical
  suffices h : ∀ n, n ≤ N →
      ∃ E ⊆ A, mass w A ≤ (∏ j ∈ Finset.range n, b j) * mass w E ∧
        ∀ j, j < n → ∀ x y, x ∈ E → y ∈ E → q j x = q j y → k j x = k j y from
    h N (Nat.le_refl N)
  intro n
  induction n with
  | zero =>
    intro _hn
    refine ⟨A, Finset.Subset.refl _, ?_, ?_⟩
    · simp
    · intro j hj
      omega
  | succ n ih =>
    intro hn
    obtain ⟨B, hBA, hBmass, hBcompatible⟩ := ih (by omega)
    have hmenu : ∀ t, ((B.filter (fun x => q n x = t)).image (k n)).card ≤ b n := by
      intro t
      cases n with
      | zero =>
        apply (Finset.card_le_card (Finset.image_subset_image
          (show B.filter (fun x => q 0 x = t) ⊆ A.filter (fun x => q 0 x = t) from ?_))).trans
          (hroot t)
        intro x hx
        exact Finset.mem_filter.mpr ⟨hBA (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
      | succ j =>
        by_cases hnonempty : (B.filter (fun x => q (j + 1) x = t)).Nonempty
        · obtain ⟨z, hz⟩ := hnonempty
          have hzB := (Finset.mem_filter.mp hz).1
          have hzq := (Finset.mem_filter.mp hz).2
          have hsub : B.filter (fun x => q (j + 1) x = t) ⊆
              A.filter (fun x => q (j + 1) x = t ∧ k j x = k j z) := by
            intro x hx
            obtain ⟨hxB, hxq⟩ := Finset.mem_filter.mp hx
            refine Finset.mem_filter.mpr ⟨hBA hxB, hxq, ?_⟩
            exact hBcompatible j (by omega) x z hxB hzB
              (hq j (by omega) x z (hxq.trans hzq.symm))
          exact (Finset.card_le_card (Finset.image_subset_image hsub)).trans
            (hstep j (by omega) t (k j z))
        · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
          simp
    obtain ⟨E, hEB, hEmass, hEcompatible⟩ := weighted_spatial_selection w B (q n) (k n) (b n) hmenu
    refine ⟨E, hEB.trans hBA, ?_, ?_⟩
    · calc
        mass w A ≤ (∏ j ∈ Finset.range n, b j) * mass w B := hBmass
        _ ≤ (∏ j ∈ Finset.range n, b j) * (b n * mass w E) :=
          Nat.mul_le_mul_left _ hEmass
        _ = (∏ j ∈ Finset.range (n + 1), b j) * mass w E := by
          rw [Finset.prod_range_succ]
          ring
    · intro j hj x y hx hy hxy
      by_cases hjn : j < n
      · exact hBcompatible j hjn x y (hEB hx) (hEB hy) hxy
      · have hjeq : j = n := by omega
        subst j
        exact hEcompatible x y hx hy hxy

/-- On pairs `(original label, good terminal tuple)`, final compatibility makes
the projection to original labels injective whenever the final spatial cell
depends only on the original label and the final angular state is the tuple.
Consequently the retained pair mass is exactly retained ORIGINAL-label mass.
The numerator is the entire original weighted good-tuple count. -/
theorem weighted_original_label_selection {ι σ τ : Type*}
    [DecidableEq ι] [DecidableEq σ] [DecidableEq τ]
    (w : ι → ℕ) (A : Finset (ι × τ))
    (q : ℕ → ι × τ → σ) (k : ℕ → ι × τ → τ) (b : ℕ → ℕ) (J : ℕ)
    (hq : ∀ j, j + 1 < J + 1 → ∀ x y, q (j + 1) x = q (j + 1) y → q j x = q j y)
    (hroot : ∀ t, ((A.filter (fun x => q 0 x = t)).image (k 0)).card ≤ b 0)
    (hstep : ∀ j, j + 1 < J + 1 → ∀ t u,
      ((A.filter (fun x => q (j + 1) x = t ∧ k j x = u)).image (k (j + 1))).card
        ≤ b (j + 1))
    (hqfinal : ∀ (x y : ι × τ), x.1 = y.1 → q J x = q J y)
    (hkfinal : ∀ (x : ι × τ), k J x = x.2) :
    ∃ E ⊆ A, ∃ S ⊆ A.image Prod.fst,
      S = E.image Prod.fst ∧
      (∀ x y, x ∈ E → y ∈ E → x.1 = y.1 → x = y) ∧
      mass (fun x => w x.1) E = mass w S ∧
      mass (fun x => w x.1) A ≤ (∏ j ∈ Finset.range (J + 1), b j) * mass w S ∧
      (∀ j, j < J + 1 → ∀ x y, x ∈ E → y ∈ E → q j x = q j y → k j x = k j y) := by
  classical
  obtain ⟨E, hEA, hEmass, hEcompatible⟩ :=
    weighted_compatible_selection (fun x => w x.1) A q k b (J + 1) hq hroot hstep
  have hinj : ∀ x y, x ∈ E → y ∈ E → x.1 = y.1 → x = y := by
    intro x y hx hy hxy
    apply Prod.ext hxy
    have h := hEcompatible J (by omega) x y hx hy (hqfinal x y hxy)
    simpa only [hkfinal] using h
  have hmass : mass (fun x => w x.1) E = mass w (E.image Prod.fst) := by
    unfold mass
    exact (Finset.sum_image (fun x hx y hy hxy => hinj x y hx hy hxy)).symm
  refine ⟨E, hEA, E.image Prod.fst, Finset.image_subset_image hEA, rfl,
    hinj, hmass, ?_, hEcompatible⟩
  simpa only [hmass] using hEmass

/-- All good terminal witnesses, keeping the original label as the first
coordinate. No choice of a single witness is made before refinement. -/
def goodPairs {ι τ : Type*} (I : Finset ι) (G : ι → Finset τ) : Finset (ι × τ) :=
  (I.sigma G).map (Equiv.sigmaEquivProd ι τ).toEmbedding

@[simp] lemma mem_goodPairs {ι τ : Type*} (I : Finset ι) (G : ι → Finset τ)
    (p : ι × τ) : p ∈ goodPairs I G ↔ p.1 ∈ I ∧ p.2 ∈ G p.1 := by
  rcases p with ⟨x, u⟩
  simp [goodPairs, Equiv.sigmaEquivProd]

lemma mass_goodPairs {ι τ : Type*} (w : ι → ℕ) (I : Finset ι) (G : ι → Finset τ) :
    mass (fun p => w p.1) (goodPairs I G) = ∑ x ∈ I, w x * (G x).card := by
  classical
  unfold mass
  rw [Finset.sum_finset_product (goodPairs I G) I G (mem_goodPairs I G)]
  simp [Nat.mul_comm]

/-- Original-label selection from a SET of good terminal tuples per label.
The product loss is paid against the entire weighted good-tuple count, not
against an arbitrarily chosen single tuple per label. All selected witness
pairs lie in the original good family, their projection to labels is injective,
and the resulting original-label set is compatible at every stage. -/
theorem weighted_good_tuple_family_selection {ι σ τ : Type*}
    [DecidableEq ι] [DecidableEq σ] [DecidableEq τ]
    (w : ι → ℕ) (I : Finset ι) (G : ι → Finset τ)
    (q : ℕ → ι → σ) (k : ℕ → τ → τ) (b : ℕ → ℕ) (J : ℕ)
    (hq : ∀ j, j + 1 < J + 1 → ∀ x y, q (j + 1) x = q (j + 1) y → q j x = q j y)
    (hroot : ∀ t,
      (((goodPairs I G).filter (fun p => q 0 p.1 = t)).image (fun p => k 0 p.2)).card ≤ b 0)
    (hstep : ∀ j, j + 1 < J + 1 → ∀ t u,
      (((goodPairs I G).filter (fun p => q (j + 1) p.1 = t ∧ k j p.2 = u)).image
        (fun p => k (j + 1) p.2)).card ≤ b (j + 1))
    (hkfinal : ∀ u, k J u = u) :
    ∃ E ⊆ goodPairs I G, ∃ S ⊆ I,
      S = E.image Prod.fst ∧
      (∀ x y, x ∈ E → y ∈ E → x.1 = y.1 → x = y) ∧
      mass (fun x => w x.1) E = mass w S ∧
      (∑ x ∈ I, w x * (G x).card) ≤
        (∏ j ∈ Finset.range (J + 1), b j) * mass w S ∧
      (∀ j, j < J + 1 → ∀ x y, x ∈ E → y ∈ E →
        q j x.1 = q j y.1 → k j x.2 = k j y.2) := by
  classical
  obtain ⟨E, hEA, S, hSA, hS, hinj, hmass, hret, hcompatible⟩ :=
    weighted_original_label_selection w (goodPairs I G)
      (fun j p => q j p.1) (fun j p => k j p.2) b J
      (fun j hj x y hxy => hq j hj x.1 y.1 hxy) hroot hstep
      (fun x y hxy => congrArg (q J) hxy) (fun x => hkfinal x.2)
  refine ⟨E, hEA, S, ?_, hS, hinj, hmass, ?_, hcompatible⟩
  · intro x hx
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp (hSA hx)
    rw [← hpx]
    exact ((mem_goodPairs I G p).mp hp).1
  · simpa only [mass_goodPairs] using hret

end CompatibleTupleSelection
