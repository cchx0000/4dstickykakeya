import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log

/-!
# Quantitative uniform cores for actual finite incidence laws

Largest profile classes and a decreasing finite coordinate rank construct
nested sets C subset B subset A. Local comparisons are made inside the SAME
B, and both the retention estimate and neighborhood counts retain the original
fixed weights. No geometric gain or small-hairbrush payment is postulated.

The integer-weight endpoint is useful for finite occurrence multiplicities.
It does not assert an extension to arbitrary real weights without a positive
atom floor, or derive the missing geometric charge from this uniformity alone.
-/

set_option autoImplicit false

open scoped BigOperators

namespace StickyKakeya4.UniformIncidenceCore

/-- A largest profile class loses at most the number of profiles. -/
theorem exists_large_fiber {X P : Type*} [DecidableEq X] [Fintype P] [DecidableEq P]
    (A : Finset X) (hA : A.Nonempty) (f : X → P) :
    ∃ p : P, (A.filter fun x => f x = p).Nonempty ∧
      A.card ≤ Fintype.card P * (A.filter fun x => f x = p).card := by
  classical
  let : Nonempty P := ⟨f hA.choose⟩
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image (Finset.univ : Finset P)
    (fun p => (A.filter fun x => f x = p).card) Finset.univ_nonempty
  have hcard : A.card ≤ Fintype.card P * (A.filter fun x => f x = p).card := by
    simpa only [Finset.card_univ, Nat.mul_comm] using
      Finset.card_le_mul_card_image_of_maps_to (s := A) (t := Finset.univ)
        (f := f) (fun _ _ => Finset.mem_univ _) _ hp
  refine ⟨p, ?_, hcard⟩
  apply Finset.card_pos.mp
  have hpos := Finset.card_pos.mpr hA
  by_contra h
  have hz : (A.filter fun x => f x = p).card = 0 := by omega
  rw [hz, Nat.mul_zero] at hcard
  omega

/-- Coordinatewise descent strictly decreases the total rank unless the profiles agree. -/
theorem profile_rank_lt {I : Type*} [Fintype I] {L : ℕ}
    {p q : I → Fin (L + 1)} (hle : ∀ i, q i ≤ p i) (hne : q ≠ p) :
    (∑ i, (q i).val) < ∑ i, (p i).val := by
  classical
  have hstrict : ∃ i, (q i).val < (p i).val := by
    by_contra h
    apply hne
    funext i
    apply Fin.ext
    have hi := hle i
    have hnot : ¬(q i).val < (p i).val := fun hi => h ⟨i, hi⟩
    exact Nat.le_antisymm hi (Nat.le_of_not_gt hnot)
  obtain ⟨i, hi⟩ := hstrict
  exact Finset.sum_lt_sum (fun i _ => hle i) ⟨i, Finset.mem_univ i, hi⟩

/-- Finite monotone-profile descent with quantitative retention. -/
theorem uniformize_profiles_of_bound {X I : Type*} [DecidableEq X] [Fintype I] [DecidableEq I]
    (L : ℕ) (profile : Finset X → X → I → Fin (L + 1))
    (hmono : ∀ (A B : Finset X), B ⊆ A → ∀ x ∈ B, ∀ i,
      profile B x i ≤ profile A x i)
    (n : ℕ) :
    ∀ (A : Finset X) (p : I → Fin (L + 1)),
      (∑ i, (p i).val) ≤ n → A.Nonempty →
      (∀ x ∈ A, ∀ i, profile A x i ≤ p i) →
      ∃ B C : Finset X, B ⊆ A ∧ C ⊆ B ∧ C.Nonempty ∧
        A.card ≤ (Fintype.card (I → Fin (L + 1))) ^ (n + 1) * C.card ∧
        ∀ x ∈ C, ∀ y ∈ B, ∀ i, profile B y i ≤ profile B x i := by
  classical
  let K := Fintype.card (I → Fin (L + 1))
  induction n with
  | zero =>
    intro A p hrank hA hbound
    obtain ⟨q, hF, hcard⟩ := exists_large_fiber A hA (profile A)
    let F := A.filter fun x => profile A x = q
    have hFA : F ⊆ A := Finset.filter_subset _ _
    have hqp : ∀ i, q i ≤ p i := by
      obtain ⟨x, hx⟩ := hF
      have heq := (Finset.mem_filter.mp hx).2
      intro i
      rw [← heq]
      exact hbound x (Finset.mem_filter.mp hx).1 i
    have heq : q = p := by
      by_contra hne
      have := profile_rank_lt hqp hne
      omega
    refine ⟨A, F, Finset.Subset.refl _, hFA, hF, ?_, ?_⟩
    · simpa only [Nat.zero_add, pow_one] using hcard
    · intro x hx y hy i
      have hxq := (Finset.mem_filter.mp hx).2
      rw [hxq, heq]
      exact hbound y hy i
  | succ n ih =>
    intro A p hrank hA hbound
    obtain ⟨q, hF, hcard⟩ := exists_large_fiber A hA (profile A)
    let F := A.filter fun x => profile A x = q
    have hFA : F ⊆ A := Finset.filter_subset _ _
    have hqp : ∀ i, q i ≤ p i := by
      obtain ⟨x, hx⟩ := hF
      have heq := (Finset.mem_filter.mp hx).2
      intro i
      rw [← heq]
      exact hbound x (Finset.mem_filter.mp hx).1 i
    by_cases heq : q = p
    · refine ⟨A, F, Finset.Subset.refl _, hFA, hF, ?_, ?_⟩
      · have hp : K ≤ K ^ (n + 1 + 1) := by
          exact le_trans (le_refl K) (Nat.le_self_pow (by omega) K)
        exact hcard.trans (Nat.mul_le_mul_right F.card hp)
      · intro x hx y hy i
        have hxq := (Finset.mem_filter.mp hx).2
        rw [hxq, heq]
        exact hbound y hy i
    · have hqrank : (∑ i, (q i).val) ≤ n := by
        have := profile_rank_lt hqp heq
        omega
      have hFbound : ∀ x ∈ F, ∀ i, profile F x i ≤ q i := by
        intro x hx i
        have hlocal := hmono A F hFA x hx i
        have hxq := (Finset.mem_filter.mp hx).2
        rwa [hxq] at hlocal
      obtain ⟨B, C, hBF, hCB, hC, hretain, hcomp⟩ := ih F q hqrank hF hFbound
      refine ⟨B, C, hBF.trans hFA, hCB, hC, ?_, hcomp⟩
      calc
        A.card ≤ K * F.card := hcard
        _ ≤ K * (K ^ (n + 1) * C.card) := Nat.mul_le_mul_left K hretain
        _ = K ^ (n + 1 + 1) * C.card := by
          simp only [pow_succ]
          ac_rfl

/-- The initial constant profile gives a bound depending only on coordinate count. -/
theorem uniformize_profiles {X I : Type*} [DecidableEq X] [Fintype I] [DecidableEq I]
    (L : ℕ) (profile : Finset X → X → I → Fin (L + 1))
    (hmono : ∀ (A B : Finset X), B ⊆ A → ∀ x ∈ B, ∀ i,
      profile B x i ≤ profile A x i)
    (A : Finset X) (hA : A.Nonempty) :
    ∃ B C : Finset X, B ⊆ A ∧ C ⊆ B ∧ C.Nonempty ∧
      A.card ≤ ((L + 1) ^ Fintype.card I) ^ (Fintype.card I * L + 1) * C.card ∧
      ∀ x ∈ C, ∀ y ∈ B, ∀ i, profile B y i ≤ profile B x i := by
  classical
  let p : I → Fin (L + 1) := fun _ => ⟨L, Nat.lt_succ_self L⟩
  have hrank : (∑ i, (p i).val) ≤ Fintype.card I * L := by simp [p]
  have hbound : ∀ x ∈ A, ∀ i, profile A x i ≤ p i := by
    intro x hx i
    exact Nat.le_of_lt_succ (profile A x i).isLt
  simpa only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ] using
    uniformize_profiles_of_bound L profile hmono (Fintype.card I * L) A p hrank hA hbound

/-- Truncate every logarithmic local incidence count to a finite profile. -/
def incidenceProfile {X I : Type*} [DecidableEq X]
    (R : I → X → Finset X) (Q L : ℕ) (A : Finset X) (x : X) (i : I) : Fin (L + 1) :=
  ⟨min (Nat.log Q (A ∩ R i x).card) L, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- Restricting the source cannot increase any logarithmic incidence coordinate. -/
theorem incidenceProfile_mono {X I : Type*} [DecidableEq X]
    (R : I → X → Finset X) (Q L : ℕ) (A B : Finset X) (hBA : B ⊆ A)
    (x : X) (i : I) : incidenceProfile R Q L B x i ≤ incidenceProfile R Q L A x i := by
  change min (Nat.log Q (B ∩ R i x).card) L ≤ min (Nat.log Q (A ∩ R i x).card) L
  exact min_le_min (Nat.log_mono_right (Finset.card_le_card
    (Finset.inter_subset_inter hBA (Finset.Subset.refl _)))) le_rfl

/-- Finite local-incidence uniformization. The retained `C` and its parent `B` are actual
subsets of `A`. For every retained center in `C`, every local count of `B` anywhere in `B`
is less than `Q` times the corresponding count at that center. No symmetry or transitivity
is assumed for the neighborhood family. -/
theorem uniformize_local_incidence {X I : Type*} [DecidableEq X] [Fintype I] [DecidableEq I]
    (R : I → X → Finset X) (hrefl : ∀ i x, x ∈ R i x)
    (Q L : ℕ) (hQ : 2 ≤ Q) (A : Finset X) (hA : A.Nonempty)
    (hsize : A.card ≤ Q ^ L) :
    ∃ B C : Finset X, B ⊆ A ∧ C ⊆ B ∧ C.Nonempty ∧
      A.card ≤ ((L + 1) ^ Fintype.card I) ^ (Fintype.card I * L + 1) * C.card ∧
      ∀ x ∈ C, ∀ y ∈ B, ∀ i, (B ∩ R i y).card < Q * (B ∩ R i x).card := by
  classical
  obtain ⟨B, C, hBA, hCB, hC, hretain, hcomp⟩ := uniformize_profiles L
    (incidenceProfile R Q L)
    (fun A B hBA x _ i => incidenceProfile_mono R Q L A B hBA x i) A hA
  refine ⟨B, C, hBA, hCB, hC, hretain, ?_⟩
  have hQ' : 1 < Q := by omega
  have hlogbound : ∀ x i, Nat.log Q (B ∩ R i x).card ≤ L := by
    intro x i
    have hc : (B ∩ R i x).card ≤ Q ^ L :=
      (Finset.card_le_card (Finset.inter_subset_left)).trans
        ((Finset.card_le_card hBA).trans hsize)
    simpa only [Nat.log_pow hQ'] using (Nat.log_mono_right (b := Q) hc)
  intro x hx y hy i
  have hxy := hcomp x hx y hy i
  change min (Nat.log Q (B ∩ R i y).card) L ≤
    min (Nat.log Q (B ∩ R i x).card) L at hxy
  rw [min_eq_left (hlogbound y i), min_eq_left (hlogbound x i)] at hxy
  have hxpos : (B ∩ R i x).card ≠ 0 := by
    exact Nat.ne_of_gt (Finset.card_pos.mpr
      ⟨x, Finset.mem_inter.mpr ⟨hCB hx, hrefl i x⟩⟩)
  calc
    (B ∩ R i y).card < Q ^ (Nat.log Q (B ∩ R i y).card + 1) :=
      Nat.lt_pow_succ_log_self hQ' _
    _ ≤ Q ^ (Nat.log Q (B ∩ R i x).card + 1) :=
      Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hxy 1)
    _ = Q * Q ^ Nat.log Q (B ∩ R i x).card := by rw [pow_succ']
    _ ≤ Q * (B ∩ R i x).card := Nat.mul_le_mul_left Q (Nat.pow_log_le_self Q hxpos)


/-- A largest profile class retains its share of any fixed nonnegative integer weight. -/
theorem exists_large_weight_fiber {X P : Type*} [DecidableEq X] [Fintype P] [DecidableEq P]
    (w : X → ℕ) (A : Finset X) (hApos : 0 < A.sum w) (f : X → P) :
    ∃ p : P, (A.filter fun x => f x = p).Nonempty ∧
      0 < (A.filter fun x => f x = p).sum w ∧
      A.sum w ≤ Fintype.card P * (A.filter fun x => f x = p).sum w := by
  classical
  have hA : A.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp [he] at hApos
  let : Nonempty P := ⟨f hA.choose⟩
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image (Finset.univ : Finset P)
    (fun p => (A.filter fun x => f x = p).sum w) Finset.univ_nonempty
  have hmass : A.sum w ≤ Fintype.card P * (A.filter fun x => f x = p).sum w := by
    calc
      A.sum w = ∑ p : P, (A.filter fun x => f x = p).sum w :=
        (Finset.sum_fiberwise A f w).symm
      _ ≤ ∑ _p : P, (A.filter fun x => f x = p).sum w := Finset.sum_le_sum hp
      _ = _ := by simp
  have hpos : 0 < (A.filter fun x => f x = p).sum w := by
    by_contra h
    have hz : (A.filter fun x => f x = p).sum w = 0 := by omega
    rw [hz, Nat.mul_zero] at hmass
    omega
  refine ⟨p, ?_, hpos, hmass⟩
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  simp [he] at hpos
/-- Finite monotone-profile descent with quantitative retention. -/
theorem uniformize_weighted_profiles_of_bound {X I : Type*} [DecidableEq X] [Fintype I] [DecidableEq I]
    (w : X → ℕ) (L : ℕ) (profile : Finset X → X → I → Fin (L + 1))
    (hmono : ∀ (A B : Finset X), B ⊆ A → ∀ x ∈ B, ∀ i,
      profile B x i ≤ profile A x i)
    (n : ℕ) :
    ∀ (A : Finset X) (p : I → Fin (L + 1)),
      (∑ i, (p i).val) ≤ n → 0 < A.sum w →
      (∀ x ∈ A, ∀ i, profile A x i ≤ p i) →
      ∃ B C : Finset X, B ⊆ A ∧ C ⊆ B ∧ 0 < C.sum w ∧
        A.sum w ≤ (Fintype.card (I → Fin (L + 1))) ^ (n + 1) * C.sum w ∧
        ∀ x ∈ C, ∀ y ∈ B, ∀ i, profile B y i ≤ profile B x i := by
  classical
  let K := Fintype.card (I → Fin (L + 1))
  induction n with
  | zero =>
    intro A p hrank hA hbound
    obtain ⟨q, hFnonempty, hF, hcard⟩ := exists_large_weight_fiber w A hA (profile A)
    let F := A.filter fun x => profile A x = q
    have hFA : F ⊆ A := Finset.filter_subset _ _
    have hqp : ∀ i, q i ≤ p i := by
      obtain ⟨x, hx⟩ := hFnonempty
      have heq := (Finset.mem_filter.mp hx).2
      intro i
      rw [← heq]
      exact hbound x (Finset.mem_filter.mp hx).1 i
    have heq : q = p := by
      by_contra hne
      have := profile_rank_lt hqp hne
      omega
    refine ⟨A, F, Finset.Subset.refl _, hFA, hF, ?_, ?_⟩
    · simpa only [Nat.zero_add, pow_one] using hcard
    · intro x hx y hy i
      have hxq := (Finset.mem_filter.mp hx).2
      rw [hxq, heq]
      exact hbound y hy i
  | succ n ih =>
    intro A p hrank hA hbound
    obtain ⟨q, hFnonempty, hF, hcard⟩ := exists_large_weight_fiber w A hA (profile A)
    let F := A.filter fun x => profile A x = q
    have hFA : F ⊆ A := Finset.filter_subset _ _
    have hqp : ∀ i, q i ≤ p i := by
      obtain ⟨x, hx⟩ := hFnonempty
      have heq := (Finset.mem_filter.mp hx).2
      intro i
      rw [← heq]
      exact hbound x (Finset.mem_filter.mp hx).1 i
    by_cases heq : q = p
    · refine ⟨A, F, Finset.Subset.refl _, hFA, hF, ?_, ?_⟩
      · have hp : K ≤ K ^ (n + 1 + 1) := by
          exact le_trans (le_refl K) (Nat.le_self_pow (by omega) K)
        exact hcard.trans (Nat.mul_le_mul_right (F.sum w) hp)
      · intro x hx y hy i
        have hxq := (Finset.mem_filter.mp hx).2
        rw [hxq, heq]
        exact hbound y hy i
    · have hqrank : (∑ i, (q i).val) ≤ n := by
        have := profile_rank_lt hqp heq
        omega
      have hFbound : ∀ x ∈ F, ∀ i, profile F x i ≤ q i := by
        intro x hx i
        have hlocal := hmono A F hFA x hx i
        have hxq := (Finset.mem_filter.mp hx).2
        rwa [hxq] at hlocal
      obtain ⟨B, C, hBF, hCB, hC, hretain, hcomp⟩ := ih F q hqrank hF hFbound
      refine ⟨B, C, hBF.trans hFA, hCB, hC, ?_, hcomp⟩
      calc
        A.sum w ≤ K * F.sum w := hcard
        _ ≤ K * (K ^ (n + 1) * C.sum w) := Nat.mul_le_mul_left K hretain
        _ = K ^ (n + 1 + 1) * C.sum w := by
          simp only [pow_succ]
          ac_rfl

/-- The initial constant profile gives a bound depending only on coordinate count. -/
theorem uniformize_weighted_profiles {X I : Type*} [DecidableEq X] [Fintype I] [DecidableEq I]
    (w : X → ℕ) (L : ℕ) (profile : Finset X → X → I → Fin (L + 1))
    (hmono : ∀ (A B : Finset X), B ⊆ A → ∀ x ∈ B, ∀ i,
      profile B x i ≤ profile A x i)
    (A : Finset X) (hA : 0 < A.sum w) :
    ∃ B C : Finset X, B ⊆ A ∧ C ⊆ B ∧ 0 < C.sum w ∧
      A.sum w ≤ ((L + 1) ^ Fintype.card I) ^ (Fintype.card I * L + 1) * C.sum w ∧
      ∀ x ∈ C, ∀ y ∈ B, ∀ i, profile B y i ≤ profile B x i := by
  classical
  let p : I → Fin (L + 1) := fun _ => ⟨L, Nat.lt_succ_self L⟩
  have hrank : (∑ i, (p i).val) ≤ Fintype.card I * L := by simp [p]
  have hbound : ∀ x ∈ A, ∀ i, profile A x i ≤ p i := by
    intro x hx i
    exact Nat.le_of_lt_succ (profile A x i).isLt
  simpa only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ] using
    uniformize_weighted_profiles_of_bound w L profile hmono (Fintype.card I * L) A p hrank hA hbound


/-- Logarithmic profile of actual local weighted occurrence counts. -/
def weightedIncidenceProfile {X I : Type*} [DecidableEq X]
    (R : I → X → Finset X) (w : X → ℕ) (Q L : ℕ)
    (A : Finset X) (x : X) (i : I) : Fin (L + 1) :=
  ⟨min (Nat.log Q ((A ∩ R i x).sum w)) L, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- Restricting a set decreases every actual weighted neighborhood count. -/
theorem weightedIncidenceProfile_mono {X I : Type*} [DecidableEq X]
    (R : I → X → Finset X) (w : X → ℕ) (Q L : ℕ)
    (A B : Finset X) (hBA : B ⊆ A) (x : X) (i : I) :
    weightedIncidenceProfile R w Q L B x i ≤ weightedIncidenceProfile R w Q L A x i := by
  change min (Nat.log Q ((B ∩ R i x).sum w)) L ≤
    min (Nat.log Q ((A ∩ R i x).sum w)) L
  exact min_le_min (Nat.log_mono_right (Finset.sum_le_sum_of_subset
    (Finset.inter_subset_inter hBA (Finset.Subset.refl _)))) le_rfl

/-- Integer-weighted local-incidence uniformization retains the original occurrence weights.
Its local comparisons use sums of those same fixed weights over actual intersections. -/
theorem uniformize_weighted_local_incidence {X I : Type*}
    [DecidableEq X] [Fintype I] [DecidableEq I]
    (R : I → X → Finset X) (hrefl : ∀ i x, x ∈ R i x)
    (w : X → ℕ) (Q L : ℕ) (hQ : 2 ≤ Q)
    (A : Finset X) (hA : A.Nonempty) (hweight : ∀ x ∈ A, 0 < w x)
    (hsize : A.sum w ≤ Q ^ L) :
    ∃ B C : Finset X, B ⊆ A ∧ C ⊆ B ∧ C.Nonempty ∧
      A.sum w ≤ ((L + 1) ^ Fintype.card I) ^ (Fintype.card I * L + 1) * C.sum w ∧
      ∀ x ∈ C, ∀ y ∈ B, ∀ i, (B ∩ R i y).sum w < Q * (B ∩ R i x).sum w := by
  classical
  have hApos : 0 < A.sum w := by
    obtain ⟨x, hx⟩ := hA
    exact lt_of_lt_of_le (hweight x hx)
      (Finset.single_le_sum (fun z _ => Nat.zero_le (w z)) hx)
  obtain ⟨B, C, hBA, hCB, hCpos, hretain, hcomp⟩ := uniformize_weighted_profiles w L
    (weightedIncidenceProfile R w Q L)
    (fun A B hBA x _ i => weightedIncidenceProfile_mono R w Q L A B hBA x i) A hApos
  have hC : C.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp [he] at hCpos
  refine ⟨B, C, hBA, hCB, hC, hretain, ?_⟩
  have hQ' : 1 < Q := by omega
  have hlogbound : ∀ x i, Nat.log Q ((B ∩ R i x).sum w) ≤ L := by
    intro x i
    have hc : (B ∩ R i x).sum w ≤ Q ^ L :=
      (Finset.sum_le_sum_of_subset (Finset.inter_subset_left)).trans
        ((Finset.sum_le_sum_of_subset hBA).trans hsize)
    simpa only [Nat.log_pow hQ'] using (Nat.log_mono_right (b := Q) hc)
  intro x hx y hy i
  have hxy := hcomp x hx y hy i
  change min (Nat.log Q ((B ∩ R i y).sum w)) L ≤
    min (Nat.log Q ((B ∩ R i x).sum w)) L at hxy
  rw [min_eq_left (hlogbound y i), min_eq_left (hlogbound x i)] at hxy
  have hxpos : (B ∩ R i x).sum w ≠ 0 := by
    apply Nat.ne_of_gt
    exact lt_of_lt_of_le (hweight x (hBA (hCB hx)))
      (Finset.single_le_sum (fun z _ => Nat.zero_le (w z))
        (Finset.mem_inter.mpr ⟨hCB hx, hrefl i x⟩))
  calc
    (B ∩ R i y).sum w < Q ^ (Nat.log Q ((B ∩ R i y).sum w) + 1) :=
      Nat.lt_pow_succ_log_self hQ' _
    _ ≤ Q ^ (Nat.log Q ((B ∩ R i x).sum w) + 1) :=
      Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hxy 1)
    _ = Q * Q ^ Nat.log Q ((B ∩ R i x).sum w) := by rw [pow_succ']
    _ ≤ Q * (B ∩ R i x).sum w := Nat.mul_le_mul_left Q (Nat.pow_log_le_self Q hxpos)

end StickyKakeya4.UniformIncidenceCore
