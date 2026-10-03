import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace DisjointProfileEpochs

open scoped BigOperators

variable {α C I : Type*} [DecidableEq α] [Fintype C]

/-- Actual remaining points in an indexed spatial cell. Cells may overlap. -/
def population (cells : C → Finset α) (E : Finset α) (c : C) : Finset α :=
  E ∩ cells c

/-- Each originally occupied cell contributes its threshold only once. -/
noncomputable def penalty (cells : C → Finset α) (threshold : C → ℕ)
    (E : Finset α) : ℕ :=
  ∑ c : C, if (population cells E c).Nonempty then threshold c else 0

def Regular (cells : C → Finset α) (threshold : C → ℕ) (E : Finset α) : Prop :=
  ∀ c, (population cells E c).Nonempty → threshold c ≤ (population cells E c).card

omit [Fintype C] in
lemma population_mono (cells : C → Finset α) {E D : Finset α} (h : E ⊆ D) (c : C) :
    population cells E c ⊆ population cells D c := Finset.inter_subset_inter_right h

lemma penalty_mono (cells : C → Finset α) (threshold : C → ℕ)
    {E D : Finset α} (h : E ⊆ D) : penalty cells threshold E ≤ penalty cells threshold D := by
  classical
  unfold penalty
  apply Finset.sum_le_sum
  intro c _
  by_cases hE : (population cells E c).Nonempty
  · have hD := hE.mono (population_mono cells h c)
    simp [hE, hD]
  · simp [hE]

lemma penalty_delete_cell (cells : C → Finset α) (threshold : C → ℕ)
    (E : Finset α) (c : C) (hc : (population cells E c).Nonempty) :
    penalty cells threshold (E \ population cells E c) + threshold c ≤
      penalty cells threshold E := by
  classical
  let D := E \ population cells E c
  have hD : ¬(population cells D c).Nonempty := by
    rintro ⟨x, hx⟩
    have hx' := Finset.mem_inter.mp hx
    exact (Finset.mem_sdiff.mp hx'.1).2 (Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp hx'.1).1, hx'.2⟩)
  have hsum : (∑ j ∈ (Finset.univ : Finset C).erase c,
      if (population cells D j).Nonempty then threshold j else 0) ≤
      ∑ j ∈ (Finset.univ : Finset C).erase c,
      if (population cells E j).Nonempty then threshold j else 0 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : (population cells D j).Nonempty
    · have hj' := hj.mono (population_mono cells Finset.sdiff_subset j)
      simp [hj, hj']
    · simp [hj]
  have hleft := Finset.sum_erase_add (Finset.univ : Finset C)
    (fun j => if (population cells D j).Nonempty then threshold j else 0)
    (Finset.mem_univ c)
  have hright := Finset.sum_erase_add (Finset.univ : Finset C)
    (fun j => if (population cells E j).Nonempty then threshold j else 0)
    (Finset.mem_univ c)
  simp only [hD, ↓reduceIte, add_zero] at hleft
  simp only [hc, ↓reduceIte] at hright
  change (∑ j : C, if (population cells D j).Nonempty then threshold j else 0) + _ ≤ _
  unfold penalty
  rw [← hleft, ← hright]
  exact Nat.add_le_add_right hsum _

def mass (pieces : List (Finset α)) : ℕ := (pieces.map Finset.card).sum

omit [DecidableEq α] in
@[simp] lemma mass_nil : mass ([] : List (Finset α)) = 0 := rfl
omit [DecidableEq α] in
@[simp] lemma mass_cons (F : Finset α) (pieces : List (Finset α)) :
    mass (F :: pieces) = F.card + mass pieces := rfl

/-- The output carries the actual extraction sources, not just a cardinal certificate. -/
structure Harvest (cells : C → Finset α) (threshold : C → ℕ)
    (good : Finset α → Finset α → Prop) (stop : Finset α → Prop)
    (A : Finset α) where
  remainder : Finset α
  pieces : List (Finset α)
  remainder_subset : remainder ⊆ A
  pieces_subset : ∀ F ∈ pieces, F ⊆ A
  pieces_nonempty : ∀ F ∈ pieces, F.Nonempty
  pairwise : pieces.Pairwise Disjoint
  remainder_disjoint : ∀ F ∈ pieces, Disjoint remainder F
  sources : ∀ F ∈ pieces, ∃ E ⊆ A, Regular cells threshold E ∧ F ⊆ E ∧ good E F
  regular : Regular cells threshold remainder
  stopped : remainder = ∅ ∨ stop remainder
  accounting : A.card + penalty cells threshold remainder ≤
    remainder.card + mass pieces + penalty cells threshold A

/-- Finite recursion: delete an entire deficient cell; otherwise extract the supplied
nonempty subset. No cell budget is reset when an extraction intervenes. -/
theorem exists_harvest (cells : C → Finset α) (threshold : C → ℕ)
    (good : Finset α → Finset α → Prop) (stop : Finset α → Prop)
    (A : Finset α)
    (extract : ∀ E ⊆ A, Regular cells threshold E → E.Nonempty → ¬stop E →
      ∃ F ⊆ E, F.Nonempty ∧ good E F) :
    Nonempty (Harvest cells threshold good stop A) := by
  classical
  induction hcard : A.card using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases hreg : Regular cells threshold A
    · by_cases hhalt : A = ∅ ∨ stop A
      · exact ⟨⟨A, [], by rfl, by simp, by simp, by simp, by simp,
          by simp, hreg, hhalt, by simp⟩⟩
      · have hne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun h => hhalt (Or.inl h))
        have hnostop : ¬stop A := fun h => hhalt (Or.inr h)
        obtain ⟨F, hFA, hFne, hgood⟩ := extract A (by rfl) hreg hne hnostop
        let D := A \ F
        have hDsub : D ⊆ A := Finset.sdiff_subset
        have hDcard : D.card < n := by
          have := Finset.card_sdiff_add_card_eq_card hFA
          have := Finset.card_pos.mpr hFne
          dsimp [D]
          omega
        obtain ⟨r⟩ := ih D.card hDcard D (fun E hED => extract E (hED.trans hDsub)) rfl
        refine ⟨⟨r.remainder, F :: r.pieces, r.remainder_subset.trans hDsub, ?_, ?_, ?_, ?_,
          ?_, r.regular, r.stopped, ?_⟩⟩
        · intro G hG
          rcases List.mem_cons.mp hG with rfl | hG
          · exact hFA
          · exact (r.pieces_subset G hG).trans hDsub
        · intro G hG
          rcases List.mem_cons.mp hG with rfl | hG
          · exact hFne
          · exact r.pieces_nonempty G hG
        · apply List.pairwise_cons.mpr
          refine ⟨?_, r.pairwise⟩
          intro G hG
          exact Finset.sdiff_disjoint.symm.mono_right (r.pieces_subset G hG)
        · intro G hG
          rcases List.mem_cons.mp hG with rfl | hG
          · exact Finset.sdiff_disjoint.mono_left r.remainder_subset
          · exact r.remainder_disjoint G hG
        · intro G hG
          rcases List.mem_cons.mp hG with rfl | hG
          · exact ⟨A, by rfl, hreg, hFA, hgood⟩
          · obtain ⟨E, hED, hEr, hGE, hEg⟩ := r.sources G hG
            exact ⟨E, hED.trans hDsub, hEr, hGE, hEg⟩
        · have hp := penalty_mono cells threshold hDsub
          have hc := Finset.card_sdiff_add_card_eq_card hFA
          have hr := r.accounting
          simp only [mass_cons]
          dsimp [D] at hr hp
          omega
    · have hbad : ∃ c, (population cells A c).Nonempty ∧
          (population cells A c).card < threshold c := by
        by_contra hnone
        apply hreg
        intro c hc
        by_contra hlow
        exact hnone ⟨c, hc, Nat.lt_of_not_ge hlow⟩
      obtain ⟨c, hc, hlow⟩ := hbad
      let F := population cells A c
      let D := A \ F
      have hFA : F ⊆ A := Finset.inter_subset_left
      have hDsub : D ⊆ A := Finset.sdiff_subset
      have hDcard : D.card < n := by
        have hdiff := Finset.card_sdiff_add_card_eq_card hFA
        have hpos := Finset.card_pos.mpr hc
        dsimp [D, F] at *
        omega
      obtain ⟨r⟩ := ih D.card hDcard D (fun E hED => extract E (hED.trans hDsub)) rfl
      refine ⟨⟨r.remainder, r.pieces, r.remainder_subset.trans hDsub,
        (fun G hG => (r.pieces_subset G hG).trans hDsub), r.pieces_nonempty,
        r.pairwise, r.remainder_disjoint, ?_, r.regular, r.stopped, ?_⟩⟩
      · intro G hG
        obtain ⟨E, hED, hEr, hGE, hEg⟩ := r.sources G hG
        exact ⟨E, hED.trans hDsub, hEr, hGE, hEg⟩
      · have hp := penalty_delete_cell cells threshold A c hc
        have hc' := Finset.card_sdiff_add_card_eq_card hFA
        have hr := r.accounting
        dsimp [D, F] at hr hc'
        omega

/-- Integer digit budget: zero for zero, one plus the floor base logarithm otherwise. -/
def rank (K n : ℕ) : ℕ := if n = 0 then 0 else Nat.log K n + 1

@[simp] lemma rank_zero (K : ℕ) : rank K 0 = 0 := by simp [rank]

lemma rank_pos (K : ℕ) {n : ℕ} (hn : 0 < n) : 0 < rank K n := by
  simp [rank, Nat.ne_of_gt hn]

lemma rank_mono (K : ℕ) {m n : ℕ} (h : m ≤ n) : rank K m ≤ rank K n := by
  by_cases hm : m = 0
  · simp [hm]
  · have hn : n ≠ 0 := by omega
    simpa [rank, hm, hn] using Nat.add_le_add_right (Nat.log_mono_right h) 1

lemma rank_drop {K m n : ℕ} (hK : 1 < K) (hdrop : K * m < n) :
    rank K m < rank K n := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hdrop
  by_cases hm : m = 0
  · simpa [hm] using rank_pos K hn
  · have hlog : Nat.log K m + 1 ≤ Nat.log K n := by
      rw [← Nat.log_mul_base hK hm]
      exact Nat.log_mono_right (by simpa [Nat.mul_comm] using hdrop.le)
    simp only [rank, hm, Nat.ne_of_gt hn, ↓reduceIte]
    omega

variable [Fintype I]

noncomputable def profileBudget (K : ℕ) (profile : I → Finset α → ℕ)
    (A : Finset α) : ℕ := ∑ i : I, rank K (profile i A)

omit [DecidableEq α] in
lemma profileBudget_mono (K : ℕ) (profile : I → Finset α → ℕ)
    (mono : ∀ i, Monotone (profile i)) {A B : Finset α} (h : A ⊆ B) :
    profileBudget K profile A ≤ profileBudget K profile B := by
  classical
  exact Finset.sum_le_sum (fun i _ => rank_mono K (mono i h))

omit [DecidableEq α] in
lemma profileBudget_drop {K : ℕ} (hK : 1 < K) (profile : I → Finset α → ℕ)
    (mono : ∀ i, Monotone (profile i)) {A B : Finset α} (h : B ⊆ A)
    (i : I) (hdrop : K * profile i B < profile i A) :
    profileBudget K profile B < profileBudget K profile A := by
  classical
  exact Finset.sum_lt_sum
    (fun j _ => rank_mono K (mono j h))
    ⟨i, Finset.mem_univ i, rank_drop hK hdrop⟩

omit [DecidableEq α] in
lemma profileBudget_le (K B : ℕ) (profile : I → Finset α → ℕ)
    (A : Finset α) (hbound : ∀ i, rank K (profile i A) ≤ B) :
    profileBudget K profile A ≤ Fintype.card I * B := by
  classical
  calc
    profileBudget K profile A ≤ ∑ _ : I, B := Finset.sum_le_sum (fun i _ => hbound i)
    _ = Fintype.card I * B := by simp

-- A finite power bound on the raw profiles gives a finite epoch budget.
omit [DecidableEq α] in
lemma profileBudget_le_of_pow_bound {K B : ℕ}
    (profile : I → Finset α → ℕ) (A : Finset α)
    (hbound : ∀ i, profile i A < K ^ B) :
    profileBudget K profile A ≤ Fintype.card I * B := by
  apply profileBudget_le
  intro i
  by_cases hi : profile i A = 0
  · simp [hi]
  · have := Nat.log_lt_of_lt_pow hi (hbound i)
    simp only [rank, hi, ↓reduceIte]
    omega

/-- One epoch has a fixed source set and one selected profile. -/
structure Epoch (α I : Type*) where
  index : I
  start : Finset α
  pieces : List (Finset α)

def allPieces (epochs : List (Epoch α I)) : List (Finset α) :=
  epochs.flatMap Epoch.pieces

omit [DecidableEq α] [Fintype I] in
@[simp] lemma allPieces_nil : allPieces ([] : List (Epoch α I)) = [] := rfl
omit [DecidableEq α] [Fintype I] in
@[simp] lemma allPieces_cons (e : Epoch α I) (es : List (Epoch α I)) :
    allPieces (e :: es) = e.pieces ++ allPieces es := rfl

omit [DecidableEq α] in
lemma mass_append (xs ys : List (Finset α)) : mass (xs ++ ys) = mass xs + mass ys := by
  simp [mass]

/-- Every extracted piece records the actual regular residual at extraction time,
and its selected profile is still at least one K-th of the epoch's start value. -/
def ValidEpoch (cells : C → Finset α) (threshold : C → ℕ)
    (K : ℕ) (profile : I → Finset α → ℕ)
    (rule : I → Finset α → Finset α → Finset α → Prop) (e : Epoch α I) : Prop :=
  e.start.Nonempty ∧ ∀ F ∈ e.pieces, ∃ E ⊆ e.start,
    Regular cells threshold E ∧ F ⊆ E ∧
    profile e.index e.start ≤ K * profile e.index E ∧ rule e.index e.start E F

structure Decomposition (cells : C → Finset α) (threshold : C → ℕ)
    (K : ℕ) (profile : I → Finset α → ℕ)
    (rule : I → Finset α → Finset α → Finset α → Prop) (A : Finset α) where
  epochs : List (Epoch α I)
  starts_subset : ∀ e ∈ epochs, e.start ⊆ A
  valid : ∀ e ∈ epochs, ValidEpoch cells threshold K profile rule e
  pieces_subset : ∀ F ∈ allPieces epochs, F ⊆ A
  pieces_nonempty : ∀ F ∈ allPieces epochs, F.Nonempty
  pairwise : (allPieces epochs).Pairwise Disjoint
  accounting : A.card ≤ mass (allPieces epochs) + penalty cells threshold A
  epoch_bound : epochs.length ≤ profileBudget K profile A

/-- The actual greedy construction. The only geometric inputs are monotonicity,
positive selected profiles, and a nonempty extraction rule on regular residuals. -/
theorem exists_decomposition (cells : C → Finset α) (threshold : C → ℕ)
    (K : ℕ) (hK : 1 < K) (profile : I → Finset α → ℕ)
    (mono : ∀ i, Monotone (profile i))
    (zero : ∀ i, profile i ∅ = 0)
    (select : Finset α → I)
    (positive : ∀ A, A.Nonempty → 0 < profile (select A) A)
    (rule : I → Finset α → Finset α → Finset α → Prop)
    (extract : ∀ A, A.Nonempty → ∀ E ⊆ A, Regular cells threshold E → E.Nonempty →
      profile (select A) A ≤ K * profile (select A) E →
      ∃ F ⊆ E, F.Nonempty ∧ rule (select A) A E F)
    (A : Finset α) : Nonempty (Decomposition cells threshold K profile rule A) := by
  classical
  induction hb : profileBudget K profile A using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases hA : A = ∅
    · subst A
      exact ⟨⟨[], by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩⟩
    · have hAne := Finset.nonempty_iff_ne_empty.mpr hA
      let i := select A
      let stop := fun E => K * profile i E < profile i A
      let good := fun E F => profile i A ≤ K * profile i E ∧ rule i A E F
      obtain ⟨r⟩ := exists_harvest cells threshold good stop A (by
        intro E hEA hEr hEn hns
        have hactive : profile i A ≤ K * profile i E := Nat.le_of_not_gt hns
        obtain ⟨F, hFE, hFn, hFg⟩ := extract A hAne E hEA hEr hEn hactive
        exact ⟨F, hFE, hFn, hactive, hFg⟩)
      have hdrop : K * profile i r.remainder < profile i A := by
        rcases r.stopped with hz | hs
        · rw [hz, zero, Nat.mul_zero]
          exact positive A hAne
        · exact hs
      have hrank : profileBudget K profile r.remainder < n := by
        rw [← hb]
        exact profileBudget_drop hK profile mono r.remainder_subset i hdrop
      obtain ⟨d⟩ := ih (profileBudget K profile r.remainder) hrank r.remainder rfl
      let e : Epoch α I := ⟨i, A, r.pieces⟩
      refine ⟨⟨e :: d.epochs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact Finset.Subset.refl A
        · exact (d.starts_subset f hf).trans r.remainder_subset
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact ⟨hAne, r.sources⟩
        · exact d.valid f hf
      · intro F hF
        rcases List.mem_append.mp hF with hF | hF
        · exact r.pieces_subset F hF
        · exact (d.pieces_subset F hF).trans r.remainder_subset
      · intro F hF
        rcases List.mem_append.mp hF with hF | hF
        · exact r.pieces_nonempty F hF
        · exact d.pieces_nonempty F hF
      · apply List.pairwise_append.mpr
        refine ⟨r.pairwise, d.pairwise, ?_⟩
        intro F hF G hG
        exact (r.remainder_disjoint F hF).symm.mono_right (d.pieces_subset G hG)
      · have hr := r.accounting
        have hd := d.accounting
        simp only [allPieces_cons, mass_append]
        change A.card ≤ mass r.pieces + mass (allPieces d.epochs) + penalty cells threshold A
        omega
      · have hd := d.epoch_bound
        simp only [List.length_cons]
        rw [hb]
        omega

omit [DecidableEq α] [Fintype I] in
lemma mass_allPieces_le (epochs : List (Epoch α I)) (M : ℕ)
    (h : ∀ e ∈ epochs, mass e.pieces ≤ M) :
    mass (allPieces epochs) ≤ epochs.length * M := by
  induction epochs with
  | nil => simp
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun f hf => h f (by simp [hf]))
    simp only [allPieces_cons, mass_append, List.length_cons]
    nlinarith

/-- Pigeonhole one of the actually constructed epochs. -/
theorem Decomposition.exists_large_epoch
    {cells : C → Finset α} {threshold : C → ℕ} {K : ℕ}
    {profile : I → Finset α → ℕ}
    {rule : I → Finset α → Finset α → Finset α → Prop} {A : Finset α}
    (d : Decomposition cells threshold K profile rule A)
    (hbudget : penalty cells threshold A < A.card) :
    ∃ e ∈ d.epochs,
      A.card ≤ profileBudget K profile A * mass e.pieces + penalty cells threshold A := by
  classical
  have hne : d.epochs.toFinset.Nonempty := by
    by_contra h
    have hz : d.epochs = [] := by simpa using h
    have hc := d.accounting
    simp [hz] at hc
    omega
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image d.epochs.toFinset
    (fun e => mass e.pieces) hne
  refine ⟨e, List.mem_toFinset.mp he, ?_⟩
  have hmass := mass_allPieces_le d.epochs (mass e.pieces)
    (fun f hf => hmax f (List.mem_toFinset.mpr hf))
  have hcount := Nat.mul_le_mul_right (mass e.pieces) d.epoch_bound
  have haccount := d.accounting
  omega

/-- Quantitative disjoint-fiber preparation. The retained mass is charged just one
initial occupied-cell budget, and the divisor is the actual number of profiles
multiplied by a finite power budget B. Each fiber keeps its own original source. -/
theorem exists_large_disjoint_epoch (cells : C → Finset α) (threshold : C → ℕ)
    (K B : ℕ) (hK : 1 < K) (profile : I → Finset α → ℕ)
    (mono : ∀ i, Monotone (profile i))
    (zero : ∀ i, profile i ∅ = 0)
    (select : Finset α → I)
    (positive : ∀ A, A.Nonempty → 0 < profile (select A) A)
    (rule : I → Finset α → Finset α → Finset α → Prop)
    (extract : ∀ A, A.Nonempty → ∀ E ⊆ A, Regular cells threshold E → E.Nonempty →
      profile (select A) A ≤ K * profile (select A) E →
      ∃ F ⊆ E, F.Nonempty ∧ rule (select A) A E F)
    (A : Finset α)
    (hbound : ∀ i, profile i A < K ^ B)
    (hbudget : penalty cells threshold A < A.card) :
    ∃ e : Epoch α I,
      e.start ⊆ A ∧ ValidEpoch cells threshold K profile rule e ∧
      (∀ F ∈ e.pieces, F.Nonempty) ∧ e.pieces.Pairwise Disjoint ∧
      A.card ≤ (Fintype.card I * B) * mass e.pieces + penalty cells threshold A := by
  classical
  obtain ⟨d⟩ := exists_decomposition cells threshold K hK profile mono zero select
    positive rule extract A
  obtain ⟨e, he, hmass⟩ := d.exists_large_epoch hbudget
  have hpieces : ∀ F ∈ e.pieces, F ∈ allPieces d.epochs := by
    intro F hF
    exact List.mem_flatMap.mpr ⟨e, he, hF⟩
  refine ⟨e, d.starts_subset e he, d.valid e he,
    fun F hF => d.pieces_nonempty F (hpieces F hF), ?_, ?_⟩
  · exact (List.pairwise_flatMap.mp d.pairwise).1 e he
  · have hp := profileBudget_le_of_pow_bound profile A hbound
    have hmul := Nat.mul_le_mul_right (mass e.pieces) hp
    omega

/-- The actual retained original points, as a finite union. -/
def support : List (Finset α) → Finset α
  | [] => ∅
  | F :: Fs => F ∪ support Fs

lemma mem_support (Fs : List (Finset α)) (a : α) :
    a ∈ support Fs ↔ ∃ F ∈ Fs, a ∈ F := by
  induction Fs with
  | nil => simp [support]
  | cons F Fs ih => simp [support, ih]

lemma support_subset (Fs : List (Finset α)) (A : Finset α)
    (h : ∀ F ∈ Fs, F ⊆ A) : support Fs ⊆ A := by
  intro a ha
  obtain ⟨F, hF, haF⟩ := (mem_support Fs a).mp ha
  exact h F hF haF

lemma support_card (Fs : List (Finset α)) (h : Fs.Pairwise Disjoint) :
    (support Fs).card = mass Fs := by
  induction Fs with
  | nil => simp [support]
  | cons F Fs ih =>
    obtain ⟨hF, htail⟩ := List.pairwise_cons.mp h
    have hd : Disjoint F (support Fs) := by
      apply Finset.disjoint_left.mpr
      intro a haF has
      obtain ⟨G, hG, haG⟩ := (mem_support Fs a).mp has
      exact Finset.disjoint_left.mp (hF G hG) haF haG
    simp only [support, Finset.card_union_of_disjoint hd, mass_cons, ih htail]

/-- An explicit whole-cell extraction: retain all residual points whose cell has
a witness in the tube population W. -/
noncomputable def wholeCells {β : Type*} (cell : α → β)
    (E W : Finset α) : Finset α := by
  classical
  exact E.filter (fun a => ∃ b ∈ E ∩ W, cell a = cell b)

omit [Fintype C] [Fintype I] in
lemma wholeCells_subset {β : Type*} (cell : α → β) (E W : Finset α) :
    wholeCells cell E W ⊆ E := by
  classical
  exact Finset.filter_subset _ _

omit [Fintype C] [Fintype I] in
lemma inter_subset_wholeCells {β : Type*} (cell : α → β) (E W : Finset α) :
    E ∩ W ⊆ wholeCells cell E W := by
  classical
  intro a ha
  exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp ha).1, a, ha, rfl⟩

omit [Fintype C] [Fintype I] in
lemma wholeCells_nonempty {β : Type*} (cell : α → β) (E W : Finset α)
    (h : (E ∩ W).Nonempty) : (wholeCells cell E W).Nonempty :=
  h.mono (inter_subset_wholeCells cell E W)

omit [Fintype C] [Fintype I] in
lemma wholeCells_full {β : Type*} (cell : α → β) (E W : Finset α)
    {a b : α} (ha : a ∈ wholeCells cell E W) (hb : b ∈ E)
    (heq : cell b = cell a) : b ∈ wholeCells cell E W := by
  classical
  obtain ⟨_, c, hc, hac⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨hb, c, hc, heq.trans hac⟩

/-- For occupied cells, using the natural floor loses at most a factor two in
the real threshold. Nonemptiness supplies the lower bound when the floor is zero. -/
lemma half_real_threshold_le_of_floor_le (x : ℝ) (n : ℕ)
    (hn : 0 < n) (hfloor : ⌊x⌋₊ ≤ n) : x / 2 ≤ (n : ℝ) := by
  have hfloorR : (⌊x⌋₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hfloor
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlt := Nat.lt_floor_add_one x
  linarith

omit [Fintype C] in
lemma Regular.half_real_threshold
    {cells : C → Finset α} {threshold : C → ℝ} {E : Finset α}
    (h : Regular cells (fun c => ⌊threshold c⌋₊) E)
    (c : C) (hc : (population cells E c).Nonempty) :
    threshold c / 2 ≤ ((population cells E c).card : ℝ) :=
  half_real_threshold_le_of_floor_le (threshold c) _ (Finset.card_pos.mpr hc) (h c hc)

/-- Crucially, floor thresholds have no additive cost per occupied cell. -/
lemma penalty_floor_le_real_occupied_budget (cells : C → Finset α)
    (threshold : C → ℝ) (hnonneg : ∀ c, 0 ≤ threshold c) (E : Finset α) :
    (penalty cells (fun c => ⌊threshold c⌋₊) E : ℝ) ≤
      ∑ c : C, if (population cells E c).Nonempty then threshold c else 0 := by
  classical
  unfold penalty
  push_cast
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : (population cells E c).Nonempty
  · simp only [hc, ↓reduceIte]
    exact Nat.floor_le (hnonneg c)
  · simp [hc]

lemma penalty_floor_le_real_total_budget (cells : C → Finset α)
    (threshold : C → ℝ) (hnonneg : ∀ c, 0 ≤ threshold c) (E : Finset α) :
    (penalty cells (fun c => ⌊threshold c⌋₊) E : ℝ) ≤ ∑ c : C, threshold c := by
  classical
  apply (penalty_floor_le_real_occupied_budget cells threshold hnonneg E).trans
  apply Finset.sum_le_sum
  intro c _
  split_ifs
  · exact le_rfl
  · exact hnonneg c

/-- A strict real budget implies the strict integer budget required by the
finite-epoch pigeonhole constructor, without adding a ceiling error. -/
lemma penalty_floor_lt_card_of_real_budget (cells : C → Finset α)
    (threshold : C → ℝ) (hnonneg : ∀ c, 0 ≤ threshold c) (A : Finset α)
    (hbudget : (∑ c : C,
      if (population cells A c).Nonempty then threshold c else 0) < (A.card : ℝ)) :
    penalty cells (fun c => ⌊threshold c⌋₊) A < A.card := by
  classical
  have h := (penalty_floor_le_real_occupied_budget cells threshold hnonneg A).trans_lt hbudget
  exact_mod_cast h

/-- The constructed disjoint family retains all but one original real threshold
budget when pruning is performed with natural floors. -/
theorem Decomposition.accounting_real_floor
    {cells : C → Finset α} {threshold : C → ℝ} {K : ℕ}
    {profile : I → Finset α → ℕ}
    {rule : I → Finset α → Finset α → Finset α → Prop} {A : Finset α}
    (d : Decomposition cells (fun c => ⌊threshold c⌋₊) K profile rule A)
    (hnonneg : ∀ c, 0 ≤ threshold c) :
    (A.card : ℝ) ≤ (mass (allPieces d.epochs) : ℝ) +
      ∑ c : C, if (population cells A c).Nonempty then threshold c else 0 := by
  classical
  have hc : (A.card : ℝ) ≤ (mass (allPieces d.epochs) : ℝ) +
      (penalty cells (fun c => ⌊threshold c⌋₊) A : ℝ) := by
    exact_mod_cast d.accounting
  have hp := penalty_floor_le_real_occupied_budget cells threshold hnonneg A
  linarith

end DisjointProfileEpochs
