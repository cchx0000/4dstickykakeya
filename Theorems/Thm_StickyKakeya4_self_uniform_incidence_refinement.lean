import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

namespace SelfUniform

open scoped Classical

noncomputable def mass {α : Type*} (w : α → ℕ) (A : Finset α) : ℕ :=
  ∑ x ∈ A, w x

noncomputable def degree {α : Type*} (w : α → ℕ) (R : α → α → Prop)
    (A : Finset α) (x : α) : ℕ := by
  classical
  exact ∑ y ∈ A, if R x y then w y else 0

noncomputable def energy {α : Type*} (w : α → ℕ) (R : α → α → Prop)
    (A : Finset α) : ℕ := ∑ x ∈ A, w x * degree w R A x

variable {α : Type*}

lemma mass_mono (w : α → ℕ) {A B : Finset α} (h : A ⊆ B) :
    mass w A ≤ mass w B := Finset.sum_le_sum_of_subset h

lemma degree_mono (w : α → ℕ) (R : α → α → Prop) {A B : Finset α}
    (h : A ⊆ B) (x : α) : degree w R A x ≤ degree w R B x := by
  classical
  exact Finset.sum_le_sum_of_subset h

lemma weight_le_degree (w : α → ℕ) (R : α → α → Prop) (hR : ∀ x, R x x)
    {A : Finset α} {x : α} (hx : x ∈ A) : w x ≤ degree w R A x := by
  classical
  simpa [degree, hR] using
    (Finset.single_le_sum (f := fun y => if R x y then w y else 0)
      (fun y _ => Nat.zero_le _) hx)

lemma degree_le_mass (w : α → ℕ) (R : α → α → Prop) (A : Finset α) (x : α) :
    degree w R A x ≤ mass w A := by
  classical
  exact Finset.sum_le_sum (fun y _ => by split <;> omega)

lemma mass_insert (w : α → ℕ) {A : Finset α} {x : α} (hx : x ∉ A) :
    mass w (insert x A) = w x + mass w A := by
  classical
  exact Finset.sum_insert hx

lemma degree_insert (w : α → ℕ) (R : α → α → Prop)
    {A : Finset α} {x : α} (hx : x ∉ A) (y : α) :
    degree w R (insert x A) y = (if R y x then w x else 0) + degree w R A y := by
  classical
  exact Finset.sum_insert hx

lemma energy_insert_le (w : α → ℕ) (R : α → α → Prop)
    (hsym : ∀ x y, R x y → R y x) {A S : Finset α} {x : α}
    (hx : x ∉ S) (hS : S ⊆ A) (hxa : x ∈ A) :
    energy w R (insert x S) ≤ energy w R S + 2 * w x * degree w R A x := by
  classical
  have hdegree : degree w R (insert x S) x ≤ degree w R A x :=
    degree_mono w R (Finset.insert_subset hxa hS) x
  have hcross : (∑ y ∈ S, w y * (if R y x then w x else 0)) =
      w x * degree w R S x := by
    rw [degree, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : R y x
    · have h' := hsym y x h
      simp [h, h', Nat.mul_comm]
    · have h' : ¬ R x y := fun hh => h (hsym x y hh)
      simp [h, h']
  calc
    energy w R (insert x S) =
        w x * degree w R (insert x S) x +
          (∑ y ∈ S, w y * degree w R (insert x S) y) := by
      exact Finset.sum_insert hx
    _ = w x * degree w R (insert x S) x +
          ((∑ y ∈ S, w y * (if R y x then w x else 0)) + energy w R S) := by
      simp only [degree_insert w R hx, Nat.mul_add, Finset.sum_add_distrib, energy]
    _ ≤ w x * degree w R A x + (w x * degree w R A x + energy w R S) := by
      rw [hcross]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hdegree)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (degree_mono w R hS x)) _)
    _ = energy w R S + 2 * w x * degree w R A x := by ring

/-- Simultaneous weighted peeling. Vertices removed for each color have small
weighted induced energy, including the diagonal. -/
theorem peeling_decomposition {d : ℕ} (w : α → ℕ)
    (R : Fin d → α → α → Prop) (hrefl : ∀ i x, R i x x)
    (hsym : ∀ i x y, R i x y → R i y x) (m : Fin d → ℕ)
    (A : Finset α) (hw : ∀ x ∈ A, 0 < w x) :
    ∃ K : Finset α, ∃ E : Fin d → Finset α,
      K ⊆ A ∧ (∀ i, E i ⊆ A) ∧
      (∀ i x, x ∈ K → m i ≤ degree w (R i) K x) ∧
      mass w A = mass w K + ∑ i, mass w (E i) ∧
      (∀ i, energy w (R i) (E i) ≤ 2 * m i * mass w (E i)) ∧
      (∀ i, (E i).Nonempty → 1 < m i) := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hgood : ∀ i x, x ∈ A → m i ≤ degree w (R i) A x
    · refine ⟨A, fun _ => ∅, Finset.Subset.refl _, ?_, hgood, ?_, ?_, ?_⟩
      · simp
      · simp [mass]
      · simp [energy, mass]
      · simp
    · push Not at hgood
      obtain ⟨i, x, hx, hbad⟩ := hgood
      obtain ⟨K, E, hKA, hEA, hmin, hmass, hen, hnon⟩ :=
        ih (A.erase x) (Finset.erase_ssubset hx)
          (fun y hy => hw y (Finset.mem_of_mem_erase hy))
      have hxE : ∀ j, x ∉ E j := by
        intro j hj
        exact (Finset.mem_erase.mp (hEA j hj)).1 rfl
      have hA : A = insert x (A.erase x) := (Finset.insert_erase hx).symm
      have hm : 1 < m i := by
        have hself := weight_le_degree w (R i) (hrefl i) hx
        have hp := hw x hx
        omega
      let E' : Fin d → Finset α := fun j => if j = i then insert x (E j) else E j
      have hmassE : (∑ j, mass w (E' j)) = w x + ∑ j, mass w (E j) := by
        have hid : ∀ j, mass w (E' j) = (if j = i then w x else 0) + mass w (E j) := by
          intro j
          dsimp [E']
          split_ifs with hj
          · exact mass_insert w (hxE j)
          · simp
        simp only [hid, Finset.sum_add_distrib]
        simp
      refine ⟨K, E', hKA.trans (Finset.erase_subset x A), ?_, hmin, ?_, ?_, ?_⟩
      · intro j
        dsimp [E']
        split_ifs
        · exact Finset.insert_subset hx ((hEA j).trans (Finset.erase_subset x A))
        · exact (hEA j).trans (Finset.erase_subset x A)
      · rw [hmassE]
        have hxA : x ∉ A.erase x := Finset.notMem_erase x A
        have hmassA : mass w A = w x + mass w (A.erase x) := by
          conv_lhs => rw [hA]
          exact mass_insert w hxA
        omega
      · intro j
        dsimp [E']
        split_ifs with hj
        · subst j
          have hener := energy_insert_le w (R i) (hsym i) (hxE i)
            ((hEA i).trans (Finset.erase_subset x A)) hx
          have hmul := Nat.mul_le_mul_left (2 * w x) (Nat.le_of_lt hbad)
          rw [mass_insert w (hxE i)]
          nlinarith [hen i]
        · exact hen j
      · intro j hj
        dsimp [E'] at hj
        split_ifs at hj with hji
        · simpa [hji] using hm
        · exact hnon j hj

/-- Weighted Markov extraction: half the mass has degree at most four times
an upper bound for half the weighted average degree. -/
theorem weighted_markov_extraction {α : Type*} (w : α → ℕ)
    (R : α → α → Prop) (A : Finset α) (m : ℕ) (hm : 0 < m)
    (henergy : energy w R A ≤ 2 * m * mass w A) :
    ∃ G ⊆ A, mass w A ≤ 2 * mass w G ∧
      ∀ x ∈ G, degree w R A x ≤ 4 * m := by
  classical
  let G := A.filter (fun x => degree w R A x ≤ 4 * m)
  let B := A.filter (fun x => ¬ degree w R A x ≤ 4 * m)
  have hsplit : mass w G + mass w B = mass w A := by
    simpa only [mass, G, B] using
      Finset.sum_filter_add_sum_filter_not A (fun x => degree w R A x ≤ 4 * m) w
  have hBsub : B ⊆ A := Finset.filter_subset _ _
  have hBlower : 4 * m * mass w B ≤ energy w R A := by
    calc
      4 * m * mass w B = ∑ x ∈ B, w x * (4 * m) := by
        simp only [mass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        exact Nat.mul_comm _ _
      _ ≤ ∑ x ∈ B, w x * degree w R A x := by
        apply Finset.sum_le_sum
        intro x hx
        have hxdegree : ¬ degree w R A x ≤ 4 * m := (Finset.mem_filter.mp hx).2
        exact Nat.mul_le_mul_left (w x) (by omega)
      _ ≤ energy w R A := by
        unfold energy
        exact Finset.sum_le_sum_of_subset_of_nonneg hBsub (by intros; omega)
  refine ⟨G, Finset.filter_subset _ _, ?_, ?_⟩
  · nlinarith
  · intro x hx
    exact (Finset.mem_filter.mp hx).2


lemma mass_pos (w : α → ℕ) {A : Finset α} (hne : A.Nonempty)
    (hw : ∀ x ∈ A, 0 < w x) : 0 < mass w A := by
  obtain ⟨x, hx⟩ := hne
  exact (hw x hx).trans_le (Finset.single_le_sum (fun y _ => Nat.zero_le (w y)) hx)

lemma nonempty_of_mass_pos (w : α → ℕ) {A : Finset α} (h : 0 < mass w A) :
    A.Nonempty := by
  by_contra hn
  simp [Finset.not_nonempty_iff_eq_empty.mp hn, mass] at h

/-- Either peeling keeps half the mass with all required minimum degrees, or
one color admits a quarter-over-dimension mass refinement of small degree. -/
theorem peeling_dichotomy {d : ℕ} (hd : 0 < d) (w : α → ℕ)
    (R : Fin d → α → α → Prop) (hrefl : ∀ i x, R i x x)
    (hsym : ∀ i x y, R i x y → R i y x) (m : Fin d → ℕ)
    (A : Finset α) (hne : A.Nonempty) (hw : ∀ x ∈ A, 0 < w x) :
    (∃ K ⊆ A, K.Nonempty ∧ mass w A ≤ 2 * mass w K ∧
      ∀ i x, x ∈ K → m i ≤ degree w (R i) K x) ∨
    (∃ i, ∃ G ⊆ A, G.Nonempty ∧ mass w A ≤ 4 * d * mass w G ∧
      1 < m i ∧ ∀ x ∈ G, degree w (R i) G x ≤ 4 * m i) := by
  classical
  obtain ⟨K, E, hK, hE, hmin, hmass, henergy, hnon⟩ :=
    peeling_decomposition w R hrefl hsym m A hw
  have hpos := mass_pos w hne hw
  by_cases hhalf : mass w A ≤ 2 * mass w K
  · exact Or.inl ⟨K, hK, nonempty_of_mass_pos w (by omega), hhalf, hmin⟩
  · obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
      (fun j : Fin d => mass w (E j)) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    have hsum : (∑ j, mass w (E j)) ≤ d * mass w (E i) := by
      calc
        (∑ j, mass w (E j)) ≤ ∑ _j : Fin d, mass w (E i) :=
          Finset.sum_le_sum (fun j hj => hmax j hj)
        _ = d * mass w (E i) := by simp
    have hEi : (E i).Nonempty := nonempty_of_mass_pos w (by nlinarith)
    have hm := hnon i hEi
    obtain ⟨G, hG, hGmass, hGdegree⟩ := weighted_markov_extraction w (R i) (E i)
      (m i) (by omega) (henergy i)
    have hret : mass w A ≤ 4 * d * mass w G := by nlinarith
    refine Or.inr ⟨i, G, hG.trans (hE i), nonempty_of_mass_pos w (by nlinarith),
      hret, hm, ?_⟩
    intro x hx
    exact (degree_mono w (R i) hG x).trans (hGdegree x hx)

lemma height_ge_three_of_threshold_gt_one {Q h : ℕ} (hh : 1 < Q ^ (h - 2)) :
    3 ≤ h := by
  by_contra hsmall
  have hz : h - 2 = 0 := by omega
  simp [hz] at hh

lemma threshold_drop_bound {Q h : ℕ} (hQ : 4 ≤ Q) (hh : 3 ≤ h) :
    4 * Q ^ (h - 2) ≤ Q ^ (h - 1) := by
  have hexp : h - 1 = h - 2 + 1 := by omega
  rw [hexp, pow_succ, Nat.mul_comm (Q ^ (h - 2)) Q]
  exact Nat.mul_le_mul_right _ hQ

lemma height_upper_bound {Q h : ℕ} (hQ : 1 ≤ Q) :
    Q ^ h ≤ Q ^ 2 * Q ^ (h - 2) := by
  rw [← pow_add]
  exact Nat.pow_le_pow_right hQ (by omega)

lemma sum_height_update {d : ℕ} (h : Fin d → ℕ) (i : Fin d)
    (hi : 0 < h i) :
    (∑ j, Function.update h i (h i - 1) j) + 1 = ∑ j, h j := by
  classical
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ h (Finset.mem_univ i)
  omega


/-- Quantitative simultaneous self-uniform refinement, with one unit of height
charged for each unsuccessful peeling round. All degrees in the conclusion
are counted inside the retained set itself. -/
theorem self_uniform_of_heights {d Q : ℕ} (hd : 0 < d) (hQ : 4 ≤ Q)
    (w : α → ℕ) (R : Fin d → α → α → Prop)
    (hrefl : ∀ i x, R i x x) (hsym : ∀ i x y, R i x y → R i y x)
    (n : ℕ) :
    ∀ (A : Finset α) (h : Fin d → ℕ), A.Nonempty →
      (∀ x ∈ A, 0 < w x) → (∑ i, h i) = n →
      (∀ i x, x ∈ A → degree w (R i) A x ≤ Q ^ h i) →
      ∃ B ⊆ A, B.Nonempty ∧
        mass w A ≤ 2 * (4 * d) ^ n * mass w B ∧
        ∀ i x y, x ∈ B → y ∈ B →
          degree w (R i) B x ≤ Q ^ 2 * degree w (R i) B y := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A h hne hw hsum hmax
    obtain hcore | hdrop := peeling_dichotomy hd w R hrefl hsym
      (fun i => Q ^ (h i - 2)) A hne hw
    · obtain ⟨K, hK, hKne, hhalf, hmin⟩ := hcore
      refine ⟨K, hK, hKne, ?_, ?_⟩
      · have hp : 0 < (4 * d) ^ n := pow_pos (by omega) _
        nlinarith
      · intro i x y hx hy
        calc
          degree w (R i) K x ≤ degree w (R i) A x := degree_mono w (R i) hK x
          _ ≤ Q ^ h i := hmax i x (hK hx)
          _ ≤ Q ^ 2 * Q ^ (h i - 2) := height_upper_bound (by omega)
          _ ≤ Q ^ 2 * degree w (R i) K y := Nat.mul_le_mul_left _ (hmin i y hy)
    · obtain ⟨i, G, hG, hGne, hret, hthreshold, hsmall⟩ := hdrop
      have hlarge : 3 ≤ h i := height_ge_three_of_threshold_gt_one hthreshold
      let h' : Fin d → ℕ := Function.update h i (h i - 1)
      have hsum' : (∑ j, h' j) + 1 = n := by
        rw [← hsum]
        exact sum_height_update h i (by omega)
      have hmax' : ∀ j x, x ∈ G → degree w (R j) G x ≤ Q ^ h' j := by
        intro j x hx
        by_cases hji : j = i
        · subst j
          simpa [h'] using (hsmall x hx).trans (threshold_drop_bound hQ hlarge)
        · have hbound := (degree_mono w (R j) hG x).trans (hmax j x (hG hx))
          simpa [h', hji] using hbound
      obtain ⟨B, hB, hBne, hBmass, hBuniform⟩ :=
        ih (∑ j, h' j) (by omega) G h' hGne (fun x hx => hw x (hG hx)) rfl hmax'
      refine ⟨B, hB.trans hG, hBne, ?_, hBuniform⟩
      calc
        mass w A ≤ 4 * d * mass w G := hret
        _ ≤ 4 * d * (2 * (4 * d) ^ (∑ j, h' j) * mass w B) :=
          Nat.mul_le_mul_left _ hBmass
        _ = 2 * (4 * d) ^ n * mass w B := by
          rw [← hsum', pow_succ]
          ring

/-- A finite weighted self-uniform refinement for finitely many symmetric,
reflexive incidence relations. The loss is exponential in the logarithmic
height bound, rather than in the number of vertices or the total weight. -/
theorem weighted_self_uniform_refinement {d Q L : ℕ}
    (hd : 0 < d) (hQ : 4 ≤ Q) (w : α → ℕ)
    (R : Fin d → α → α → Prop) (hrefl : ∀ i x, R i x x)
    (hsym : ∀ i x y, R i x y → R i y x)
    (A : Finset α) (hne : A.Nonempty) (hw : ∀ x ∈ A, 0 < w x)
    (hheight : mass w A ≤ Q ^ L) :
    ∃ B ⊆ A, B.Nonempty ∧
      mass w A ≤ 2 * (4 * d) ^ (d * L) * mass w B ∧
      ∀ i x y, x ∈ B → y ∈ B →
        degree w (R i) B x ≤ Q ^ 2 * degree w (R i) B y := by
  apply self_uniform_of_heights hd hQ w R hrefl hsym (d * L) A (fun _ => L) hne hw
  · simp
  · intro i x _hx
    exact (degree_le_mass w (R i) A x).trans hheight

end SelfUniform
