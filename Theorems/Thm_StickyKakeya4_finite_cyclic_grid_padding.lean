import Mathlib
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators
namespace FiniteCyclicGridPadding

/-- The residue of an integer-offset cyclic translation; negative offsets are allowed. -/
noncomputable def residue {N P : ℕ} (hPN : P ∣ N) (b : ℤ) (q : ZMod N) : ZMod P :=
  (b : ZMod P) + ZMod.castHom hPN (ZMod P) q

theorem cast_fiber_card {N P : ℕ} [NeZero N] [NeZero P] (hPN : P ∣ N)
    (x : ZMod P) :
    (Finset.univ.filter (fun q : ZMod N => ZMod.castHom hPN (ZMod P) q = x)).card = N / P := by
  classical
  let f := ZMod.castHom hPN (ZMod P)
  let c := (Finset.univ.filter (fun q : ZMod N => f q = 0)).card
  have hf (y : ZMod P) : (Finset.univ.filter (fun q : ZMod N => f q = y)).card = c :=
    AddMonoidHom.card_fiber_eq_of_mem_range f
      (ZMod.castHom_surjective hPN y) (ZMod.castHom_surjective hPN 0)
  have ht : N = P * c := by
    have hh := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (ZMod N)) (Finset.univ : Finset (ZMod P)) f
    simpa only [hf, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul,
      Finset.mem_univ, Finset.filter_true] using hh.symm
  change (Finset.univ.filter (fun q : ZMod N => f q = x)).card = N / P
  rw [hf, ht, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne P))]

theorem residue_fiber_card {N P : ℕ} [NeZero N] [NeZero P] (hPN : P ∣ N)
    (b : ℤ) (x : ZMod P) :
    (Finset.univ.filter (fun q : ZMod N => residue hPN b q = x)).card = N / P := by
  classical
  simp only [residue, add_comm (b : ZMod P), ← eq_sub_iff_add_eq]
  exact cast_fiber_card hPN (x - (b : ZMod P))

theorem residue_preimage_card {N P : ℕ} [NeZero N] [NeZero P] (hPN : P ∣ N)
    (b : ℤ) (E : Finset (ZMod P)) :
    (Finset.univ.filter (fun q : ZMod N => residue hPN b q ∈ E)).card = E.card * (N / P) := by
  classical
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  simp [residue_fiber_card]

theorem residue_val_eq {N P : ℕ} [NeZero N] [NeZero P] (hPN : P ∣ N)
    (b : ℤ) (q : ZMod N) :
    ((residue hPN b q).val : ℤ) = (b + (q.val : ℤ)) % (P : ℤ) := by
  have hf : ZMod.castHom hPN (ZMod P) q = (q.val : ZMod P) := by
    calc
      ZMod.castHom hPN (ZMod P) q =
          ZMod.castHom hPN (ZMod P) (q.val : ZMod N) :=
        congrArg (ZMod.castHom hPN (ZMod P)) (ZMod.natCast_zmod_val q).symm
      _ = _ := map_natCast _ _
  rw [residue, hf, ← Int.cast_natCast q.val, ← Int.cast_add, ZMod.val_intCast]


/-- At most the interval length many residues have values in a natural interval. -/
theorem card_residue_interval_le (P L U : ℕ) [NeZero P] :
    (Finset.univ.filter (fun x : ZMod P => L ≤ x.val ∧ x.val < U)).card ≤ U - L := by
  classical
  calc
    _ ≤ (Finset.Ico L U).card := Finset.card_le_card_of_injOn ZMod.val
      (fun x hx => Finset.mem_Ico.2 (Finset.mem_filter.1 hx).2)
      (ZMod.val_injective P).injOn
    _ = _ := Nat.card_Ico _ _

noncomputable def badResidues (H R : ℕ) [NeZero (H * R)] : Finset (ZMod (H * R)) :=
  Finset.univ.filter (fun x => x.val < 4 * R ∨ (H - 4) * R ≤ x.val)

theorem badResidues_card_le (H R : ℕ) [NeZero (H * R)] (hH : 4 ≤ H) :
    (badResidues H R).card ≤ 8 * R := by
  classical
  have hlo : (Finset.univ.filter (fun x : ZMod (H * R) => x.val < 4 * R)).card ≤ 4 * R := by
    simpa using card_residue_interval_le (H * R) 0 (4 * R)
  have hhi : (Finset.univ.filter (fun x : ZMod (H * R) => (H - 4) * R ≤ x.val)).card ≤ 4 * R := by
    have hi := card_residue_interval_le (H * R) ((H - 4) * R) (H * R)
    have he : H * R - (H - 4) * R = 4 * R := by
      rw [Nat.sub_mul, Nat.sub_sub_self (Nat.mul_le_mul_right R hH)]
    simpa only [ZMod.val_lt, and_true, he] using hi
  calc
    (badResidues H R).card ≤
        (Finset.univ.filter (fun x : ZMod (H * R) => x.val < 4 * R)).card +
        (Finset.univ.filter (fun x : ZMod (H * R) => (H - 4) * R ≤ x.val)).card := by
      rw [badResidues, Finset.filter_or]
      exact Finset.card_union_le _ _
    _ ≤ 4 * R + 4 * R := Nat.add_le_add hlo hhi
    _ = 8 * R := by omega

/-- A bad boundary strip contains at most an 8/H fraction of the shifts. -/
theorem bad_shift_card_mul_le {N H R : ℕ} [NeZero N] [NeZero H] [NeZero R]
    (hPN : H * R ∣ N) (hH : 4 ≤ H) (b : ℤ) :
    (Finset.univ.filter (fun q : ZMod N => residue hPN b q ∈ badResidues H R)).card * H
      ≤ 8 * N := by
  have hmul : (N / (H * R)) * (H * R) = N := Nat.div_mul_cancel hPN
  rw [residue_preimage_card]
  have hc := Nat.mul_le_mul_right ((N / (H * R)) * H) (badResidues_card_le H R hH)
  calc
    (badResidues H R).card * (N / (H * R)) * H =
        (badResidues H R).card * ((N / (H * R)) * H) := by ring
    _ ≤ 8 * R * ((N / (H * R)) * H) := hc
    _ = 8 * N := by nlinarith [hmul]


/-- Weighted finite averaging retains actual old labels, with their old integer weights. -/
theorem finite_weighted_avoid {α Q : Type*} [Fintype Q] [Nonempty Q]
    (A : Finset α) (w : α → ℕ) (E : α → Finset Q)
    (hE : ∀ a ∈ A, 2 * (E a).card ≤ Fintype.card Q) :
    ∃ q : Q, ∃ B : Finset α, B ⊆ A ∧
      (∑ a ∈ A, w a) ≤ 2 * (∑ a ∈ B, w a) ∧ ∀ a ∈ B, q ∉ E a := by
  classical
  let loss : Q → ℕ := fun q => ∑ a ∈ A, if q ∈ E a then w a else 0
  have hsum : ∑ q, loss q = ∑ a ∈ A, (E a).card * w a := by
    dsimp [loss]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    simp
  have havg : (∑ q : Q, 2 * loss q) ≤ ∑ _q : Q, ∑ a ∈ A, w a := by
    rw [← Finset.mul_sum, hsum, Finset.mul_sum]
    calc
      (∑ a ∈ A, 2 * ((E a).card * w a)) ≤ ∑ a ∈ A, Fintype.card Q * w a := by
        apply Finset.sum_le_sum
        intro a ha
        simpa only [mul_assoc] using Nat.mul_le_mul_right (w a) (hE a ha)
      _ = _ := by simp [← Finset.mul_sum]
  obtain ⟨q, _, hq⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty havg
  let B := A.filter (fun a => q ∉ E a)
  have hpart : loss q + ∑ a ∈ B, w a = ∑ a ∈ A, w a := by
    simpa [loss, B, Finset.sum_filter] using
      Finset.sum_filter_add_sum_filter_not A (fun a => q ∈ E a) w
  refine ⟨q, B, Finset.filter_subset _ _, by omega, ?_⟩
  intro a ha
  exact (Finset.mem_filter.1 ha).2

/-- Finite union bound expressed without division. -/
theorem card_biUnion_mul_le {Q τ : Type*} [DecidableEq Q] [Fintype τ]
    (E : τ → Finset Q) (H K : ℕ) (hE : ∀ t, (E t).card * H ≤ K) :
    (Finset.univ.biUnion E).card * H ≤ Fintype.card τ * K := by
  classical
  calc
    _ ≤ (∑ t, (E t).card) * H := Nat.mul_le_mul_right H Finset.card_biUnion_le
    _ = ∑ t, (E t).card * H := Finset.sum_mul _ _ _
    _ ≤ ∑ _t : τ, K := Finset.sum_le_sum fun t _ => hE t
    _ = _ := by simp


/-- A common finite-mesh shift pads every retained original label at every scale. -/
theorem cyclic_translation {α τ : Type*} [Fintype τ]
    (N H : ℕ) (hN : 0 < N) (hH : 4 ≤ H)
    (A : Finset α) (w : α → ℕ) (b : α → τ → ℤ) (R : τ → ℕ)
    (hR : ∀ t, 0 < R t) (hdiv : ∀ t, H * R t ∣ N)
    (hsize : 16 * Fintype.card τ ≤ H) :
    ∃ q : Fin N, ∃ B : Finset α, B ⊆ A ∧
      (∑ a ∈ A, w a) ≤ 2 * (∑ a ∈ B, w a) ∧
      ∀ a ∈ B, ∀ t : τ,
        4 * (R t : ℤ) ≤ (b a t + (q.val : ℤ)) % (H * R t : ℕ) ∧
        (b a t + (q.val : ℤ)) % (H * R t : ℕ) < ((H - 4) * R t : ℕ) := by
  classical
  have hHpos : 0 < H := by omega
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have : NeZero H := ⟨Nat.ne_of_gt hHpos⟩
  have (t : τ) : NeZero (R t) := ⟨Nat.ne_of_gt (hR t)⟩
  let E : α → τ → Finset (ZMod N) := fun a t =>
    Finset.univ.filter (fun q => residue (hdiv t) (b a t) q ∈ badResidues H (R t))
  let F : α → Finset (ZMod N) := fun a => Finset.univ.biUnion (E a)
  have hF (a : α) : 2 * (F a).card ≤ Fintype.card (ZMod N) := by
    rw [ZMod.card]
    have hu : (F a).card * H ≤ Fintype.card τ * (8 * N) :=
      card_biUnion_mul_le (E a) H (8 * N)
        (fun t => bad_shift_card_mul_le (hdiv t) hH (b a t))
    apply le_of_mul_le_mul_right (a := H) _ hHpos
    calc
      (2 * (F a).card) * H ≤ 2 * (Fintype.card τ * (8 * N)) := by nlinarith [hu]
      _ = (16 * Fintype.card τ) * N := by ring
      _ ≤ H * N := Nat.mul_le_mul_right N hsize
      _ = N * H := Nat.mul_comm _ _
  obtain ⟨q, B, hBA, hw, havoid⟩ := finite_weighted_avoid A w F (fun a _ => hF a)
  refine ⟨⟨q.val, ZMod.val_lt q⟩, B, hBA, hw, ?_⟩
  intro a ha t
  have hnot : residue (hdiv t) (b a t) q ∉ badResidues H (R t) := by
    intro he
    exact havoid a ha (Finset.mem_biUnion.2
      ⟨t, Finset.mem_univ t, Finset.mem_filter.2 ⟨Finset.mem_univ q, he⟩⟩)
  have hgood : 4 * R t ≤ (residue (hdiv t) (b a t) q).val ∧
      (residue (hdiv t) (b a t) q).val < (H - 4) * R t := by
    simpa [badResidues, not_or, not_lt, not_le] using hnot
  change 4 * (R t : ℤ) ≤ (b a t + (q.val : ℤ)) % (H * R t : ℕ) ∧
    (b a t + (q.val : ℤ)) % (H * R t : ℕ) < ((H - 4) * R t : ℕ)
  rw [← residue_val_eq (hdiv t) (b a t) q]
  exact_mod_cast hgood

/-- Diagonal translation by q fine-grid units, simultaneously in all coordinates. -/
theorem cyclic_vector_translation {α : Type*} (r m N H : ℕ)
    (hN : 0 < N) (hH : 4 ≤ H)
    (A : Finset α) (w : α → ℕ) (b : α → Fin r → ℤ) (R : Fin m → ℕ)
    (hR : ∀ j, 0 < R j) (hdiv : ∀ j, H * R j ∣ N)
    (hsize : 16 * r * m ≤ H) :
    ∃ q : Fin N, ∃ B : Finset α, B ⊆ A ∧
      (∑ a ∈ A, w a) ≤ 2 * (∑ a ∈ B, w a) ∧
      ∀ a ∈ B, ∀ i : Fin r, ∀ j : Fin m,
        4 * (R j : ℤ) ≤ (b a i + (q.val : ℤ)) % (H * R j : ℕ) ∧
        (b a i + (q.val : ℤ)) % (H * R j : ℕ) < ((H - 4) * R j : ℕ) := by
  obtain ⟨q, B, hBA, hw, hpad⟩ := cyclic_translation (τ := Fin r × Fin m)
    N H hN hH A w (fun a t => b a t.1) (fun t => R t.2)
    (fun t => hR t.2) (fun t => hdiv t.2) (by simpa [mul_assoc] using hsize)
  exact ⟨q, B, hBA, hw, fun a ha i j => hpad a ha (i, j)⟩

end FiniteCyclicGridPadding
